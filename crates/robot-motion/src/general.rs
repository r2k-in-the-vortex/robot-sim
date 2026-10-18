//! General boundary conditions: stop, rest-to-rest move, start.
//!
//! This is a feasibility-first decomposition, not a time-optimal general planner. A
//! state is viable when its acceleration can be brought to zero without the velocity
//! leaving the band (`stop_feasible`). The planner then brakes to rest, uses the verified
//! conservative rest-to-rest planner for the middle, and time-reverses a stop profile to
//! reach the target. `None`/`Infeasible` is exact for this decomposition; it is not a
//! global infeasibility certificate — a direct profile that never passes through rest can
//! exist outside the viability predicate.

use crate::conservative::plan_rest_conservative;
use crate::error::{PlanError, ProfileError};
use crate::math::sqrt;
use crate::profile::{Limits, MAX_PHASES, PlanKind, Profile, Segment, State};

/// Reverse velocity, keep position and acceleration.
pub fn rev(state: State<f64>) -> State<f64> {
    State::new(state.q, -state.v, state.a)
}

/// Whether the state can be brought to rest without leaving the velocity band.
///
/// `v_s = v + a|a|/(2J)` is the velocity after the fastest legal acceleration-removal
/// ramp. That ramp is unavoidable, so `|v_s| > V` means this decomposition cannot stop.
pub fn stop_feasible(state: State<f64>, lim: Limits<f64>) -> bool {
    if !state.is_finite() {
        return false;
    }
    let j = lim.jmax();
    let vs = state.v + state.a * state.a.abs() / (2.0 * j);
    state.a.abs() <= lim.amax() && state.v.abs() <= lim.vmax() && vs.abs() <= lim.vmax()
}

/// The exact viability predicate of the stop–move–start decomposition.
pub fn viable(s0: State<f64>, s1: State<f64>, lim: Limits<f64>) -> bool {
    stop_feasible(s0, lim) && stop_feasible(rev(s1), lim)
}

/// A feasible profile from `state` to rest, or `Infeasible`.
pub fn stop_profile(state: State<f64>, lim: Limits<f64>) -> Result<Profile<f64>, PlanError> {
    if !state.is_finite() {
        return Err(PlanError::NonFiniteInput);
    }
    if !stop_feasible(state, lim) {
        return Err(PlanError::Infeasible);
    }

    let zero = 0.0;
    let jmax = lim.jmax();
    let mut segments = [Segment {
        dur: zero,
        jerk: zero,
    }; MAX_PHASES];
    let mut len = 0usize;
    let mut current = state;

    if current.a != zero {
        let dur = current.a.abs() / jmax;
        let jerk = if current.a > zero { -jmax } else { jmax };
        segments[len] = Segment { dur, jerk };
        len += 1;
        current = current.advance(jerk, dur);
    }

    brake(current.v, lim, &mut segments, &mut len)?;

    Profile::from_parts_with_kind(state, &segments[..len], PlanKind::General)
        .map_err(map_profile_error)
}

/// A profile from rest to `target`, the time reversal of a stop.
pub fn start_profile(target: State<f64>, lim: Limits<f64>) -> Result<Profile<f64>, PlanError> {
    Ok(stop_profile(rev(target), lim)?.reverse())
}

/// General boundary-condition planner: stop, move, start.
pub fn plan_general(
    s0: State<f64>,
    s1: State<f64>,
    lim: Limits<f64>,
) -> Result<Profile<f64>, PlanError> {
    if !s0.is_finite() || !s1.is_finite() {
        return Err(PlanError::NonFiniteInput);
    }
    if !viable(s0, s1, lim) {
        return Err(PlanError::Infeasible);
    }

    let stop = stop_profile(s0, lim)?;
    let start = start_profile(s1, lim)?;
    let middle = plan_rest_conservative(stop.end().q, start.start().q, lim)?;

    // Concatenate the segment lists directly. The profiles join at rest states, so the
    // relative motion is what matters; this avoids an exact float equality check on the
    // intermediate junction positions (the exact-q check belongs to `Profile::append`
    // and is used by exact-rational callers/tests).
    let mut segments = [Segment {
        dur: 0.0,
        jerk: 0.0,
    }; MAX_PHASES];
    let mut len = 0usize;
    for profile in [&stop, &middle, &start] {
        for seg in profile.segments() {
            if len == MAX_PHASES {
                return Err(PlanError::ProfileOverflow);
            }
            segments[len] = *seg;
            len += 1;
        }
    }
    Profile::from_parts_with_kind(s0, &segments[..len], PlanKind::General)
        .map_err(map_profile_error)
}

/// Append the brake phases from velocity `v` to rest.
fn brake(
    v: f64,
    lim: Limits<f64>,
    segments: &mut [Segment<f64>; MAX_PHASES],
    len: &mut usize,
) -> Result<(), PlanError> {
    let zero = 0.0;
    let jmax = lim.jmax();
    let amax = lim.amax();
    let vmax = lim.vmax();
    if !v.is_finite() || v.abs() > vmax {
        return Err(PlanError::Infeasible);
    }
    if v == zero {
        return Ok(());
    }

    let sign = if v < zero { -1.0 } else { 1.0 };
    let speed = v.abs();
    let v_a = amax * amax / jmax;
    let t_j = amax / jmax;
    let mut push = |dur: f64, jerk: f64| -> Result<(), PlanError> {
        if !dur.is_finite() || !jerk.is_finite() || dur < zero {
            return Err(PlanError::NumericalFailure);
        }
        if *len == MAX_PHASES {
            return Err(PlanError::ProfileOverflow);
        }
        segments[*len] = Segment { dur, jerk };
        *len += 1;
        Ok(())
    };

    if speed >= v_a {
        let t_a = speed / amax - t_j;
        if !t_a.is_finite() || t_a < zero {
            return Err(PlanError::NumericalFailure);
        }
        // Decelerate: jerk -J, hold -A, then ramp back to zero.
        push(t_j, -sign * jmax)?;
        push(t_a, zero)?;
        push(t_j, sign * jmax)?;
    } else {
        let t_r = sqrt(speed / jmax);
        if !t_r.is_finite() || t_r <= zero {
            return Err(PlanError::NumericalFailure);
        }
        push(t_r, -sign * jmax)?;
        push(t_r, sign * jmax)?;
    }
    Ok(())
}

fn map_profile_error(error: ProfileError) -> PlanError {
    match error {
        ProfileError::TooManySegments => PlanError::ProfileOverflow,
        _ => PlanError::NumericalFailure,
    }
}
