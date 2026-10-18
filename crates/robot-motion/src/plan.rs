//! The optimal 7-phase rest-to-rest planner (M1-opt).
//!
//! This mirrors `docs/motion_control.md` §3.3–§3.4. Every case emits the same canonical
//! seven slots; a slot the case does not use has duration zero:
//!
//! ```text
//! jerk:     (+J, 0, -J, 0, -J, 0, +J)
//! duration: ( t1, t2, t3, t4, t5, t6, t7)
//! ```
//!
//! The positive-displacement profile is built at `q = 0`, shifted by [`Profile::translate`]
//! and, for `q1 < q0`, mirrored. The case order is zero motion, cruise at `V`,
//! peak-without-cruise and triangular.
//!
//! Unlike [`crate::conservative`], this planner needs `sqrt`/`cbrt`, so it is `f64`-only.
//! Derived quantities that overflow, and negative durations larger than rounding noise at
//! a case boundary, are reported as [`PlanError::NumericalFailure`] rather than producing
//! a malformed profile.

use crate::error::{PlanError, ProfileError};
use crate::math::{cbrt, sqrt};
use crate::profile::{Limits, PlanKind, Profile, Segment, State};

/// Plan a time-optimal rest-to-rest move between `q0` and `q1`.
///
/// `V = vmax`, `A = amax`, `J = jmax`; the result starts and ends at rest and respects
/// all three limits. `q1 < q0` mirrors the positive profile, so the same durations apply.
pub fn plan_rest_to_rest(q0: f64, q1: f64, lim: Limits<f64>) -> Result<Profile<f64>, PlanError> {
    let v_max = lim.vmax();
    let a_max = lim.amax();
    let j_max = lim.jmax();
    // `Limits::new` already enforces this; re-checking keeps the planner total if the
    // invariant is ever weakened.
    if !q0.is_finite()
        || !q1.is_finite()
        || !v_max.is_finite()
        || !a_max.is_finite()
        || !j_max.is_finite()
    {
        return Err(PlanError::NonFiniteInput);
    }
    if v_max <= 0.0 || a_max <= 0.0 || j_max <= 0.0 {
        return Err(PlanError::NonPositiveLimit);
    }

    let delta = q1 - q0;
    if delta == 0.0 {
        return Ok(Profile::constant(State::new(q0, 0.0, 0.0)));
    }
    let d = delta.abs();
    if !d.is_finite() {
        return Err(PlanError::NumericalFailure);
    }

    let (durations, kind) = positive_durations(d, v_max, a_max, j_max)?;
    let durations = sanitize(durations)?;

    let jerks = [j_max, 0.0, -j_max, 0.0, -j_max, 0.0, j_max];
    let segments: [Segment<f64>; 7] = core::array::from_fn(|i| Segment {
        dur: durations[i],
        jerk: jerks[i],
    });
    let positive = Profile::from_parts_with_kind(State::new(0.0, 0.0, 0.0), &segments, kind)
        .map_err(map_profile_error)?;

    let profile = positive.translate(q0);
    let profile = if delta < 0.0 {
        profile.mirror()
    } else {
        profile
    };
    ensure_finite(&profile)?;
    Ok(profile)
}

/// Durations for a positive displacement `d > 0`, in canonical slot order.
fn positive_durations(
    d: f64,
    v_max: f64,
    a_max: f64,
    j_max: f64,
) -> Result<([f64; 7], PlanKind), PlanError> {
    let t_j = a_max / j_max;
    let v_a = a_max * a_max / j_max;
    if !t_j.is_finite() || t_j <= 0.0 || !v_a.is_finite() || v_a <= 0.0 {
        return Err(PlanError::NumericalFailure);
    }

    // `d_v = d(V)` and `D_full = 2 d(V)`; computed once so the cruise duration uses the
    // same value as the case test and cannot go negative at the boundary.
    let d_v = half_displacement(v_max, t_j, v_a, a_max, j_max)?;
    let d_full = 2.0 * d_v;
    if !d_full.is_finite() {
        return Err(PlanError::NumericalFailure);
    }

    if d >= d_full {
        // Case A: cruise at V.
        if v_max >= v_a {
            let t_a = v_max / a_max - t_j;
            let t_c = (d - d_full) / v_max;
            Ok(([t_j, t_a, t_j, t_c, t_j, t_a, t_j], PlanKind::Cruise))
        } else {
            let t_r = sqrt(v_max / j_max);
            let t_c = (d - d_full) / v_max;
            Ok(([t_r, 0.0, t_r, t_c, t_r, 0.0, t_r], PlanKind::Cruise))
        }
    } else if v_max >= v_a && d >= 2.0 * v_a * t_j {
        // Case B: A reached, no cruise; `2 A^3 / J^2 == 2 v_A t_j`.
        // `v_p` is the positive root of `v_p^2 + v_A v_p = A D`.
        let disc = v_a * v_a + 4.0 * a_max * d;
        if !disc.is_finite() || disc < 0.0 {
            return Err(PlanError::NumericalFailure);
        }
        let v_p = 0.5 * (sqrt(disc) - v_a);
        if !v_p.is_finite() || v_p < 0.0 {
            return Err(PlanError::NumericalFailure);
        }
        let t_a = v_p / a_max - t_j;
        Ok(([t_j, t_a, t_j, 0.0, t_j, t_a, t_j], PlanKind::PeakNoCruise))
    } else {
        // Case C: triangular, no cruise.
        let t_r = cbrt(d / (2.0 * j_max));
        if !t_r.is_finite() || t_r <= 0.0 {
            return Err(PlanError::NumericalFailure);
        }
        Ok(([t_r, 0.0, t_r, 0.0, t_r, 0.0, t_r], PlanKind::Triangular))
    }
}

/// Symmetric acceleration-half displacement `d(v)` of §3.2.
fn half_displacement(v: f64, t_j: f64, v_a: f64, a_max: f64, j_max: f64) -> Result<f64, PlanError> {
    let d = if v <= v_a {
        v * sqrt(v / j_max)
    } else {
        v * (t_j + v / a_max) / 2.0
    };
    if !d.is_finite() || d < 0.0 {
        return Err(PlanError::NumericalFailure);
    }
    Ok(d)
}

/// Rounding at a case boundary (`V = v_A`, `D = D_full`, `D = 2A^3/J^2`) can leave a
/// duration an ulp below zero. Clamp that to zero; anything larger is a real failure.
fn sanitize(durations: [f64; 7]) -> Result<[f64; 7], PlanError> {
    let mut scale: f64 = 0.0;
    for &dur in &durations {
        if !dur.is_finite() {
            return Err(PlanError::NumericalFailure);
        }
        scale = scale.max(dur.abs());
    }
    let tolerance = (1e-9 * scale).max(f64::MIN_POSITIVE);
    let mut out = durations;
    for dur in &mut out {
        if *dur < 0.0 {
            if *dur >= -tolerance {
                *dur = 0.0;
            } else {
                return Err(PlanError::NumericalFailure);
            }
        }
    }
    Ok(out)
}

fn ensure_finite(profile: &Profile<f64>) -> Result<(), PlanError> {
    if !profile.start().is_finite() || !profile.end().is_finite() {
        return Err(PlanError::NumericalFailure);
    }
    for i in 0..profile.segments().len() {
        match profile.phase_start(i) {
            Some(state) if state.is_finite() => {}
            _ => return Err(PlanError::NumericalFailure),
        }
    }
    Ok(())
}

fn map_profile_error(error: ProfileError) -> PlanError {
    match error {
        ProfileError::TooManySegments => PlanError::ProfileOverflow,
        ProfileError::NegativeDuration
        | ProfileError::NonFinite
        | ProfileError::InvalidStretch
        | ProfileError::JunctionMismatch => PlanError::NumericalFailure,
    }
}
