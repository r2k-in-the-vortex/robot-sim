//! The verified default planner: a rational, conservative S-curve template.
//!
//! It is deliberately not time-optimal. It uses only `min`, comparison, multiplication
//! and division, so it is generic over [`robot_kinematics::Field`] and exactly evaluable
//! over the rationals. The shape is the same 7-slot pattern as the optimal planner:
//!
//! ```text
//! jerk:     (+j, 0, -j, 0, -j, 0, +j)
//! duration: ( τ, 0,  τ, τc,  τ, 0,  τ)
//! ```
//!
//! With `τ = min 1 (min (A/J) (V/J))`, the peak acceleration is `jτ ≤ A` and the peak
//! velocity is `jτ² ≤ V`. For large displacement `j = J` and the cruise fills the rest;
//! for small displacement `j = D/(2τ³)`, `τc = 0`.

use crate::error::{PlanError, ProfileError};
use crate::profile::{Limits, PlanKind, Profile, Segment, State};
use robot_kinematics::Field;

/// Plan a rest-to-rest move with the conservative rational template.
pub fn plan_rest_conservative<S: Field>(
    q0: S,
    q1: S,
    lim: Limits<S>,
) -> Result<Profile<S>, PlanError> {
    if !q0.is_finite() || !q1.is_finite() {
        return Err(PlanError::NonFiniteInput);
    }

    let zero = S::zero();
    let one = S::one();
    let two = S::from_f64(2.0);
    let start = State::new(q0, zero, zero);
    let delta = q1 - q0;
    if delta == zero {
        return Ok(Profile::constant(start));
    }

    let d = delta.abs();
    if !d.is_finite() {
        return Err(PlanError::NumericalFailure);
    }

    let jmax = lim.jmax();
    let a_over_j = lim.amax() / jmax;
    let v_over_j = lim.vmax() / jmax;
    let mut tau = one;
    if a_over_j < tau {
        tau = a_over_j;
    }
    if v_over_j < tau {
        tau = v_over_j;
    }
    if !tau.is_finite() || tau <= zero {
        return Err(PlanError::NumericalFailure);
    }

    let tau2 = tau * tau;
    let tau3 = tau2 * tau;
    let dmin = two * jmax * tau3;
    let (j, tc) = if d >= dmin {
        (jmax, (d - dmin) / (jmax * tau2))
    } else {
        (d / (two * tau3), zero)
    };
    if !j.is_finite() || !tc.is_finite() || j <= zero || tc < zero {
        return Err(PlanError::NumericalFailure);
    }

    let sign = if delta < zero { -one } else { one };
    let sj = sign * j;
    let nsj = -sj;
    let segments = [
        Segment { dur: tau, jerk: sj },
        Segment {
            dur: zero,
            jerk: zero,
        },
        Segment {
            dur: tau,
            jerk: nsj,
        },
        Segment {
            dur: tc,
            jerk: zero,
        },
        Segment {
            dur: tau,
            jerk: nsj,
        },
        Segment {
            dur: zero,
            jerk: zero,
        },
        Segment { dur: tau, jerk: sj },
    ];

    Profile::from_parts_with_kind(start, &segments, PlanKind::Conservative)
        .map_err(map_profile_error)
}

fn map_profile_error(_: ProfileError) -> PlanError {
    PlanError::NumericalFailure
}
