//! Joint synchronization and the scalar MoveJ.
//!
//! `synchronize` is the independent-timing mode: each joint keeps its own profile shape
//! and is stretched to the common maximum duration. A zero-duration joint becomes a
//! constant hold for that duration; it is not an empty profile, because `JointProfile`
//! asserts one common duration for every joint.
//!
//! `plan_movej_scalar` is the standard joint-space-line mode: one scalar S-curve in
//! `s ∈ [0,1]`, with `q_i(t) = q0_i + s(t) Δq_i` and effective limits derived from the
//! per-joint limits divided by `|Δq_i|`.

use crate::conservative::plan_rest_conservative;
use crate::error::{PlanError, ProfileError};
use crate::profile::{JointProfile, Limits, PlanKind, Profile, Segment, State};
use robot_kinematics::Field;

/// Stretch the joint profiles to a common duration.
///
/// The caller must pass rest-to-rest profiles: stretching a profile with a nonzero start
/// velocity would change that velocity and the joints would no longer share the measured
/// state. A zero-total-time profile is held at its start position.
pub fn synchronize<const N: usize, S: Field>(
    joints: [Profile<S>; N],
) -> Result<JointProfile<N, S>, PlanError> {
    let zero = S::zero();
    let mut sync_time = zero;
    for joint in &joints {
        let t = joint.total_time();
        if sync_time < t {
            sync_time = t;
        }
    }

    let mut synchronized = [Profile::constant(State::new(zero, zero, zero)); N];
    for i in 0..N {
        let joint = joints[i];
        debug_assert!(
            joint.start().v == zero
                && joint.start().a == zero
                && joint.end().v == zero
                && joint.end().a == zero,
            "synchronize requires rest-to-rest profiles"
        );
        let t = joint.total_time();
        let stretched = if t == zero {
            hold(joint.start().q, sync_time)
        } else {
            let factor = sync_time / t;
            joint.stretch(factor).map_err(map_profile_error)?
        };
        synchronized[i] = stretched;
    }
    Ok(JointProfile::new(synchronized, sync_time))
}

/// The standard MoveJ: one scalar S-curve, straight line in joint space.
///
/// The scalar profile is the verified conservative template. If every joint is
/// stationary, the result is an empty move with total time zero.
pub fn plan_movej_scalar<const N: usize, S: Field>(
    start: [S; N],
    target: [S; N],
    limits: [Limits<S>; N],
) -> Result<JointProfile<N, S>, PlanError> {
    let zero = S::zero();
    let one = S::one();

    let mut delta = [zero; N];
    for i in 0..N {
        if !start[i].is_finite() || !target[i].is_finite() {
            return Err(PlanError::NonFiniteInput);
        }
        delta[i] = target[i] - start[i];
        if !delta[i].is_finite() {
            return Err(PlanError::NumericalFailure);
        }
    }

    let mut any_moving = false;
    let mut vs: Option<S> = None;
    let mut as_: Option<S> = None;
    let mut js: Option<S> = None;
    for i in 0..N {
        if delta[i] == zero {
            continue;
        }
        any_moving = true;
        let d = delta[i].abs();
        let v = limits[i].vmax() / d;
        let a = limits[i].amax() / d;
        let j = limits[i].jmax() / d;
        if !v.is_finite() || !a.is_finite() || !j.is_finite() {
            return Err(PlanError::NumericalFailure);
        }
        vs = Some(match vs {
            None => v,
            Some(x) if v < x => v,
            Some(x) => x,
        });
        as_ = Some(match as_ {
            None => a,
            Some(x) if a < x => a,
            Some(x) => x,
        });
        js = Some(match js {
            None => j,
            Some(x) if j < x => j,
            Some(x) => x,
        });
    }

    if !any_moving {
        let joints = core::array::from_fn(|i| Profile::constant(State::new(start[i], zero, zero)));
        return Ok(JointProfile::new(joints, zero));
    }

    let scalar_limits = Limits::new(
        vs.ok_or(PlanError::NumericalFailure)?,
        as_.ok_or(PlanError::NumericalFailure)?,
        js.ok_or(PlanError::NumericalFailure)?,
    )?;
    let scalar = plan_rest_conservative(zero, one, scalar_limits)?;
    let scalar_time = scalar.total_time();

    let mut joints = [Profile::constant(State::new(zero, zero, zero)); N];
    for i in 0..N {
        if delta[i] == zero {
            joints[i] = hold(start[i], scalar_time);
            continue;
        }
        let mut segments = [Segment {
            dur: zero,
            jerk: zero,
        }; crate::profile::MAX_PHASES];
        let scalar_segments = scalar.segments();
        for (k, seg) in scalar_segments.iter().enumerate() {
            segments[k] = Segment {
                dur: seg.dur,
                jerk: seg.jerk * delta[i],
            };
        }
        let profile = Profile::from_parts_with_kind(
            State::new(start[i], zero, zero),
            &segments[..scalar_segments.len()],
            PlanKind::Conservative,
        )
        .map_err(map_profile_error)?;
        joints[i] = profile;
    }

    Ok(JointProfile::new(joints, scalar_time))
}

/// A constant zero-jerk profile of duration `duration` at position `q`.
fn hold<S: Field>(q: S, duration: S) -> Profile<S> {
    let zero = S::zero();
    Profile::from_parts_with_kind(
        State::new(q, zero, zero),
        &[Segment {
            dur: duration,
            jerk: zero,
        }],
        PlanKind::ZeroMotion,
    )
    .unwrap_or_else(|_| Profile::constant(State::new(q, zero, zero)))
}

fn map_profile_error(_: ProfileError) -> PlanError {
    PlanError::NumericalFailure
}
