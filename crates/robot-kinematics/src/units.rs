//! The angle and unit conventions, and the boundary between them.
//!
//! Everything in this crate is in **radians** and **total DH angles**, matching the
//! Lean development exactly. `kinematics.py` differs in two ways, both of which are a
//! change of variable rather than mathematics, and both of which live here so that the
//! core stays identical to the specification:
//!
//! * Python keeps the static `theta_offset` separate and reports `wrap(total - offset)`;
//!   Lean folds the offset in and every statement is modulo a full turn.
//! * Python takes degrees at its JSON and UI boundary; the model is in radians.
//!
//! `wrap_angle` is `math.atan2(sin, cos)`, i.e. `RealAtan2.wrap`, with range `(-π, π]`.

use crate::scalar::Scalar;

/// The number of joints the arm has. Six is structural in the specification, not a
/// configuration: `forward_kinematics` and every solver entry point in `kinematics.py`
/// raise on anything else.
pub const JOINT_COUNT: usize = 6;

/// The number of frames the cumulative tower carries: the base plus one per joint.
/// `Kinematics.carrierPose` is a `Fin 7 → Pose`.
pub const FRAME_COUNT: usize = JOINT_COUNT + 1;

/// Degrees to radians.
#[inline]
pub fn deg_to_rad<S: Scalar>(degrees: S) -> S {
    degrees * (S::pi() / S::from_f64(180.0))
}

/// Radians to degrees.
#[inline]
pub fn rad_to_deg<S: Scalar>(radians: S) -> S {
    radians * (S::from_f64(180.0) / S::pi())
}

/// Reduce an angle to `(-π, π]`, the range `RealAtan2.atan2_mem_Ioc` establishes.
///
/// Written as `atan2 (sin θ) (cos θ)` rather than by a remainder operation because that
/// is literally the Lean definition, and because it is total: it maps `NaN` to `NaN`
/// and agrees with `atan2`'s own branch cut at `π`.
#[inline]
pub fn wrap_angle<S: Scalar>(angle: S) -> S {
    angle.sin().atan2(angle.cos())
}

/// Fold a static theta offset and a runtime angle into the total DH angle the model
/// works in, which is what `compose_dh_parameters` does in `kinematics.py`.
///
/// The sum happens in degrees before conversion there, so this takes both in degrees
/// and returns radians; both operands and the result are the same real number either
/// way, and doing the addition in the caller's own unit avoids introducing a rounding
/// step the specification does not have.
#[inline]
pub fn total_angle<S: Scalar>(theta_offset_deg: S, joint_angle_deg: S) -> S {
    deg_to_rad(theta_offset_deg + joint_angle_deg)
}

/// The runtime angle for a total angle and a static offset, wrapped into `(-π, π]`.
/// The inverse of [`total_angle`], and what a solver result reports back to the UI.
#[inline]
pub fn runtime_angle<S: Scalar>(total: S, theta_offset_deg: S) -> S {
    wrap_angle(total - deg_to_rad(theta_offset_deg))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrap_is_the_identity_inside_its_range() {
        let inside: [f64; 5] = [-3.0, -1.0, 0.0, 1.0, 3.0];
        for angle in inside {
            assert!((wrap_angle(angle) - angle).abs() < 1e-15);
        }
    }

    #[test]
    fn wrap_folds_outside_its_range() {
        use core::f64::consts::PI;
        assert!((wrap_angle(PI + 0.5) - (0.5 - PI)).abs() < 1e-12);
        assert!((wrap_angle(-PI - 0.5) - (PI - 0.5)).abs() < 1e-12);
        assert!((wrap_angle(4.0 * PI + 0.25) - 0.25).abs() < 1e-12);
    }

    #[test]
    fn a_full_turn_wraps_to_zero() {
        use core::f64::consts::PI;
        assert!(wrap_angle(2.0 * PI).abs() < 1e-15);
    }

    #[test]
    fn offset_and_runtime_round_trip() {
        // The shipped table has a 90 degree offset on joint 2; a runtime angle of 30
        // degrees must come back out of the total unchanged.
        let total = total_angle::<f64>(90.0, 30.0);
        assert!((total - core::f64::consts::FRAC_PI_2 - core::f64::consts::FRAC_PI_6).abs() < 1e-15);
        assert!((runtime_angle(total, 90.0) - core::f64::consts::FRAC_PI_6).abs() < 1e-15);
    }
}
