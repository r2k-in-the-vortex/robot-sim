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
//! `wrap_angle` is `math.atan2(sin, cos)`, i.e. `RealAtan2.wrap`, with range `(-π, π]`. It is
//! a *canonical* form, not the whole story: an angle on the arm is continuous — a joint jog
//! accumulates (`joint_angles[joint_index] += direction * step`, `simulator.py:335`) and can
//! leave a joint several turns from zero — while `wrap_angle` throws that winding away.
//! [`nearest_representative`] places a wrapped angle back beside the one the arm is holding
//! and [`turn_index`] names the turns it carries; a pose jog needs both, because a solver
//! result is defined modulo a full turn and the turn must be kept.

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
///
/// Wrapping is right for *reporting* a solved configuration — the six angles describe the one
/// pose either way — but not for *moving* to one. A solver angle is defined modulo a full
/// turn, and the joint it is about to be sent to is not: it has a winding of its own from the
/// jogs it has taken. A pose jog therefore uses [`nearest_representative`] instead, which
/// keeps that winding; wrapping first would cost the arm whatever whole turns it had wound.
#[inline]
pub fn runtime_angle<S: Scalar>(total: S, theta_offset_deg: S) -> S {
    wrap_angle(total - deg_to_rad(theta_offset_deg))
}

/// The representative of `angle` nearest `reference`: `reference + wrap_angle(angle - reference)`.
///
/// A solver result is an angle *modulo a full turn*. Every statement about it in the Lean
/// development is an equality in `Real.Angle` — which is what `RealAtan2.wrap_coe_angle`
/// records — and `kinematics.py` materialises that by wrapping each angle it returns
/// (`_wrap_angle(total - joint.theta)`, `:562`). A joint on the arm carries no such equivalence:
/// it accumulates (`_jog_joint`'s `joint_angles[joint_index] += direction * step`,
/// `simulator.py:335`), so J6 can sit at 400 degrees, and the solver's 40 degrees is the same
/// place a whole turn away.
///
/// This places such an answer back beside the joint. The motion it implies is exactly
/// `wrap_angle(angle - reference)` — at most a half turn, and never a whole one — and adding it
/// to the reference carries the arm's own winding into the result, which is what makes a pose
/// jog from a wound joint a small move rather than a full turn. [`wrap_angle`] cannot do this
/// by itself; [`turn_index`] names what it discarded.
///
/// This is the *placement* of a chosen candidate. The selection of which candidate — the
/// nearest configuration, in this same wrapped metric — is
/// [`SolutionSet::nearest_to`](crate::solution::SolutionSet::nearest_to) with
/// [`Solution::wrapped_distance_sq`](crate::solution::Solution::wrapped_distance_sq)
/// (`_pose_jog`'s `min(solutions, key=Σ wrap(angle - current)²)`, `simulator.py:392-395`); the
/// reference then stores what the solver returned verbatim (`:396`), wrapped angles and all.
///
/// `RealAtan2.nearestRepresentative` states the same function in Lean, with the half-turn bound
/// as a theorem about it.
#[inline]
pub fn nearest_representative<S: Scalar>(angle: S, reference: S) -> S {
    reference + wrap_angle(angle - reference)
}

/// How many whole turns `angle` carries: `(angle - wrap_angle(angle)) / 2π`, rounded to the
/// nearest integer.
///
/// The companion of [`nearest_representative`], and the name for what `wrap_angle` discards:
/// the winding that puts a solver angle where the arm actually is. `400` degrees is turn `1`,
/// `-400` degrees is turn `-1`, and anything already in `wrap_angle`'s own range `(-π, π]` is
/// turn `0`. The quotient is an integer by construction — `angle - wrap_angle(angle)` is a
/// whole number of turns — so the rounding rule at a half-integer tie is never reached and the
/// value is the one the decomposition names. `RealAtan2.turnIndex` states the same function in
/// Lean.
///
/// Total, and that is a control-path requirement rather than a nicety: this runs inside a jog
/// handler, and a jog handler must not be brought down by an angle that turned out to be
/// non-finite. A non-finite `angle` — or one so large that the winding will not fit in an
/// `i32` — never traps: the cast from `f64` *saturates*, so `NaN` (what `inf - wrap_angle(inf)`
/// is, since `sin inf` is `NaN`) yields `0`, and a winding beyond the type yields `i32::MIN` or
/// `i32::MAX`. `0` is a defensible answer there because a non-finite angle has no turn count at
/// all; what matters is that the caller gets a value it can carry on with, not a panic. The
/// division is done in `S` and only the rounding step widens through [`Scalar::to_f64`].
#[inline]
pub fn turn_index<S: Scalar>(angle: S) -> i32 {
    let turns = (angle - wrap_angle(angle)) / (S::from_f64(2.0) * S::pi());
    round_to_nearest(turns.to_f64())
}

/// The nearest integer to `value`, in the `i32` the turn index is reported as.
///
/// `core` carries no `round` for `f64` — the method is the platform's — and this crate takes
/// its mathematics from the scalar layer rather than the platform, so the nearest integer is
/// reached directly: shift half a unit in the value's own direction and let the cast truncate,
/// which rounds halves away from zero exactly as `f64::round` does. The half unit takes its
/// sign from `value` rather than the other way round (`copysign` reads its *argument's* sign),
/// and that is what keeps a negative winding rounding to `-1` rather than `0`. The cast also
/// saturates instead of trapping, so the function is total: `NaN` lands on `0` and a value past
/// `i32`'s range on its end point.
///
/// The tie rule is never actually exercised by [`turn_index`]: its quotient is an integer plus
/// a few ulps of rounding, so a half-integer cannot arise.
#[inline]
fn round_to_nearest(value: f64) -> i32 {
    (value + 0.5_f64.copysign(value)) as i32
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
        assert!(
            (total - core::f64::consts::FRAC_PI_2 - core::f64::consts::FRAC_PI_6).abs() < 1e-15
        );
        assert!((runtime_angle(total, 90.0) - core::f64::consts::FRAC_PI_6).abs() < 1e-15);
    }

    /// Degrees as the radians the model works in. `deg_to_rad` is the only conversion between
    /// the two, and it is the one every caller of these functions goes through — a joint is
    /// held and displayed in degrees, so the angles a jog works with arrive here.
    fn radians(degrees: f64) -> f64 {
        deg_to_rad(degrees)
    }

    /// The issue's own case. A J6 jogged to 400 degrees is a whole turn from the solver's 40
    /// degrees, and a pose jog must keep the joint where it is: the representative is the 400
    /// degree one — within the rounding of a `wrap_angle` round trip — and the turn it carries
    /// is index 1. `runtime_angle` would return 40 degrees here, which is the whole turn the
    /// arm used to spin.
    #[test]
    fn a_solver_angle_is_placed_beside_a_wound_joint() {
        let reference = radians(400.0);
        let placed = nearest_representative(radians(40.0), reference);
        assert!(
            (placed - reference).abs() < 1e-12,
            "40 degrees placed beside 400 degrees is {placed} rad, want {reference} rad"
        );
        assert_eq!(
            turn_index(placed),
            1,
            "a joint at 400 degrees carries one whole turn"
        );
    }

    /// The placement's motion is exactly the wrapped difference, so it is at most a half turn
    /// for any reference and angle: the "no unintended large joint motion" guarantee an
    /// over-360 degree pose jog rests on. The comparison is a tolerance and not `==` because
    /// reading the motion back as `placed - reference` rounds twice, once adding the difference
    /// on and once taking it off again; `1e-12` rad is a few hundred times that rounding at
    /// these magnitudes, and small enough that a real half-turn overrun could not hide in it.
    #[test]
    fn placement_is_the_reference_plus_the_wrapped_difference() {
        let spread = [
            -720.0, -400.0, -359.9, -270.0, -180.0, -90.0, -0.1, 0.0, 0.1, 90.0, 180.0, 270.0,
            359.9, 400.0, 720.0,
        ];
        for reference_deg in spread {
            for angle_deg in spread {
                let reference = radians(reference_deg);
                let angle = radians(angle_deg);
                let placed = nearest_representative(angle, reference);
                let motion = placed - reference;
                let want = wrap_angle(angle - reference);
                assert!(
                    (motion - want).abs() < 1e-12,
                    "placing {angle_deg} deg beside {reference_deg} deg moved {motion} rad, \
                     want the wrapped difference {want} rad"
                );
                assert!(
                    motion.abs() <= core::f64::consts::PI + 1e-12,
                    "placing {angle_deg} deg beside {reference_deg} deg moved {motion} rad, \
                     past a half turn"
                );
            }
        }
    }

    /// The half-turn bound as a property rather than a case: over three turns either side of
    /// zero, at thirty-degree steps, no angle is ever placed further than halfway round from
    /// its reference. References are wrapped angles and wound ones alike, because the bound
    /// holds for any pair at all — that is what makes it safe on a jog from a joint whose
    /// winding no one tracked.
    #[test]
    fn a_placement_never_moves_further_than_a_half_turn() {
        for reference_deg in (-360..=360).step_by(30) {
            for angle_deg in (-360..=360).step_by(30) {
                let reference = radians(f64::from(reference_deg));
                let angle = radians(f64::from(angle_deg));
                let motion = nearest_representative(angle, reference) - reference;
                assert!(
                    motion.abs() <= core::f64::consts::PI + 1e-12,
                    "placing {angle_deg} deg beside {reference_deg} deg moved {motion} rad, \
                     past a half turn"
                );
            }
        }
    }

    /// `nearestRepresentative_sub_le` executed: the representative placed is the nearest of
    /// *all* the members `angle + 2πk`, not merely of the ones a step either side of the
    /// wrapped value. The half-turn test above is this theorem's `k = ±1` corollary — the case
    /// a jog actually meets, since a further translate is more than a full turn of motion away
    /// — but the minimality is what makes the placement canonical rather than a convention, so
    /// it is asserted directly here, over seven translates either side of zero.
    ///
    /// The tolerance is the same `1e-12` as the placement tests: at `k = -1` with an angle
    /// just past `+π` the two sides are the same real number computed two ways, so an exact
    /// `<=` would be asserting the rounding rather than the bound.
    #[test]
    fn a_placement_is_the_nearest_of_all_the_whole_turn_translates() {
        let spread = [
            -720.0, -400.0, -359.9, -270.0, -180.0, -90.0, -0.1, 0.0, 0.1, 90.0, 180.0, 270.0,
            359.9, 400.0, 720.0,
        ];
        for reference_deg in spread {
            for angle_deg in spread {
                let reference = radians(reference_deg);
                let angle = radians(angle_deg);
                let placed = nearest_representative(angle, reference);
                let motion = (placed - reference).abs();
                for k in -7_i32..=7 {
                    let translate = angle + f64::from(k) * 2.0 * core::f64::consts::PI;
                    let alternative = (translate - reference).abs();
                    assert!(
                        motion <= alternative + 1e-12,
                        "placing {angle_deg} deg beside {reference_deg} deg moved {motion} rad, \
                         but the k = {k} translate is {alternative} rad away"
                    );
                }
            }
        }
    }

    /// Just below a full turn and the solver's answer just above zero: the representative
    /// lands just past 360 degrees, not at 0.1, so crossing the turn boundary is the fifth of
    /// a degree between the two angles rather than the whole turn between their canonical
    /// forms — and the index says which side of the boundary the joint ends up on.
    #[test]
    fn a_placement_crosses_a_turn_boundary_without_a_whole_turn_of_motion() {
        let reference = radians(359.9);
        let placed = nearest_representative(radians(0.1), reference);
        assert!(
            (placed - radians(360.1)).abs() < 1e-12,
            "0.1 degrees placed beside 359.9 degrees is {placed} rad, want 360.1 degrees"
        );
        assert_eq!(
            turn_index(placed),
            1,
            "360.1 degrees carries one whole turn"
        );
        let motion = placed - reference;
        assert!(
            (motion - radians(0.2)).abs() < 1e-12,
            "the motion across the turn boundary is {motion} rad, want 0.2 degrees"
        );
    }

    /// The same facts wound the other way, which is what rules out an implementation that
    /// happens to prefer the positive turn: -400 degrees carries index -1, the solver's -40
    /// degrees places back at -400, and an answer of -0.1 degree beside a joint at -359.9
    /// degrees lands at -360.1, a fifth of a degree of motion backwards.
    #[test]
    fn negative_winding_places_the_same_way() {
        assert_eq!(
            turn_index(radians(-400.0)),
            -1,
            "a joint at -400 degrees carries one whole turn backwards"
        );
        let reference = radians(-400.0);
        let placed = nearest_representative(radians(-40.0), reference);
        assert!(
            (placed - reference).abs() < 1e-12,
            "-40 degrees placed beside -400 degrees is {placed} rad, want {reference} rad"
        );

        let across_reference = radians(-359.9);
        let across = nearest_representative(radians(-0.1), across_reference);
        assert!(
            (across - radians(-360.1)).abs() < 1e-12,
            "-0.1 degrees placed beside -359.9 degrees is {across} rad, want -360.1 degrees"
        );
        assert_eq!(
            turn_index(across),
            -1,
            "-360.1 degrees carries one whole turn backwards"
        );
        let motion = across - across_reference;
        assert!(
            (motion - radians(-0.2)).abs() < 1e-12,
            "the motion across the turn boundary is {motion} rad, want -0.2 degrees"
        );
    }

    /// The index's definition in one place. Nothing inside `wrap_angle`'s own range `(-π, π]`
    /// carries a turn — the ends included, since `-180` and `180` degrees are the same joint
    /// angle and either way the half turn is index 0 — and every exact multiple of a full turn
    /// beyond it is its own index, sign and all: just short of a turn is turn 1, not turn 0.
    #[test]
    fn turn_index_names_whole_turns() {
        for degrees in [-180.0, -90.0, -0.1, 0.0, 0.1, 90.0, 179.9, 180.0] {
            assert_eq!(
                turn_index(radians(degrees)),
                0,
                "{degrees} degrees is inside (-180, 180] and carries no whole turn"
            );
        }
        assert_eq!(
            turn_index(radians(359.9)),
            1,
            "just short of a turn is turn 1"
        );
        assert_eq!(turn_index(radians(360.0)), 1);
        assert_eq!(turn_index(radians(400.0)), 1);
        assert_eq!(turn_index(radians(720.0)), 2);
        assert_eq!(turn_index(radians(-360.0)), -1);
        assert_eq!(turn_index(radians(-400.0)), -1);
        assert_eq!(turn_index(radians(-1080.0)), -3);
    }

    /// A control path runs this inside a jog handler, so it must answer rather than trap even
    /// when the angle is not a number: `NaN` and both infinities are documented as turn 0 —
    /// `angle - wrap_angle(angle)` is `NaN` for each of them and the saturating cast of `NaN`
    /// is zero — and a winding too large for the index type saturates instead of wrapping
    /// round to a small and plausible-looking number.
    #[test]
    fn turn_index_is_total_on_non_finite_angles() {
        for angle in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let first = turn_index(angle);
            assert_eq!(
                first,
                turn_index(angle),
                "{angle} did not give the same index twice"
            );
            assert_eq!(
                first, 0,
                "{angle} has no winding and is documented as turn 0"
            );
        }
        assert_eq!(turn_index(1e300), i32::MAX);
        assert_eq!(turn_index(-1e300), i32::MIN);
    }
}
