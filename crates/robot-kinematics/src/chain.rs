//! The forward chain: the six DH transforms, the cumulative frame tower, and the wrist
//! centre the inverse solver works from.
//!
//! The counterpart of the `The chain` and `The planar reduction` sections of
//! `lean/Kinematics.lean`. Angles are total DH angles in radians; see [`crate::units`]
//! for the boundary with the degrees the configuration file uses.

use crate::angle::{AnglesCosSin, CosSin};
use crate::geometry::Geometry;
use crate::mat3::Mat3;
use crate::pose::Pose;
use crate::scalar::{Field, Scalar};
use crate::units::{FRAME_COUNT, JOINT_COUNT};
use crate::vec3::Vec3;

/// The six joint angles, `Fin 6 → ℝ` in Lean.
pub type Angles<S> = [S; JOINT_COUNT];

/// The fixed twists of the supported arm: `90, 0, 90, 90, -90, 0` degrees. Lean writes
/// these inline in `joint`, as `quarter`, `0`, `quarter`, `quarter`, `-quarter`, `0`.
///
/// The quarter turn's cosine and sine are `0` and `1` exactly, so every alpha in the
/// table is exactly representable and the chain is a polynomial in the joint angles'
/// cosine/sine pairs. That is what makes the whole forward chain evaluable over `ℚ`.
#[inline]
fn joint_transforms_cs<S: Field>(
    g: &Geometry<S>,
    theta: &AnglesCosSin<S>,
) -> [Pose<S>; JOINT_COUNT] {
    let quarter = CosSin::<S>::quarter_turn();
    let zero = CosSin::<S>::identity();
    [
        // dh (θ 0) g.d1 g.a1 quarter
        Pose::dh_cs(theta[0], g.d1, g.a1, quarter),
        // dh (θ 1) 0 g.linkOne 0
        Pose::dh_cs(theta[1], S::zero(), g.link_one, zero),
        // dh (θ 2) 0 0 quarter
        Pose::dh_cs(theta[2], S::zero(), S::zero(), quarter),
        // dh (θ 3) g.linkTwo 0 quarter -- alpha3 turns d4 into a link perpendicular to
        // the joint-4 axis, which is why the second link length lives in `d`.
        Pose::dh_cs(theta[3], g.link_two, S::zero(), quarter),
        // dh (θ 4) 0 0 (-quarter)
        Pose::dh_cs(theta[4], S::zero(), S::zero(), quarter.negated()),
        // dh (θ 5) g.toolOffset 0 0
        Pose::dh_cs(theta[5], g.tool_offset, S::zero(), zero),
    ]
}

/// Frames 0 to 3: the shoulder, the upper arm and the `alpha3 = 90` twist. Lean's
/// `armPose`. The bracketing is Lean's — `(A1 * A2) * A3` — so the floating-point
/// rounding matches the specification's evaluation order.
#[inline]
pub fn arm_pose_cs<S: Field>(g: &Geometry<S>, theta: &AnglesCosSin<S>) -> Pose<S> {
    let joint = joint_transforms_cs(g, theta);
    joint[0] * joint[1] * joint[2]
}

/// Frames 3 to 6: the spherical wrist, whose three axes meet at the frame-4 origin.
/// Lean's `wristPose`.
#[inline]
pub fn wrist_pose_cs<S: Field>(g: &Geometry<S>, theta: &AnglesCosSin<S>) -> Pose<S> {
    let joint = joint_transforms_cs(g, theta);
    joint[3] * joint[4] * joint[5]
}

/// The full forward kinematics, `A1 · A2 · ⋯ · A6`. Lean's `fk`.
///
/// This is what `forward_kinematics` reports in its last entry: the end-effector pose
/// `T6`. Note that the bracketing follows Lean's `armPose * wristPose` rather than the
/// strictly left-nested product `kinematics.py` accumulates; the two agree to rounding,
/// and `carrier_pose` gives the left-nested tower the renderer draws.
#[inline]
pub fn fk_cs<S: Field>(g: &Geometry<S>, theta: &AnglesCosSin<S>) -> Pose<S> {
    arm_pose_cs(g, theta) * wrist_pose_cs(g, theta)
}

/// The cumulative frame tower `⁰T_0 … ⁰T_6`, the array `forward_kinematics` returns and
/// the simulator draws. Lean's `carrierPose`.
///
/// Entry `0` is the base frame and entry `i` is frame `i` in base coordinates, so
/// `tower[4].p` is the wrist centre — `carrierPose_four_p` — and `tower[6]` is `fk`.
#[inline]
pub fn carrier_pose_cs<S: Field>(
    g: &Geometry<S>,
    theta: &AnglesCosSin<S>,
) -> [Pose<S>; FRAME_COUNT] {
    let j = joint_transforms_cs(g, theta);
    let arm = j[0] * j[1] * j[2];
    // Built left to right through frame 3, matching Lean's literal vector: the arm's
    // three joints are bracketed as `armPose` and every later frame extends it by one
    // transform, which is the recurrence `carrierPose_succ` records.
    let t3 = arm;
    let t4 = t3 * j[3];
    let t5 = t4 * j[4];
    let t6 = t5 * j[5];
    [
        Pose::identity(),
        j[0],
        j[0] * j[1],
        t3,
        t4,
        t5,
        t6,
    ]
}

/// Frames 0 to 3, from angles in radians. See [`arm_pose_cs`].
#[inline]
pub fn arm_pose<S: Scalar>(g: &Geometry<S>, theta: &Angles<S>) -> Pose<S> {
    arm_pose_cs(g, &pairs(theta))
}

/// Frames 3 to 6, from angles in radians. See [`wrist_pose_cs`].
#[inline]
pub fn wrist_pose<S: Scalar>(g: &Geometry<S>, theta: &Angles<S>) -> Pose<S> {
    wrist_pose_cs(g, &pairs(theta))
}

/// The full forward kinematics, from angles in radians. See [`fk_cs`].
#[inline]
pub fn fk<S: Scalar>(g: &Geometry<S>, theta: &Angles<S>) -> Pose<S> {
    fk_cs(g, &pairs(theta))
}

/// The cumulative frame tower, from angles in radians. See [`carrier_pose_cs`].
#[inline]
pub fn carrier_pose<S: Scalar>(g: &Geometry<S>, theta: &Angles<S>) -> [Pose<S>; FRAME_COUNT] {
    carrier_pose_cs(g, &pairs(theta))
}

/// An angle vector as cosine/sine pairs.
#[inline]
pub fn pairs<S: Scalar>(theta: &Angles<S>) -> AnglesCosSin<S> {
    [
        CosSin::from_angle(theta[0]),
        CosSin::from_angle(theta[1]),
        CosSin::from_angle(theta[2]),
        CosSin::from_angle(theta[3]),
        CosSin::from_angle(theta[4]),
        CosSin::from_angle(theta[5]),
    ]
}

/// The rotation from the base frame to frame 3. Joints 2 and 3 rotate about the same
/// axis, so only their sum appears. Lean's `armRotation`, and the left factor of
/// `fk_R`.
///
/// The sum `θ2 + θ3` is taken on the pairs rather than on the angles, by `CosSin::then`,
/// because a rational scalar has no angles to add — `rotZ_add` is the identity that lets
/// the two z rotations be merged at all.
pub fn arm_rotation_cs<S: Field>(
    theta1: CosSin<S>,
    theta2: CosSin<S>,
    theta3: CosSin<S>,
) -> Mat3<S> {
    let quarter = CosSin::<S>::quarter_turn();
    // Left-associated, as Lean writes it; the product is associative in the
    // mathematics and the bracketing only fixes the floating-point rounding.
    Mat3::rot_z_cs(theta1) * Mat3::rot_x_cs(quarter) * Mat3::rot_z_cs(theta2.then(theta3))
        * Mat3::rot_x_cs(quarter)
}

/// The rotation from frame 3 to frame 6: a ZYZ decomposition, because joints 4, 5 and 6
/// form a spherical wrist. Lean's `wristRotation`.
///
/// The middle angle is `-θ5`; that negation is what `rotX_conj` produces when the
/// `alpha4 = 90`, `alpha5 = -90` twists conjugate the three z rotations into a ball
/// joint, and it is the reason the wrist reads as ZYZ rather than ZXZ.
#[inline]
pub fn wrist_rotation_cs<S: Field>(theta4: CosSin<S>, theta5: CosSin<S>, theta6: CosSin<S>) -> Mat3<S> {
    Mat3::rot_z_cs(theta4) * Mat3::rot_y_cs(theta5.negated()) * Mat3::rot_z_cs(theta6)
}

/// The rotation from the base frame to frame 3, from angles in radians.
#[inline]
pub fn arm_rotation<S: Scalar>(theta1: S, theta2: S, theta3: S) -> Mat3<S> {
    arm_rotation_cs(
        CosSin::from_angle(theta1),
        CosSin::from_angle(theta2),
        CosSin::from_angle(theta3),
    )
}

/// The rotation from frame 3 to frame 6, from angles in radians.
#[inline]
pub fn wrist_rotation<S: Scalar>(theta4: S, theta5: S, theta6: S) -> Mat3<S> {
    wrist_rotation_cs(
        CosSin::from_angle(theta4),
        CosSin::from_angle(theta5),
        CosSin::from_angle(theta6),
    )
}

/// The wrist centre: the end-effector origin pulled back along frame 6's z axis by the
/// tool offset. Lean's `wristCenter`, `mathematics.md` §1.
///
/// `a6 = 0` in the supported arm, so only the `d6` term appears. The third column of the
/// rotation is frame 6's z axis — the same thing `kinematics.py` reads as
/// `target_pose[axis][2]`.
#[inline]
pub fn wrist_center<S: Field>(g: &Geometry<S>, target: &Pose<S>) -> Vec3<S> {
    target.p - target.z_axis().scale(g.tool_offset)
}

/// The planar reduction of `mathematics.md` §3–§6: the wrist centre in the frame-1
/// plane, as `(q, h)`.
///
/// `q` is the signed radial distance from the frame-1 origin and `h` the height above
/// it, *after* the shoulder branch `sigma` has chosen which half-plane the arm solves
/// in. Diverging from `kinematics.py`, the sign of `q` carries the branch: the two
/// shoulder candidates are `+r - a1` and `-r - a1`, not a re-derived angle.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct PlanarTarget<S> {
    /// The shoulder radius `r`, always non-negative.
    pub radius: S,
    /// `sigma * r - a1`, the signed radial coordinate of the planar problem.
    pub q: S,
    /// `z4 - d1`.
    pub h: S,
}

/// Reduce the wrist centre to the planar problem. Lean's `planarQ` and `planarH`
/// together with `shoulderRadius`.
#[inline]
pub fn planar_target<S: Scalar>(g: &Geometry<S>, center: Vec3<S>, sigma: S) -> PlanarTarget<S> {
    let radius = center.hypot_xy();
    PlanarTarget {
        radius,
        q: sigma * radius - g.a1,
        h: center.z() - g.d1,
    }
}

/// The law of cosines for the elbow, `Kinematics`' / `InverseKinematics.lean`'s
/// `elbowCosine`.
///
/// Lean keeps this dimensionless; the caller compares it against `Set.Icc (-1) 1`
/// exactly, which is what `branch.rs` reproduces with a tolerance.
#[inline]
pub fn elbow_cosine<S: Field>(g: &Geometry<S>, planar: &PlanarTarget<S>) -> S {
    let distance_sq = planar.q * planar.q + planar.h * planar.h;
    (distance_sq - g.link_one * g.link_one - g.link_two * g.link_two)
        / (S::from_f64(2.0) * g.link_one * g.link_two)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::units::total_angle;

    /// The shipped table's zero pose. `doc/main_window_image.png` shows the same numbers:
    /// the arm lies horizontal along +x with the tool 60 units from the base axis.
    #[test]
    fn zero_pose_matches_the_documented_frame_origins() {
        let g = Geometry::<f64>::shipped();
        // Joint 2's static offset is 90 degrees, so "zero runtime angles" is not the
        // zero angle vector. This is exactly the trap the offset exists to represent.
        let theta = [
            0.0,
            total_angle(90.0, 0.0),
            0.0,
            0.0,
            0.0,
            0.0,
        ];
        let tower = carrier_pose(&g, &theta);
        let expected = [
            (0.0, 0.0, 0.0),
            (10.0, 0.0, 40.0),
            (10.0, 0.0, 80.0),
            (10.0, 0.0, 80.0),
            (50.0, 0.0, 80.0),
            (50.0, 0.0, 80.0),
            (60.0, 0.0, 80.0),
        ];
        for (frame, (x, y, z)) in tower.iter().zip(expected) {
            assert!((frame.p.x() - x).abs() < 1e-12, "frame origin x");
            assert!((frame.p.y() - y).abs() < 1e-12, "frame origin y");
            assert!((frame.p.z() - z).abs() < 1e-12, "frame origin z");
        }
    }

    #[test]
    fn the_sixth_cumulative_frame_is_the_forward_kinematics() {
        // `carrierPose_six`, checked numerically rather than structurally because the
        // two bracket the product differently.
        let g = Geometry::<f64>::shipped();
        let theta = [0.3, 1.9, -0.4, 2.2, -0.8, 1.1];
        let tower = carrier_pose(&g, &theta);
        let direct = fk(&g, &theta);
        assert!(tower[6].r.frobenius_distance(direct.r) < 1e-12);
        assert!(tower[6].p.distance(direct.p) < 1e-12);
    }

    #[test]
    fn the_fourth_cumulative_frame_is_the_wrist_centre() {
        // `carrierPose_four_p`.
        let g = Geometry::<f64>::shipped();
        let theta = [0.3, 1.9, -0.4, 2.2, -0.8, 1.1];
        let tower = carrier_pose(&g, &theta);
        let center = wrist_center(&g, &fk(&g, &theta));
        assert!(tower[4].p.distance(center) < 1e-12);
    }

    #[test]
    fn the_forward_rotation_is_a_rotation() {
        // `fk_R_orth` and `fk_R_det`.
        let g = Geometry::<f64>::shipped();
        for theta in [
            [0.0; 6],
            [0.3, 1.9, -0.4, 2.2, -0.8, 1.1],
            [-2.5, 0.1, 3.0, -1.6, 0.9, 2.7],
        ] {
            let pose = fk(&g, &theta);
            assert!(pose.rotation_is_a_rotation(1e-12), "theta = {theta:?}");
        }
    }

    #[test]
    fn the_forward_kinematics_is_invariant_under_a_full_turn() {
        // `fk_congr`: the chain reads each angle only through its cosine and sine.
        let g = Geometry::<f64>::shipped();
        let theta = [0.3, 1.9, -0.4, 2.2, -0.8, 1.1];
        let turned = theta.map(|angle| angle + 2.0 * core::f64::consts::PI);
        let a = fk(&g, &theta);
        let b = fk(&g, &turned);
        assert!(a.r.frobenius_distance(b.r) < 1e-12);
        assert!(a.p.distance(b.p) < 1e-9);
    }

    #[test]
    fn the_rotation_factors_through_frame_three() {
        // `fk_R`: `R_0^6 = armRotation θ0 θ1 θ2 · wristRotation θ3 θ4 θ5`.
        let g = Geometry::<f64>::shipped();
        let theta = [0.3, 1.9, -0.4, 2.2, -0.8, 1.1];
        let factored = arm_rotation(theta[0], theta[1], theta[2])
            * wrist_rotation(theta[3], theta[4], theta[5]);
        assert!(fk(&g, &theta).r.frobenius_distance(factored) < 1e-12);
    }

    #[test]
    fn the_wrist_centre_never_depends_on_joint_six() {
        // Joint 6 turns frame 6 about its own z axis, and `wristCenter` subtracts a
        // multiple of that axis, so the centre is fixed by joints 1 to 5.
        let g = Geometry::<f64>::shipped();
        let theta = [0.3, 1.9, -0.4, 2.2, -0.8, 1.1];
        let base = wrist_center(&g, &fk(&g, &theta));
        for extra in [0.5, 1.4, -2.0] {
            let mut turned = theta;
            turned[5] += extra;
            let center = wrist_center(&g, &fk(&g, &turned));
            assert!(center.distance(base) < 1e-12);
        }
    }
}
