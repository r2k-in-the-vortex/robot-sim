//! The closed-form inverse solver, in two functions that are deliberately not one.
//!
//! [`solutions`] is `InverseKinematics.solutions` read across: total (it returns a
//! candidate for every pose, degenerate ones included), tolerance-free, with no pose
//! filter, and constructing exactly the candidates Lean's `candidateAngles` constructs. The
//! theorems `fk_of_mem_solutions`, `solutions_ne_nil`, `length_solutions_le_eight`,
//! `solutions_eq_nil_of_not_reachable` and `exists_solution_angles_eq` are all statements
//! about *that* function, so it is the one they must be checked against.
//!
//! [`solve`] is the application's behavior: `kinematics.py`'s `inverse_kinematics`, with
//! every tolerance it adds collected into [`Tolerances`], plus the two things Python does
//! that Lean does not — it offers the flat wrist split as an *extra* candidate near the
//! singularity, and it discards candidates that fail a forward-kinematics pose check.
//!
//! Keeping them apart is the point rather than an implementation detail. Over `ℝ` the
//! pose filter has nothing to reject, so bolting it into `solutions` would make the Lean
//! theorems statements about a function that does not exist in the Lean development, and
//! there would be nothing left to check them against.
//!
//! Both take a `&mut SolutionSet` rather than returning a list: the crate is `no_std` and
//! allocates nothing, and [`crate::MAX_SOLUTIONS`] is a proved bound rather than an
//! estimate.
//!
//! # Joint numbering
//!
//! Angles are indexed `0..6` and are **total DH angles**, exactly as `θ` is in Lean and in
//! [`crate::chain`]. Lean's `θ 4` is therefore the *fifth* joint — the middle of the
//! wrist — and it is `angles[4]` here. The two numberings agree; the warning is only that
//! "joint 5" in prose means index 4.

pub use crate::branch::Tolerances;
use crate::branch::{
    BranchPlan, ELBOW_BRANCHES, SHOULDER_BRANCHES, WRIST_BRANCHES, branch_sign, shoulder_index,
    wrist_plan,
};
use crate::chain::{PlanarTarget, arm_rotation, elbow_cosine, fk, planar_target, wrist_center};
use crate::geometry::Geometry;
use crate::mat3::Mat3;
use crate::pose::Pose;
use crate::scalar::Scalar;
use crate::solution::{Solution, SolutionSet};
use crate::units::wrap_angle;
use crate::zyz::{
    WristAngles, hypot_third_column, read_theta4, read_theta5, read_theta6, read_theta6_flat,
};

/// The total, tolerance-free closed form: Lean's `InverseKinematics.solutions`.
///
/// Up to eight candidates, in Lean's generation order: shoulder branch `[1, -1]`, then the
/// elbow branches `elbowBranches g T σ` keeps (in `[1, -1]` order), then wrist branch
/// `[1, -1]` — `flatMap`-nested, so the wrist branch varies fastest. The goldens compare
/// that order, so it is part of the function's specification rather than an accident of
/// the loops below.
///
/// Every decision it branches on is exact: `shoulderAngle`'s `shoulderRadius g T = 0`, and
/// `elbowBranches`' band membership. It does not test `NonDegenerate`, and it does not test
/// whether a candidate reproduces the target — `fk_of_mem_solutions` is the theorem that
/// saying so is unnecessary.
pub fn solutions<S: Scalar>(g: &Geometry<S>, target: &Pose<S>, out: &mut SolutionSet<S>) {
    // The exact tolerances, which is what makes this Lean's function rather than Python's:
    // `r <= 0` is `r = 0` and `c ∈ [-1, 1]` is the `Set.Icc` test, because neither `hypot`
    // nor the band's clearing ever produces a negative slack.
    let tolerances = Tolerances::exact();
    let plan = BranchPlan::of_pose(g, target, &tolerances);
    let center = wrist_center(g, target);
    // Both shoulder slots carry the same radius decision; `ShoulderPlan` records it per
    // branch only so that a reader does not have to know that.
    let radius_is_zero = plan.shoulder[0].radius_is_zero;

    for sigma in SHOULDER_BRANCHES {
        let slot = shoulder_index(sigma);
        let sign = branch_sign::<S>(sigma);
        let theta1 = if radius_is_zero {
            // `shoulderAngle`'s `r = 0` case. At the origin every azimuth is a solution, so
            // Lean anchors the arm plane on the `+x` half-axis; `atan2 (σ*0) (σ*0)` would
            // answer `0` for both branches and silently collapse them into one plane.
            if sigma == 1 { S::zero() } else { S::pi() }
        } else {
            (sign * center.y()).atan2(sign * center.x())
        };
        let planar = planar_target(g, center, sign);
        let cosine = elbow_cosine(g, &planar);

        for epsilon in ELBOW_BRANCHES {
            if !plan.elbow_branches[slot].keeps(epsilon) {
                continue;
            }
            // `elbowAngle` and `elbowTheta2`: the law of cosines for the bend, then the
            // difference of the target's polar angle and the second link's. `ψ` is the
            // interior bend, not a joint angle; `elbowTheta3` adds the quarter turn that
            // `alpha3 = 90` puts between them.
            let psi = branch_sign::<S>(epsilon) * cosine.acos();
            let theta2 = planar.h.atan2(planar.q)
                - (g.link_two * psi.sin()).atan2(g.link_one + g.link_two * psi.cos());
            let theta3 = psi + Mat3::<S>::quarter_turn();
            // `relativeRotationAt`: the wrist is solved in frame 3, so the target rotation
            // is conjugated by the arm rotation the three angles above produce.
            let relative = arm_rotation(theta1, theta2, theta3).transpose() * target.r;
            let singular = wrist_plan(&relative, &tolerances).singular;
            for wrist in WRIST_BRANCHES {
                let wrist = candidate_wrist(&relative, wrist, singular);
                out.push(Solution {
                    angles: [
                        theta1,
                        theta2,
                        theta3,
                        wrist.theta4,
                        wrist.theta5,
                        wrist.theta6,
                    ],
                    shoulder: sigma,
                    elbow: epsilon,
                });
            }
        }
    }
}

/// The application's solver: `kinematics.py`'s `inverse_kinematics`, to the tolerance.
///
/// This is [`solutions`] plus the three things the Python oracle does and Lean does not.
/// The first two are the reason the functions are separate; the third is a bound.
///
/// 1. **Widened predicates.** Python decides `shoulderRadius = 0`, the reachability band
///    and the wrist singularity against tolerances rather than exactly. Those live in
///    [`Tolerances`] and in [`BranchPlan::of_pose`], and every one of them is a named
///    constant citing the Lean predicate it stands in for.
/// 2. **The flat wrist split.** Within the singularity threshold Python offers *both* the
///    read-back triple and the flat split (joint 4 held at zero), and lets the pose check
///    pick; `solutions` offers only the flat one, because over `ℝ` the other is not a
///    solution. This is the divergence with teeth: it is why `solve` needs the pose check
///    that Lean's `fk_of_mem_solutions` proves unnecessary.
/// 3. **The pose check.** Python keeps a candidate only if its forward kinematics
///    reproduces the target's position and orientation to within `Tolerances::pose`. Lean
///    has no counterpart, and nothing else in the crate filters candidates.
///
/// A consequence of the first two: Python can return more than eight candidates for a
/// single target at the wrist singularity, where the direct and flat splits of the same
/// family can both reproduce the pose. [`SolutionSet`] holds the eight
/// `length_solutions_le_eight` bounds and reports the overflow through
/// [`SolutionSet::overflowed`]; candidates are built in Python's order and the first eight
/// are kept.
///
/// Past that bound "Python's list" and "this list" are two different lists, and not only
/// because of truncation: at a target whose relative rotation has an *exactly* vertical
/// third column the two conjugate the target by expressions that round differently, so they
/// read the same angle through different noise and split joints 4 and 6 differently — and
/// the pose check then keeps whichever split happens to reproduce the rotation.
/// `tests/python_compat.rs` records such a fold-back target, where Python returns twelve
/// candidates and this returns eight, two of Python's among the dropped.
pub fn solve<S: Scalar>(
    g: &Geometry<S>,
    target: &Pose<S>,
    tolerances: &Tolerances,
    out: &mut SolutionSet<S>,
) {
    let plan = BranchPlan::of_pose(g, target, tolerances);
    let center = wrist_center(g, target);
    let radius = center.hypot_xy();
    let height = center.z() - g.d1;
    let one = S::one();
    let singularity = S::from_f64(tolerances.wrist_singularity);
    let pose_tolerance = S::from_f64(tolerances.pose);
    // Python's `base_azimuth`: zero rather than `atan2 0 0` when the wrist centre is on the
    // base axis, which is what the tolerance-widened `shoulderRadius = 0` decides here.
    let base_azimuth = if plan.shoulder[0].radius_is_zero {
        S::zero()
    } else {
        center.y().atan2(center.x())
    };

    for sigma in SHOULDER_BRANCHES {
        let slot = shoulder_index(sigma);
        let sign = branch_sign::<S>(sigma);
        // `_wrap_angle (base_azimuth + π)` rather than `atan2 (-y) (-x)`: the two are equal
        // in `ℝ` and differ by an ulp in `f64`, and this is the one the oracle computes.
        let theta1 = if sigma == 1 {
            base_azimuth
        } else {
            wrap_angle(base_azimuth + S::pi())
        };
        if plan.elbow_branches[slot].is_empty() {
            continue;
        }
        let planar = PlanarTarget {
            radius,
            q: sign * radius - g.a1,
            h: height,
        };
        // Python's clamp into `[-1, 1]` before the `acos`, which the exact branch never
        // needs: the tolerance admits a cosine a hair outside the range, and `acos` of one
        // is `NaN`, not the `0` or `π` the clamped value gives.
        let mut cosine = elbow_cosine(g, &planar);
        if cosine < -one {
            cosine = -one;
        }
        if cosine > one {
            cosine = one;
        }

        for epsilon in ELBOW_BRANCHES {
            let psi = branch_sign::<S>(epsilon) * cosine.acos();
            let theta2 = height.atan2(planar.q)
                - (g.link_two * psi.sin()).atan2(g.link_one + g.link_two * psi.cos());
            let theta3 = psi + Mat3::<S>::quarter_turn();
            let relative = arm_rotation(theta1, theta2, theta3).transpose() * target.r;
            // Python's `sine_five`: read off the rotation rather than recovered through an
            // `acos`, which would stall at the square root of rounding noise near zero.
            let sine = hypot_third_column(&relative);

            for wrist in WRIST_BRANCHES {
                let theta5 = read_theta5(&relative, wrist);
                // The mirror is θ4 and θ6 turned by π, which is `wristRotation_mirror`;
                // it pairs with the branch whose `sin θ5` is positive.
                let mirror = if wrist < 0 { S::zero() } else { S::pi() };
                let direct = [
                    theta1,
                    theta2,
                    theta3,
                    read_theta4(&relative) + mirror,
                    theta5,
                    read_theta6(&relative) + mirror,
                ];
                if reproduces(g, target, &direct, pose_tolerance) {
                    out.push(Solution {
                        angles: direct,
                        shoulder: sigma,
                        elbow: epsilon,
                    });
                }
                if sine <= singularity {
                    let flat = [
                        theta1,
                        theta2,
                        theta3,
                        S::zero(),
                        theta5,
                        flat_read(&relative, theta5),
                    ];
                    if reproduces(g, target, &flat, pose_tolerance) {
                        out.push(Solution {
                            angles: flat,
                            shoulder: sigma,
                            elbow: epsilon,
                        });
                    }
                }
            }
        }
    }
}

/// `InverseKinematics.candidateAngles`' wrist half for one branch family.
///
/// The two cases are the two halves of `Zyz.lean`: off the singularity both branches read
/// the rotation back directly, one of them with joints 4 and 6 turned by π
/// (`wristRotation_reconstruct` and `wristRotation_reconstruct_mirror`); at the singularity
/// joint 4 is held at zero and joint 6 read off the flattened rotation
/// (`wristRotation_reconstruct_flat`, `wristRotation_singular_flat`).
///
/// Which is which is *not* a choice: `wristBranch θ = if 0 < Real.sin (θ 4) then 1 else -1`
/// labels the branch by the sign of `sin θ5`, the read-back of `wristTheta4` already carries
/// the π offset for the positive one, and the flat read is only available where the sine is
/// zero — so the branch labels and the case agree by construction.
fn candidate_wrist<S: Scalar>(relative: &Mat3<S>, wrist: i8, singular: bool) -> WristAngles<S> {
    let theta5 = read_theta5(relative, wrist);
    if singular {
        WristAngles {
            theta4: S::zero(),
            theta5,
            theta6: read_theta6_flat(relative),
        }
    } else {
        let mirror = if wrist < 0 { S::zero() } else { S::pi() };
        WristAngles {
            theta4: read_theta4(relative) + mirror,
            theta5,
            theta6: read_theta6(relative) + mirror,
        }
    }
}

/// Python's flat read: joint 6 from the rotation with the middle joint divided back out.
///
/// Differs from `Zyz.lean`'s `wristReadTheta6Flat` in the angle it divides out. Lean uses
/// `rotY (atan2 0 (Q [2][2]))`, the positive `0` or `π`; Python uses `rotY total_theta5`,
/// the branch-signed one. Over `ℝ` the two are the same rotation — `rotY π = rotY (-π)` —
/// and in `f64` they differ only in the sign of a `1.2e-16` sine, so this exists to make
/// [`solve`] reproduce the oracle rather than to make it correct. The read *indices* are
/// Lean's: the first column's first two entries.
fn flat_read<S: Scalar>(relative: &Mat3<S>, theta5: S) -> S {
    let flattened = Mat3::rot_y(theta5) * *relative;
    flattened.at(1, 0).atan2(flattened.at(0, 0))
}

/// Python's final check, which Lean's `fk_of_mem_solutions` makes unnecessary.
///
/// `kinematics.py` recomputes the forward kinematics from the *wrapped runtime* angles and
/// requires both the position error and the Frobenius norm of the rotation difference to be
/// within the tolerance. The wrapping is a no-op here: the crate's candidates are total DH
/// angles, and the offset that separates the two conventions is not a property of
/// `Geometry`, so a caller that wants Python's exact expression converts through
/// [`crate::units`] itself.
fn reproduces<S: Scalar>(g: &Geometry<S>, target: &Pose<S>, angles: &[S; 6], tolerance: S) -> bool {
    let reconstructed = fk(g, angles);
    reconstructed.p.distance(target.p) <= tolerance
        && reconstructed.r.frobenius_distance(target.r) <= tolerance
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solution::MAX_SOLUTIONS;

    /// The pose of the arm's documented rest configuration, which is the one case the
    /// corpus names: joints 2 at its 90 degree offset, everything else zero.
    fn rest_pose() -> (Geometry<f64>, Pose<f64>) {
        let g = Geometry::<f64>::shipped();
        let theta = [
            0.0,
            crate::units::total_angle(90.0, 0.0),
            0.0,
            0.0,
            0.0,
            0.0,
        ];
        (g, fk(&g, &theta))
    }

    #[test]
    fn the_solution_count_is_bounded_by_the_proved_maximum() {
        let (g, target) = rest_pose();
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(!out.is_empty(), "the rest pose is reachable");
        assert!(out.len() <= MAX_SOLUTIONS);
        assert!(!out.overflowed(), "length_solutions_le_eight");
    }

    #[test]
    fn every_candidate_reproduces_the_target_pose() {
        // `fk_of_mem_solutions`, in its crudest form; `tests/theorem_soundness.rs` is the
        // adversarial version.
        let (g, target) = rest_pose();
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        for candidate in out.iter() {
            let reconstructed = fk(&g, &candidate.angles);
            assert!(reconstructed.p.distance(target.p) < 1e-9);
            assert!(reconstructed.r.frobenius_distance(target.r) < 1e-9);
        }
    }

    #[test]
    fn the_rest_pose_has_both_shoulder_branches_and_both_elbow_branches() {
        // Eight candidates, one per (shoulder, elbow, wrist) label. The wrist branch is not
        // recorded on `Solution`, so it is the count that witnesses it.
        let (g, target) = rest_pose();
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert_eq!(out.len(), 8);
        for sigma in SHOULDER_BRANCHES {
            for epsilon in ELBOW_BRANCHES {
                assert!(
                    out.iter()
                        .any(|s| s.shoulder == sigma && s.elbow == epsilon),
                    "branch labels ({sigma}, {epsilon})"
                );
            }
        }
    }

    #[test]
    fn a_target_out_of_reach_yields_nothing() {
        // `solutions_eq_nil_of_not_reachable`: beyond `L1 + L2` in the plane.
        let g = Geometry::<f64>::shipped();
        let target = Pose::new(Mat3::identity(), crate::vec3::Vec3::new(0.0, 0.0, 400.0));
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn solve_agrees_with_solutions_away_from_the_singularity() {
        // Off the singularity Python constructs exactly what Lean constructs, so the
        // compat layer's extra machinery changes nothing but the filter.
        let g = Geometry::<f64>::shipped();
        let theta = [
            0.4,
            crate::units::total_angle(90.0, 20.0),
            -0.3,
            0.9,
            1.2,
            2.1,
        ];
        let target = fk(&g, &theta);
        let mut exact = SolutionSet::new();
        let mut compat = SolutionSet::new();
        solutions(&g, &target, &mut exact);
        solve(&g, &target, &Tolerances::python(), &mut compat);
        assert_eq!(exact.len(), compat.len());
        for (a, b) in exact.iter().zip(compat.iter()) {
            assert_eq!(a.shoulder, b.shoulder);
            assert_eq!(a.elbow, b.elbow);
            for joint in 0..6 {
                let delta = wrap_angle(a.angles[joint] - b.angles[joint]);
                assert!(delta.abs() < 1e-9, "joint {joint}: {delta}");
            }
        }
    }

    #[test]
    fn the_singularity_threshold_buys_the_flat_split() {
        // A commanded configuration whose fifth joint is exactly zero, so the wrist is
        // singular in `ℝ`. What the solver *sees* is the recovered sine, which is rounding
        // noise rather than a zero — and that gap between the mathematics and the bits is
        // the whole reason `Tolerances::wrist_singularity` exists. `solutions` cannot see
        // the singularity here; `solve` can, and pays for it with candidates the exact
        // function does not construct.
        let g = Geometry::<f64>::shipped();
        let theta = [
            0.4,
            crate::units::total_angle(90.0, 20.0),
            -0.3,
            0.9,
            0.0,
            2.1,
        ];
        let target = fk(&g, &theta);
        let mut exact = SolutionSet::new();
        let mut compat = SolutionSet::new();
        solutions(&g, &target, &mut exact);
        solve(&g, &target, &Tolerances::python(), &mut compat);
        assert_eq!(exact.len(), 8, "one candidate per branch triple");
        assert!(!exact.overflowed());
        assert!(
            compat.iter().any(|s| s.angles[3] == 0.0),
            "Python's flat split, which pins joint 4 to zero, is offered"
        );
        // The read-back is noise-driven on the singular family, and the failure shows up in
        // the *third column* of the rotation, not in its position: with `sin θ5` at 2e-16 the
        // z axis is right to rounding either way, so the position error stays at 1e-15 while
        // the split of joint 4 against joint 6 is wrong by O(1). That is the argument for the
        // filter, and for `wrist_singularity` being more than a compatibility knob: `solutions`
        // is faithful to Lean — this pose's *recovered* sine is not zero, so `wristIsSingular`
        // does not hold of it — and Lean's `fk_of_mem_solutions` is a theorem about data that
        // has not already lost the singularity.
        let worst = exact
            .iter()
            .map(|s| fk(&g, &s.angles).r.frobenius_distance(target.r))
            .fold(0.0, f64::max);
        assert!(
            worst > 1e-3,
            "the noise-driven read-back misses the orientation by {worst}"
        );
        assert!(compat.iter().all(|s| {
            let reconstructed = fk(&g, &s.angles);
            reconstructed.p.distance(target.p) <= 1e-7
                && reconstructed.r.frobenius_distance(target.r) <= 1e-7
        }));
        for sigma in SHOULDER_BRANCHES {
            for epsilon in ELBOW_BRANCHES {
                assert!(
                    compat
                        .iter()
                        .any(|s| s.shoulder == sigma && s.elbow == epsilon)
                );
            }
        }
    }

    #[test]
    fn the_compat_layer_can_exceed_the_proved_candidate_bound() {
        // `length_solutions_le_eight` is a theorem about `solutions`. The compat layer offers
        // Python's flat split *in addition to* the read-back whenever it judges the wrist
        // singular, so it can offer more than the eight the buffer holds — here by widening
        // every tolerance, which makes all four families singular and every candidate
        // reproduce the pose. This is the case `SolutionSet::overflowed` reports instead of
        // panicking, and it is why `solve` is documented as keeping Python's first eight.
        let g = Geometry::<f64>::shipped();
        let theta = [
            0.4,
            crate::units::total_angle(90.0, 20.0),
            -0.3,
            0.9,
            0.0,
            2.1,
        ];
        let target = fk(&g, &theta);
        let wide = Tolerances::all(1e9);
        let mut compat = SolutionSet::new();
        solve(&g, &target, &wide, &mut compat);
        assert!(compat.overflowed());
        assert_eq!(compat.len(), MAX_SOLUTIONS);
        assert!(
            compat.iter().any(|s| s.angles[3] == 0.0),
            "the flat split is among them"
        );
        let mut exact = SolutionSet::new();
        solutions(&g, &target, &mut exact);
        assert_eq!(exact.len(), 8);
        assert!(!exact.overflowed());
    }

    #[test]
    fn the_flat_read_back_is_the_singular_case() {
        // The decision layer directly: `rotZ φ` has its third column exactly on the z axis,
        // so `wristSine` is exactly zero and `wristIsSingular` holds. No pose the forward
        // chain produces lands there — see the note in `tests/theorem_coverage.rs`.
        let q = Mat3::<f64>::rot_z(0.7);
        assert!(wrist_plan(&q, &Tolerances::exact()).singular);
        assert!(wrist_plan(&q, &Tolerances::python()).singular);

        let flat = candidate_wrist(&q, -1, true);
        assert_eq!(flat.theta4, 0.0, "joint 4 is held at zero");
        // Flattening by the middle joint leaves the rotation alone here, so joint 6 reads
        // back the `φ` that built it.
        assert!(
            (flat.theta6 - 0.7).abs() < 1e-15,
            "theta6 = {}",
            flat.theta6
        );

        // Off the singularity the same rotation reads back as the pair that produced it.
        let read = candidate_wrist(&q, 1, false);
        assert!((read.theta4 - core::f64::consts::PI).abs() < 1e-15);
        assert!(read.theta5.abs() < 1e-15);
    }
}
