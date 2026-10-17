//! The closed-form inverse solver the pose jogs call.
//!
//! A thin adapter, not a solver. The solve itself is [`robot_kinematics::solve`], the
//! Python-compatible layer over the Lean function: it widens the degeneracy predicates by
//! `Tolerances::python()`, offers the flat wrist candidate at the singularity, and keeps
//! only the candidates whose forward kinematics reproduces the target — which is what
//! `inverse_kinematics` does, `kinematics.py:447-600`.
//!
//! What is left here is the part that is about the *table* rather than the mathematics:
//! `inverse_kinematics` validates the arm's structure before it solves anything, and an
//! unsupported table is reported by name rather than solved approximately
//! (`_validate_supported_geometry`, `kinematics.py:409-444`). That is what puts the
//! offending parameter in the jog status line (`simulator.py:385-387`), and the order the
//! failures are reported in is the reference's.
//!
//! This module exists rather than the call being inline at the jog site so that the error
//! mapping has one home. Nothing here duplicates the mathematics.
//!
//! # Units
//!
//! [`Solution::angles`] are **total DH angles in radians**, the crate's convention
//! everywhere. `kinematics.py` reports `wrap(total - offset)` instead, and that change of
//! variable is not part of a solve: it belongs to the caller, where the answer meets the arm
//! and the table the jog was built from.
//!
//! [`robot_kinematics::units::runtime_angle`] is not what the pose jog uses to get there. It
//! wraps, and wrapping is right only for *reporting* a configuration — a solver angle is
//! defined modulo a full turn, an arm's joint is not, and a joint jog accumulates
//! (`joint_angles[joint_index] += direction * step`, `simulator.py:335`). The jog instead
//! places the chosen candidate beside the arm's own continuous angles
//! ([`Solution::representative_near`]) and subtracts the offset without wrapping, so a joint
//! at 400° stays at 400° rather than snapping to the solver's 40°. That divergence is
//! `session.rs`'s to document; this module's boundary is only that the angles come back as
//! totals.

use robot_kinematics::{GeometryError, Pose, SolutionSet, Tolerances};
use robot_model::{DHParameters, TableError};

/// Every configuration that reproduces `target`, or nothing if none does.
///
/// `parameters` is the DH table with its static offsets and no runtime angles folded in;
/// the returned angles are totals, so the caller adds nothing to them.
pub fn solve(
    parameters: &DHParameters,
    target: &Pose<f64>,
) -> Result<SolutionSet<f64>, TableError> {
    // Python's error order: every value finite, then the structural constants in table
    // order, then the two link signs. `structure_error` performs all three in that order,
    // so the first problem it reports is the one Python would have raised.
    if let Some(error) = parameters.structure_error() {
        return Err(error);
    }
    // Unreachable once `structure_error` has passed, since it proves the same finiteness
    // and positivity, but total rather than a panic: a solve is a control path.
    let geometry = match parameters.geometry() {
        Ok(geometry) => geometry,
        Err(GeometryError::LinkOneNotPositive) => return Err(TableError::LinkOneNotPositive),
        Err(GeometryError::LinkTwoNotPositive) => return Err(TableError::LinkTwoNotPositive),
        Err(GeometryError::NotFinite) => return Err(TableError::NotFinite),
    };

    let mut solutions = SolutionSet::new();
    robot_kinematics::solve(&geometry, target, &Tolerances::python(), &mut solutions);
    Ok(solutions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::units::{self, total_angle};
    use robot_kinematics::{FRAME_COUNT, Geometry, JOINT_COUNT, Mat3, Solution, carrier_pose, fk};
    use robot_model::DhRow;

    fn shipped_geometry() -> Geometry<f64> {
        DHParameters::shipped()
            .geometry()
            .expect("the shipped table is the supported arm")
    }

    /// The total angles a set of runtime degrees produces, which is the change of variable
    /// every boundary in this crate performs.
    fn totals(runtime_deg: &[f64; JOINT_COUNT]) -> [f64; JOINT_COUNT] {
        DHParameters::shipped().total_angles_rad(runtime_deg)
    }

    /// The pose a known joint vector produces.
    fn pose_at(runtime_deg: &[f64; JOINT_COUNT]) -> Pose<f64> {
        fk(&shipped_geometry(), &totals(runtime_deg))
    }

    #[test]
    fn relative_rotation_is_the_third_cumulative_frame() {
        // `arm_rotation` is used where the reference multiplies the first three DH
        // transforms and reads frame 3's rotation block (`kinematics.py:524`). This is the
        // equivalence that lets the cheaper form stand in.
        let geometry = shipped_geometry();
        for theta in [
            [0.0; JOINT_COUNT],
            [0.3, 1.9, -0.4, 2.2, -0.8, 1.1],
            [-2.5, 0.1, 3.0, -1.6, 0.9, 2.7],
        ] {
            let tower: [Pose<f64>; FRAME_COUNT] = carrier_pose(&geometry, &theta);
            let arm = robot_kinematics::arm_rotation(theta[0], theta[1], theta[2]);
            assert!(
                arm.frobenius_distance(tower[3].r) < 1e-12,
                "theta = {theta:?}"
            );
        }
    }

    #[test]
    fn a_known_configuration_is_recovered_from_its_own_pose() {
        // `test_kinematics.py:589-610` sweeps every joint from three base configurations
        // and requires one returned solution to match the commanded angles to 1e-7. The
        // base is zero here and the commanded angles are off every axis' zero so a dropped
        // or transposed joint cannot pass by symmetry.
        let commanded = [25.0, -35.0, 30.0, 40.0, -55.0, 15.0];
        let solutions =
            solve(&DHParameters::shipped(), &pose_at(&commanded)).expect("shipped table");
        assert!(!solutions.is_empty());
        assert!(!solutions.overflowed());

        let expected = totals(&commanded);
        let best = solutions
            .iter()
            .map(|solution| {
                (0..JOINT_COUNT)
                    .map(|joint| units::wrap_angle(solution.angles[joint] - expected[joint]).abs())
                    .fold(0.0_f64, f64::max)
            })
            .fold(f64::INFINITY, f64::min);
        assert!(
            best < 1e-7,
            "recovered {best} rad away from the commanded angles"
        );
    }

    #[test]
    fn every_solution_reproduces_the_target_pose() {
        // `test_kinematics.py:546-560`: not just the best candidate, but all of them.
        // Poses are built by forward kinematics from angles chosen before the solver runs,
        // so every case has an exact answer.
        let geometry = shipped_geometry();
        let cases: [[f64; JOINT_COUNT]; 5] = [
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [30.0, -25.0, 20.0, 45.0, -50.0, 10.0],
            [-170.0, 15.0, 70.0, -100.0, 120.0, 33.5],
            [90.0, 5.0, -5.0, 179.0, -95.0, -120.0],
            [12.5, 47.0, -128.0, 6.0, 88.0, 179.0],
        ];
        for commanded in cases {
            let target = pose_at(&commanded);
            let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
            assert!(!solutions.is_empty(), "no solution for {commanded:?}");
            for solution in solutions.iter() {
                let recovered = fk(&geometry, &solution.angles);
                assert!(
                    recovered.p.distance(target.p) <= 1e-8,
                    "{commanded:?}: position error {}",
                    recovered.p.distance(target.p)
                );
                assert!(
                    recovered.r.frobenius_distance(target.r) <= 1e-8,
                    "{commanded:?}: orientation error {}",
                    recovered.r.frobenius_distance(target.r)
                );
            }
        }
    }

    #[test]
    fn an_unreachable_target_returns_no_solutions() {
        // `test_kinematics.py:155-162`: 100 units out on every axis is far outside an arm
        // whose links are 25 units each.
        let target = Pose::new(
            Mat3::identity(),
            robot_kinematics::Vec3::new(100.0, 100.0, 100.0),
        );
        let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
        assert!(solutions.is_empty(), "{solutions:?}");
    }

    #[test]
    fn a_target_whose_orientation_fights_its_position_is_refused() {
        // `test_kinematics.py:164-170`: flipping one entry of the rotation block leaves the
        // position reachable but the pose itself inconsistent, and the re-check is what
        // catches it rather than the branch arithmetic.
        let mut target = pose_at(&[40.0, -17.0, 46.0, -11.0, 63.0, -34.0]);
        // `target[0][0] *= -1` and nothing else: the position stays reachable and the
        // orientation stays *a* rotation, so only the re-check can catch it.
        target.r.set(0, 0, -target.r.at(0, 0));
        let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
        assert!(solutions.is_empty(), "{solutions:?}");
    }

    #[test]
    fn the_wrist_singularity_is_still_solvable() {
        // `test_kinematics.py:658-673`. Joint 5's static offset is zero, so a runtime angle
        // of `-0` puts `sin θ5` at zero and the wrist's two branches collapse into one.
        let mut commanded = [20.0, -30.0, 40.0, 0.0, 0.0, 60.0];
        commanded[4] = -DHParameters::shipped().joints[4].theta_offset_deg;
        let target = pose_at(&commanded);
        let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
        assert!(
            !solutions.is_empty(),
            "the singularity must still be reachable"
        );
        for solution in solutions.iter() {
            let recovered = fk(&shipped_geometry(), &solution.angles);
            assert!(recovered.p.distance(target.p) <= 1e-8);
            assert!(recovered.r.frobenius_distance(target.r) <= 1e-8);
        }
    }

    #[test]
    fn an_unsupported_table_is_named_rather_than_solved() {
        // `test_kinematics.py:413-430` types 45 into joint 3's alpha and expects the status
        // line to name it. `solve` is where that name comes from.
        let mut parameters = DHParameters::shipped();
        parameters.joints[2].alpha_deg = 45.0;
        let error = solve(&parameters, &Pose::identity()).expect_err("alpha3 = 45 is unsupported");
        assert!(error.to_string().contains("joint 3 alpha"), "{error}");
    }

    #[test]
    fn a_table_with_a_legacy_theta_key_still_solves() {
        // The document's static offsets are the only angles that reach the solver, and
        // joint 2's shipped offset of 90 degrees is the one that must be folded in.
        let row = DhRow::new(90.0, 0.0, 25.0, 0.0);
        assert_eq!(row.theta_offset_deg, 90.0);
        let parameters = DHParameters::shipped();
        let theta = parameters.total_angles_rad(&[0.0; JOINT_COUNT]);
        assert!((theta[1] - core::f64::consts::FRAC_PI_2).abs() < 1e-15);
        let target = fk(&shipped_geometry(), &theta);
        let solutions = solve(&parameters, &target).expect("shipped table");
        assert!(!solutions.is_empty());
        // Solving the zero configuration must return a configuration that *is* the zero
        // configuration, offset and all.
        let best = solutions
            .iter()
            .map(|solution| {
                (0..JOINT_COUNT)
                    .map(|joint| units::wrap_angle(solution.angles[joint] - theta[joint]).abs())
                    .fold(0.0_f64, f64::max)
            })
            .fold(f64::INFINITY, f64::min);
        assert!(
            best < 1e-7,
            "recovered {best} rad from the zero configuration"
        );
    }

    #[test]
    fn the_solver_reads_a_free_base_offset_and_tool_length() {
        // `d1`, `a1`, `theta`, and `d6` are the four parameters the structure check leaves
        // open, so a table that moves them is still the supported arm and must still solve.
        let mut parameters = DHParameters::shipped();
        parameters.joints[0].d = 55.0;
        parameters.joints[0].a = 12.5;
        parameters.joints[0].theta_offset_deg = 20.0;
        parameters.joints[5].d = 17.0;
        assert_eq!(parameters.structure_error(), None);

        let theta = parameters.total_angles_rad(&[0.0; JOINT_COUNT]);
        let geometry = parameters.geometry().expect("supported");
        let target = fk(&geometry, &theta);
        let solutions = solve(&parameters, &target).expect("supported");
        assert!(!solutions.is_empty());
        for solution in solutions.iter() {
            let recovered = fk(&geometry, &solution.angles);
            assert!(recovered.p.distance(target.p) <= 1e-8);
        }
    }

    #[test]
    fn a_full_turn_off_a_commanded_angle_is_still_the_same_configuration() {
        // `fk_congr`: the chain reads every angle only through its cosine and sine, so a
        // solution that lands a whole turn away is the same arm. The wrapped-distance
        // comparison `_pose_jog` makes depends on this.
        let commanded = [0.0, 0.0, 0.0, 0.0, 40.0, 0.0];
        let target = pose_at(&commanded);
        let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
        let reference = Solution {
            angles: totals(&commanded),
            shoulder: 1,
            elbow: 1,
        };
        let nearest = solutions.nearest_to(&reference).expect("non-empty");
        assert!(nearest.wrapped_distance_sq(&reference) < 1e-14);

        let mut turned = commanded;
        turned[5] += 360.0;
        let turned_reference = Solution {
            angles: totals(&turned),
            shoulder: 1,
            elbow: 1,
        };
        assert!(nearest.wrapped_distance_sq(&turned_reference) < 1e-14);

        // The selection above is turn-blind by design, so the turn has to be put back before
        // the arm is moved anywhere: `representative_near` is the other half of the pair, and
        // it is what the pose jog calls once it has chosen (`session.rs`). Every joint lands
        // at the reference — this candidate *is* the commanded configuration, so each of its
        // angles is at worst a whole turn out — and joint 6 is the one that has a turn to
        // keep: the solver's own representative wraps it to 0, the placement leaves it at 2π.
        let placed = nearest.representative_near(&turned_reference);
        for joint in 0..JOINT_COUNT {
            assert!(
                (placed.angles[joint] - turned_reference.angles[joint]).abs() < 1e-9,
                "joint {} is {} after placement, not the reference's {}",
                joint + 1,
                placed.angles[joint],
                turned_reference.angles[joint]
            );
        }
        assert!(
            units::rad_to_deg(placed.angles[5]).abs() > 359.0,
            "joint 6 landed at {} degrees instead of keeping the whole turn",
            units::rad_to_deg(placed.angles[5])
        );

        // The issue's own geometry (#1): a joint commanded to 400 degrees, where the solver
        // answers inside a single turn at 40. Placing that answer beside the reference puts it
        // back at 400 — the whole turn the selection ignores and the placement restores. The
        // reference stores the 40 (`simulator.py:392-396`), which is the spin.
        let mut wound = commanded;
        wound[5] = 400.0;
        let wound_reference = Solution {
            angles: totals(&wound),
            shoulder: 1,
            elbow: 1,
        };
        let wound_solutions =
            solve(&DHParameters::shipped(), &pose_at(&wound)).expect("shipped table");
        let wound_nearest = wound_solutions
            .nearest_to(&wound_reference)
            .expect("non-empty");
        assert!(
            (units::rad_to_deg(wound_nearest.angles[5]) - 40.0).abs() < 1e-6,
            "the solver answers joint 6 at {} degrees, not inside a single turn",
            units::rad_to_deg(wound_nearest.angles[5])
        );
        let placed_wound = wound_nearest.representative_near(&wound_reference);
        assert!(
            (units::rad_to_deg(placed_wound.angles[5]) - 400.0).abs() < 1e-6,
            "joint 6 is {} degrees after placement, not the 400 of the reference",
            units::rad_to_deg(placed_wound.angles[5])
        );
    }

    #[test]
    fn the_nearest_branch_is_picked_by_wrapped_angle_not_raw_difference() {
        // `_pose_jog`'s `min(solutions, key=Σ wrap(angle - current)²)` (`simulator.py:392-395`).
        // A joint sitting at +π and one at -π are zero apart, not a full turn apart, so a
        // solution a hair inside the branch cut must not be penalised for it.
        let mut set = SolutionSet::new();
        set.push(Solution {
            angles: [core::f64::consts::PI - 1e-9; JOINT_COUNT],
            shoulder: 1,
            elbow: 1,
        });
        set.push(Solution {
            angles: [0.0; JOINT_COUNT],
            shoulder: 1,
            elbow: 1,
        });
        let reference = Solution {
            angles: [-core::f64::consts::PI + 1e-9; JOINT_COUNT],
            shoulder: 1,
            elbow: 1,
        };
        let nearest = set.nearest_to(&reference).expect("non-empty");
        assert!((nearest.angles[0] - core::f64::consts::PI).abs() < 1e-6);
    }

    #[test]
    fn a_singular_target_may_overflow_the_eight_slot_buffer_without_panicking() {
        // The reference's singularity handling offers up to four candidates per
        // shoulder/elbow pair, so a target sitting exactly on the wrist singularity can
        // produce more than `MAX_SOLUTIONS`. `SolutionSet` drops the surplus and flags it
        // rather than panicking; this records that the drop is reachable and harmless,
        // since every dropped candidate reproduces the same pose.
        let commanded = [20.0, -30.0, 40.0, 0.0, 0.0, 60.0];
        let target = pose_at(&commanded);
        let solutions = solve(&DHParameters::shipped(), &target).expect("shipped table");
        assert!(solutions.len() <= robot_kinematics::MAX_SOLUTIONS);
        for solution in solutions.iter() {
            let recovered = fk(&shipped_geometry(), &solution.angles);
            assert!(recovered.p.distance(target.p) <= 1e-8);
        }
    }

    #[test]
    fn the_theta_offset_is_the_only_thing_between_runtime_and_total() {
        // `units::total_angle` and `units::runtime_angle` are inverse, which is what lets
        // the solver work entirely in totals while the UI stores runtime degrees.
        for offset_deg in [0.0_f64, 90.0, -90.0, 137.5] {
            for runtime_deg in [0.0_f64, 5.0, -180.0, 359.0] {
                let total = total_angle(offset_deg, runtime_deg);
                let back = units::runtime_angle(total, offset_deg);
                assert!(
                    units::wrap_angle(back - runtime_deg.to_radians()).abs() < 1e-12,
                    "offset {offset_deg}, runtime {runtime_deg}"
                );
            }
        }

        // The *placement* round trip is the one a joint that has wound a turn takes, and it
        // is not `runtime_angle`'s: the solver's answer for the same configuration, a whole
        // turn away, is placed beside the total the joint is holding
        // (`representative_near`), and only then does the offset come back off — with no
        // wrap, or the winding would be the whole turn `runtime_angle` folds away.
        for (offset_deg, runtime_deg) in [
            (0.0_f64, 400.0_f64),
            (90.0, 400.0),
            (-90.0, -400.0),
            (137.5, 719.95),
        ] {
            // What the joint holds, and what the solver reports for the same place: the same
            // total reduced into the single turn `atan2` reads it out of.
            let held = total_angle(offset_deg, runtime_deg);
            let solver = total_angle(offset_deg, runtime_deg % 360.0);
            let placed = units::nearest_representative(solver, held);
            let back = placed - units::deg_to_rad(offset_deg);
            assert!(
                units::wrap_angle(back - runtime_deg.to_radians()).abs() < 1e-12,
                "offset {offset_deg}, runtime {runtime_deg}: placement gives {} degrees",
                units::rad_to_deg(back)
            );
            assert!(
                (placed - held).abs() < 1e-9,
                "offset {offset_deg}, runtime {runtime_deg}: the placed total {} is not the \
                 one the joint holds {held}",
                placed
            );
        }
    }
}
