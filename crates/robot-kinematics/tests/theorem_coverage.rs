//! `solutions_ne_nil`, `length_solutions_le_eight`, `solutions_eq_nil_of_not_reachable`,
//! `exists_fk_eq_of_solutions_ne_nil` and `exists_solution_sin_five_eq_zero`: the properties of
//! the candidate *list* rather than of any angle in it.
//!
//! These are the theorems that say what the solver's shape is. The list is non-empty for every
//! pose the arm can strike, at most eight entries long for every pose at all, empty exactly
//! when nothing reaches the target, and — where the wrist is singular — containing a candidate
//! with joint 4 pinned at zero. Two of them are exact in `f64` and not merely approximate:
//! `length_solutions_le_eight` is a bound on a fixed-capacity buffer, and the flat candidate
//! pins joint 4 at the *literal* `0.0`, which is what makes `exists_solution_sin_five_eq_zero`
//! checkable with `==` rather than with a tolerance.
//!
//! The one gap this file states rather than hides: `exists_solution_sin_five_eq_zero`'s
//! hypothesis, `sin θ5 = 0`, is satisfied by a commanded configuration but *not* by the pose
//! that configuration strikes in `f64`. The solver reads the middle wrist angle off the
//! relative rotation's third column, and that column is rounding noise there rather than a
//! zero, so the exact function never takes its flat branch on a pose that came out of `fk`.
//! The property is therefore exercised where it lives — the reconstruction layer, on a
//! rotation whose third column *is* exactly the z axis — and the compat layer's
//! tolerance-based route to the same candidate is exercised through `solve`.

use robot_kinematics::{
    BranchPlan, Geometry, MAX_SOLUTIONS, Mat3, Pose, SolutionSet, Tolerances, Vec3, arm_rotation,
    branch::ExactTarget, fk, hypot_third_column, reconstruct_flat, solutions, solve, wrist_plan,
    wrist_plan_exact,
};

/// The declared tolerance of the f64 claims that need one, as in the other two suites.
const DECLARED: f64 = 1e-9;

/// The recovered sine above which the wrist read-back is well conditioned.
const WELL_CONDITIONED_SINE: f64 = 1e-6;

fn shipped() -> Geometry<f64> {
    Geometry::shipped()
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn spread(state: &mut u64, low: f64, high: f64) -> f64 {
    let bits = splitmix64(state) >> 11;
    low + (bits as f64 / (1u64 << 53) as f64) * (high - low)
}

fn recovered_sine(target: &Pose<f64>, angles: &[f64; 6]) -> f64 {
    let relative = arm_rotation(angles[0], angles[1], angles[2]).transpose() * target.r;
    hypot_third_column(&relative)
}

/// The configurations whose poses are the awkward ones: the wrist exactly at each end of its
/// middle angle, a straight elbow, the fold-back, and each wrist joint at a boundary value.
fn awkward_configurations() -> Vec<[f64; 6]> {
    let half = core::f64::consts::FRAC_PI_2;
    vec![
        [0.0; 6],
        [
            0.4,
            robot_kinematics::total_angle(90.0, 20.0),
            -0.3,
            0.9,
            0.0,
            2.1,
        ],
        [
            0.4,
            robot_kinematics::total_angle(90.0, 20.0),
            -0.3,
            0.9,
            core::f64::consts::PI,
            2.1,
        ],
        [1.1, 0.7, half, -2.0, half, 0.3],
        // The fold-back: `psi = pi` puts the second link back along the first.
        [0.4, 1.0, 3.0 * half, 0.9, 1.1, 2.1],
        [0.4, -2.0, -half, -0.9, -1.4, 3.0],
    ]
}

/// `solutions_ne_nil`: for *every* configuration — degenerate ones included, and no
/// non-degeneracy hypothesis anywhere — the pose it strikes has at least one candidate.
///
/// The proof's witness is the configuration's own shoulder branch with any elbow and wrist
/// labels, so what this asserts is that the solver's band test accepts a planar target that a
/// real configuration produced.
#[test]
fn solutions_ne_nil_for_every_configuration() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0005u64;
    let mut configurations = awkward_configurations();
    for _ in 0..300 {
        configurations.push([
            spread(&mut state, -3.2, 3.2),
            spread(&mut state, -3.2, 3.2),
            spread(&mut state, -3.2, 3.2),
            spread(&mut state, -3.2, 3.2),
            spread(&mut state, -3.2, 3.2),
            spread(&mut state, -3.2, 3.2),
        ]);
    }
    for theta in configurations {
        let mut out = SolutionSet::new();
        solutions(&g, &fk(&g, &theta), &mut out);
        assert!(!out.is_empty(), "solutions_ne_nil at {theta:?}");
    }
}

/// `length_solutions_le_eight`: two shoulder branches, at most two elbow branches each, one
/// candidate per wrist branch. The bound mentions nothing about the pose, so the targets here
/// include ones no configuration reaches, ones whose rotation is not a rotation, and ones
/// whose coordinates are absurd — the solver reads them all the same way.
///
/// This is the strongest `f64` statement in the suite: it is a bound on a fixed-capacity
/// buffer, so it holds with no tolerance and `overflowed` must never be set on this path.
#[test]
fn length_solutions_le_eight_for_arbitrary_targets() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0006u64;
    let mut targets = vec![
        Pose::identity(),
        Pose::new(Mat3::identity(), Vec3::new(400.0, 0.0, 40.0)),
        Pose::new(Mat3::identity(), Vec3::new(0.0, 0.0, 1e12)),
        Pose::new(Mat3::identity(), Vec3::new(0.0, 0.0, -1e12)),
        // Not a rotation at all, and not even symmetric once the shear is applied: the solver
        // reads the third column and nothing else, so it builds candidates anyway.
        Pose::new(
            Mat3::from_rows([[1.1, 0.2, 0.0], [0.0, 1.1, 0.0], [0.0, 0.0, 1.1]]),
            Vec3::new(10.0, 0.0, 40.0),
        ),
        Pose::new(
            Mat3::scale(Mat3::identity(), 1.1),
            Vec3::new(10.0, 0.0, 60.0),
        ),
    ];
    for _ in 0..200 {
        let rotation = Mat3::rot_z(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_y(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_z(spread(&mut state, -3.2, 3.2));
        targets.push(Pose::new(
            rotation,
            Vec3::new(
                spread(&mut state, -500.0, 500.0),
                spread(&mut state, -500.0, 500.0),
                spread(&mut state, -500.0, 500.0),
            ),
        ));
    }
    for target in targets {
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(
            out.len() <= MAX_SOLUTIONS,
            "length_solutions_le_eight: {} candidates",
            out.len()
        );
        assert!(
            !out.overflowed(),
            "a ninth candidate was built for {target:?}"
        );
    }
}

/// The candidate count is `candidate_count` computed from the plan, not merely bounded by the
/// shape of the loops: `solutions` pushes exactly the candidates the plan says it will, so
/// `length_solutions_le_eight`'s bound is the sum it was written as.
#[test]
fn the_candidate_count_is_the_plan_computed() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0007u64;
    let mut counts = [0usize; 9];
    let mut targets: Vec<Pose<f64>> = awkward_configurations()
        .into_iter()
        .map(|theta| fk(&g, &theta))
        .collect();
    for _ in 0..200 {
        let rotation = Mat3::rot_z(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_y(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_z(spread(&mut state, -3.2, 3.2));
        targets.push(Pose::new(
            rotation,
            Vec3::new(
                spread(&mut state, -120.0, 120.0),
                spread(&mut state, -120.0, 120.0),
                spread(&mut state, -60.0, 140.0),
            ),
        ));
    }
    for target in targets {
        let plan = BranchPlan::of_pose(&g, &target, &Tolerances::exact());
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert_eq!(
            out.len(),
            robot_kinematics::candidate_count(&plan),
            "the plan predicts the count at {target:?}"
        );
        counts[out.len()] += 1;
    }
    // Both an empty and a full candidate list occur in this sweep, so the equality above is
    // not the trivial one it would be on a grid where every target behaves the same way.
    assert!(counts[0] > 0, "an unreachable target is in the sweep");
    assert!(
        counts[MAX_SOLUTIONS] > 0,
        "a target with all three branch families is in the sweep"
    );
}

/// `solutions_eq_nil_of_not_reachable`: a pose no configuration reaches is a pose the solver
/// answers with nothing. Stated in Lean with the unreachability as an explicit
/// `∀ θ, fk g θ ≠ T`; here the unreachability is witnessable from the target's geometry, which
/// is what the exact plan's empty elbow families say.
#[test]
fn solutions_eq_nil_of_not_reachable() {
    let g = shipped();
    // Beyond `L1 + L2` in the plane, on both shoulder branches: far out along x, and straight
    // up the base axis (where the planar target degenerates to `q = -a1`, `h` alone).
    let far_out = Pose::new(Mat3::identity(), Vec3::new(400.0, 0.0, 40.0));
    let far_up = Pose::new(Mat3::identity(), Vec3::new(0.0, 0.0, 400.0));
    // Just outside the band, which the *exact* test rejects and Python's tolerance accepts:
    // `q = 80 + 1e-3` against the bound `L1 + L2 = 80`.
    let just_outside = Pose::new(Mat3::identity(), Vec3::new(90.001, 0.0, 40.0));
    for (name, target) in [
        ("far out", far_out),
        ("far up", far_up),
        ("just outside", just_outside),
    ] {
        let plan = BranchPlan::of_pose(&g, &target, &Tolerances::exact());
        assert!(
            plan.elbow_branches[0].is_empty() && plan.elbow_branches[1].is_empty(),
            "{name}: the exact plan rejects both shoulder branches"
        );
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(out.is_empty(), "{name}");
    }

    // And the reason the exact plan is the right witness: `q² + h²` against `(L1 + L2)²`,
    // which for the shipped geometry is the same test the plan makes.
    let center = Vec3::new(90.001, 0.0, 40.0);
    let target = ExactTarget::of_center(
        g.a1,
        g.d1,
        g.link_one,
        g.link_two,
        center.x(),
        center.y(),
        center.z(),
    );
    let reach = g.link_one + g.link_two;
    assert!(target.height * target.height + (center.hypot_xy() - g.a1).powi(2) > reach * reach);
}

/// The orthogonality hypotheses of `solutions_eq_nil_of_not_reachable` are load-bearing, not
/// hygiene: the theorem's other hypothesis is that nothing reaches the target, and for a
/// target whose rotation is not a rotation that hypothesis *does* hold — `fk`'s rotation has
/// determinant one (`fk_R_det`) while this one has determinant `1.331` — and yet the solver
/// returns candidates, because it reads the target only through its wrist centre and so
/// through the third column of `R`.
#[test]
fn the_orthogonality_hypothesis_is_load_bearing() {
    let g = shipped();
    let theta = [
        0.4,
        robot_kinematics::total_angle(90.0, 20.0),
        -0.3,
        0.9,
        1.2,
        2.1,
    ];
    let reachable = fk(&g, &theta);
    let scaled = Pose::new(reachable.r.scale(1.1), reachable.p);
    assert!(
        (scaled.r.det() - 1.0).abs() > 0.1,
        "no configuration reaches it: fk's rotation has determinant one"
    );
    let mut out = SolutionSet::new();
    solutions(&g, &scaled, &mut out);
    assert!(
        !out.is_empty(),
        "the non-reachability hypothesis alone does not empty the list"
    );
}

/// `exists_fk_eq_of_solutions_ne_nil`: a non-empty candidate list means the pose is reachable —
/// the converse of `solutions_ne_nil`, and the statement that an empty list is the whole of the
/// solver's rejection behavior. In `f64` the witness is a candidate that reproduces the target,
/// which is `fk_of_mem_solutions` read at one removing.
#[test]
fn exists_fk_eq_of_solutions_ne_nil() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0008u64;
    let mut targets: Vec<Pose<f64>> = awkward_configurations()
        .into_iter()
        .map(|theta| fk(&g, &theta))
        .collect();
    for _ in 0..200 {
        let rotation = Mat3::rot_z(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_y(spread(&mut state, -3.2, 3.2))
            * Mat3::rot_z(spread(&mut state, -3.2, 3.2));
        targets.push(Pose::new(
            rotation,
            Vec3::new(
                spread(&mut state, -100.0, 100.0),
                spread(&mut state, -100.0, 100.0),
                spread(&mut state, -40.0, 120.0),
            ),
        ));
    }
    let mut reachable = 0usize;
    for target in targets {
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        if out.is_empty() {
            continue;
        }
        reachable += 1;
        let witness = out.iter().any(|candidate| {
            let reconstructed = fk(&g, &candidate.angles);
            reconstructed.p.distance(target.p) <= DECLARED
                && (recovered_sine(&target, &candidate.angles) <= WELL_CONDITIONED_SINE
                    || reconstructed.r.frobenius_distance(target.r) <= DECLARED)
        });
        assert!(witness, "no witness for a reachable target {target:?}");
    }
    assert!(reachable > 20, "the sweep is not vacuous: {reachable}");
}

/// `exists_solution_sin_five_eq_zero`, at the layer where its hypothesis is reachable in
/// `f64`: the reconstruction. A rotation whose third column *is* the z axis has
/// `wristSine = hypot (Q02) (Q12) = 0` exactly, so the wrist is at the singularity, the flat
/// candidate pins joint 4 at zero, and the middle angle collapses to `atan2 0 (Q22) = 0` — a
/// zero whose sine is exactly zero, not a small number.
///
/// The gap this states: no pose `fk` produces lands there. The last block measures it — for a
/// commanded configuration with `θ5 = 0` the *recovered* sine is noise, so the exact solver
/// takes its read-back branch and only the compat layer's declared tolerance reaches the flat
/// candidate. That is `Tolerances::wrist_singularity` earning its place.
#[test]
fn exists_solution_sin_five_eq_zero_at_the_reconstruction() {
    for phi in [0.0, 0.7, -2.2, 3.0] {
        let relative = Mat3::<f64>::rot_z(phi);
        assert!(wrist_plan(&relative, &Tolerances::exact()).singular);
        assert!(wrist_plan_exact(&relative).singular);
        let flat = reconstruct_flat(&relative);
        assert_eq!(flat.theta4, 0.0, "joint 4 is pinned at zero, literally");
        assert_eq!(flat.theta5, 0.0, "atan2 0 1 is zero, exactly");
        assert_eq!(flat.theta5.sin(), 0.0, "so its sine is zero, exactly");
        // Flattening leaves the rotation alone here, so joint 6 reads back the angle that
        // built it: the flat candidate is a genuine solution, not a degenerate guess.
        assert!((flat.theta6 - phi).abs() <= DECLARED);
    }

    // The measurement that makes the paragraph above true, and the reason the compat layer's
    // threshold is a numerical necessity rather than a compatibility knob.
    let g = shipped();
    let theta = [
        0.4,
        robot_kinematics::total_angle(90.0, 20.0),
        -0.3,
        0.9,
        0.0,
        2.1,
    ];
    let target = fk(&g, &theta);
    let mut out = SolutionSet::new();
    solutions(&g, &target, &mut out);
    let worst = out
        .iter()
        .map(|candidate| recovered_sine(&target, &candidate.angles))
        .fold(f64::INFINITY, f64::min);
    assert!(
        worst > 0.0 && worst < 1e-12,
        "a commanded singularity arrives as noise: {worst}"
    );
    // The compat layer reaches the flat candidate by its declared tolerance instead.
    let mut compat = SolutionSet::new();
    solve(&g, &target, &Tolerances::python(), &mut compat);
    assert!(
        compat.iter().any(|candidate| candidate.angles[3] == 0.0),
        "the flat candidate is what the compat layer offers"
    );
}
