//! `fk_of_mem_solutions`: every candidate the closed form returns reproduces the target pose.
//!
//! The Lean statement carries two hypotheses on the target — `T.Rᵀ * T.R = 1` and
//! `T.R.det = 1`, i.e. that its rotation is a rotation — and no reachability hypothesis at
//! all: the theorem holds for targets no configuration reaches, because then the candidate
//! list is simply empty (`solutions_eq_nil_of_not_reachable`). Over `ℝ` the theorem is why
//! `kinematics.py`'s final pose check has nothing to reject, and why the Lean solver does not
//! construct the candidates that check would have thrown away.
//!
//! In `f64` the claim survives everywhere except one place, which this file pins down instead
//! of hiding. The solver reads `sin θ5` off the relative rotation as `hypot (Q02, Q12)`, and a
//! pose that is singular over `ℝ` does not arrive singular as a float: the recovered sine is
//! rounding noise instead of zero. The read-back then splits joints 4 and 6 with an angle the
//! rounding error, divided by that noise, makes meaningless. This degrades the *orientation*
//! only: the third column of the reconstruction — which is the whole of what the position
//! reads, and the whole of what the read-back is built from — stays right to rounding. So the
//! f64 form of the theorem is "position always, orientation while the recovered sine is away
//! from zero", and `the_recovered_sine_guards_the_orientation_claim` is that statement with
//! its guard shown to be necessary rather than decorative.

use robot_kinematics::{
    Geometry, Mat3, Pose, SolutionSet, Tolerances, Vec3, arm_rotation, branch::BranchPlan, fk,
    hypot_third_column, solutions,
};

/// The declared tolerance of the f64 claim. The theorems are exact over `ℝ`; this is the
/// measured rounding of a run of `atan2`/`acos` over a chain of unit-scale links, and the
/// assertions below report the observed worst case so a regression cannot hide under it.
const DECLARED: f64 = 1e-9;

/// The recovered sine above which the wrist read-back is well conditioned. Below it the
/// `θ4`/`θ6` split carries an error of order `ε / sin θ5`, which is the observation that makes
/// `Tolerances::wrist_singularity` a numerical necessity rather than a compatibility knob.
const WELL_CONDITIONED_SINE: f64 = 1e-6;

fn shipped() -> Geometry<f64> {
    Geometry::shipped()
}

/// splitmix64: a seeded generator, so a failure is reproducible from the seed and no test
/// depends on a dependency's RNG.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A uniform `f64` in `[low, high)`.
fn spread(state: &mut u64, low: f64, high: f64) -> f64 {
    let bits = splitmix64(state) >> 11;
    low + (bits as f64 / (1u64 << 53) as f64) * (high - low)
}

/// A commanded configuration. `five` is the fifth joint's total angle's range, which is the
/// knob the callers below use to walk from well conditioned to exactly singular.
fn commanded(state: &mut u64, five: (f64, f64)) -> [f64; 6] {
    [
        spread(state, -3.1, 3.1),
        spread(state, -3.1, 3.1),
        spread(state, -3.1, 3.1),
        spread(state, -3.1, 3.1),
        spread(state, five.0, five.1),
        spread(state, -3.1, 3.1),
    ]
}

/// The two error measures `kinematics.py` filters on, in the order it names them: the
/// Euclidean distance of the positions, and the Frobenius norm of the 3x3 rotation
/// difference.
fn errors(g: &Geometry<f64>, target: &Pose<f64>, angles: &[f64; 6]) -> (f64, f64) {
    let reconstructed = fk(g, angles);
    (
        reconstructed.p.distance(target.p),
        reconstructed.r.frobenius_distance(target.r),
    )
}

/// The recovered wrist sine of a candidate: `wristSine` at the candidate's own arm angles, by
/// the definition `wrist_plan_exact` names — the length of the relative rotation's third
/// column's first two entries.
fn recovered_sine(target: &Pose<f64>, angles: &[f64; 6]) -> f64 {
    let relative = arm_rotation(angles[0], angles[1], angles[2]).transpose() * target.r;
    hypot_third_column(&relative)
}

/// A pose whose wrist centre is `(x, y, z)` and whose rotation is the identity: the identity's
/// z axis is `(0, 0, 1)`, so the geometry's tool offset `d6` is added along it.
fn pose_at_center(g: &Geometry<f64>, x: f64, y: f64, z: f64) -> Pose<f64> {
    Pose::new(Mat3::identity(), Vec3::new(x, y, z + g.tool_offset))
}

/// The round trip on configurations the arm can actually strike, which is `fk_of_mem_solutions`
/// instantiated at `T = fk g θ` with `fk_R_orth` and `fk_R_det`. The fifth joint is kept away
/// from the singularity, which is the guard derived below.
#[test]
fn fk_of_mem_solutions_on_commanded_configurations() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0001u64;
    let mut worst = (0.0f64, 0.0f64);
    let mut candidates = 0usize;
    for _ in 0..200 {
        let theta = commanded(&mut state, (0.3, 2.9));
        if theta[4].abs() < 0.3 {
            continue;
        }
        let target = fk(&g, &theta);
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(!out.is_empty(), "solutions_ne_nil at {theta:?}");
        for candidate in out.iter() {
            let measured = errors(&g, &target, &candidate.angles);
            worst = (worst.0.max(measured.0), worst.1.max(measured.1));
            candidates += 1;
        }
    }
    assert!(candidates > 1000, "the grid is not vacuous: {candidates}");
    assert!(
        worst.0 <= DECLARED && worst.1 <= DECLARED,
        "worst (position, orientation) error over {candidates} candidates: {worst:?}"
    );
}

/// The f64 form of the theorem, with the guard that `f64` needs and `ℝ` does not: the position
/// is reproduced always, the orientation while the recovered sine is away from zero.
///
/// The fifth joint walks from well inside to exactly zero, and the test also asserts that the
/// guard is *necessary* — that at least one candidate in this sweep is off in orientation by
/// more than the declared tolerance. Without that, the guard could be hiding a solver that
/// never read a rotation at all.
#[test]
fn the_recovered_sine_guards_the_orientation_claim() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0002u64;
    let mut worst_position = 0.0f64;
    let mut worst_conditioned = 0.0f64;
    let mut worst_ill = 0.0f64;
    let mut ill = 0usize;
    let mut cases = vec![
        // The two exact arm configurations that are singular over `ℝ`: joints 4 and 6 share an
        // axis at `θ5 = 0` and at `θ5 = π`.
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
    ];
    for exponent in 4..14 {
        let tiny = 10f64.powi(-exponent);
        for sign in [1.0, -1.0] {
            cases.push([
                0.7,
                robot_kinematics::total_angle(90.0, -35.0),
                0.4,
                -1.1,
                sign * tiny,
                0.8,
            ]);
        }
    }
    for _ in 0..120 {
        cases.push(commanded(&mut state, (-0.02, 0.02)));
    }
    for theta in cases {
        let target = fk(&g, &theta);
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(!out.is_empty(), "solutions_ne_nil at {theta:?}");
        for candidate in out.iter() {
            let (position, orientation) = errors(&g, &target, &candidate.angles);
            let sine = recovered_sine(&target, &candidate.angles);
            worst_position = worst_position.max(position);
            if sine > WELL_CONDITIONED_SINE {
                worst_conditioned = worst_conditioned.max(orientation);
            } else {
                worst_ill = worst_ill.max(orientation);
                if orientation > DECLARED {
                    ill += 1;
                }
            }
        }
    }
    assert!(
        worst_position <= DECLARED,
        "position error {worst_position} at a near-singular target"
    );
    assert!(
        worst_conditioned <= DECLARED,
        "orientation error {worst_conditioned} with the sine well conditioned"
    );
    assert!(
        ill > 0,
        "the sine guard is not vacuous only if it excludes something; worst ill-conditioned \
         orientation error was {worst_ill}"
    );
}

/// The rotation hypothesis is load-bearing, not hygiene: `solutions` reads a target only
/// through its wrist centre — and so through the third column of `R` alone — so a target whose
/// rotation is not a rotation still comes back with candidates, while no configuration
/// reproduces it. Over `ℝ` there is no filter to discard them with; this is exactly the case
/// that makes `solutions_eq_nil_of_not_reachable` state its hypotheses.
#[test]
fn the_rotation_hypothesis_is_load_bearing() {
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
    // A rotation scaled by 11/10: still symmetric, no longer a rotation. Its third column is
    // off by a tenth of a unit before normalization, and `wrist_center` moves with it.
    let scaled = Pose::new(reachable.r.scale(1.1), reachable.p);
    let mut out = SolutionSet::new();
    solutions(&g, &scaled, &mut out);
    assert!(
        !out.is_empty(),
        "the solver builds candidates from a target that is not a pose"
    );
    for candidate in out.iter() {
        let (position, orientation) = errors(&g, &scaled, &candidate.angles);
        assert!(
            orientation > 1e-3,
            "no candidate should reproduce a non-rotation: {orientation}"
        );
        assert!(
            position > 1e-3,
            "the position is off along the scaled third column: {position}"
        );
    }
    // The same target with its rotation left alone is reproduced, so the failure above is the
    // hypothesis and not the tolerance.
    let mut exact = SolutionSet::new();
    solutions(&g, &reachable, &mut exact);
    for candidate in exact.iter() {
        let (position, orientation) = errors(&g, &reachable, &candidate.angles);
        assert!(position <= DECLARED && orientation <= DECLARED);
    }
}

/// The degenerate targets the specification singles out, which are the ones a pose filter
/// would be tempted to throw away and the ones a tolerance-based band test gets wrong:
/// the folded arm, the wrist centre exactly on the base axis, and both exact band edges.
/// Soundness claims nothing about them being *recoverable*, only that what comes back
/// reproduces the pose — `theorem_completeness.rs` is where the degeneracy bites.
#[test]
fn degenerate_targets_are_still_sound() {
    let g = shipped();
    // The fold-back: `linkOne = linkTwo` and the planar target `(0, 0)`, so `q = r - a1 = 0`
    // and `h = z - d1 = 0`. This is also the shipped geometry's *inner* band edge, since
    // `(L1 - L2)² = 0`.
    let folded = pose_at_center(&g, 10.0, 0.0, 32.0);
    // The outer band edge: `q = r - a1 = 50 = L1 + L2`, straight out along the arm's plane.
    let stretched = pose_at_center(&g, 60.0, 0.0, 32.0);
    // The wrist centre on the base axis: `θ1` has no azimuth to be read off, so the solver
    // anchors the plane at zero.
    let on_axis = pose_at_center(&g, 0.0, 0.0, 32.0);
    // And a target between the shoulders, where the two branches swap roles.
    let other_side = pose_at_center(&g, -30.0, 0.0, 52.0);
    for (name, target) in [
        ("folded", folded),
        ("stretched", stretched),
        ("on axis", on_axis),
        ("negative radial target", other_side),
    ] {
        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        assert!(!out.is_empty(), "{name}: solutions_ne_nil");
        for candidate in out.iter() {
            let (position, orientation) = errors(&g, &target, &candidate.angles);
            assert!(
                position <= DECLARED && orientation <= DECLARED,
                "{name}: ({position}, {orientation})"
            );
        }
    }

    // The inner band edge for a geometry with `L1 ≠ L2`, where it is not the fold-back:
    // `q = L2 - L1 = 30` with `h = 0` puts `q² + h²` exactly on `(L1 + L2)²`'s partner bound.
    let asymmetric = Geometry::new(10.0, 40.0, 20.0, 50.0, 10.0).expect("positive links");
    let inner = pose_at_center(&asymmetric, 40.0, 0.0, 40.0);
    let mut out = SolutionSet::new();
    solutions(&asymmetric, &inner, &mut out);
    assert!(!out.is_empty(), "the inner edge is reachable, exactly");
    for candidate in out.iter() {
        let (position, orientation) = errors(&asymmetric, &inner, &candidate.angles);
        assert!(position <= DECLARED && orientation <= DECLARED);
    }
}

/// The exact plan agrees with the float plan on these targets, which is what makes the
/// degeneracy classification in `branch.rs` the right one to cite here: the fold-back and the
/// radius anchor are decisions the exact and float layers make the same way, so the cases
/// above really are the degenerate ones rather than targets near them.
#[test]
fn the_named_targets_are_the_degenerate_ones() {
    let g = shipped();
    let folded = pose_at_center(&g, 10.0, 0.0, 32.0);
    let plan = BranchPlan::of_pose(&g, &folded, &Tolerances::exact());
    assert!(plan.degenerate.fold_back[0], "q = 0 with L1 = L2 and h = 0");
    assert!(!plan.degenerate.fold_back[1], "sigma = -1 has q = -20");

    let on_axis = pose_at_center(&g, 0.0, 0.0, 32.0);
    let plan = BranchPlan::of_pose(&g, &on_axis, &Tolerances::exact());
    assert!(plan.shoulder[0].radius_is_zero);
    assert!(plan.degenerate.wrist_center_on_base_axis);

    let stretched = pose_at_center(&g, 60.0, 0.0, 32.0);
    let plan = BranchPlan::of_pose(&g, &stretched, &Tolerances::exact());
    assert!(
        plan.elbow_branches[0].count() == 2,
        "the exact band test accepts its own boundary: q = 50 = L1 + L2 exactly"
    );
    assert!(
        plan.elbow_branches[1].is_empty(),
        "and the other shoulder branch is out of reach: q = -70"
    );
}

mod properties {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// `fk_of_mem_solutions` over random commanded configurations, in the f64 form the
        /// guard above establishes: position always, orientation while the recovered sine is
        /// well conditioned. The elbow is kept away from straight, where the two branches
        /// coincide and the recovered `θ2`/`θ3` split is as ill conditioned as the wrist's.
        #[test]
        fn soundness_on_random_configurations(theta in prop::array::uniform6(-3.1f64..3.1f64)) {
            prop_assume!(theta[4].abs() >= 0.25);
            let g = shipped();
            let target = fk(&g, &theta);
            let mut out = SolutionSet::new();
            solutions(&g, &target, &mut out);
            prop_assert!(!out.is_empty());
            for candidate in out.iter() {
                let (position, orientation) = errors(&g, &target, &candidate.angles);
                prop_assert!(position <= DECLARED, "position {}", position);
                if recovered_sine(&target, &candidate.angles) > WELL_CONDITIONED_SINE {
                    prop_assert!(orientation <= DECLARED, "orientation {}", orientation);
                }
            }
        }

        /// The same theorem on random *poses* rather than poses built by the chain: an
        /// arbitrary rotation with the wrist centre inside the reachable band. The rotation is
        /// a product of three axis rotations, so it is a rotation — the theorem's hypothesis,
        /// which `fk` would have supplied for free.
        ///
        /// The box is drawn around the shipped arm's reach (`L1 + L2 = 50`, `d1 = 32`), so
        /// most of what it samples is a pose the arm can actually strike.
        #[test]
        fn soundness_on_random_poses(
            a in -3.1f64..3.1,
            b in -3.1f64..3.1,
            c in -3.1f64..3.1,
            x in -60f64..60.0,
            y in -60f64..60.0,
            z in -20f64..90.0,
        ) {
            let g = shipped();
            let rotation = Mat3::rot_z(a) * Mat3::rot_y(b) * Mat3::rot_z(c);
            let target = Pose::new(rotation, Vec3::new(x, y, z));
            let mut out = SolutionSet::new();
            solutions(&g, &target, &mut out);
            // Off the base axis and away from the wrist singularity the solver has candidates;
            // whether it does is `theorem_coverage.rs`'s business, not this property's.
            for candidate in out.iter() {
                let (position, orientation) = errors(&g, &target, &candidate.angles);
                prop_assert!(position <= DECLARED, "position {}", position);
                if recovered_sine(&target, &candidate.angles) > WELL_CONDITIONED_SINE {
                    prop_assert!(orientation <= DECLARED, "orientation {}", orientation);
                }
            }
        }
    }
}
