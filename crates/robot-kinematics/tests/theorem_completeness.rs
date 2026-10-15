//! `exists_solution_angles_eq`: a commanded configuration outside the degenerate cases comes
//! back among the candidates, labelled with its own branches and equal to it in every joint
//! modulo a full turn.
//!
//! The three hypotheses are `NonDegenerate`'s, and each one is a joint the *pose* does not
//! determine: `a1 + planarQ ≠ 0` is `r ≠ 0`, without which joint 1 has no azimuth to be read
//! off; the fold-back `L1 = L2 ∧ q = h = 0`, without which joints 2 and 3 trade off against
//! each other; and `sin θ5 ≠ 0`, without which joints 4 and 6 share an axis and only their sum
//! is observable. This file checks the theorem, checks that its conclusion is *not* vacuous by
//! perturbing a commanded configuration, and checks that each of the three hypotheses is
//! load-bearing — one degenerate configuration per clause, where the conclusion fails.
//!
//! The angle comparison is modulo a full turn, which is the strongest form the claim can take:
//! a pose cannot tell a joint angle apart from that angle plus a full turn. In `f64` the
//! recovery itself rounds — it is a run of `atan2` and `acos` over a chain of rounded
//! products — so the wrapped differences are asserted against the declared tolerance below,
//! which is the same quantifier the Lean omits because over `ℝ` it is zero.

use robot_kinematics::{
    Geometry, SolutionSet, Tolerances, branch::BranchPlan, fk, solutions, solve, total_angle,
    wrap_angle,
};

/// The declared tolerance of the f64 claim, as in `theorem_soundness.rs`. The recovery runs
/// through `atan2`/`acos` of quantities that have already been rounded once, so an exact bit
/// comparison to the commanded angles is not available even for a commanded configuration:
/// what is available is the branch labels, exactly, and the angles modulo a full turn.
const DECLARED: f64 = 1e-9;

fn shipped() -> Geometry<f64> {
    Geometry::shipped()
}

/// splitmix64, so the grid is seeded and a failure is reproducible.
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

/// The planar reduction at a commanded configuration: `Kinematics.planarQ`/`planarH`, which
/// are `planarQAt g (θ 1) (psi θ)` and its vertical companion with `psi = θ 2 - π/2`. The
/// frame-4 origin relative to the frame-1 origin, in the plane joint 1 swung to.
fn planar(g: &Geometry<f64>, theta: &[f64; 6]) -> (f64, f64) {
    let psi = theta[2] - core::f64::consts::FRAC_PI_2;
    let q = g.link_one * theta[1].cos() + g.link_two * (theta[1] + psi).cos();
    let h = g.link_one * theta[1].sin() + g.link_two * (theta[1] + psi).sin();
    (q, h)
}

/// `shoulderBranch`: the sign of `a1 + planarQ`, the projection of the wrist centre onto the
/// direction joint 1 points in. The tie at zero goes to `-1`, the convention the solver's
/// `planarTargetQ` reads the same pose with.
fn shoulder_branch(g: &Geometry<f64>, theta: &[f64; 6]) -> i8 {
    if 0.0 < g.a1 + planar(g, theta).0 {
        1
    } else {
        -1
    }
}

/// `elbowBranch`: the sign of `planarVAt = L2 sin psi`, which is the second link's
/// perpendicular offset. The tie at a straight elbow goes to `+1`.
fn elbow_branch(g: &Geometry<f64>, theta: &[f64; 6]) -> i8 {
    let psi = theta[2] - core::f64::consts::FRAC_PI_2;
    if 0.0 <= g.link_two * psi.sin() { 1 } else { -1 }
}

/// `NonDegenerate`, with the margins a float test needs. Each clause is checked against the
/// commanded configuration's own quantities, exactly as the Lean definition states them.
fn non_degenerate(g: &Geometry<f64>, theta: &[f64; 6]) -> bool {
    let (q, h) = planar(g, theta);
    (g.a1 + q).abs() > 1e-3
        && !(g.link_one == g.link_two && q.abs() <= 1e-6 && h.abs() <= 1e-6)
        && theta[4].sin().abs() > 0.1
}

/// Whether some returned candidate carries the commanded configuration's own branch labels and
/// matches every joint modulo a full turn, which is the theorem's conclusion.
fn recovers(g: &Geometry<f64>, theta: &[f64; 6], out: &SolutionSet<f64>) -> Option<f64> {
    let (sigma, epsilon) = (shoulder_branch(g, theta), elbow_branch(g, theta));
    let mut worst: Option<f64> = None;
    for candidate in out.iter() {
        if candidate.shoulder != sigma || candidate.elbow != epsilon {
            continue;
        }
        let mut worst_here = 0.0f64;
        for (angle, commanded) in candidate.angles.iter().zip(theta.iter()) {
            worst_here = worst_here.max(wrap_angle(*angle - *commanded).abs());
        }
        worst = Some(match worst {
            Some(previous) => previous.min(worst_here),
            None => worst_here,
        });
    }
    worst
}

/// A configuration whose planar target is the fold-back: `q = h = 0` needs the second link
/// turned a half turn from the first, so `psi = π` and `θ3 = 3π/2`. `L1 = L2` comes from the
/// shipped geometry.
fn folded_command(theta2: f64) -> [f64; 6] {
    [
        0.4,
        theta2,
        3.0 * core::f64::consts::FRAC_PI_2,
        0.9,
        1.1,
        2.1,
    ]
}

#[test]
fn exists_solution_angles_eq_on_a_grid() {
    let g = shipped();
    let mut state = 0x5EED_1234_ABCD_0003u64;
    let mut worst = 0.0f64;
    let mut cases = 0usize;
    for _ in 0..400 {
        let theta = [
            spread(&mut state, -3.1, 3.1),
            spread(&mut state, -3.1, 3.1),
            spread(&mut state, -3.1, 3.1),
            spread(&mut state, -3.1, 3.1),
            spread(&mut state, -3.1, 3.1),
            spread(&mut state, -3.1, 3.1),
        ];
        if !non_degenerate(&g, &theta) {
            continue;
        }
        // The transcription's own check: `a1 + planarQ` is the projection of the wrist centre
        // onto the plane joint 1 swung to, which is what `a1_add_planarTargetQ_fk_shoulderBranch`
        // says the solver's planar target reduces to at the configuration's own branch.
        let target = fk(&g, &theta);
        let center = robot_kinematics::wrist_center(&g, &target);
        let sigma = f64::from(shoulder_branch(&g, &theta));
        assert!(
            (g.a1 + planar(&g, &theta).0 - sigma * center.hypot_xy()).abs() <= 1e-9,
            "planarQ transcription at {theta:?}"
        );
        assert!((planar(&g, &theta).1 - (center.z() - g.d1)).abs() <= 1e-9);

        let mut out = SolutionSet::new();
        solutions(&g, &target, &mut out);
        let measured = recovers(&g, &theta, &out)
            .unwrap_or_else(|| panic!("no candidate on the commanded branches at {theta:?}"));
        worst = worst.max(measured);
        cases += 1;
    }
    assert!(cases > 300, "the grid is not vacuous: {cases}");
    assert!(
        worst <= DECLARED,
        "worst wrapped angle difference over {cases} configurations: {worst}"
    );
}

/// The conclusion is not vacuous: perturbing one commanded joint by a milliradian moves the
/// candidate away from the commanded angles by two orders of magnitude more than the tolerance
/// above. A solver that ignored the target, or returned a candidate from the wrong branch,
/// would be caught here rather than absorbed by `DECLARED`.
#[test]
fn the_recovery_is_not_vacuous() {
    let g = shipped();
    let theta = [0.4, total_angle(90.0, 20.0), -0.3, 0.9, 1.2, 2.1];
    let mut other = theta;
    other[1] += 1e-3;
    assert!(non_degenerate(&g, &theta) && non_degenerate(&g, &other));
    assert_eq!(shoulder_branch(&g, &other), shoulder_branch(&g, &theta));
    assert_eq!(elbow_branch(&g, &other), elbow_branch(&g, &theta));
    let mut out = SolutionSet::new();
    solutions(&g, &fk(&g, &theta), &mut out);
    let difference = recovers(&g, &other, &out).expect("the labelled candidate exists");
    assert!(
        difference > 1e-4,
        "a 1e-3 perturbation moved the candidate by only {difference}"
    );
}

/// The wrist clause is load-bearing: at `sin θ5 = 0` joints 4 and 6 share an axis, so the
/// commanded `θ4` cannot come back. Over `ℝ` the solver's candidate is the flat one, holding
/// joint 4 at zero (`wristTheta4`); the swing of its joint 4 away from the commanded 0.9 is the
/// statement that no candidate recovers this configuration.
#[test]
fn the_wrist_clause_is_load_bearing() {
    let g = shipped();
    let theta = [0.4, total_angle(90.0, 20.0), -0.3, 0.9, 0.0, 2.1];
    let target = fk(&g, &theta);
    let mut out = SolutionSet::new();
    solutions(&g, &target, &mut out);
    assert!(!out.is_empty(), "solutions_ne_nil, degenerate or not");
    let (sigma, epsilon) = (shoulder_branch(&g, &theta), elbow_branch(&g, &theta));
    let mut worst_theta4 = 0.0f64;
    for candidate in out
        .iter()
        .filter(|s| s.shoulder == sigma && s.elbow == epsilon)
    {
        worst_theta4 = worst_theta4.max(wrap_angle(candidate.angles[3] - theta[3]).abs());
    }
    assert!(
        worst_theta4 > 0.1,
        "the commanded joint 4 comes back to within {worst_theta4}, so the clause would be free"
    );

    // And the compat layer is where the degenerate case is handled instead: it offers the flat
    // split, which pins joint 4 at zero, and filters the read-backs that do not reproduce the
    // pose. This is divergence 2 of the three `solve` documents.
    let mut compat = SolutionSet::new();
    solve(&g, &target, &Tolerances::python(), &mut compat);
    assert!(
        compat.iter().any(|s| s.angles[3] == 0.0),
        "the flat candidate is the compat layer's answer at the singularity"
    );
}

/// The fold-back clause is load-bearing: `L1 = L2` with `q = h = 0` lets joints 2 and 3 trade
/// off against each other, and the solver's pair is not the commanded one.
#[test]
fn the_fold_back_clause_is_load_bearing() {
    let g = shipped();
    for theta2 in [1.0, -2.0, 2.6] {
        let theta = folded_command(theta2);
        let (q, h) = planar(&g, &theta);
        assert!(
            q.abs() < 1e-9 && h.abs() < 1e-9,
            "the construction is the fold-back: ({q}, {h})"
        );
        assert!(!non_degenerate(&g, &theta), "the clause excludes it");
        let mut out = SolutionSet::new();
        solutions(&g, &fk(&g, &theta), &mut out);
        assert!(!out.is_empty(), "solutions_ne_nil");
        let difference = recovers(&g, &theta, &out).expect("the elbow band keeps both labels here");
        assert!(
            difference > 0.1,
            "theta2 = {theta2}: the folded configuration comes back to within {difference}"
        );
    }
}

/// The base-axis clause is load-bearing at the decision layer: the exact plan says `r = 0` for
/// a wrist centre on the axis and not for one a hair off it, and the pose with `r = 0` does not
/// determine joint 1 at all — the solver anchors the plane at zero and at `π`, which are the
/// only two values that come back.
#[test]
fn the_base_axis_clause_is_load_bearing() {
    use robot_kinematics::{ExactTarget, Mat3, Pose, Vec3};

    let g = shipped();
    let on_axis = ExactTarget::of_center(g.a1, g.d1, g.link_one, g.link_two, 0.0, 0.0, g.d1);
    let plan = BranchPlan::exact(&on_axis);
    assert!(plan.shoulder[0].radius_is_zero);
    assert!(plan.degenerate.wrist_center_on_base_axis);
    assert_eq!(
        plan.elbow_branches[0].count(),
        2,
        "q = -a1 = -10 is still inside the band"
    );

    // The pose that plan describes: its wrist centre is exactly on the axis, so joint 1 is
    // free, and the solver's two anchors are exactly 0 and π.
    let target = Pose::new(Mat3::identity(), Vec3::new(0.0, 0.0, g.d1 + g.tool_offset));
    let mut out = SolutionSet::new();
    solutions(&g, &target, &mut out);
    assert!(!out.is_empty());
    for candidate in out.iter() {
        assert!(
            candidate.angles[0] == 0.0
                || (candidate.angles[0].abs() - core::f64::consts::PI).abs() < 1e-15,
            "joint 1 is anchored, not recovered: {}",
            candidate.angles[0]
        );
    }
}

mod properties {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// The theorem over random non-degenerate configurations: the labels come back exactly
        /// and every joint modulo a full turn.
        #[test]
        fn completeness_on_random_configurations(
            theta in prop::array::uniform6(-3.1f64..3.1f64),
        ) {
            let g = shipped();
            prop_assume!(non_degenerate(&g, &theta));
            let mut out = SolutionSet::new();
            solutions(&g, &fk(&g, &theta), &mut out);
            let measured = recovers(&g, &theta, &out);
            prop_assert!(measured.is_some(), "no candidate on the commanded branches");
            prop_assert!(measured.unwrap() <= DECLARED, "worst {}", measured.unwrap());
        }
    }
}
