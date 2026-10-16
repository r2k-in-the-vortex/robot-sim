//! The branch and degeneracy decisions against the exact plans `lean/BranchDecisionQ.lean`
//! generates.
//!
//! That file evaluates the decision layer of `InverseKinematics.lean` over `ℚ` and writes
//! `test_data/branch_plans.json`; regenerate it with `cargo xtask gen-golden`. Every numeral
//! in the document is exact, so everything below is compared with `==` on `Ratio` values
//! rather than against a tolerance — a failure here is a disagreement with the specification,
//! not floating-point drift.
//!
//! This is the counterpart of `tests/lean_ground_truth.rs`: that file holds the forward chain
//! to the rational vectors Lean computed, and this one holds `branch.rs`'s exact layer to the
//! plans Lean computed for the same kind of target. The reachability band is why the plans
//! could not be compared this way before: `elbowCosine` is a comparison in `ℚ(√ρ)`, so the
//! generator carries the radical symbolically and squares with sign care, and the consumer
//! runs the same five-way split. The `f64` route is checked against these plans too, in
//! `the_float_plan_agrees_where_the_target_is_representable`, but as a diagnostic: the
//! tolerance-free agreement that matters is the exact one.

use robot_golden::{Ratio as R, entries, matrix3, name, numeral_at, vec3};
use robot_kinematics::branch::{SHOULDER_BRANCHES, branch_sign};
use robot_kinematics::{
    BranchPlan, Degeneracy, ElbowBranches, ExactTarget, Field, Geometry, Mat3, Pose, ShoulderPlan,
    Tolerances, Vec3, WristBranches, candidate_count, wrist_center, wrist_plan_exact,
};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

/// The generated corpus, embedded at compile time: the test then depends on nothing but the
/// file the repository commits, and not on the working directory it runs from.
const DOCUMENT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../test_data/branch_plans.json"
));

/// The forward-chain corpus, for two things the branch decisions do not need: the tool offset
/// of each geometry, and the arm dimensions the two corpora have to agree on.
const FRAMES: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../test_data/kinematics_frames.json"
));

/// One entry, with the parts the checks need read out.
struct Case {
    name: String,
    /// The geometry's dimensions as the branch corpus states them.
    geometry: Geometry<R>,
    /// The name the entry refers to its geometry by, for the float route's lookup.
    geometry_name: String,
    /// The wrist centre `(x₄, y₄, z₄)` — the exact target's only free input.
    center: [R; 3],
    /// The relative rotation `R_3^6` the wrist decision reads.
    rotation: Mat3<R>,
    /// The `leOfRadical` arm the entry is written for, as the corpus names it.
    branch: String,
    /// `√ρ` when the entry states it, which obliges the entry to be right about it.
    radius: Option<R>,
    /// The `expected` block, left as JSON so each check reads the fields it wants.
    expected: Value,
}

impl Case {
    /// The exact target this entry is a case for.
    fn target(&self) -> ExactTarget<R> {
        ExactTarget::of_center(
            self.geometry.a1,
            self.geometry.d1,
            self.geometry.link_one,
            self.geometry.link_two,
            self.center[0],
            self.center[1],
            self.center[2],
        )
    }

    /// The plan the entry says the decision layer produces for it.
    fn expected_plan(&self) -> BranchPlan {
        BranchPlan::exact(&self.target())
    }
}

/// The document, parsed for this test. Parsing is microseconds, and a test that owns its data
/// cannot be disturbed by another one.
fn document() -> Value {
    serde_json::from_str(DOCUMENT).expect("the generated branch plans are valid JSON")
}

/// The geometries the branch corpus defines, by the name an entry refers to them by.
fn geometries(document: &Value) -> BTreeMap<String, Geometry<R>> {
    entries(document, "geometries")
        .expect("the document defines its geometries")
        .iter()
        .map(|record| {
            let geometry_name = name(record).to_owned();
            let dimension = |key: &str| {
                numeral_at(record, key)
                    .unwrap_or_else(|error| panic!("geometry {geometry_name}: {error}"))
            };
            let geometry = Geometry::new(
                dimension("a1"),
                dimension("d1"),
                dimension("link_one"),
                dimension("link_two"),
                // The branch decisions read no tool offset, so the corpus carries none; the
                // geometry is still built through the same constructor as everywhere else,
                // and the offset is checked against the forward-chain corpus in
                // `the_geometries_are_the_arms_the_forward_chain_corpus_uses`.
                R::zero(),
            )
            .expect("a generated geometry is a supported arm");
            (geometry_name, geometry)
        })
        .collect()
}

/// Every entry of the document.
fn cases() -> Vec<Case> {
    let document = document();
    let geometries = geometries(&document);
    entries(&document, "entries")
        .expect("the document lists its entries")
        .iter()
        .map(|record| {
            let case = name(record).to_owned();
            let geometry_name = record
                .get("geometry")
                .and_then(Value::as_str)
                .unwrap_or_else(|| panic!("entry {case}: no geometry named"))
                .to_owned();
            let geometry = *geometries
                .get(&geometry_name)
                .unwrap_or_else(|| panic!("entry {case}: undefined geometry {geometry_name:?}"));
            let center = vec3(&record["center"]).expect("a wrist centre is a three-vector");
            let radius = match &record["radius"] {
                Value::Null => None,
                value => Some(
                    robot_golden::numeral(value)
                        .unwrap_or_else(|error| panic!("entry {case}: radius: {error}")),
                ),
            };
            Case {
                branch: record["branch"]
                    .as_str()
                    .unwrap_or_else(|| panic!("entry {case}: no branch tag"))
                    .to_owned(),
                rotation: Mat3::from_rows(
                    matrix3(&record["relative_rotation"]).expect("a relative rotation is 3x3"),
                ),
                center: [center[0], center[1], center[2]],
                expected: record["expected"].clone(),
                geometry,
                geometry_name,
                radius,
                name: case,
            }
        })
        .collect()
}

/// A Boolean field of an `expected` block.
fn expect_bool(block: &Value, key: &str, case: &str) -> bool {
    block
        .get(key)
        .and_then(Value::as_bool)
        .unwrap_or_else(|| panic!("{case}: {key} is not a Boolean"))
}

/// A two-element Boolean field, in generation order.
fn expect_bool_pair(block: &Value, key: &str, case: &str) -> [bool; 2] {
    let array = block
        .get(key)
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{case}: {key} is not an array"));
    assert_eq!(
        array.len(),
        2,
        "{case}: {key} has one entry per shoulder branch"
    );
    core::array::from_fn(|i| {
        array[i]
            .as_bool()
            .unwrap_or_else(|| panic!("{case}: {key}[{i}] is not a Boolean"))
    })
}

/// A 2x2 Boolean field: one pair per shoulder branch, `+1` first.
fn expect_bool_matrix(block: &Value, key: &str, case: &str) -> [[bool; 2]; 2] {
    let array = block
        .get(key)
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{case}: {key} is not an array"));
    assert_eq!(
        array.len(),
        2,
        "{case}: {key} has one entry per shoulder branch"
    );
    core::array::from_fn(|slot| {
        let pair = array[slot]
            .as_array()
            .unwrap_or_else(|| panic!("{case}: {key}[{slot}] is not an array"));
        assert_eq!(
            pair.len(),
            2,
            "{case}: {key}[{slot}] has one entry per elbow label"
        );
        core::array::from_fn(|i| {
            pair[i]
                .as_bool()
                .unwrap_or_else(|| panic!("{case}: {key}[{slot}][{i}] is not a Boolean"))
        })
    })
}

/// The count field of an `expected` block.
fn expect_count(block: &Value, key: &str, case: &str) -> usize {
    block
        .get(key)
        .and_then(Value::as_u64)
        .unwrap_or_else(|| panic!("{case}: {key} is not a count")) as usize
}

/// Which of `le_of_radical`'s five arms a comparison `m <= k * sqrt rho` enters, as the
/// corpus's tags name them.
fn arm_of(m: R, k: R) -> &'static str {
    let zero = R::zero();
    if k == zero {
        "k_zero"
    } else if m <= zero {
        if k > zero {
            "m_nonpos_k_pos"
        } else {
            "m_nonpos_k_neg"
        }
    } else if k > zero {
        "m_pos_k_pos"
    } else {
        "m_pos_k_neg"
    }
}

/// The arms a target's four comparisons enter: the lower and upper edge comparison of `+1`,
/// then the same two for `-1`, mirroring `BranchPlan::exact`'s two `le_of_radical` calls per
/// shoulder branch. The corpus states the arm each entry is written for; this is the check
/// that the claim is true of the entry rather than merely plausible.
fn radical_arms(target: &ExactTarget<R>) -> BTreeSet<&'static str> {
    let rho = target.radius_sq;
    let alpha = rho + target.a1 * target.a1 + target.height * target.height;
    let lower = (target.link_one - target.link_two) * (target.link_one - target.link_two);
    let upper = (target.link_one + target.link_two) * (target.link_one + target.link_two);
    let mut arms = BTreeSet::new();
    for sigma in SHOULDER_BRANCHES {
        let beta = -(R::from_f64(2.0) * branch_sign::<R>(sigma) * target.a1);
        for (m, k) in [(lower - alpha, beta), (alpha - upper, -beta)] {
            arms.insert(arm_of(m, k));
        }
    }
    arms
}

/// Every plan field, exactly: `BranchPlan::exact` against the plan Lean computed for the same
/// target, built from the entry's `expected` block and compared whole with `==`. No tolerance
/// appears anywhere in this file.
#[test]
fn the_exact_plan_matches_the_lean_branch_plans() {
    for case in cases() {
        assert_eq!(
            case.expected_plan(),
            plan_from_json(&case),
            "{}: the whole plan",
            case.name
        );
    }
}

/// The plan the entry's `expected` block spells out, as a `BranchPlan` — every field of it,
/// so that the whole-struct comparison above can fail on any of them.
fn plan_from_json(case: &Case) -> BranchPlan {
    let expected = &case.expected;
    let radius_is_zero = expect_bool(expected, "radius_is_zero", &case.name);
    let wrist_center_on_base_axis = expect_bool(expected, "wrist_center_on_base_axis", &case.name);
    // The corpus carries the predicate in both places the Rust plan does, and the two are one
    // predicate; a document that disagrees with itself is a document to fix, not to read.
    assert_eq!(
        radius_is_zero, wrist_center_on_base_axis,
        "{}: radius_is_zero and wrist_center_on_base_axis are the same predicate",
        case.name
    );
    let elbow = expect_bool_matrix(expected, "elbow_branches", &case.name);
    let fold_back = expect_bool_pair(expected, "fold_back", &case.name);
    let mut elbow_branches = [ElbowBranches::NONE; 2];
    for slot in 0..2 {
        // `elbowBranches g T σ` returns `[1, -1]` or `[]`: the two labels are kept together,
        // so an `expected` block claiming one without the other is not a plan the solver can
        // produce.
        assert_eq!(
            elbow[slot][0], elbow[slot][1],
            "{}: shoulder slot {slot}: the two elbow labels are kept together or not at all",
            case.name
        );
        elbow_branches[slot] = if elbow[slot][0] {
            ElbowBranches::BOTH
        } else {
            ElbowBranches::NONE
        };
    }
    BranchPlan {
        shoulder: [
            ShoulderPlan {
                sigma: SHOULDER_BRANCHES[0],
                radius_is_zero,
            },
            ShoulderPlan {
                sigma: SHOULDER_BRANCHES[1],
                radius_is_zero,
            },
        ],
        elbow_branches,
        wrist: WristBranches::both(),
        degenerate: Degeneracy {
            wrist_center_on_base_axis,
            fold_back,
        },
    }
}

/// The exact plan, field by field against the entry's own `expected` block. The point of the
/// whole workstream: these are `==` on exact values, not thresholds standing in for
/// `InverseKinematics`'s predicates.
#[test]
fn every_field_of_the_exact_plan_is_the_lean_value() {
    for case in cases() {
        let plan = BranchPlan::exact(&case.target());
        let expected = &case.expected;
        let radius_is_zero = expect_bool(expected, "radius_is_zero", &case.name);
        let elbow = expect_bool_matrix(expected, "elbow_branches", &case.name);
        let fold_back = expect_bool_pair(expected, "fold_back", &case.name);

        assert_eq!(
            plan.shoulder[0].sigma, 1,
            "{}: first shoulder label",
            case.name
        );
        assert_eq!(
            plan.shoulder[1].sigma, -1,
            "{}: second shoulder label",
            case.name
        );
        assert_eq!(
            plan.shoulder[0].radius_is_zero, radius_is_zero,
            "{}: shoulder +1: radius_is_zero",
            case.name
        );
        assert_eq!(
            plan.shoulder[1].radius_is_zero, radius_is_zero,
            "{}: shoulder -1: radius_is_zero",
            case.name
        );
        for slot in 0..2 {
            assert_eq!(
                plan.elbow_branches[slot].keeps(1),
                elbow[slot][0],
                "{}: shoulder slot {slot}: elbow +1 kept",
                case.name
            );
            assert_eq!(
                plan.elbow_branches[slot].keeps(-1),
                elbow[slot][1],
                "{}: shoulder slot {slot}: elbow -1 kept",
                case.name
            );
            assert_eq!(
                plan.degenerate.fold_back[slot], fold_back[slot],
                "{}: shoulder slot {slot}: fold_back",
                case.name
            );
        }
        assert_eq!(
            plan.degenerate.wrist_center_on_base_axis,
            expect_bool(expected, "wrist_center_on_base_axis", &case.name),
            "{}: wrist_center_on_base_axis",
            case.name
        );
        assert_eq!(
            plan.wrist.labels(),
            [1, -1],
            "{}: the wrist family is both labels, always",
            case.name
        );
        assert_eq!(
            candidate_count(&plan),
            expect_count(expected, "candidate_count", &case.name),
            "{}: candidate_count",
            case.name
        );
        // The plan's own shape: two elbow labels per kept branch, so the count is two per
        // kept elbow label.
        let kept_per_slot = (0..2)
            .map(|slot| plan.elbow_branches[slot].count())
            .collect::<Vec<_>>();
        assert_eq!(
            candidate_count(&plan),
            kept_per_slot.iter().sum::<usize>() * 2,
            "{}: candidate_count is two wrist labels per kept elbow branch",
            case.name
        );
    }
}

/// The exact wrist decision, `wrist_plan_exact`, against Lean's `wristIsSingular` for the
/// entry's rotation. `hypot x y = 0` holds exactly when both entries vanish, which is what
/// makes this half of the plan rational.
#[test]
fn the_wrist_decision_is_the_lean_wrist_singularity() {
    for case in cases() {
        let singular = wrist_plan_exact(&case.rotation).singular;
        assert_eq!(
            singular,
            expect_bool(&case.expected, "wrist_singular", &case.name),
            "{}: wrist_singular",
            case.name
        );
        // The decision reads exactly two entries, and both of them.
        let first = case.rotation.at(0, 2) == R::zero();
        let second = case.rotation.at(1, 2) == R::zero();
        assert_eq!(
            singular,
            first && second,
            "{}: the wrist sine vanishes exactly when both entries do",
            case.name
        );
    }
}

/// Every entry that states `√ρ` is held to it, and to the two decisions it makes available
/// the long way round: the band through `elbowCosine` with the root substituted, and the
/// fold-back through `q_σ = σ·√ρ − a₁`.
#[test]
fn a_stated_radius_is_the_root_of_rho() {
    let mut stated = 0;
    for case in cases() {
        let Some(radius) = case.radius else { continue };
        stated += 1;
        let target = case.target();
        assert!(
            radius >= R::zero(),
            "{}: the stated radius is non-negative",
            case.name
        );
        assert_eq!(
            radius * radius,
            target.radius_sq,
            "{}: the stated radius squares to rho",
            case.name
        );
        let plan = BranchPlan::exact(&target);
        let one = R::one();
        for (slot, sigma) in [(0usize, 1i8), (1, -1)] {
            let q = branch_sign::<R>(sigma) * radius - target.a1;
            let distance_sq = q * q + target.height * target.height;
            let known = target.link_one * target.link_one + target.link_two * target.link_two;
            let denominator = R::from_f64(2.0) * target.link_one * target.link_two;
            let cosine = (distance_sq - known) / denominator;
            // `elbowCosine ∈ Set.Icc (-1) 1`, with the positive denominator cleared - which
            // is the same band `le_of_radical` decides in `ℚ(√ρ)`, reached here without the
            // extension because `√ρ` is rational for this entry.
            let reachable = cosine >= -one && cosine <= one;
            assert_eq!(
                reachable,
                plan.elbow_branches[slot].keeps(1),
                "{}: shoulder {sigma}: the band through elbowCosine",
                case.name
            );
            let folds =
                target.link_one == target.link_two && q == R::zero() && target.height == R::zero();
            assert_eq!(
                folds, plan.degenerate.fold_back[slot],
                "{}: shoulder {sigma}: the fold-back through the planar target",
                case.name
            );
        }
    }
    assert!(
        stated >= 6,
        "the corpus states {stated} rational radii; the second route to the band is meant to \
         cover a real share of it"
    );
}

/// The two arms are the ones the forward-chain corpus uses, dimension for dimension, and the
/// `shipped` one is the arm `geometry.rs` builds.
#[test]
fn the_geometries_are_the_arms_the_forward_chain_corpus_uses() {
    let branch_corpus = geometries(&document());
    let frames = serde_json::from_str::<Value>(FRAMES).expect("the forward-chain corpus is JSON");
    let frames = frame_geometries(&frames);
    assert_eq!(
        branch_corpus.len(),
        2,
        "the branch corpus is written for the two arms the forward chain uses"
    );
    for (geometry_name, geometry) in &branch_corpus {
        let frame = frames
            .get(geometry_name)
            .unwrap_or_else(|| panic!("{geometry_name}: not a geometry of the forward chain"));
        assert_eq!(
            (
                geometry.a1,
                geometry.d1,
                geometry.link_one,
                geometry.link_two
            ),
            (frame.a1, frame.d1, frame.link_one, frame.link_two),
            "{geometry_name}: the two corpora describe one arm"
        );
    }
    // `geometry.rs`'s `shipped()` is the arm `robot_parameters.json` ships, and that is the
    // arm the branch corpus calls `shipped`.
    let shipped = Geometry::<R>::shipped();
    let branch_shipped = &branch_corpus["shipped"];
    assert_eq!(
        (
            branch_shipped.a1,
            branch_shipped.d1,
            branch_shipped.link_one,
            branch_shipped.link_two
        ),
        (shipped.a1, shipped.d1, shipped.link_one, shipped.link_two),
        "the corpus's `shipped` is `Geometry::shipped`"
    );
    assert_eq!(
        (shipped.a1, shipped.d1, shipped.link_one, shipped.link_two),
        (
            R::integer(10),
            R::integer(32),
            R::integer(25),
            R::integer(25)
        ),
        "`Geometry::shipped` is the arm the corpus's `shipped` documents"
    );
}

/// The geometries of the forward-chain corpus: the same four dimensions, plus the tool offset
/// the branch decisions do not read.
fn frame_geometries(document: &Value) -> BTreeMap<String, Geometry<R>> {
    entries(document, "geometries")
        .expect("the forward-chain corpus defines its geometries")
        .iter()
        .map(|record| {
            let geometry_name = name(record).to_owned();
            let dimension = |key: &str| {
                numeral_at(record, key)
                    .unwrap_or_else(|error| panic!("geometry {geometry_name}: {error}"))
            };
            let geometry = Geometry::new(
                dimension("a1"),
                dimension("d1"),
                dimension("a2"),
                dimension("d4"),
                dimension("d6"),
            )
            .expect("a generated geometry is a supported arm");
            (geometry_name, geometry)
        })
        .collect()
}

/// The same geometries as `f64`, for the float route: `of_pose` is `Scalar`-bounded and
/// `Ratio` does not implement `Scalar` — the exact path needs no square root and the float one
/// needs nothing else — so the float comparison is the one place where the corpus's dimensions
/// are converted rather than carried.
fn float_geometries(document: &Value) -> BTreeMap<String, Geometry<f64>> {
    entries(document, "geometries")
        .expect("the forward-chain corpus defines its geometries")
        .iter()
        .map(|record| {
            let geometry_name = name(record).to_owned();
            let dimension = |key: &str| {
                numeral_at(record, key)
                    .unwrap_or_else(|error| panic!("geometry {geometry_name}: {error}"))
                    .to_f64()
            };
            let geometry = Geometry::new(
                dimension("a1"),
                dimension("d1"),
                dimension("a2"),
                dimension("d4"),
                dimension("d6"),
            )
            .expect("a generated geometry is a supported arm");
            (geometry_name, geometry)
        })
        .collect()
}

/// The corpus is not vacuous: every decision it is meant to pin down is present in it, and so
/// is every arm of `le_of_radical`, with each entry's declared arm re-derived rather than
/// taken on trust.
#[test]
fn the_corpus_covers_every_decision_it_claims_to() {
    let cases = cases();
    assert!(
        cases.len() >= 20,
        "the corpus carries {} entries; it is meant to name every decision, and 20 is the floor",
        cases.len()
    );
    let names = cases
        .iter()
        .map(|case| case.name.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(names.len(), cases.len(), "two entries share a name");

    let geometry_names = cases
        .iter()
        .map(|case| case.geometry_name.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        geometry_names,
        BTreeSet::from(["shipped", "short_arm"]),
        "both arms of the forward-chain corpus are covered"
    );

    let mut arms_covered: BTreeSet<&'static str> = BTreeSet::new();
    let mut on_base_axis: BTreeSet<&str> = BTreeSet::new();
    let mut singular = 0usize;
    let mut non_singular = 0usize;
    let mut one_entry_zero = 0usize;
    let mut folded = 0usize;
    let mut both_elbows = 0usize;
    let mut no_elbows = 0usize;
    let mut rational_radius = 0usize;
    let mut irrational_radius = 0usize;
    for case in &cases {
        let target = case.target();
        let plan = case.expected_plan();
        let arms = radical_arms(&target);
        assert!(
            arms.contains(case.branch.as_str()),
            "{}: no comparison enters the arm {:?} the entry is written for; it enters {arms:?}",
            case.name,
            case.branch
        );
        arms_covered.extend(arms);
        if plan.degenerate.wrist_center_on_base_axis {
            on_base_axis.insert(case.geometry_name.as_str());
        }
        if wrist_plan_exact(&case.rotation).singular {
            singular += 1;
        } else {
            non_singular += 1;
        }
        let first = case.rotation.at(0, 2) == R::zero();
        let second = case.rotation.at(1, 2) == R::zero();
        if first != second {
            one_entry_zero += 1;
        }
        if plan.degenerate.fold_back.iter().any(|&folds| folds) {
            folded += 1;
        }
        if plan.elbow_branches.iter().any(|elbows| !elbows.is_empty()) {
            both_elbows += 1;
        }
        if plan.elbow_branches.iter().all(|elbows| elbows.is_empty()) {
            no_elbows += 1;
        }
        if case.radius.is_some() {
            rational_radius += 1;
        } else {
            irrational_radius += 1;
        }
    }

    assert_eq!(
        arms_covered,
        BTreeSet::from([
            "k_zero",
            "m_nonpos_k_pos",
            "m_nonpos_k_neg",
            "m_pos_k_pos",
            "m_pos_k_neg"
        ]),
        "all five arms of le_of_radical are exercised"
    );
    assert_eq!(
        on_base_axis,
        BTreeSet::from(["shipped", "short_arm"]),
        "both arms put the wrist centre on the base rotation axis somewhere in the corpus"
    );
    assert!(singular >= 1, "the wrist singularity is covered");
    assert!(non_singular >= 1, "the non-singular wrist is covered");
    assert!(
        one_entry_zero >= 1,
        "an entry with exactly one of Q 0 2, Q 1 2 zero witnesses the singularity test as a \
         conjunction; the corpus has {one_entry_zero}"
    );
    assert!(folded >= 1, "the fold-back is covered");
    assert!(both_elbows >= 1, "a reachable band is covered");
    assert!(no_elbows >= 1, "an empty band is covered");
    assert!(rational_radius >= 1, "a rational radius is covered");
    assert!(
        irrational_radius >= 1,
        "a radius with no rational root is covered - the case the extension exists for"
    );
}

/// The float route against the exact one, for the entries whose wrist centres are exactly
/// representable as `f64`.
///
/// This is the diagnostic, not the comparison that matters: the layer's exact plan is checked
/// above with `==` on `Ratio`, and a disagreement here is a statement about the rounding of
/// `hypot` and `elbowCosine`, not about the specification. An entry whose centre is not an
/// `f64` is skipped, because the float route would be handed a *different* centre and there
/// would be nothing to compare: that is the families built from `n / 10⁶` and the off-axis
/// edge case whose coordinates are `174/5` and `232/5`, and the exact route above is what
/// decides those. What is left is the entries where `wrist_center` lands on the entry's centre
/// to the bit, including both exact band edges of `short_arm`, whose radius is irrational and
/// whose cosine is therefore `±1` only up to rounding: that is exactly where a float route
/// could be expected to disagree, and the run reports whether it does.
#[test]
fn the_float_plan_agrees_where_the_target_is_representable() {
    let cases = cases();
    let frames = serde_json::from_str::<Value>(FRAMES).expect("the forward-chain corpus is JSON");
    // The float route takes `f64` dimensions, so these are the corpus's dimensions converted
    // once; the exact comparisons above stay on the `Ratio` geometry.
    let frames = float_geometries(&frames);
    let mut checked = 0usize;
    let mut skipped: Vec<&str> = Vec::new();
    let mut disagreements: Vec<String> = Vec::new();
    for case in &cases {
        // `R::from_f64` is exact with respect to the `f64` it is given, so this is the test
        // that the entry's centre survives the conversion in both directions.
        let representable = case
            .center
            .iter()
            .all(|component| R::from_f64(component.to_f64()) == *component);
        if !representable {
            skipped.push(&case.name);
            continue;
        }
        let geometry = frames
            .get(&case.geometry_name)
            .expect("a geometry of the forward chain");
        let [x, y, z] = case.center.map(R::to_f64);
        // The wrist centre is the end effector pulled back along frame 6's z axis, so an
        // identity rotation needs the end effector at `(x, y, z + d6)` to put the centre on
        // `(x, y, z)`.
        let pose = Pose::new(Mat3::identity(), Vec3::new(x, y, z + geometry.tool_offset));
        let center = wrist_center(geometry, &pose);
        assert_eq!(
            (center.x(), center.y(), center.z()),
            (x, y, z),
            "{}: the pose places the wrist centre on the entry's centre",
            case.name
        );
        let float_plan = BranchPlan::of_pose(geometry, &pose, &Tolerances::exact());
        let exact_plan = case.expected_plan();
        checked += 1;
        compare(
            &case.name,
            "radius_is_zero",
            float_plan.shoulder[0].radius_is_zero,
            exact_plan.shoulder[0].radius_is_zero,
            &mut disagreements,
        );
        compare(
            &case.name,
            "wrist_center_on_base_axis",
            float_plan.degenerate.wrist_center_on_base_axis,
            exact_plan.degenerate.wrist_center_on_base_axis,
            &mut disagreements,
        );
        for (slot, sigma) in [(0usize, 1i8), (1, -1)] {
            compare(
                &case.name,
                &format!("shoulder {sigma}: elbow +1"),
                float_plan.elbow_branches[slot].keeps(1),
                exact_plan.elbow_branches[slot].keeps(1),
                &mut disagreements,
            );
            compare(
                &case.name,
                &format!("shoulder {sigma}: elbow -1"),
                float_plan.elbow_branches[slot].keeps(-1),
                exact_plan.elbow_branches[slot].keeps(-1),
                &mut disagreements,
            );
            compare(
                &case.name,
                &format!("shoulder {sigma}: fold_back"),
                float_plan.degenerate.fold_back[slot],
                exact_plan.degenerate.fold_back[slot],
                &mut disagreements,
            );
        }
    }
    println!(
        "float plan checked on {checked} of {} entries ({} skipped: not f64 centres)",
        cases.len(),
        skipped.len()
    );
    assert!(
        checked >= 12,
        "the float comparison covered only {checked} entries; the sample is meant to be the \
         corpus minus the entries whose centres are not f64"
    );
    assert!(
        disagreements.is_empty(),
        "the float plan disagrees with the exact plan on:\n{}",
        disagreements.join("\n")
    );
}

/// Record a float-versus-exact disagreement with both values, rather than stopping at the
/// first: the useful diagnosis needs to know whether the boundary cases moved together.
fn compare(case: &str, field: &str, float: bool, exact: bool, disagreements: &mut Vec<String>) {
    if float != exact {
        disagreements.push(format!("{case}: {field}: float {float}, exact {exact}"));
    }
}
