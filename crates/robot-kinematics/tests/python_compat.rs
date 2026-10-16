//! The differential harness: `kinematics.py`'s `inverse_kinematics` against
//! [`solve`] with [`Tolerances::python()`], on a deterministic grid of targets.
//!
//! The port's claim is that the compat layer *is* the Python oracle — same candidates,
//! same order, same angles — and that it differs from the exact solver
//! ([`solutions`], Lean's `InverseKinematics.solutions`) only in the three places
//! `src/ik.rs` documents. This file is where that claim meets a real CPython.
//!
//! The oracle runs as a child process: the driver script below is embedded as a string,
//! the grid is serialized to its stdin, and its stdout is the answer. Both sides write
//! floats at shortest-round-trip precision (Python's `repr`, `serde_json`'s `ryu`), so
//! every matrix and every angle crosses the boundary bit-exactly and the comparison
//! below is between numbers, not between printouts.
//!
//! Four things keep the grids from being a coin flip:
//!
//! * The grid's random source is a hand-rolled splitmix64, so a failure is reproducible
//!   from the test alone, with no new dependency.
//! * Well-conditioned targets are *filtered* for being well-conditioned — clear of the
//!   reachability band, of the base axis, and of the wrist singularity by margins far
//!   wider than any tolerance — because a target sitting on a widened predicate is
//!   exactly where a disagreement is legitimate rather than a bug.
//! * The three divergences get their own tests, each constructing the case that makes
//!   the divergence bite and asserting the exact layer's *opposite* answer there.
//! * Every empirical constant is measured and recorded in a comment, and asserted with
//!   margin rather than at the last bit.

use robot_kinematics::{
    Geometry, MAX_SOLUTIONS, Mat3, Pose, Solution, SolutionSet, Tolerances, Vec3, arm_rotation,
    elbow_cosine, fk, planar_target, read_theta4, read_theta5, read_theta6, runtime_angle,
    solutions, solve, total_angle, wrap_angle, wrist_center,
};
use serde_json::{Value, json};
use std::io::{ErrorKind, Write};
use std::process::{Command, Stdio};

/// The repository root, the directory `kinematics.py` and `robot_parameters.json` sit in.
/// The driver gets it as `sys.argv[1]`, which is what makes the oracle importable without
/// installing anything.
const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// The static theta offsets of `robot_parameters.json`, in degrees.
///
/// The oracle reads the same table out of the file, so this constant agreeing with it is
/// load-bearing rather than a convenience: Python reports `wrap(total - offset)` while
/// the crate reports totals, and a stale offset here would show up as a several-radian
/// "disagreement" in every angle comparison below.
const OFFSETS_DEG: [f64; 6] = [0.0, 90.0, 0.0, 0.0, 0.0, 0.0];

/// `inverse_kinematics`'s `tolerance` argument, and so the width of the band
/// `_validate_supported_geometry`, the reachability test and the final pose check all
/// share in the oracle.
const PYTHON_TOLERANCE: f64 = 1e-7;

/// What the two implementations are expected to agree to, modulo a full turn.
///
/// The formulas are the same formulas in the same order, but they are not the same
/// *expression*: `solve` conjugates the target by `chain::arm_rotation`, a product of four
/// matrices built from cosine/sine pairs, while `inverse_kinematics` conjugates it by the
/// rotation of `forward_kinematics(partial)[2]`, the left-nested product of three DH
/// transforms. The two agree mathematically and differ in the last bit or two, so the
/// measured difference is ~1e-15 and the assertion is three orders above it.
const ANGLE_AGREEMENT: f64 = 1e-9;

/// How far the well-conditioned filter stays away from every tolerance-widened predicate.
///
/// `1e-3` in the planar distance is `5e-5` in `elbowCosine`, against the oracle's `1e-7`
/// widening — three orders of margin — and `1e-3` in the recovered sine is against its
/// `1e-6` flat-split window, also three orders.
const CONDITIONING_MARGIN: f64 = 1e-3;

/// The number of well-conditioned targets the differential runs over.
const WELL_CONDITIONED_TARGETS: usize = 64;

/// The seed for the splitmix64 that spreads the commanded joint vectors. Fixed, so the
/// grid is a constant of the test rather than a property of the day it ran.
const GRID_SEED: u64 = 0x5EED_2026_1015_0001;

// ---------------------------------------------------------------------------------------
// The oracle: a CPython child process running the embedded driver.
// ---------------------------------------------------------------------------------------

/// The driver, run as `python -c DRIVER <repo_root>` with a `{"targets": [...]}` document
/// on stdin.
///
/// It builds the geometry from `robot_parameters.json` exactly as `test_kinematics.py`'s
/// `configured_geometry` does, calls `inverse_kinematics(tuple(tuple(row) for row in
/// matrix), geometry, tolerance=1e-7)` — the matrix is a JSON array of arrays, and the
/// solver wants a tuple of tuples — and prints one list of solutions per target, in the
/// order they arrived.
///
/// `json.dump` writes floats at `repr` precision, which is shortest-round-trip, so the
/// angles and errors come back bit-identical to what `inverse_kinematics` returned. No
/// angle is ever formatted into a string.
const DRIVER: &str = r#"
import sys
sys.path.insert(0, sys.argv[1])

import json
import math
import kinematics

with open(sys.argv[1] + "/robot_parameters.json", encoding="utf-8") as handle:
    configuration = json.load(handle)

geometry = tuple(
    kinematics.DHParameters(
        theta=math.radians(float(joint.get("theta_offset_deg", joint.get("theta_deg", 0.0)))),
        d=float(joint["d"]),
        a=float(joint["a"]),
        alpha=math.radians(float(joint["alpha_deg"])),
    )
    for joint in configuration["joints"]
)

report = []
for matrix in json.load(sys.stdin)["targets"]:
    pose = tuple(tuple(row) for row in matrix)
    found = kinematics.inverse_kinematics(pose, geometry, tolerance=1e-7)
    report.append([
        {
            "angles": list(solution.angles),
            "shoulder_branch": solution.shoulder_branch,
            "elbow_branch": solution.elbow_branch,
            "position_error": solution.position_error,
            "orientation_error": solution.orientation_error,
        }
        for solution in found
    ])

json.dump(report, sys.stdout)
"#;

/// One `InverseKinematicsSolution` as the oracle reported it.
struct OracleSolution {
    /// Runtime angles, in radians: `_wrap_angle(total - geometry[i].theta)`.
    angles: [f64; 6],
    shoulder: i8,
    elbow: i8,
    position_error: f64,
    orientation_error: f64,
}

/// The oracle, and the geometry both sides solve.
struct Oracle {
    interpreter: &'static str,
    geometry: Geometry<f64>,
}

impl Oracle {
    /// Start the harness, or `None` when there is no CPython to run.
    fn start() -> Option<Self> {
        interpreter().map(|interpreter| Self {
            interpreter,
            geometry: Geometry::shipped(),
        })
    }

    /// Python's answer for each target, in order.
    fn solutions(&self, targets: &[&Target]) -> Vec<Vec<OracleSolution>> {
        let matrices: Vec<[[f64; 4]; 4]> = targets
            .iter()
            .map(|target| target.pose.to_matrix4())
            .collect();
        let payload =
            serde_json::to_vec(&json!({ "targets": matrices })).expect("a pose is serializable");
        let mut child = Command::new(self.interpreter)
            .arg("-c")
            .arg(DRIVER)
            .arg(REPO_ROOT)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap_or_else(|error| panic!("spawning {} failed: {error}", self.interpreter));
        // The child reads stdin to EOF before it writes anything, so writing the whole
        // document first cannot deadlock against a full pipe.
        child
            .stdin
            .take()
            .expect("stdin is piped")
            .write_all(&payload)
            .expect("the driver reads its targets");
        let output = child.wait_with_output().expect("the driver exits");
        assert!(
            output.status.success(),
            "{} exited with {}: {}",
            self.interpreter,
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let document: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "the driver's stdout is not the report: {error}\nstdout: {}\nstderr: {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        });
        document
            .as_array()
            .expect("the report is one list per target")
            .iter()
            .map(|entry| {
                entry
                    .as_array()
                    .expect("each target's report is a list of solutions")
                    .iter()
                    .map(read_solution)
                    .collect()
            })
            .collect()
    }
}

/// The interpreter to drive `kinematics.py` with, or `None` on a machine without one.
///
/// `python3` first, then `python`: this file is a differential harness rather than a
/// property of the crate, so a machine with no CPython skips instead of failing. A
/// candidate that *spawns* and then exits non-zero is a different matter — that is a
/// broken environment, and it panics with the interpreter's own stderr rather than being
/// hidden behind a skip.
fn interpreter() -> Option<&'static str> {
    for name in ["python3", "python"] {
        match Command::new(name).arg("--version").output() {
            Ok(output) if output.status.success() => return Some(name),
            Ok(output) => panic!(
                "{name} --version exited with {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ),
            Err(error) if error.kind() == ErrorKind::NotFound => continue,
            Err(error) => panic!("spawning {name} failed: {error}"),
        }
    }
    println!("skipping the Python differential: no `python3` or `python` on PATH");
    None
}

/// One solution out of the driver's report.
fn read_solution(value: &Value) -> OracleSolution {
    let number = |name: &str| {
        value[name]
            .as_f64()
            .unwrap_or_else(|| panic!("{name} is not a number: {value}"))
    };
    let angles = value["angles"]
        .as_array()
        .expect("angles is an array")
        .iter()
        .map(|angle| angle.as_f64().expect("an angle is a number"))
        .collect::<Vec<_>>();
    assert_eq!(angles.len(), 6, "the arm has six joints: {value}");
    OracleSolution {
        angles: core::array::from_fn(|joint| angles[joint]),
        shoulder: number("shoulder_branch") as i8,
        elbow: number("elbow_branch") as i8,
        position_error: number("position_error"),
        orientation_error: number("orientation_error"),
    }
}

// ---------------------------------------------------------------------------------------
// The grids.
// ---------------------------------------------------------------------------------------

/// A pose to put to both solvers, with a label the failure messages can name.
struct Target {
    label: String,
    pose: Pose<f64>,
}

impl Target {
    fn new(label: impl Into<String>, pose: Pose<f64>) -> Self {
        Self {
            label: label.into(),
            pose,
        }
    }

    /// A target built by forward kinematics from a commanded total angle vector — the
    /// case where the answer is known before the solver runs.
    fn commanded(geometry: &Geometry<f64>, theta: &[f64; 6]) -> Self {
        let degrees: Vec<String> = theta
            .iter()
            .map(|angle| format!("{:.3}", angle.to_degrees()))
            .collect();
        Self::new(
            format!("fk of commanded [{}] degrees", degrees.join(", ")),
            fk(geometry, theta),
        )
    }

    /// A target placed by its wrist centre, with a rotation that only has to be a
    /// rotation: reachability is a property of the centre alone, and `wristCenter` reads
    /// it back by taking `d6` off along frame 6's z axis.
    fn at_center(
        geometry: &Geometry<f64>,
        label: impl Into<String>,
        center: Vec3<f64>,
        rotation: Mat3<f64>,
    ) -> Self {
        let tool_axis = rotation.col(2).scale(geometry.tool_offset);
        Self::new(label, Pose::new(rotation, center + tool_axis))
    }
}

/// The grid the differential runs over, in three categories with different jobs.
struct Grid {
    /// Reachable, and clear of every widened predicate — the category the sharp
    /// count-and-angles comparison is entitled to.
    well_conditioned: Vec<Target>,
    /// Wrist centres beyond `link_one + link_two` on both shoulder branches: both
    /// implementations must return nothing.
    out_of_reach: Vec<Target>,
    /// Wrist centres exactly on the base rotation axis, which leaves `theta 1` free and
    /// is the case `shoulderAngle`'s anchor exists for.
    on_axis: Vec<Target>,
}

impl Grid {
    fn build() -> Self {
        let geometry = Geometry::<f64>::shipped();
        let mut random = Random::new(GRID_SEED);
        let mut well_conditioned = Vec::new();
        for _ in 0..(8 * WELL_CONDITIONED_TARGETS) {
            if well_conditioned.len() == WELL_CONDITIONED_TARGETS {
                break;
            }
            let theta = random.commanded_angles();
            let target = Target::commanded(&geometry, &theta);
            if can_agree(&geometry, &target.pose) {
                well_conditioned.push(target);
            }
        }
        Self {
            well_conditioned,
            out_of_reach: out_of_reach(&geometry),
            on_axis: on_axis(&geometry),
        }
    }
}

/// SplitMix64: deterministic, dependency-free, and long enough in period that the grid
/// is a fixture rather than a sample.
struct Random(u64);

impl Random {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A uniform draw in `[low, high)`.
    fn uniform(&mut self, low: f64, high: f64) -> f64 {
        let unit = (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64);
        low + (high - low) * unit
    }

    /// A commanded total angle vector spread over the joint ranges.
    ///
    /// Joints 1, 2, 3, 4 and 6 take a runtime angle anywhere in `[-180, 180)` degrees,
    /// composed with the static offset the way the configuration file and
    /// `compose_dh_parameters` do. Joint 5 — index 4, the middle of the wrist — is kept
    /// off zero: `|theta5| >= 0.2` puts `|sin theta5|` at `0.2` or more, well clear of
    /// the `1e-6` flat-split window, which is what makes the wrist read-back meaningful
    /// and lets the exact solver and the compat layer be compared on this grid at all.
    fn commanded_angles(&mut self) -> [f64; 6] {
        let mut theta = [0.0; 6];
        for (joint, angle) in theta.iter_mut().enumerate() {
            *angle = if joint == 4 {
                let magnitude = self.uniform(0.2, 2.9);
                if self.next_u64() & 1 == 0 {
                    magnitude
                } else {
                    -magnitude
                }
            } else {
                total_angle(OFFSETS_DEG[joint], self.uniform(-180.0, 180.0))
            };
        }
        theta
    }
}

/// Whether both implementations are entitled to agree on this target at all.
///
/// Three exclusions, each of them a place where `solve` and `solutions` are *documented*
/// to differ, so a disagreement there would be the specification rather than a bug:
///
/// * a wrist centre within [`CONDITIONING_MARGIN`] of the base axis, where Python's
///   `base_radius > tolerance` and the exact `shoulderRadius g T = 0` can disagree;
/// * a planar distance within [`CONDITIONING_MARGIN`] of `link_one + link_two`, where
///   Python's `1e-7`-widened reachability band and `Set.Icc (-1) 1` can disagree;
/// * a recovered wrist sine within [`CONDITIONING_MARGIN`] of zero, where Python offers
///   the flat split as an extra candidate and `solutions` does not.
fn can_agree(geometry: &Geometry<f64>, target: &Pose<f64>) -> bool {
    let center = wrist_center(geometry, target);
    let radius = f64::hypot(center.x(), center.y());
    if radius <= CONDITIONING_MARGIN {
        return false;
    }
    let height = center.z() - geometry.d1;
    let reach = geometry.link_one + geometry.link_two;
    for sigma in [1.0, -1.0] {
        let distance = f64::hypot(sigma * radius - geometry.a1, height);
        if (distance - reach).abs() <= CONDITIONING_MARGIN {
            return false;
        }
    }
    let mut exact = SolutionSet::new();
    solutions(geometry, target, &mut exact);
    !exact.is_empty()
        && exact
            .iter()
            .all(|candidate| recovered_sine(target, candidate) > CONDITIONING_MARGIN)
}

/// The recovered `sin theta5` of the family a candidate came from: `hypot` of the third
/// column of `R_3^6`.
///
/// The candidate's first three angles *are* the family — they determine the arm rotation
/// — so this is `InverseKinematics.wristSine` and Python's `sine_five` recomputed from
/// the answer rather than from the solve, which is what a filter that judges the grid
/// (rather than the solver) needs.
fn recovered_sine(target: &Pose<f64>, candidate: &Solution<f64>) -> f64 {
    let arm = arm_rotation(
        candidate.angles[0],
        candidate.angles[1],
        candidate.angles[2],
    );
    let relative = arm.transpose() * target.r;
    f64::hypot(relative.at(0, 2), relative.at(1, 2))
}

/// Wrist centres beyond both branches' reach, so the answer is the empty list.
///
/// The distance that matters is from the frame-1 origin, and it carries the shoulder
/// branch: `hypot (sigma * r - a1, h)`. Each centre below clears `link_one + link_two =
/// 50` by tens of units — the closest, at `q = 50.5`, loses the band test in Python
/// (`elbowCosine = 1.0402`) as well as in the exact layer.
fn out_of_reach(geometry: &Geometry<f64>) -> Vec<Target> {
    let rotation = Mat3::<f64>::rot_z(0.3);
    let centers = [
        (
            "behind the base beyond the reach",
            Vec3::new(-150.0, 0.0, geometry.d1),
        ),
        (
            "far above the reach",
            Vec3::new(30.0, 20.0, geometry.d1 + 120.0),
        ),
        (
            "far below the reach",
            Vec3::new(25.0, -40.0, geometry.d1 - 120.0),
        ),
        (
            "sideways beyond the reach",
            Vec3::new(150.0, 0.0, geometry.d1),
        ),
        (
            "just past the stretched arm",
            Vec3::new(geometry.a1 + 50.5, 0.0, geometry.d1),
        ),
    ];
    centers
        .into_iter()
        .map(|(label, center)| Target::at_center(geometry, label, center, rotation))
        .collect()
}

/// Wrist centres exactly on the base rotation axis.
///
/// The pose is built with frame 6's z axis along the base axis, so the tool offset rides
/// on it and the wrist centre is exactly `(0, 0, z)` — not merely near it. There
/// `shoulderRadius g T = 0`, so `theta 1` is free; `shoulderAngle` anchors the plane on
/// the `+x` half-axis, and `kinematics.py` does the same with `base_azimuth = 0.0`, which
/// is why these are a category of their own rather than a degeneracy to exclude.
fn on_axis(geometry: &Geometry<f64>) -> Vec<Target> {
    let mut targets = Vec::new();
    // `d1` up to just inside the reach: the on-axis band is `|h| <= sqrt((L1 + L2)^2 - a1^2)`
    // = 48.99, so the top row keeps the category to poses the solver answers for.
    for z in [32.0, 44.0, 56.0, 68.0, 80.0] {
        for azimuth in [0.0, 0.7, 2.5] {
            let target = Target::at_center(
                geometry,
                format!("wrist centre on the base axis, z = {z}, frame 6 turned to {azimuth} rad"),
                Vec3::new(0.0, 0.0, z),
                Mat3::rot_z(azimuth),
            );
            // The category is worth only as much as the construction: each of these has
            // to land *exactly* on the axis, not near it, or `shoulderRadius` is not zero
            // and the anchor the category exists to exercise never fires.
            let center = wrist_center(geometry, &target.pose);
            assert_eq!(
                (center.x(), center.y(), center.z()),
                (0.0, 0.0, z),
                "{}",
                target.label
            );
            targets.push(target);
        }
    }
    targets
}

// ---------------------------------------------------------------------------------------
// The shared comparison.
// ---------------------------------------------------------------------------------------

/// Test 1's battery for one target, reused by the divergence tests.
///
/// Everything asserted here is `kinematics.py`'s documented behavior, checked against
/// [`solve`] with [`Tolerances::python()`]:
///
/// * the candidate count is equal — Python's list length, not a count of its own;
/// * the `(shoulder, elbow)` labels are equal element-wise and in order, which is what
///   pins the *generation order* and not merely the set;
/// * every angle agrees modulo a full turn, through the offset conversion that separates
///   Python's runtime angles from the crate's total ones;
/// * Python's own report satisfies its contract, `position_error <= 1e-7` and
///   `orientation_error <= 1e-7`;
/// * and every candidate the compat layer returns reproduces the target to `1e-7` in
///   position and in the Frobenius norm of the rotation difference — Python's final
///   check, re-established from the outside.
fn assert_python_compat(
    geometry: &Geometry<f64>,
    target: &Pose<f64>,
    python: &[OracleSolution],
    label: &str,
) {
    assert!(
        python
            .iter()
            .all(|solution| solution.position_error <= PYTHON_TOLERANCE
                && solution.orientation_error <= PYTHON_TOLERANCE),
        "{label}: Python returned a candidate outside its own tolerance: {label}"
    );
    let mut out = SolutionSet::new();
    solve(geometry, target, &Tolerances::python(), &mut out);
    assert_eq!(
        out.len(),
        python.len(),
        "{label}: the compat layer returns {} candidates, Python {}",
        out.len(),
        python.len()
    );
    assert!(
        !out.overflowed(),
        "{label}: more than MAX_SOLUTIONS candidates, which Python's list says is wrong"
    );
    for (index, (candidate, oracle)) in out.iter().zip(python).enumerate() {
        assert_eq!(
            candidate.shoulder, oracle.shoulder,
            "{label}: candidate {index} shoulder branch"
        );
        assert_eq!(
            candidate.elbow, oracle.elbow,
            "{label}: candidate {index} elbow branch"
        );
        for (joint, offset) in OFFSETS_DEG.iter().enumerate() {
            let runtime = runtime_angle(candidate.angles[joint], *offset);
            let delta = wrap_angle(runtime - oracle.angles[joint]);
            assert!(
                delta.abs() < ANGLE_AGREEMENT,
                "{label}: candidate {index} joint {} differs by {delta} \
                 (compat {runtime}, Python {})",
                joint + 1,
                oracle.angles[joint]
            );
        }
        let reconstructed = fk(geometry, &candidate.angles);
        assert!(
            reconstructed.p.distance(target.p) <= PYTHON_TOLERANCE,
            "{label}: candidate {index} misses the position by {}",
            reconstructed.p.distance(target.p)
        );
        let rotation_error = reconstructed.r.frobenius_distance(target.r);
        assert!(
            rotation_error <= PYTHON_TOLERANCE,
            "{label}: candidate {index} misses the orientation by {rotation_error}"
        );
    }
}

/// Both targets of a category, in one oracle call, then the battery on each.
fn assert_category_agrees(oracle: &Oracle, targets: &[Target]) {
    let all: Vec<&Target> = targets.iter().collect();
    let python = oracle.solutions(&all);
    assert_eq!(python.len(), targets.len(), "one report per target");
    for (target, solutions) in targets.iter().zip(&python) {
        assert_python_compat(&oracle.geometry, &target.pose, solutions, &target.label);
    }
}

// ---------------------------------------------------------------------------------------
// The tests.
// ---------------------------------------------------------------------------------------

/// The main differential: on well-conditioned targets, the compat layer and the oracle
/// return the same list.
#[test]
fn python_and_the_compat_layer_agree() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let grid = Grid::build();
    assert!(
        grid.well_conditioned.len() >= 48,
        "the conditioning filter kept only {} of {WELL_CONDITIONED_TARGETS} targets, \
         so the differential is running on a thin grid",
        grid.well_conditioned.len()
    );
    assert_category_agrees(&oracle, &grid.well_conditioned);
    assert_category_agrees(&oracle, &grid.out_of_reach);
    assert_category_agrees(&oracle, &grid.on_axis);
    println!(
        "agreed on {} well-conditioned, {} out-of-reach and {} on-axis targets",
        grid.well_conditioned.len(),
        grid.out_of_reach.len(),
        grid.on_axis.len()
    );
}

/// Out of reach is empty on both sides, and it is empty for the *exact* reason.
#[test]
fn out_of_reach_targets_are_empty_for_both_solvers() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let geometry = &oracle.geometry;
    let targets = out_of_reach(geometry);
    let all: Vec<&Target> = targets.iter().collect();
    let python = oracle.solutions(&all);
    for (target, found) in targets.iter().zip(&python) {
        assert!(
            found.is_empty(),
            "{}: Python returned {} solutions beyond the reach",
            target.label,
            found.len()
        );
        // Both layers, because emptiness is a property of the band test and the two make
        // that decision differently: the exact one against `Set.Icc (-1) 1`, the compat
        // one against Python's band widened by 1e-7.
        let mut exact = SolutionSet::new();
        solutions(geometry, &target.pose, &mut exact);
        assert!(exact.is_empty(), "{}: solutions is not empty", target.label);
        let mut compat = SolutionSet::new();
        solve(geometry, &target.pose, &Tolerances::python(), &mut compat);
        assert!(compat.is_empty(), "{}: solve is not empty", target.label);
    }
}

/// The exact solver and the compat layer return the same sequence on the same grid.
///
/// This is the sharp form of "the compat layer differs only where it is documented to":
/// away from the band's edges, the base axis, and the wrist singularity, the tolerance
/// machinery makes no difference at all, so [`solutions`] — the Lean function, with no
/// tolerance and no pose filter — and `solve(Tolerances::python())` agree candidate for
/// candidate.
///
/// The grid's joint-5 margin is what keeps this true: `|theta5| >= 0.2` puts the
/// recovered sine three orders above the `1e-6` threshold, so the compat layer never
/// offers Python's extra flat candidate, and the read-back is accurate enough that the
/// pose filter has nothing to reject.
#[test]
fn the_exact_solver_agrees_with_the_compat_layer_away_from_the_divergences() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let grid = Grid::build();
    let mut compared = 0;
    for target in &grid.well_conditioned {
        let mut exact = SolutionSet::new();
        solutions(&oracle.geometry, &target.pose, &mut exact);
        let mut compat = SolutionSet::new();
        solve(
            &oracle.geometry,
            &target.pose,
            &Tolerances::python(),
            &mut compat,
        );
        assert_eq!(
            exact.len(),
            compat.len(),
            "{}: the exact solver returns {} candidates, the compat layer {}",
            target.label,
            exact.len(),
            compat.len()
        );
        assert!(!exact.overflowed() && !compat.overflowed());
        for (index, (lean, python)) in exact.iter().zip(compat.iter()).enumerate() {
            assert_eq!(
                lean.shoulder, python.shoulder,
                "{}: candidate {index} shoulder",
                target.label
            );
            assert_eq!(
                lean.elbow, python.elbow,
                "{}: candidate {index} elbow",
                target.label
            );
            for joint in 0..6 {
                let delta = wrap_angle(lean.angles[joint] - python.angles[joint]);
                assert!(
                    delta.abs() < ANGLE_AGREEMENT,
                    "{}: candidate {index} joint {} differs by {delta}",
                    target.label,
                    joint + 1
                );
            }
        }
        compared += 1;
    }
    assert!(compared >= 48, "the grid fell to {compared} targets");
    println!("the exact solver and the compat layer agreed on {compared} targets");
}

/// Divergence 1: the reachability band is Python's, not the theorem's.
///
/// `solutions_eq_nil_of_not_reachable` says a pose whose wrist centre is beyond
/// `L1 + L2` from the frame-1 origin has no candidate at all, over `ℝ`. `kinematics.py`
/// decides the same question against `1 + 1e-7` — `if cosine < -1 - tolerance or cosine
/// > 1 + tolerance: continue` — and then *clamps* the cosine into `[-1, 1]` for the
/// `acos`, which is what lets it answer a target the arm cannot quite reach.
///
/// The target here is the smallest such case: the arm commanded perfectly straight, and
/// the tool then pushed `5e-8` further out along the arm plane's own radial direction.
/// The push is in the plane by construction — the plane's `q` direction is the azimuth
/// the straight arm points along — so the wrist centre moves by the full `5e-8` and the
/// tool offset, riding on an unchanged rotation, absorbs none of it.
///
/// Measured, on the shipped geometry: `elbowCosine` comes out `1 + 2.5e-9`, inside
/// Python's widened `1 + 1e-7` and outside `Set.Icc (-1) 1`; Python returns 4 solutions —
/// the `sigma = +1` family, both elbow branches, both wrist branches — each reporting
/// `position_error = 5e-8`, which is the push distance and is what the `1e-7` pose check
/// admits. A `5e-8` push is also the largest the pose check tolerates: the error *is* the
/// push, since the clamped arm reaches exactly `L1 + L2`.
///
/// There is no mirror image of this window on the *inner* edge, and that is a fact about
/// the geometry rather than a missing construction: with equal links the lower bound
/// `|L1 - L2|` is zero, so the cosine's minimum `-1` is reached exactly at `D = 0` and a
/// `hypot` never goes below it. The test below, `the_inner_band_edge_is_the_fold_back`,
/// pins what is there instead.
#[test]
fn the_band_tolerance_is_pythons_not_the_theorems() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let geometry = &oracle.geometry;

    // Straight out along the plane's `q` axis: `total_theta3 = psi + pi/2` at `psi = 0`
    // and `total_theta2 = atan2(h, q) = 0` is the fully stretched arm.
    let azimuth = 0.7;
    let stretched = fk(
        geometry,
        &[azimuth, 0.0, core::f64::consts::FRAC_PI_2, 0.9, 1.1, 2.1],
    );
    let push = 5e-8;
    let target = Pose::new(
        stretched.r,
        stretched.p + Vec3::new(push * azimuth.cos(), push * azimuth.sin(), 0.0),
    );

    // The window the construction lands in, asserted rather than asserted-to-work:
    // outside the exact band, inside Python's.
    let planar = planar_target(geometry, wrist_center(geometry, &target), 1.0);
    let cosine = elbow_cosine(geometry, &planar);
    assert!(
        cosine > 1.0,
        "the push did not leave the exact band: cosine = {cosine}"
    );
    assert!(
        cosine < 1.0 + PYTHON_TOLERANCE,
        "the push left Python's widened band too: cosine = {cosine}"
    );
    let distance = f64::hypot(planar.q, planar.h);
    let reach = geometry.link_one + geometry.link_two;
    assert!(
        (distance - reach - push).abs() < 1e-12,
        "the wrist centre sits {distance} from the frame-1 origin, not {}",
        reach + push
    );

    let pushed = Target::new("pushed past the stretched arm", target);
    let all: Vec<&Target> = vec![&pushed];
    let python = oracle.solutions(&all);
    let python = &python[0];
    assert!(
        !python.is_empty(),
        "Python rejected the pushed target, so the construction is outside its window"
    );
    assert!(
        python.iter().all(|solution| solution.position_error > 1e-8),
        "Python's candidates reproduce the pose too well to be outside the reachable set"
    );

    // The theorem's answer, at the exact layer, is nothing.
    let mut exact = SolutionSet::new();
    solutions(geometry, &target, &mut exact);
    assert!(
        exact.is_empty(),
        "solutions_eq_nil_of_not_reachable: the wrist centre is beyond L1 + L2"
    );

    // And the compat layer's answer is Python's, candidate for candidate.
    assert_python_compat(geometry, &target, python, "pushed past the stretched arm");
}

/// The inner edge of the band, and the corner that sits on it.
///
/// The construction the outer edge uses is impossible on the inside, and that is a fact
/// about the geometry rather than a gap in the test: with equal links the lower bound
/// `|L1 - L2|` is zero, so `elbowCosine = (D^2 - L1^2 - L2^2) / (2 L1 L2)` has its
/// minimum `-1` exactly at `D = 0`, and a `hypot` is never negative. Rounding cannot
/// break the bound either, because `-1` is representable and rounding is monotone, so a
/// value in `[-1, inf)` stays in it. There is therefore no inner-edge counterpart of the
/// outer-edge window: Python's widening has nothing to admit here, and
/// `Set.Icc (-1) 1` is the whole story.
///
/// What does sit on the edge is the fold-back: a wrist centre exactly on the frame-1
/// origin has `D = 0` and `elbowCosine = -1.0` exactly, and the exact solver keeps it,
/// which is the part of the original guess that holds. What the harness found *around*
/// it is a corner the three documented divergences do not cover, and it is recorded here
/// rather than asserted away.
///
/// Measured on this target: Python returns **12** candidates — the arm is folded back on
/// itself, so both shoulder branches are singular in the wrist, and every one of the four
/// families offers its flat split alongside its read-back. That is more than
/// `MAX_SOLUTIONS`, and the compat layer reports it exactly as `solve`'s doc comment says
/// it does (`overflowed()`, eight kept). But the eight it keeps are *not* Python's first
/// eight, as that comment claims. Python's 4th and 6th candidates are the `(1, -1)`
/// family's direct read-backs; the crate's own read of that family lands on
/// `(theta4, theta6) = (pi, 0)`, whose reconstruction misses the orientation by `0.4227`
/// in Frobenius — an axis-angle error of 0.3 rad, with the position still good to
/// `3.6e-15` — where Python's read of the same family lands on `(-pi/2, 1.8708)` and
/// reproduces the pose to `2.5e-16`. The pose check is therefore right to drop the crate's
/// version of those two candidates, and the count is right to report the overflow; the
/// divergence is one level down, in which split the rounding noise lands on.
///
/// Neither read is *the* answer, and the reason is in the specification: the third column
/// of the relative rotation is exactly vertical here, which is precisely the `hne`
/// hypothesis `Zyz.wristRotation_reconstruct` does not cover. This is the one place the
/// harness looked where the compat layer's arithmetic — not its predicates — decides a
/// candidate's fate.
#[test]
fn the_inner_band_edge_is_the_fold_back() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let geometry = &oracle.geometry;
    let frame_one = Vec3::new(geometry.a1, 0.0, geometry.d1);

    // The wrist centre exactly on the frame-1 origin of the `theta 1 = 0` plane. The
    // centre's radius is `a1`, so `theta 1` is well defined and the anchor does not fire.
    let target = Target::at_center(
        geometry,
        "wrist centre on the frame-1 origin",
        frame_one,
        Mat3::rot_z(0.3),
    );
    let all: Vec<&Target> = vec![&target];
    let python = &oracle.solutions(&all)[0];

    let center = wrist_center(geometry, &target.pose);
    assert_eq!(center.x(), geometry.a1);
    assert_eq!(center.y(), 0.0);
    let planar = planar_target(geometry, center, 1.0);
    let cosine = elbow_cosine(geometry, &planar);
    assert_eq!(
        cosine, -1.0,
        "the fold-back should sit exactly on the lower bound, not at {cosine}"
    );

    // The lower end is in the exact band, so the theorem keeps the pose, and it keeps it
    // within the proved count.
    let mut exact = SolutionSet::new();
    solutions(geometry, &target.pose, &mut exact);
    assert_eq!(
        exact.len(),
        MAX_SOLUTIONS,
        "the exact band includes its lower end, so this pose is reachable"
    );
    assert!(
        !exact.overflowed(),
        "length_solutions_le_eight is a theorem about the exact solver"
    );

    // Python's list runs past the bound, and the compat layer says so rather than
    // pretending otherwise.
    let mut compat = SolutionSet::new();
    solve(geometry, &target.pose, &Tolerances::python(), &mut compat);
    assert!(
        python.len() > MAX_SOLUTIONS,
        "Python returned {} candidates, so this target does not exercise the overflow",
        python.len()
    );
    assert!(
        compat.overflowed(),
        "Python returned {} candidates and the compat layer did not report the overflow",
        python.len()
    );
    assert_eq!(compat.len(), MAX_SOLUTIONS);
    println!(
        "the fold-back: Python {} candidates, the compat layer {} with overflow reported",
        python.len(),
        compat.len()
    );

    // Every candidate the compat layer keeps is one of Python's — the overflow is the
    // only reason its list is shorter, not a candidate the crate made up.
    for candidate in compat.iter() {
        assert!(
            python
                .iter()
                .any(|oracle| same_candidate(oracle, candidate)),
            "the compat layer returned a candidate Python does not have: {:?} \
             (shoulder {}, elbow {})",
            candidate.angles,
            candidate.shoulder,
            candidate.elbow
        );
    }

    // The mechanism, measured: the crate's own read of the `(1, -1)` family — the one
    // Python's missing pair belongs to — reconstructs the *position* exactly and the
    // orientation not at all, so the pose check is not the thing that is wrong here.
    let family = compat
        .iter()
        .find(|candidate| candidate.shoulder == 1 && candidate.elbow == -1)
        .expect("the (1, -1) family has to survive, one way or another");
    let relative = arm_rotation(family.angles[0], family.angles[1], family.angles[2]).transpose()
        * target.pose.r;
    for branch in [1i8, -1i8] {
        let mirror = if branch < 0 {
            0.0
        } else {
            core::f64::consts::PI
        };
        let direct = [
            family.angles[0],
            family.angles[1],
            family.angles[2],
            read_theta4(&relative) + mirror,
            read_theta5(&relative, branch),
            read_theta6(&relative) + mirror,
        ];
        let reconstructed = fk(geometry, &direct);
        let position = reconstructed.p.distance(target.pose.p);
        let orientation = reconstructed.r.frobenius_distance(target.pose.r);
        assert!(
            position <= PYTHON_TOLERANCE,
            "the read-back's position is fine; it is the split that goes wrong: {position}"
        );
        assert!(
            orientation > 1e-3,
            "the crate's read of the (1, -1) family now reconstructs the orientation to \
             {orientation}, so this recorded divergence is stale and the test should be \
             updated to whatever the compat layer does now"
        );
    }
}

/// Whether a compat-layer candidate and a Python one are the same candidate: the same
/// branch labels and the same six angles modulo a full turn.
///
/// The labels are compared exactly and the angles through [`wrap_angle`], because near a
/// singularity Python can hold two candidates a rounding error apart — the fold-back's
/// list has two that are identical entry for entry — and a set comparison is the right
/// question for "is this one of Python's".
fn same_candidate(oracle: &OracleSolution, candidate: &Solution<f64>) -> bool {
    oracle.shoulder == candidate.shoulder
        && oracle.elbow == candidate.elbow
        && (0..6).all(|joint| {
            let runtime = runtime_angle(candidate.angles[joint], OFFSETS_DEG[joint]);
            wrap_angle(runtime - oracle.angles[joint]).abs() < ANGLE_AGREEMENT
        })
}

/// Divergence 2: the flat wrist split, which the exact solver must not construct.
///
/// Commanded from a configuration with joint 5 exactly zero — `total_angle(90, 20)` for
/// joint 2, per `robot_parameters.json`'s offset. Over `ℝ` joints 4 and 6 share an axis
/// there and only `theta4 + theta6` is observable, so Python offers, *in addition* to the
/// read-back triple, the split that holds joint 4 at zero
/// (`sine_five <= 1e-6`, then `wrist_candidates.append((0.0, total_theta5, ...))`) and
/// lets the pose check choose.
///
/// [`solutions`] cannot make that choice, and must not: what it sees is the *recovered*
/// sine, which is rounding noise around `2e-16` rather than a zero, so Lean's
/// `wristIsSingular` — `wristSine g T sigma epsilon = 0` — does not hold of this pose and
/// `candidate_wrist` takes the read-back branch. Over `ℝ` the mirrored pair the noise
/// produces is not a solution at all, and `solutions` has no pose check to fall back on
/// (`fk_of_mem_solutions` says it does not need one, for data that has not already lost
/// the singularity). So this is the deliberate divergence: Python's extra candidate is
/// the price of solving a pose that is singular in the mathematics and merely near it in
/// the bits.
#[test]
fn the_flat_split_is_the_exact_solver_s_documented_divergence() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let geometry = &oracle.geometry;
    let target = Target::commanded(
        geometry,
        &[0.4, total_angle(90.0, 20.0), -0.3, 0.9, 0.0, 2.1],
    );
    let all: Vec<&Target> = vec![&target];
    let python = &oracle.solutions(&all)[0];

    // Python's flat split is a candidate whose fourth angle is exactly zero. Joint 4's
    // static offset is zero, so "joint 4 held at zero" reads the same in runtime angles.
    assert!(
        python.iter().any(|solution| solution.angles[3] == 0.0),
        "Python did not offer its flat split"
    );

    // The exact solver never constructs that candidate for its own reasons.
    let mut exact = SolutionSet::new();
    solutions(geometry, &target.pose, &mut exact);
    assert_eq!(exact.len(), 8, "one candidate per branch triple");
    // The flat split is the *pair* — joint 4 held at zero with the wrist itself read as
    // singular. `theta4 = 0` alone is not the witness: a read-back can land there by
    // rounding at a wrist bent well away from the singularity, and at the shipped arm's
    // lengths one does.
    assert!(
        exact
            .iter()
            .all(|candidate| candidate.angles[3] != 0.0 || candidate.angles[4].abs() > 1e-6),
        "solutions is not supposed to construct Python's flat split"
    );

    // And the compat layer reports Python's list, flat split included.
    assert_python_compat(geometry, &target.pose, python, &target.label);
    let mut compat = SolutionSet::new();
    solve(geometry, &target.pose, &Tolerances::python(), &mut compat);
    assert!(
        compat.iter().any(|candidate| candidate.angles[3] == 0.0),
        "the compat layer should offer the flat split Python offers"
    );
}

/// Divergence 3: the pose check, which is why the compat layer can offer a candidate the
/// exact solver's read-back gets wrong.
///
/// Same construction as the singularity test, with joint 5 tiny instead of zero. The
/// recovered sine is then far below Python's `1e-6` flat-split threshold, so the wrist is
/// *judged* singular and the flat split is offered — but the true `theta4` is `0.9`, not
/// zero, so the flat candidate is only as good as the near-singularity makes it and the
/// read-back is the one that carries the noise.
///
/// That is the trade the pose check settles: Python keeps whichever candidate reproduces
/// the pose and discards the other, and `solutions`, which has no check, returns the
/// noise-driven read-back for that family. Its error is `O(rounding / sin theta5)`, which
/// is why the failure scales with how small the commanded joint 5 is — and why the
/// command here is `1e-12` rather than something the read-back could survive: measured,
/// the exact solver's worst candidate misses the orientation by `1.0e-4`, three orders
/// above the `1e-7` the filter allows.
#[test]
fn the_pose_filter_is_pythons() {
    let Some(oracle) = Oracle::start() else {
        return;
    };
    let geometry = &oracle.geometry;
    // 1e-12: the recovered sine is ~1e-12, six orders below the 1e-6 flat-split
    // threshold, while the read-back's rounding noise divided by that sine is three
    // orders *above* the 1e-7 pose tolerance. Measured on this target, the worst exact
    // candidate misses the orientation by 1.0e-4.
    let target = Target::commanded(
        geometry,
        &[0.4, total_angle(90.0, 20.0), -0.3, 0.9, 1e-12, 2.1],
    );
    let all: Vec<&Target> = vec![&target];
    let python = &oracle.solutions(&all)[0];

    // Python's contract: everything it returns reproduces the pose.
    assert!(
        python
            .iter()
            .all(|solution| solution.position_error <= PYTHON_TOLERANCE
                && solution.orientation_error <= PYTHON_TOLERANCE),
        "Python returned a candidate outside its own tolerance"
    );
    assert!(
        !python.is_empty(),
        "Python found nothing at the near-singular wrist"
    );

    // The exact solver returns the read-back, and it is wrong by more than Python's
    // tolerance would allow — the filter is not decoration.
    let mut exact = SolutionSet::new();
    solutions(geometry, &target.pose, &mut exact);
    assert!(
        !exact.is_empty(),
        "the exact solver has a candidate for every pose"
    );
    let worst = exact
        .iter()
        .map(|candidate| {
            fk(geometry, &candidate.angles)
                .r
                .frobenius_distance(target.pose.r)
        })
        .fold(0.0, f64::max);
    assert!(
        worst > PYTHON_TOLERANCE,
        "the exact solver's worst candidate misses the orientation by {worst}, \
         which the pose filter would have had nothing to reject"
    );
    println!("the exact solver's worst candidate misses the orientation by {worst:e}");

    // And the compat layer reports exactly what Python reports.
    assert_python_compat(geometry, &target.pose, python, &target.label);
}
