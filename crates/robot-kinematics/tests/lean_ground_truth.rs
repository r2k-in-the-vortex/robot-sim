//! The forward chain against the ground truth `lean/KinematicsTestData.lean` generates.
//!
//! That file evaluates `Kinematics.lean` over `ℚ` and writes
//! `test_data/kinematics_frames.json`; regenerate it with `cargo xtask gen-golden`. Every
//! numeral in the document is exact, so everything below is compared with `==` on `Ratio`
//! values rather than against a tolerance — a failure here is a disagreement with the
//! specification, not floating-point drift.
//!
//! `tests/exact_ring.rs` shows the exact-rational path is reachable and checks a handful of
//! hand-transcribed expectations; this file is the same idea over the whole generated
//! corpus, against the values Lean itself computed.

use robot_golden::{Ratio as R, entries, matrix3, name, numeral, numeral_at, vec3};
use robot_kinematics::{
    CosSin, Geometry, Mat3, Pose, Vec3, arm_rotation_cs, carrier_pose_cs, fk_cs, wrist_center,
    wrist_rotation_cs,
};
use serde_json::Value;
use std::collections::BTreeMap;

/// The generated corpus, embedded at compile time: the test then depends on nothing but
/// the file the repository commits, and not on the working directory it runs from.
const DOCUMENT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../test_data/kinematics_frames.json"
));

/// One case, with the parts the properties need read out.
struct Case {
    name: String,
    geometry: Geometry<R>,
    theta: [CosSin<R>; 6],
    /// The `expected` block, left as JSON so each property reads the fields it wants.
    expected: Value,
    /// Whether the case claims the wrist centre coincides with the frame-1 origin.
    wrist_center_at_frame_one: bool,
}

/// The document, parsed for this test. Parsing is microseconds, and a test that owns its
/// data cannot be disturbed by another one.
fn document() -> Value {
    serde_json::from_str(DOCUMENT).expect("the generated ground truth is valid JSON")
}

/// The geometries the document defines, by the name a case refers to them by.
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
                dimension("a2"),
                dimension("d4"),
                dimension("d6"),
            )
            .expect("a generated geometry is a supported arm");
            (geometry_name, geometry)
        })
        .collect()
}

/// Every case of the document.
fn cases() -> Vec<Case> {
    let document = document();
    let geometries = geometries(&document);
    entries(&document, "cases")
        .expect("the document lists its cases")
        .iter()
        .map(|record| {
            let case = name(record).to_owned();
            let geometry_name = record
                .get("geometry")
                .and_then(Value::as_str)
                .unwrap_or_else(|| panic!("case {case}: no geometry named"));
            let geometry = *geometries
                .get(geometry_name)
                .unwrap_or_else(|| panic!("case {case}: undefined geometry {geometry_name:?}"));
            Case {
                theta: pairs(&record["theta_cos_sin"], &case),
                expected: record["expected"].clone(),
                wrist_center_at_frame_one: record["wrist_center_at_frame_one"]
                    .as_bool()
                    .unwrap_or(false),
                name: case,
                geometry,
            }
        })
        .collect()
}

/// The six cosine/sine pairs of a configuration, in joint order.
fn pairs(value: &Value, case: &str) -> [CosSin<R>; 6] {
    let array = value
        .as_array()
        .unwrap_or_else(|| panic!("{case}: theta_cos_sin is not an array"));
    assert_eq!(array.len(), 6, "{case}: the arm has six joints");
    core::array::from_fn(|i| {
        let component = |key: &str| {
            numeral_at(&array[i], key).unwrap_or_else(|error| panic!("{case}: joint {i}: {error}"))
        };
        CosSin::new(component("cos"), component("sin"))
    })
}

/// A pose from an `{"R": ..., "p": ...}` block.
fn expected_pose(value: &Value) -> Pose<R> {
    let p = vec3(&value["p"]).expect("a frame origin is a three-vector");
    Pose::new(
        Mat3::from_rows(matrix3(&value["R"]).expect("a rotation block is 3x3")),
        Vec3::new(p[0], p[1], p[2]),
    )
}

/// A three-vector from a bare array.
fn expected_vec3(value: &Value) -> Vec3<R> {
    let v = vec3(value).expect("a three-vector");
    Vec3::new(v[0], v[1], v[2])
}

/// A 3x3 matrix from a bare array.
fn expected_mat3(value: &Value) -> Mat3<R> {
    Mat3::from_rows(matrix3(value).expect("a 3x3 block"))
}

/// A 4x4 matrix, row-major, in the layout `Pose::to_matrix4` returns.
fn expected_matrix4(value: &Value) -> [[R; 4]; 4] {
    let rows = value.as_array().expect("a homogeneous matrix is four rows");
    assert_eq!(rows.len(), 4, "a homogeneous matrix has four rows");
    core::array::from_fn(|i| {
        let row = rows[i].as_array().expect("a homogeneous matrix row");
        assert_eq!(row.len(), 4, "a homogeneous matrix has four columns");
        core::array::from_fn(|j| numeral(&row[j]).expect("an exact numeral"))
    })
}

/// Every frame of the cumulative tower, exactly: `carrier_pose_cs` against Lean's
/// `carrierPose`, base frame first.
#[test]
fn carrier_pose_matches_the_lean_tower() {
    for case in cases() {
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        let expected = entries(&case.expected, "carrier_pose").expect("a carrier_pose array");
        assert_eq!(tower.len(), expected.len(), "{}: seven frames", case.name);
        for (i, (frame, want)) in tower.iter().zip(expected).enumerate() {
            assert_eq!(*frame, expected_pose(want), "{}: frame {i}", case.name);
        }
    }
}

/// The end-effector pose: `fk_cs` against Lean's `fk`.
#[test]
fn fk_matches_the_lean_pose() {
    for case in cases() {
        let pose = fk_cs(&case.geometry, &case.theta);
        assert_eq!(pose, expected_pose(&case.expected["fk"]), "{}", case.name);
    }
}

/// `carrierPose_six`: the last frame of the tower is the forward kinematics. The two are
/// built by different bracketings — the tower extends frame 3 one joint at a time, `fk_cs`
/// composes `armPose` with `wristPose` — so this is an equality of two routes.
#[test]
fn the_sixth_carrier_pose_is_the_forward_kinematics() {
    for case in cases() {
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        assert_eq!(
            tower[6],
            fk_cs(&case.geometry, &case.theta),
            "{}",
            case.name
        );
        assert_eq!(
            tower[6],
            expected_pose(&case.expected["fk"]),
            "{}",
            case.name
        );
    }
}

/// `wristCenter`: the end-effector origin pulled back along frame 6's z axis by `d6`,
/// against Lean's `wristCenter`.
#[test]
fn wrist_center_matches_the_lean_wrist_center() {
    for case in cases() {
        let center = wrist_center(&case.geometry, &fk_cs(&case.geometry, &case.theta));
        assert_eq!(
            center,
            expected_vec3(&case.expected["wrist_center"]),
            "{}",
            case.name
        );
    }
}

/// `carrierPose_four_p`: the wrist centre is the frame-4 origin of the tower.
#[test]
fn the_fourth_carrier_pose_is_the_wrist_center() {
    for case in cases() {
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        let center = wrist_center(&case.geometry, &fk_cs(&case.geometry, &case.theta));
        assert_eq!(tower[4].p, center, "{}", case.name);
        assert_eq!(
            tower[4].p,
            expected_vec3(&case.expected["wrist_center"]),
            "{}",
            case.name
        );
    }
}

/// The cases the generator marks put the wrist centre exactly on the frame-1 origin. With
/// the two link lengths equal and the second link folded back onto the first, the planar
/// offsets `q` and `h` of `wristCenter_fk` both vanish, so the frame-4 origin lands where
/// frame 1 is. `wristCenter_fk` is the identity being witnessed.
#[test]
fn the_wrist_center_can_sit_on_the_frame_one_origin() {
    let mut witnessed = 0;
    for case in cases() {
        if !case.wrist_center_at_frame_one {
            continue;
        }
        witnessed += 1;
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        let center = wrist_center(&case.geometry, &fk_cs(&case.geometry, &case.theta));
        assert_eq!(center, tower[1].p, "{}", case.name);
        assert_eq!(
            expected_vec3(&case.expected["wrist_center"]),
            tower[1].p,
            "{}",
            case.name
        );
    }
    assert!(
        witnessed > 0,
        "the corpus witnesses the coincidence nowhere"
    );
}

/// `Pose::to_matrix4` on every frame, against the homogeneous matrices Lean wrote —
/// `mathematics.md`'s layout, and the one `kinematics.py` works in.
#[test]
fn the_homogeneous_matrices_match_the_lean_matrix4() {
    for case in cases() {
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        let expected = entries(&case.expected, "carrier_matrix4").expect("a matrix4 array");
        assert_eq!(tower.len(), expected.len(), "{}: seven frames", case.name);
        for (i, (frame, want)) in tower.iter().zip(expected).enumerate() {
            assert_eq!(
                frame.to_matrix4(),
                expected_matrix4(want),
                "{}: frame {i}",
                case.name
            );
        }
    }
}

/// `fk_R`: the forward rotation is the frame-3 rotation times the wrist rotation. Both
/// factors are compared against Lean's own values as well as against `fk_cs`, so the
/// factorization is checked against the specification rather than against itself.
#[test]
fn the_forward_rotation_factorises_through_frame_three() {
    for case in cases() {
        let arm = arm_rotation_cs(case.theta[0], case.theta[1], case.theta[2]);
        let wrist = wrist_rotation_cs(case.theta[3], case.theta[4], case.theta[5]);
        assert_eq!(
            arm,
            expected_mat3(&case.expected["arm_rotation"]),
            "{}: the arm rotation",
            case.name
        );
        assert_eq!(
            wrist,
            expected_mat3(&case.expected["wrist_rotation"]),
            "{}: the wrist rotation",
            case.name
        );
        assert_eq!(
            arm * wrist,
            fk_cs(&case.geometry, &case.theta).r,
            "{}",
            case.name
        );
    }
}

/// The orthogonality the spec derives for its rotation factors — `rotX_orth`, `rotZ_orth`,
/// `mul_orth`, hence `armRotation_orth` — carried to every rotation the chain produces, with
/// no tolerance anywhere: `Rᵀ R = 1` exactly. The determinant has no Lean counterpart
/// (`det3` here is the generator's own Sarrus transcription), so it is checked alongside.
#[test]
fn every_rotation_the_chain_produces_is_a_rotation() {
    // Recomputed from the input pairs rather than read out of the file: the property is
    // about the Rust chain, and the file only supplies the configurations.
    for case in cases() {
        let tower = carrier_pose_cs(&case.geometry, &case.theta);
        for (i, frame) in tower.iter().enumerate() {
            assert_eq!(
                frame.r.transpose() * frame.r,
                Mat3::<R>::identity(),
                "{}: frame {i} is not orthogonal",
                case.name
            );
            assert_eq!(
                frame.r.det(),
                R::ONE,
                "{}: frame {i} is not a rotation",
                case.name
            );
        }
    }
}

/// The corpus is not silently one arm's: both geometries appear, and the shipped one is
/// the geometry `robot_parameters.json` gives.
#[test]
fn the_corpus_covers_more_than_one_arm() {
    let shipped = Geometry::new(
        R::integer(10),
        R::integer(32),
        R::integer(25),
        R::integer(25),
        R::integer(6),
    )
    .expect("the shipped geometry is a supported arm");

    let mut distinct: Vec<Geometry<R>> = Vec::new();
    for case in cases() {
        if !distinct.contains(&case.geometry) {
            distinct.push(case.geometry);
        }
    }
    assert!(
        distinct.contains(&shipped),
        "the shipped geometry is not covered"
    );
    assert!(
        distinct.len() > 1,
        "every case runs on the same arm, so the corpus is hard-wired to one geometry"
    );
}

/// The arm's rest pose: the simulator opens with joint 2 at its 90 degree static offset, so
/// the configuration drawn in `doc/main_window_image.png` is the case named for it, and its
/// frame origins are the documented ones.
#[test]
fn the_documented_zero_pose_matches_the_simulator() {
    let case = cases()
        .into_iter()
        .find(|case| case.name == "documented_zero_pose")
        .expect("the corpus carries the arm's rest pose");
    let tower = carrier_pose_cs(&case.geometry, &case.theta);
    let origins = [
        (0, 0, 0),
        (10, 0, 32),
        (10, 0, 57),
        (10, 0, 57),
        (35, 0, 57),
        (35, 0, 57),
        (41, 0, 57),
    ];
    for (i, (frame, (x, y, z))) in tower.iter().zip(origins).enumerate() {
        assert_eq!(
            frame.p,
            Vec3::new(R::integer(x), R::integer(y), R::integer(z)),
            "frame {i} origin"
        );
    }
}
