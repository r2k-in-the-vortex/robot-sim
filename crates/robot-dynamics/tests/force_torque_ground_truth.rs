//! The exact-rational ground truth for the wrench algebra and the sensor dynamics.
//!
//! `test_data/force_torque_frames.json` holds 29 cases the Lean generator emitted —
//! `lean/ForceTorqueTestData.lean`, evaluated over `ℚ` — and this module is the first
//! implementation that consumes them: 15 static frame transforms, 3 chains, and 11 dynamics
//! cases. `test_force_torque.py` says as much in its own docstring ("the transforms themselves
//! are not implemented in Python yet"); the Rust is where they exist.
//!
//! Every numeral in the file is an exact integer or a `"num/den"` string, so every comparison
//! here is `==` over [`Ratio`] with no tolerance anywhere. A failure is a disagreement with the
//! specification, not floating-point drift — and a JSON *number* in the file is an error rather
//! than a value, because it would have gone through a float already. `numerals()` in the Python
//! checker enforces the same rule from the other side; [`assert_every_leaf_is_a_string`] is its
//! Rust counterpart, and is stricter (it rejects integers too, which the Python sweep walks past).
//!
//! The conventions the file declares, and which the calls below take apart:
//!
//! * `R` rotates tip coordinates into sensor coordinates, `p` is the tip origin in sensor
//!   coordinates, and both are stored row-major, so `R[i][j]` is Lean's `R i j`.
//! * In a dynamics case the mass properties are in **tip** coordinates, while the twist,
//!   acceleration and gravity are in **sensor** coordinates, and the tip wrench is the external
//!   wrench at the tip in tip coordinates.
//! * `g` is the gravitational acceleration, pointing down, so a sensor holding a body at rest
//!   reads *minus* its gravity wrench — the sign check in
//!   [`a_body_at_rest_reads_minus_its_gravity_wrench`].

use robot_dynamics::{
    Accel, MassProperties, Rotation, Twist, Wrench, com_accel, first_moment, gravity_wrench,
    inertial_wrench, measured_wrench, origin_inertia, recovered_contact_wrench,
    sensor_accel_to_tip, sensor_mass_to_tip, sensor_to_tip, sensor_twist_to_tip,
    sensor_twist_to_tip_velocity, tip_accel_to_sensor, tip_mass_to_sensor, tip_to_sensor,
    tip_twist_to_sensor, virtual_work,
};
use robot_golden::{Ratio as R, entries, matrix3, name, numeral, numeral_at, vec3};
use robot_kinematics::{Field, Mat3, Vec3};
use serde_json::Value;
use std::path::PathBuf;

/// The blocks of a case that hold numbers; the rest (names, source, conventions) is prose.
/// Mirrors `CASE_NUMERIC_BLOCKS` in `test_force_torque.py`.
const CASE_BLOCKS: [&str; 6] = [
    "p",
    "R",
    "tip_wrench",
    "tip_twist",
    "sensor_twist",
    "expected",
];

/// The same for a chain, `CHAIN_NUMERIC_BLOCKS`.
const CHAIN_BLOCKS: [&str; 7] = [
    "p1",
    "R1",
    "p2",
    "R2",
    "tip_wrench",
    "sensor_twist",
    "expected",
];

/// The same for a dynamics case, `DYNAMICS_NUMERIC_BLOCKS`. `parts` is `null` or two
/// mass-property blocks, so it is swept separately rather than listed here.
const DYNAMICS_BLOCKS: [&str; 8] = [
    "p",
    "R",
    "mass_properties",
    "gravity",
    "sensor_twist",
    "sensor_accel",
    "tip_wrench",
    "expected",
];

/// The ground-truth document, parsed.
fn document() -> Value {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../test_data/force_torque_frames.json");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
    serde_json::from_str(&text).expect("the ground-truth document is JSON")
}

fn cases(document: &Value) -> &Vec<Value> {
    entries(document, "cases").expect("the document has a cases array")
}

fn chains(document: &Value) -> &Vec<Value> {
    entries(document, "chains").expect("the document has a chains array")
}

fn dynamics_cases(document: &Value) -> &Vec<Value> {
    entries(document, "dynamics_cases").expect("the document has a dynamics_cases array")
}

// ---- reading the blocks -------------------------------------------------

fn ratio(value: &Value) -> R {
    numeral(value).expect("a numeral")
}

fn v3(value: &Value) -> Vec3<R> {
    Vec3::from(vec3(value).expect("a three-vector of numerals"))
}

fn m3(value: &Value) -> Mat3<R> {
    Mat3::from_rows(matrix3(value).expect("a 3x3 block of numerals"))
}

fn wrench(value: &Value) -> Wrench<R> {
    Wrench::new(v3(&value["force"]), v3(&value["torque"]))
}

fn twist(value: &Value) -> Twist<R> {
    Twist::new(v3(&value["v"]), v3(&value["omega"]))
}

fn accel(value: &Value) -> Accel<R> {
    Accel::new(v3(&value["a"]), v3(&value["alpha"]))
}

/// The stored rotation, put through the checked constructor. `R` failing to be a rotation would
/// make every case meaningless physically, so the constructor is the assertion here.
fn rotation(value: &Value) -> Rotation<R> {
    Rotation::new(m3(value)).expect("the ground truth's R is a rotation")
}

fn mass_properties(value: &Value) -> MassProperties<R> {
    MassProperties::new(
        numeral_at(value, "mass").expect("a mass numeral"),
        v3(&value["com"]),
        m3(&value["inertia"]),
    )
    .expect("the ground truth's inertia tensors are symmetric")
}

// ---- the strictness rule ------------------------------------------------

/// Every leaf of `block` has to be a numeral **string**.
///
/// This is `test_force_torque.py`'s `numerals()` rule: a JSON number would have round-tripped
/// through a float and quietly destroyed the exactness the whole arrangement exists to provide,
/// so seeing one is an error rather than a value. The Python sweep collects strings and raises on
/// floats; this one raises on any non-string leaf, which also catches an integer that slipped
/// past it.
fn assert_every_leaf_is_a_string(block: &Value, path: &str) {
    match block {
        Value::String(_) => {}
        Value::Array(items) => {
            for (index, item) in items.iter().enumerate() {
                assert_every_leaf_is_a_string(item, &format!("{path}[{index}]"));
            }
        }
        Value::Object(fields) => {
            for (key, item) in fields {
                assert_every_leaf_is_a_string(item, &format!("{path}.{key}"));
            }
        }
        Value::Number(number) => panic!(
            "{path} holds the JSON number {number}, not a numeral string: \
             the ground truth must stay exact"
        ),
        other => panic!("{path} holds {other}, which is not a numeral"),
    }
}

// ---- the schema and its numerals ---------------------------------------

#[test]
fn the_document_declares_the_supported_schema() {
    let document = document();
    assert_eq!(
        document["schema_version"],
        Value::from(3),
        "schema 3 is the shape this consumer reads"
    );
    // The inventory this workstream is accountable for; a change here means the generator moved
    // and the checks below need re-reading rather than re-running.
    assert_eq!(cases(&document).len(), 15, "static cases");
    assert_eq!(chains(&document).len(), 3, "chains");
    assert_eq!(dynamics_cases(&document).len(), 11, "dynamics cases");
}

#[test]
fn every_numeral_is_exact_and_none_is_a_json_number() {
    let document = document();

    for case in cases(&document) {
        for key in CASE_BLOCKS {
            assert_every_leaf_is_a_string(&case[key], &format!("{}.{key}", name(case)));
        }
    }
    for chain in chains(&document) {
        for key in CHAIN_BLOCKS {
            assert_every_leaf_is_a_string(&chain[key], &format!("{}.{key}", name(chain)));
        }
    }
    for case in dynamics_cases(&document) {
        for key in DYNAMICS_BLOCKS {
            assert_every_leaf_is_a_string(&case[key], &format!("{}.{key}", name(case)));
        }
        match &case["parts"] {
            Value::Null => {}
            Value::Array(parts) => {
                for (index, part) in parts.iter().enumerate() {
                    assert_every_leaf_is_a_string(part, &format!("{}.parts[{index}]", name(case)));
                }
            }
            other => panic!("{}.parts holds {other}", name(case)),
        }
    }
}

#[test]
fn every_rotation_block_is_a_rotation() {
    // `Rotation::new` checks `Rᵀ R = 1` and `det R = 1` exactly, which is what the transform
    // theorems need; a reflection would satisfy the first and anti-commute with the cross
    // product instead, so this test is the frame algebra's precondition rather than a formality.
    let document = document();
    for case in cases(&document) {
        let _ = rotation(&case["R"]);
    }
    for chain in chains(&document) {
        let _ = rotation(&chain["R1"]);
        let _ = rotation(&chain["R2"]);
    }
    for case in dynamics_cases(&document) {
        let _ = rotation(&case["R"]);
    }
}

// ---- the static frame transforms ---------------------------------------

/// The 15 static cases, every entry of every `expected` block.
///
/// The tip twist in a case is an independent datum, not the transported sensor twist: the case
/// supplies `tip_twist` and `sensor_twist` separately and the expected block reports what each one
/// transforms *to*. So the tip-frame virtual work is taken on the transported twist (the pair
/// `virtualWork_invariant` names), while `sensor_twist_from_tip` is taken on the stored tip twist.
#[test]
fn every_static_case_transforms_exactly() {
    let document = document();

    for case in cases(&document) {
        let label = name(case);
        let p = v3(&case["p"]);
        let r = rotation(&case["R"]);
        let tip_wrench = wrench(&case["tip_wrench"]);
        let tip_twist = twist(&case["tip_twist"]);
        let sensor_twist = twist(&case["sensor_twist"]);
        let expected = &case["expected"];

        // `tipToSensor` and the target direction `sensorToTip`
        let sensor_wrench = tip_to_sensor(p, r, tip_wrench);
        assert_eq!(
            sensor_wrench,
            wrench(&expected["sensor_wrench"]),
            "{label}: tipToSensor"
        );
        assert_eq!(
            sensor_to_tip(p, r, sensor_wrench),
            wrench(&expected["sensor_to_tip_wrench"]),
            "{label}: sensorToTip"
        );
        assert_eq!(
            sensor_to_tip(p, r, sensor_wrench),
            tip_wrench,
            "{label}: sensorToTip_tipToSensor returns the applied wrench"
        );

        // the three twist transforms: the shifted velocity on its own, the tip twist, and its
        // inverse
        assert_eq!(
            sensor_twist_to_tip_velocity(p, sensor_twist),
            v3(&expected["tip_velocity_in_sensor_frame"]),
            "{label}: sensorTwistToTipVelocity"
        );
        let tip_twist_from_sensor = sensor_twist_to_tip(p, r, sensor_twist);
        assert_eq!(
            tip_twist_from_sensor,
            twist(&expected["tip_twist_from_sensor"]),
            "{label}: sensorTwistToTip"
        );
        assert_eq!(
            tip_twist_to_sensor(p, r, tip_twist),
            twist(&expected["sensor_twist_from_tip"]),
            "{label}: tipTwistToSensor"
        );

        // `virtualWork_invariant`: the same work in both frames, and each side against the
        // stored scalar
        let work_sensor = virtual_work(sensor_wrench, sensor_twist);
        let work_tip = virtual_work(tip_wrench, tip_twist_from_sensor);
        assert_eq!(
            work_sensor,
            ratio(&expected["virtual_work_sensor_frame"]),
            "{label}: virtualWork in the sensor frame"
        );
        assert_eq!(
            work_tip,
            ratio(&expected["virtual_work_tip_frame"]),
            "{label}: virtualWork in the tip frame"
        );
        assert_eq!(work_sensor, work_tip, "{label}: virtualWork_invariant");

        // the two round trips the case does not store directly
        assert_eq!(
            tip_twist_to_sensor(p, r, tip_twist_from_sensor),
            sensor_twist,
            "{label}: tipTwistToSensor_sensorTwistToTip"
        );
        assert_eq!(
            sensor_twist_to_tip(p, r, tip_twist_to_sensor(p, r, tip_twist)),
            tip_twist,
            "{label}: sensorTwistToTip_tipTwistToSensor"
        );
    }
}

// ---- the chains ---------------------------------------------------------

/// The 3 chains, every entry of every `expected` block.
///
/// A chain is the same transform routed through a middle frame, and the point of storing both
/// routes is `tipToSensor_comp` / `sensorTwistToTip_comp`: the two-step result has to agree with
/// the one-step result through the folded pose `(p1 + R1 p2, R1 R2)`, or a measurement could not
/// be routed along a joint chain and still use a single identified body model.
#[test]
fn every_chain_folds_exactly() {
    let document = document();

    for chain in chains(&document) {
        let label = name(chain);
        let p1 = v3(&chain["p1"]);
        let r1 = rotation(&chain["R1"]);
        let p2 = v3(&chain["p2"]);
        let r2 = rotation(&chain["R2"]);
        let tip_wrench = wrench(&chain["tip_wrench"]);
        let sensor_twist = twist(&chain["sensor_twist"]);
        let expected = &chain["expected"];

        let composed_p = p1 + r1.mul_vec(p2);
        let composed_r = r1 * r2;
        assert_eq!(
            composed_p,
            v3(&expected["composed_p"]),
            "{label}: composed_p = p1 + R1 p2"
        );
        assert_eq!(
            composed_r.mat(),
            m3(&expected["composed_R"]),
            "{label}: composed_R = R1 R2"
        );

        assert_eq!(
            tip_to_sensor(composed_p, composed_r, tip_wrench),
            wrench(&expected["sensor_wrench_one_step"]),
            "{label}: tipToSensor through the folded pose"
        );
        assert_eq!(
            tip_to_sensor(p1, r1, tip_to_sensor(p2, r2, tip_wrench)),
            wrench(&expected["sensor_wrench_two_steps"]),
            "{label}: tipToSensor through the middle frame"
        );

        assert_eq!(
            sensor_twist_to_tip(composed_p, composed_r, sensor_twist),
            twist(&expected["tip_twist_one_step"]),
            "{label}: sensorTwistToTip through the folded pose"
        );
        assert_eq!(
            sensor_twist_to_tip(p2, r2, sensor_twist_to_tip(p1, r1, sensor_twist)),
            twist(&expected["tip_twist_two_steps"]),
            "{label}: sensorTwistToTip through the middle frame"
        );
    }
}

// ---- the dynamics -------------------------------------------------------

/// The 11 dynamics cases, every entry of every `expected` block.
///
/// Each case pins one thing beyond the static ones: the centripetal term of `comAccel`, the
/// gyroscopic torque `ω × (I ω)`, the parallel-axis form of the inertia, the two covariance
/// routes (sensor frame directly versus tip frame transported, which must agree exactly), the two
/// power identities, and compensation. The stored values are used on both sides of a covariance
/// check, so a mistake in the model cannot hide by being made twice.
#[test]
fn every_dynamics_case_recomputes_exactly() {
    let document = document();

    for case in dynamics_cases(&document) {
        let label = name(case);
        let p = v3(&case["p"]);
        let r = rotation(&case["R"]);
        let mp = mass_properties(&case["mass_properties"]);
        let g = v3(&case["gravity"]);
        let sensor_twist = twist(&case["sensor_twist"]);
        let sensor_accel = accel(&case["sensor_accel"]);
        let contact = wrench(&case["tip_wrench"]);
        let expected = &case["expected"];

        // the same body, described in sensor coordinates (`tipMassToSensor`)
        let sensor_mp = tip_mass_to_sensor(p, r, mp);
        let expected_sensor_mp = &expected["mass_properties_in_sensor_frame"];
        assert_eq!(
            sensor_mp.mass(),
            ratio(&expected_sensor_mp["mass"]),
            "{label}: the mass is unchanged by the frame"
        );
        assert_eq!(
            sensor_mp,
            mass_properties(expected_sensor_mp),
            "{label}: tipMassToSensor"
        );
        assert_eq!(
            sensor_mass_to_tip(p, r, sensor_mp),
            mp,
            "{label}: sensorMassToTip_tipMassToSensor"
        );

        // the same motion, described in tip coordinates: the twist and — differently — the
        // acceleration, which has to be told the twist because the material point moved
        let tip_twist = sensor_twist_to_tip(p, r, sensor_twist);
        let tip_accel = sensor_accel_to_tip(p, r, sensor_twist, sensor_accel);
        assert_eq!(
            tip_twist,
            twist(&expected["tip_twist"]),
            "{label}: sensorTwistToTip"
        );
        assert_eq!(
            tip_accel,
            accel(&expected["tip_accel"]),
            "{label}: sensorAccelToTip"
        );
        assert_eq!(
            accel_to_tip_round_trip(p, r, sensor_twist, sensor_accel),
            sensor_accel,
            "{label}: tipAccelToSensor_sensorAccelToTip"
        );

        // the body's own quantities, in the tip frame the case states them in
        let centred = com_accel(mp, tip_twist, tip_accel);
        assert_eq!(centred, v3(&expected["com_accel"]), "{label}: comAccel");
        assert_eq!(
            first_moment(mp),
            v3(&expected["first_moment"]),
            "{label}: firstMoment"
        );
        assert_eq!(
            origin_inertia(mp),
            m3(&expected["origin_inertia"]),
            "{label}: originInertia"
        );

        // the inertial wrench, computed in the sensor frame and again from the tip frame
        let sensor_inertial = inertial_wrench(sensor_mp, sensor_twist, sensor_accel);
        let tip_inertial = inertial_wrench(mp, tip_twist, tip_accel);
        assert_eq!(
            sensor_inertial,
            wrench(&expected["inertial_wrench"]),
            "{label}: inertialWrench in the sensor frame"
        );
        assert_eq!(
            tip_to_sensor(p, r, tip_inertial),
            wrench(&expected["inertial_wrench_from_tip"]),
            "{label}: inertialWrench carried up from the tip"
        );
        assert_eq!(
            sensor_inertial,
            tip_to_sensor(p, r, tip_inertial),
            "{label}: inertialWrench_transport"
        );

        // the gravity wrench, the same two ways, with `g` rotated into the tip frame
        let sensor_gravity = gravity_wrench(sensor_mp, g);
        let tip_gravity = gravity_wrench(mp, r.transpose_mul_vec(g));
        assert_eq!(
            sensor_gravity,
            wrench(&expected["gravity_wrench"]),
            "{label}: gravityWrench in the sensor frame"
        );
        assert_eq!(
            tip_to_sensor(p, r, tip_gravity),
            wrench(&expected["gravity_wrench_from_tip"]),
            "{label}: gravityWrench carried up from the tip"
        );
        assert_eq!(
            sensor_gravity,
            tip_to_sensor(p, r, tip_gravity),
            "{label}: gravityWrench_transport"
        );

        // power: `virtualWork_inertialWrench` and `virtualWork_gravityWrench`, both sides stored
        let centred_velocity = tip_twist.v + tip_twist.omega.cross(mp.com());
        assert_eq!(
            virtual_work(tip_inertial, tip_twist),
            ratio(&expected["power_inertial_work"]),
            "{label}: virtualWork of the inertial wrench"
        );
        assert_eq!(
            mp.mass() * centred.dot(centred_velocity)
                + tip_accel.alpha.dot(mp.inertia().mul_vec(tip_twist.omega)),
            ratio(&expected["power_inertial_formula"]),
            "{label}: virtualWork_inertialWrench"
        );
        assert_eq!(
            virtual_work(tip_gravity, tip_twist),
            ratio(&expected["power_gravity_work"]),
            "{label}: virtualWork of the gravity wrench"
        );
        assert_eq!(
            mp.mass() * r.transpose_mul_vec(g).dot(centred_velocity),
            ratio(&expected["power_gravity_formula"]),
            "{label}: virtualWork_gravityWrench"
        );

        // the measurement model and its inverse
        let measured = measured_wrench(p, r, mp, sensor_twist, sensor_accel, g, contact);
        assert_eq!(
            measured,
            wrench(&expected["measured_wrench"]),
            "{label}: measuredWrench"
        );
        let recovered = recovered_contact_wrench(p, r, mp, sensor_twist, sensor_accel, g, measured);
        assert_eq!(
            recovered,
            wrench(&expected["recovered_contact_wrench"]),
            "{label}: recoveredContactWrench"
        );
        assert_eq!(
            recovered, contact,
            "{label}: recoveredContactWrench_measuredWrench returns the contact"
        );
    }
}

/// `tipAccelToSensor_sensorAccelToTip`, spelled out so the call reads as the theorem does.
fn accel_to_tip_round_trip(
    p: Vec3<R>,
    r: Rotation<R>,
    sensor_twist: Twist<R>,
    sensor_accel: Accel<R>,
) -> Accel<R> {
    tip_accel_to_sensor(
        p,
        r,
        sensor_twist_to_tip(p, r, sensor_twist),
        sensor_accel_to_tip(p, r, sensor_twist, sensor_accel),
    )
}

/// The one case that carries `parts`: the composite's mass, first moment and origin inertia are
/// the sums of the parts', and so are its wrenches — `inertialWrench_add` / `gravityWrench_add`,
/// which is how a tool and its payload fold into one body.
#[test]
fn the_composition_parts_sum_to_the_composite() {
    let document = document();
    let mut seen = 0;

    for case in dynamics_cases(&document) {
        let Value::Array(parts) = &case["parts"] else {
            continue;
        };
        seen += 1;
        let label = name(case);
        let composite = mass_properties(&case["mass_properties"]);
        let (one, two) = (mass_properties(&parts[0]), mass_properties(&parts[1]));

        assert_eq!(
            composite.mass(),
            one.mass() + two.mass(),
            "{label}: the masses add"
        );
        assert_eq!(
            first_moment(composite),
            first_moment(one) + first_moment(two),
            "{label}: the first moments add"
        );
        assert_eq!(
            origin_inertia(composite),
            matrix_add(origin_inertia(one), origin_inertia(two)),
            "{label}: the inertias about the common origin add"
        );

        // and the wrenches: same frame (tip), same motion, same field
        let tip_twist = twist(&case["expected"]["tip_twist"]);
        let tip_accel = accel(&case["expected"]["tip_accel"]);
        let g = v3(&case["gravity"]);
        assert_eq!(
            inertial_wrench(composite, tip_twist, tip_accel),
            inertial_wrench(one, tip_twist, tip_accel) + inertial_wrench(two, tip_twist, tip_accel),
            "{label}: inertialWrench_add"
        );
        assert_eq!(
            gravity_wrench(composite, g),
            gravity_wrench(one, g) + gravity_wrench(two, g),
            "{label}: gravityWrench_add"
        );
    }

    assert_eq!(seen, 1, "exactly one case carries parts");
}

/// `a + b` for the 3x3 inertia blocks; the kinematics `Mat3` carries the product only.
fn matrix_add(left: Mat3<R>, right: Mat3<R>) -> Mat3<R> {
    let mut sum = left;
    for i in 0..3 {
        for j in 0..3 {
            sum.set(i, j, left.at(i, j) + right.at(i, j));
        }
    }
    sum
}

/// The sign convention, taken straight off the case the generator named for it:
/// `g` points down, gravity pulls the body down with `m g`, and the sensor holding it still reads
/// the reaction, `-gravityWrench`. Every other dynamics case inherits this frame of reference.
#[test]
fn a_body_at_rest_reads_minus_its_gravity_wrench() {
    let document = document();
    let case = dynamics_cases(&document)
        .iter()
        .find(|case| name(case) == "rest_gravity_only")
        .expect("the generator emits rest_gravity_only");

    let p = v3(&case["p"]);
    let r = rotation(&case["R"]);
    let mp = mass_properties(&case["mass_properties"]);
    let g = v3(&case["gravity"]);
    let expected = &case["expected"];

    // nothing is touching the tool, and nothing is moving
    assert_eq!(wrench(&case["tip_wrench"]), Wrench::zero());
    assert_eq!(twist(&case["sensor_twist"]), Twist::zero());
    assert_eq!(accel(&case["sensor_accel"]), Accel::zero());

    // gravity points down, and the body has mass
    assert!(g.z() < R::zero(), "g points down");
    assert!(!mp.mass().is_zero());

    // the whole model, at rest, with no contact
    let gravity = gravity_wrench(tip_mass_to_sensor(p, r, mp), g);
    assert_eq!(
        wrench(&expected["measured_wrench"]),
        -gravity,
        "the sensor reads minus the gravity wrench"
    );
    assert_eq!(
        wrench(&expected["gravity_wrench"]),
        gravity,
        "and the stored gravity wrench is the one being negated"
    );
    // with the force and the moment both present, so the check above is not vacuous
    assert!(gravity.force.x() != R::zero() || gravity.force.z() != R::zero());
    assert!(gravity.torque.y() != R::zero());

    // in this case the inertial wrench is zero, which is what makes the reading pure gravity
    assert_eq!(
        wrench(&expected["inertial_wrench"]),
        Wrench::zero(),
        "a body at rest has no inertial wrench"
    );
    assert_eq!(
        recovered_contact_wrench(
            p,
            r,
            mp,
            Twist::zero(),
            Accel::zero(),
            g,
            wrench(&expected["measured_wrench"])
        ),
        Wrench::zero(),
        "and compensation recovers the zero contact wrench"
    );
}
