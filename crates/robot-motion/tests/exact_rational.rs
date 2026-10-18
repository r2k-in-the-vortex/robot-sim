//! Exact tests for the polynomial layer and the conservative planner over
//! `robot_golden::Ratio`.
//!
//! The planner is radical-free, so `plan_rest_conservative::<Ratio>` produces exact
//! durations and jerks whenever its inputs are rational. Every check here uses `==`; a
//! disagreement is a real disagreement, not floating-point drift. This is the
//! `Ratio`-side counterpart of `properties.rs` and follows `docs/motion_control.md`
//! §3.8 and §6.4.

use robot_golden::Ratio;
use robot_kinematics::Field;
use robot_motion::{
    JointProfile, Limits, PlanKind, Profile, ProfileError, Segment, State, plan_rest_conservative,
};

fn r(numerator: i128, denominator: i128) -> Ratio {
    Ratio::new(numerator, denominator)
}

fn ri(value: i128) -> Ratio {
    Ratio::integer(value)
}

fn limits(v: i128, a: i128, j: i128) -> Limits<Ratio> {
    Limits::new(ri(v), ri(a), ri(j)).unwrap()
}

fn plan(q0: Ratio, q1: Ratio, lim: Limits<Ratio>) -> Profile<Ratio> {
    plan_rest_conservative(q0, q1, lim).unwrap()
}

fn seg(dur: Ratio, jerk: Ratio) -> Segment<Ratio> {
    Segment { dur, jerk }
}

fn state(q: Ratio, v: Ratio, a: Ratio) -> State<Ratio> {
    State::new(q, v, a)
}

/// Exact §3.8 feasibility: per segment, `|jerk| ≤ J`, `|a| ≤ A` at both endpoints, and
/// `|v| ≤ V` at both endpoints and at the quadratic's stationary point when that point
/// lies inside the segment.
#[track_caller]
fn check_exact_feasible(p: &Profile<Ratio>, vmax: Ratio, amax: Ratio, jmax: Ratio) {
    let zero = Ratio::ZERO;
    let two = ri(2);
    for (i, segment) in p.segments().iter().enumerate() {
        let entry = p.phase_start(i).unwrap();

        assert!(segment.dur >= zero, "segment {i}: negative duration");
        assert!(
            segment.jerk.abs() <= jmax,
            "segment {i}: |jerk| {:?} exceeds {jmax:?}",
            segment.jerk.abs()
        );

        // Acceleration is linear in time, so its extreme on a segment is an endpoint.
        let exit_a = entry.a + segment.jerk * segment.dur;
        assert!(
            entry.a.abs() <= amax,
            "segment {i}: entry |a| {:?} exceeds {amax:?}",
            entry.a.abs()
        );
        assert!(
            exit_a.abs() <= amax,
            "segment {i}: exit |a| {:?} exceeds {amax:?}",
            exit_a.abs()
        );

        // Velocity is quadratic, so check both endpoints and its vertex a(t) = 0.
        let exit_v =
            entry.v + entry.a * segment.dur + segment.jerk * segment.dur * segment.dur / two;
        assert!(
            entry.v.abs() <= vmax,
            "segment {i}: entry |v| {:?} exceeds {vmax:?}",
            entry.v.abs()
        );
        assert!(
            exit_v.abs() <= vmax,
            "segment {i}: exit |v| {:?} exceeds {vmax:?}",
            exit_v.abs()
        );
        if !segment.jerk.is_zero() {
            let vertex = -entry.a / segment.jerk;
            if vertex > zero && vertex < segment.dur {
                let peak = entry.v + entry.a * vertex + segment.jerk * vertex * vertex / two;
                assert!(
                    peak.abs() <= vmax,
                    "segment {i}: vertex |v| {:?} exceeds {vmax:?}",
                    peak.abs()
                );
            }
        }
    }
}

/// Displacement, rest endpoints and monotonicity, all exactly.
#[track_caller]
fn check_exact_endpoints_and_monotonicity(p: &Profile<Ratio>, q0: Ratio, q1: Ratio) {
    assert_eq!(p.start(), state(q0, Ratio::ZERO, Ratio::ZERO));
    assert_eq!(p.end().q, q1, "end position");
    assert_eq!(p.end().v, Ratio::ZERO, "end velocity");
    assert_eq!(p.end().a, Ratio::ZERO, "end acceleration");
    assert_eq!(p.eval(Ratio::ZERO), p.start());

    let total = p.total_time();
    let samples = 32i128;
    let mut previous = p.eval(Ratio::ZERO).q;
    for k in 1..=samples {
        let t = total * r(k, samples);
        let q = p.eval(t).q;
        if q1 >= q0 {
            assert!(
                q >= previous,
                "position decreased at sample {k}: {previous:?} -> {q:?}"
            );
        } else {
            assert!(
                q <= previous,
                "position increased at sample {k}: {previous:?} -> {q:?}"
            );
        }
        previous = q;
    }
    assert_eq!(previous, q1);
}

// ---------------------------------------------------------------------------
// The doc's representative cases, exactly.
// ---------------------------------------------------------------------------

#[test]
fn doc_cruise_case_is_exact() {
    // V=3, A=2, J=4: tau=1/2, dmin=1, D=3 -> j=4, tc=2.
    let p = plan(ri(0), ri(3), limits(3, 2, 4));
    assert_eq!(p.kind(), PlanKind::Conservative);
    assert_eq!(p.total_time(), ri(4));
    assert_eq!(
        p.segments(),
        &[
            seg(r(1, 2), ri(4)),
            seg(Ratio::ZERO, Ratio::ZERO),
            seg(r(1, 2), ri(-4)),
            seg(ri(2), Ratio::ZERO),
            seg(r(1, 2), ri(-4)),
            seg(Ratio::ZERO, Ratio::ZERO),
            seg(r(1, 2), ri(4)),
        ]
    );

    // Phase starts computed by hand from the constant-jerk recurrence.
    let expected_starts = [
        state(Ratio::ZERO, Ratio::ZERO, Ratio::ZERO),
        state(r(1, 12), r(1, 2), ri(2)),
        state(r(1, 12), r(1, 2), ri(2)),
        state(r(1, 2), ri(1), Ratio::ZERO),
        state(r(5, 2), ri(1), Ratio::ZERO),
        state(r(35, 12), r(1, 2), ri(-2)),
        state(r(35, 12), r(1, 2), ri(-2)),
    ];
    for (i, expected) in expected_starts.iter().enumerate() {
        assert_eq!(p.phase_start(i), Some(*expected), "phase start {i}");
    }
    assert_eq!(p.phase_start(7), None);

    assert_eq!(
        p.eval(Ratio::ZERO),
        state(Ratio::ZERO, Ratio::ZERO, Ratio::ZERO)
    );
    assert_eq!(p.eval(ri(4)), state(ri(3), Ratio::ZERO, Ratio::ZERO));
    check_exact_feasible(&p, ri(3), ri(2), ri(4));
    check_exact_endpoints_and_monotonicity(&p, ri(0), ri(3));
}

#[test]
fn doc_triangular_case_is_exact() {
    // D=1/2 < dmin=1 -> j=2, tc=0.
    let p = plan(ri(0), r(1, 2), limits(3, 2, 4));
    assert_eq!(p.kind(), PlanKind::Conservative);
    assert_eq!(p.total_time(), ri(2));
    assert_eq!(
        p.segments(),
        &[
            seg(r(1, 2), ri(2)),
            seg(Ratio::ZERO, Ratio::ZERO),
            seg(r(1, 2), ri(-2)),
            seg(Ratio::ZERO, Ratio::ZERO),
            seg(r(1, 2), ri(-2)),
            seg(Ratio::ZERO, Ratio::ZERO),
            seg(r(1, 2), ri(2)),
        ]
    );
    assert_eq!(p.end(), state(r(1, 2), Ratio::ZERO, Ratio::ZERO));
    check_exact_feasible(&p, ri(3), ri(2), ri(4));
    check_exact_endpoints_and_monotonicity(&p, ri(0), r(1, 2));
}

#[test]
fn zero_displacement_is_the_empty_profile_exactly() {
    let p = plan(ri(7), ri(7), limits(3, 2, 4));
    assert_eq!(p.kind(), PlanKind::ZeroMotion);
    assert!(p.segments().is_empty());
    assert_eq!(p.total_time(), Ratio::ZERO);
    assert_eq!(p.start(), state(ri(7), Ratio::ZERO, Ratio::ZERO));
    assert_eq!(p.end(), p.start());
    assert_eq!(p.eval(r(-1, 2)), p.start());
    assert_eq!(p.eval(r(1, 2)), p.start());
}

#[test]
fn negative_displacement_is_exact_and_monotone() {
    let forward = plan(ri(0), ri(3), limits(3, 2, 4));
    let backward = plan(ri(0), ri(-3), limits(3, 2, 4));
    assert_eq!(backward.total_time(), forward.total_time());
    for (f, b) in forward.segments().iter().zip(backward.segments()) {
        assert_eq!(b.dur, f.dur);
        assert_eq!(b.jerk, -f.jerk);
    }
    assert_eq!(backward.end(), state(ri(-3), Ratio::ZERO, Ratio::ZERO));
    check_exact_feasible(&backward, ri(3), ri(2), ri(4));
    check_exact_endpoints_and_monotonicity(&backward, ri(0), ri(-3));
}

// ---------------------------------------------------------------------------
// Exact feasibility over a deterministic rational grid.
// ---------------------------------------------------------------------------

#[test]
fn conservative_is_exactly_feasible_on_a_rational_grid() {
    let limit_sets = [
        limits(3, 2, 4),
        limits(1, 1, 1),
        Limits::new(r(1, 2), r(3, 4), r(5, 2)).unwrap(),
        Limits::new(ri(2), r(3, 2), r(1, 2)).unwrap(),
        limits(1, 1, 10),
    ];
    let starts = [ri(0), r(1, 2)];
    let targets = [r(-3, 2), r(-1, 2), r(1, 2), r(3, 2), ri(3)];

    for &q0 in &starts {
        for &q1 in &targets {
            for &lim in &limit_sets {
                let (vmax, amax, jmax) = (lim.vmax(), lim.amax(), lim.jmax());
                let p = plan(q0, q1, lim);
                check_exact_feasible(&p, vmax, amax, jmax);
                check_exact_endpoints_and_monotonicity(&p, q0, q1);
                assert!(p.segments().len() <= 7);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Evaluation, boundary convention, and evaluation on a scaled clock.
// ---------------------------------------------------------------------------

#[test]
fn eval_matches_the_hand_computed_polynomial() {
    // q(t) = 1 + 2t + 3t^2/2 + 6t^3/6, v(t) = 2 + 3t + 3t^2, a(t) = 3 + 6t.
    let p = Profile::from_parts(state(ri(1), ri(2), ri(3)), &[seg(ri(2), ri(6))]).unwrap();
    let two = ri(2);
    assert_eq!(p.total_time(), two);

    let cases = [
        (r(1, 2), state(r(5, 2), r(17, 4), ri(6))),
        (ri(1), state(r(11, 2), ri(8), ri(9))),
        (r(3, 2), state(r(43, 4), r(53, 4), ri(12))),
        (two, state(ri(19), ri(20), ri(15))),
    ];
    for (t, expected) in cases {
        assert_eq!(p.eval(t), expected, "eval at t={t:?}");
    }

    // Clamping outside [0, total_time].
    assert_eq!(p.eval(r(-1, 2)), p.start());
    assert_eq!(p.eval(ri(-3)), p.start());
    assert_eq!(p.eval(ri(3)), p.end());
    assert_eq!(p.end(), state(ri(19), ri(20), ri(15)));
}

#[test]
fn eval_selects_the_later_segment_at_boundaries() {
    let p = plan(ri(0), ri(3), limits(3, 2, 4));
    // tau = 1/2; at t = tau the strict `<` test has already passed phase 0.
    assert_eq!(p.eval(r(1, 2)), p.phase_start(2).unwrap());
    // At t = 1 = 2*tau the acceleration phase has ended.
    assert_eq!(p.eval(ri(1)), p.phase_start(3).unwrap());
    assert_eq!(p.eval(p.total_time()), p.end());
}

#[test]
fn eval_scaled_composes_the_clock_exactly() {
    // q = p.q(s), v = p.v(s) * rate, a = p.a(s) * rate^2 + p.v(s) * rate_dot.
    let p = Profile::from_parts(state(ri(1), ri(2), ri(3)), &[seg(ri(2), ri(6))]).unwrap();
    let scaled = p.eval_scaled(ri(1), ri(2), ri(3));
    assert_eq!(scaled.q, r(11, 2));
    assert_eq!(scaled.v, ri(16));
    assert_eq!(scaled.a, ri(60));

    // rate = 1, rate_dot = 0 is the identity on velocity and acceleration.
    let identity = p.eval_scaled(r(1, 2), ri(1), Ratio::ZERO);
    assert_eq!(identity, p.eval(r(1, 2)));
}

// ---------------------------------------------------------------------------
// stretch, translate, mirror, reverse and append, all exactly.
// ---------------------------------------------------------------------------

fn general_profile() -> Profile<Ratio> {
    Profile::from_parts(
        state(ri(1), ri(2), ri(3)),
        &[
            seg(ri(1), ri(6)),
            seg(r(1, 2), ri(-3)),
            seg(r(3, 2), Ratio::ZERO),
        ],
    )
    .unwrap()
}

#[test]
fn stretch_maps_durations_and_jerks_exactly() {
    let p = general_profile();
    let two = ri(2);
    let stretched = p.stretch(two).unwrap();

    assert_eq!(stretched.kind(), p.kind());
    assert_eq!(stretched.total_time(), two * p.total_time());
    assert_eq!(stretched.start(), state(ri(1), ri(1), r(3, 4)));

    let expected = [
        seg(ri(2), r(3, 4)),
        seg(ri(1), r(-3, 8)),
        seg(ri(3), Ratio::ZERO),
    ];
    assert_eq!(stretched.segments(), &expected);

    // The end state scales the same way: q, v/f, a/f^2.
    let f2 = two * two;
    assert_eq!(stretched.end().q, p.end().q);
    assert_eq!(stretched.end().v, p.end().v / two);
    assert_eq!(stretched.end().a, p.end().a / f2);

    // And the whole curve obeys stretched.eval(f*t) = (q, v/f, a/f^2) at t.
    let total = p.total_time();
    for k in 0..=8 {
        let t = total * r(k, 8);
        let original = p.eval(t);
        let scaled = stretched.eval(two * t);
        assert_eq!(scaled.q, original.q, "stretched q at sample {k}");
        assert_eq!(scaled.v, original.v / two, "stretched v at sample {k}");
        assert_eq!(scaled.a, original.a / f2, "stretched a at sample {k}");
    }
}

#[test]
fn stretch_one_is_the_identity_and_below_one_is_rejected() {
    let p = general_profile();
    let identity = p.stretch(Ratio::ONE).unwrap();
    assert_eq!(identity, p);
    assert_eq!(
        p.stretch(r(1, 2)).unwrap_err(),
        ProfileError::InvalidStretch
    );
    assert_eq!(
        p.stretch(Ratio::ZERO).unwrap_err(),
        ProfileError::InvalidStretch
    );
    assert_eq!(p.stretch(ri(-2)).unwrap_err(), ProfileError::InvalidStretch);
}

#[test]
fn translate_shifts_only_position() {
    let p = general_profile();
    let dq = r(7, 3);
    let moved = p.translate(dq);
    assert_eq!(moved.translate(-dq), p);

    for k in 0..=8 {
        let t = p.total_time() * r(k, 8);
        let original = p.eval(t);
        let shifted = moved.eval(t);
        assert_eq!(shifted.q, original.q + dq, "translated q at sample {k}");
        assert_eq!(shifted.v, original.v, "translated v at sample {k}");
        assert_eq!(shifted.a, original.a, "translated a at sample {k}");
    }
    assert_eq!(moved.end().q, p.end().q + dq);
    assert_eq!(moved.start().v, p.start().v);
    assert_eq!(moved.start().a, p.start().a);
}

#[test]
fn mirror_twice_is_the_identity() {
    let p = general_profile();
    let mirrored = p.mirror();
    assert_eq!(mirrored.mirror(), p);
    assert_eq!(mirrored.start(), state(ri(1), ri(-2), ri(-3)));
    for k in 0..=8 {
        let t = p.total_time() * r(k, 8);
        let original = p.eval(t);
        let reflected = mirrored.eval(t);
        // Reflection about the start position.
        assert_eq!(
            reflected.q,
            ri(2) * p.start().q - original.q,
            "mirrored q at sample {k}"
        );
        assert_eq!(reflected.v, -original.v, "mirrored v at sample {k}");
        assert_eq!(reflected.a, -original.a, "mirrored a at sample {k}");
    }
}

#[test]
fn reverse_twice_is_the_identity() {
    let p = general_profile();
    let reversed = p.reverse();
    assert_eq!(reversed.reverse(), p);
    assert_eq!(reversed.start(), state(p.end().q, -p.end().v, p.end().a));

    let total = p.total_time();
    for k in 0..=8 {
        let t = total * r(k, 8);
        let original = p.eval(t);
        let flipped = reversed.eval(total - t);
        assert_eq!(flipped.q, original.q, "reversed q at sample {k}");
        assert_eq!(flipped.v, -original.v, "reversed v at sample {k}");
        assert_eq!(flipped.a, original.a, "reversed a at sample {k}");
    }
}

#[test]
fn append_round_trips_exactly() {
    let first = plan(ri(0), ri(3), limits(3, 2, 4));
    let second = plan(ri(3), ri(5), limits(3, 2, 4));
    let joined = first.append(&second).unwrap();

    assert_eq!(
        joined.total_time(),
        first.total_time() + second.total_time()
    );
    assert_eq!(joined.segments().len(), 14);
    assert_eq!(joined.start(), first.start());
    assert_eq!(joined.end(), second.end());

    for k in 0..=20 {
        let t = joined.total_time() * r(k, 20);
        let expected = if t <= first.total_time() {
            first.eval(t)
        } else {
            second.eval(t - first.total_time())
        };
        assert_eq!(joined.eval(t), expected, "joined eval at sample {k}");
    }

    // Appending the empty profile is the identity.
    let hold = Profile::constant(joined.end());
    let extended = joined.append(&hold).unwrap();
    assert_eq!(extended, joined);

    // reverse(a ++ b) = reverse(b) ++ reverse(a).
    let reversed = joined.reverse();
    let parts = second.reverse().append(&first.reverse()).unwrap();
    assert_eq!(reversed, parts);
}

#[test]
fn append_rejects_a_mismatched_junction_exactly() {
    let first = plan(ri(0), ri(3), limits(3, 2, 4));
    let second = plan(ri(4), ri(5), limits(3, 2, 4));
    assert_eq!(
        first.append(&second).unwrap_err(),
        ProfileError::JunctionMismatch
    );
}

// ---------------------------------------------------------------------------
// JointProfile.
// ---------------------------------------------------------------------------

#[test]
fn joint_profile_evaluates_each_joint_exactly() {
    let a = Profile::from_parts(
        state(ri(0), ri(0), ri(0)),
        &[seg(ri(1), Ratio::ZERO), seg(ri(1), Ratio::ZERO)],
    )
    .unwrap();
    let b = Profile::from_parts(
        state(ri(5), ri(0), ri(0)),
        &[seg(r(1, 2), ri(2)), seg(r(3, 2), Ratio::ZERO)],
    )
    .unwrap();
    assert_eq!(a.total_time(), b.total_time());

    let joints = JointProfile::new([a, b], ri(2));
    assert_eq!(joints.total_time(), ri(2));
    assert_eq!(joints.joint(0), Some(&a));
    assert_eq!(joints.joint(1), Some(&b));
    assert_eq!(joints.joint(2), None);

    for k in 0..=8 {
        let t = ri(2) * r(k, 8);
        assert_eq!(
            joints.eval(t),
            [a.eval(t), b.eval(t)],
            "joint eval at sample {k}"
        );

        let scaled = joints.eval_scaled(t, ri(2), ri(3));
        assert_eq!(
            scaled,
            [
                a.eval_scaled(t, ri(2), ri(3)),
                b.eval_scaled(t, ri(2), ri(3))
            ]
        );
    }

    let empty = JointProfile::<0, Ratio>::new([], Ratio::ZERO);
    assert_eq!(empty.total_time(), Ratio::ZERO);
    assert_eq!(empty.eval(ri(1)), []);
}
