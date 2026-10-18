//! Property and boundary tests for the conservative planner, over `f64`.
//!
//! Everything here follows `docs/motion_control.md` §3.8 and §6.5: the doc's worked
//! cases are pinned exactly, a seeded splitmix64 supplies reproducible random cases,
//! deterministic grids sweep the case boundaries, and proptest supplies magnitude
//! coverage. Feasibility is checked by dense sampling (`|v| ≤ V`, `|a| ≤ A`, `|j| ≤ J`)
//! with a small relative slack; the exact counterpart over `Ratio` lives in
//! `exact_rational.rs`.

use robot_motion::{
    Limits, MAX_PHASES, PlanError, PlanKind, Profile, ProfileError, Segment, State,
    plan_rest_conservative,
};

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

fn close(actual: f64, expected: f64, scale: f64) -> bool {
    (actual - expected).abs() <= 1e-9 * scale.abs().max(1.0) + 1e-12
}

#[track_caller]
fn assert_close(actual: f64, expected: f64, scale: f64, what: &str) {
    assert!(
        close(actual, expected, scale),
        "{what}: actual={actual:e}, expected={expected:e}, scale={scale:e}"
    );
}

/// Check one conservative profile against the §3.8 guarantees.
#[track_caller]
fn check_conservative(
    p: &Profile<f64>,
    q0: f64,
    q1: f64,
    vmax: f64,
    amax: f64,
    jmax: f64,
    label: &str,
) {
    let total = p.total_time();
    assert!(total.is_finite(), "{label}: non-finite total time");
    assert!(total >= 0.0, "{label}: negative total time {total:e}");

    let segments = p.segments();
    assert!(
        segments.len() <= 7,
        "{label}: conservative profile has {} segments",
        segments.len()
    );
    let mut summed = 0.0;
    for (i, seg) in segments.iter().enumerate() {
        assert!(
            seg.dur.is_finite() && seg.dur >= 0.0,
            "{label}: segment {i} has duration {:?}",
            seg.dur
        );
        assert!(
            seg.jerk.is_finite(),
            "{label}: segment {i} has jerk {:?}",
            seg.jerk
        );
        assert!(
            seg.jerk.abs() <= jmax * (1.0 + 1e-12) + 1e-12,
            "{label}: segment {i} |jerk|={:e} exceeds J={jmax:e}",
            seg.jerk.abs()
        );
        summed += seg.dur;
    }
    assert_close(
        summed,
        total,
        total,
        &format!("{label}: total time vs segment sum"),
    );

    assert_eq!(p.start().v, 0.0, "{label}: start velocity must be zero");
    assert_eq!(p.start().a, 0.0, "{label}: start acceleration must be zero");
    assert_close(
        p.start().q,
        q0,
        q0.abs().max(1.0),
        &format!("{label}: start q"),
    );
    assert_eq!(p.eval(0.0), p.start(), "{label}: eval(0) must be start");
    assert_eq!(
        p.eval(-1.0),
        p.start(),
        "{label}: eval below zero must clamp to start"
    );
    assert_eq!(
        p.eval(total + 1.0),
        p.end(),
        "{label}: eval above T must clamp to end"
    );

    let end = p.end();
    assert_close(
        end.q,
        q1,
        (q1 - q0).abs().max(1.0),
        &format!("{label}: end q"),
    );
    assert!(
        end.v.abs() <= 1e-9 * vmax.max(1.0) + 1e-12,
        "{label}: end velocity {:e} is not rest",
        end.v
    );
    assert!(
        end.a.abs() <= 1e-9 * amax.max(1.0) + 1e-12,
        "{label}: end acceleration {:e} is not rest",
        end.a
    );

    if q1 == q0 {
        assert_eq!(
            segments.len(),
            0,
            "{label}: zero displacement must be empty"
        );
        assert_eq!(
            p.kind(),
            PlanKind::ZeroMotion,
            "{label}: zero displacement kind"
        );
    } else {
        assert_eq!(
            p.kind(),
            PlanKind::Conservative,
            "{label}: non-zero displacement kind"
        );
        assert_eq!(
            segments.len(),
            7,
            "{label}: conservative template is seven slots"
        );
    }

    // Dense feasibility sweep, including both clamped endpoints.
    let tol_v = 1e-9 * vmax.max(1.0) + 1e-12;
    let tol_a = 1e-9 * amax.max(1.0) + 1e-12;
    let tol_q = 1e-9 * (q1 - q0).abs().max(1.0) + 1e-12;
    let samples = 300usize;
    let mut previous_q = p.eval(0.0).q;
    for i in 0..=samples {
        let t = total * (i as f64) / (samples as f64);
        let state = p.eval(t);
        assert!(
            state.is_finite(),
            "{label}: non-finite state at t={t:e} (q={}, v={}, a={})",
            state.q,
            state.v,
            state.a
        );
        assert!(
            state.v.abs() <= vmax + tol_v,
            "{label}: |v|={:e} exceeds V={vmax:e} at t={t:e}",
            state.v.abs()
        );
        assert!(
            state.a.abs() <= amax + tol_a,
            "{label}: |a|={:e} exceeds A={amax:e} at t={t:e}",
            state.a.abs()
        );
        if q1 >= q0 {
            assert!(
                state.q + tol_q >= previous_q,
                "{label}: position decreased ({:e} -> {:e}) at t={t:e}",
                previous_q,
                state.q
            );
        } else {
            assert!(
                state.q <= previous_q + tol_q,
                "{label}: position increased ({:e} -> {:e}) at t={t:e}",
                previous_q,
                state.q
            );
        }
        previous_q = state.q;
    }
}

fn plan(q0: f64, q1: f64, v: f64, a: f64, j: f64) -> Profile<f64> {
    plan_rest_conservative(q0, q1, Limits::new(v, a, j).unwrap()).unwrap()
}

// ---------------------------------------------------------------------------
// The doc's representative cases, §3.8.
// ---------------------------------------------------------------------------

#[test]
fn doc_cruise_case_has_the_expected_shape() {
    // V=3, A=2, J=4: tau = min(1, A/J=1/2, V/J=3/4) = 1/2, dmin = 1.
    // D=3 >= dmin, so j = J and tc = (3-1)/(4 * 1/4) = 2.
    let p = plan(0.0, 3.0, 3.0, 2.0, 4.0);
    assert_eq!(p.kind(), PlanKind::Conservative);
    assert_eq!(p.total_time(), 4.0);

    let durations = [0.5, 0.0, 0.5, 2.0, 0.5, 0.0, 0.5];
    let jerks = [4.0, 0.0, -4.0, 0.0, -4.0, 0.0, 4.0];
    assert_eq!(p.segments().len(), durations.len());
    for (i, seg) in p.segments().iter().enumerate() {
        assert_eq!(seg.dur, durations[i], "segment {i} duration");
        assert_eq!(seg.jerk, jerks[i], "segment {i} jerk");
    }
    check_conservative(&p, 0.0, 3.0, 3.0, 2.0, 4.0, "doc cruise case");
}

#[test]
fn doc_triangular_case_has_the_expected_shape() {
    // D=1/2 < dmin=1, so j = D/(2 tau^3) = (1/2)/(2/8) = 2 and tc = 0.
    let p = plan(0.0, 0.5, 3.0, 2.0, 4.0);
    assert_eq!(p.kind(), PlanKind::Conservative);
    assert_eq!(p.total_time(), 2.0);
    assert_eq!(
        p.segments(),
        &[
            Segment {
                dur: 0.5,
                jerk: 2.0
            },
            Segment {
                dur: 0.0,
                jerk: 0.0
            },
            Segment {
                dur: 0.5,
                jerk: -2.0
            },
            Segment {
                dur: 0.0,
                jerk: 0.0
            },
            Segment {
                dur: 0.5,
                jerk: -2.0
            },
            Segment {
                dur: 0.0,
                jerk: 0.0
            },
            Segment {
                dur: 0.5,
                jerk: 2.0
            },
        ]
    );
    check_conservative(&p, 0.0, 0.5, 3.0, 2.0, 4.0, "doc triangular case");
}

#[test]
fn zero_displacement_is_the_empty_profile() {
    let p = plan(7.5, 7.5, 3.0, 2.0, 4.0);
    assert_eq!(p.kind(), PlanKind::ZeroMotion);
    assert_eq!(p.segments().len(), 0);
    assert_eq!(p.total_time(), 0.0);
    assert_eq!(p.start(), State::new(7.5, 0.0, 0.0));
    assert_eq!(p.end(), p.start());
    for t in [-1.0, 0.0, 1.0] {
        assert_eq!(p.eval(t), p.start(), "empty profile at t={t}");
    }
}

#[test]
fn negative_displacement_mirrors_the_jerks() {
    let forward = plan(0.0, 3.0, 3.0, 2.0, 4.0);
    let backward = plan(0.0, -3.0, 3.0, 2.0, 4.0);
    assert_eq!(backward.total_time(), forward.total_time());
    for (f, b) in forward.segments().iter().zip(backward.segments()) {
        assert_eq!(b.dur, f.dur);
        assert_eq!(b.jerk, -f.jerk);
    }
    check_conservative(&backward, 0.0, -3.0, 3.0, 2.0, 4.0, "negative displacement");
}

// ---------------------------------------------------------------------------
// Seeded random and deterministic grids.
// ---------------------------------------------------------------------------

#[test]
fn seeded_random_cases_are_feasible() {
    let mut state = 0x0123_4567_89AB_CDEFu64;
    for case in 0..400 {
        let q0 = spread(&mut state, -50.0, 50.0);
        let q1 = spread(&mut state, -50.0, 50.0);
        let vmax = 10f64.powf(spread(&mut state, -2.0, 2.0));
        let amax = 10f64.powf(spread(&mut state, -2.0, 2.0));
        let jmax = 10f64.powf(spread(&mut state, -2.0, 2.0));
        let p = plan(q0, q1, vmax, amax, jmax);
        check_conservative(
            &p,
            q0,
            q1,
            vmax,
            amax,
            jmax,
            &format!("splitmix case {case}"),
        );
    }
}

#[test]
fn deterministic_grid_is_feasible() {
    let starts = [-3.0, -1.0, 0.0, 2.0];
    let targets = [-2.0, 0.0, 1.0, 5.0];
    let speeds = [0.5, 3.0];
    let accels = [0.25, 2.0];
    let jerks = [1.0, 4.0];
    for &q0 in &starts {
        for &q1 in &targets {
            for &v in &speeds {
                for &a in &accels {
                    for &j in &jerks {
                        let p = plan(q0, q1, v, a, j);
                        check_conservative(
                            &p,
                            q0,
                            q1,
                            v,
                            a,
                            j,
                            &format!("grid q0={q0} q1={q1} V={v} A={a} J={j}"),
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn displacement_sweep_across_the_template_boundary() {
    // With V=3, A=2, J=4 the template's D >= 2 J tau^3 boundary is D = 1.
    let displacements = [1e-3, 0.25, 0.5, 0.999, 1.0, 1.001, 2.0, 3.0, 100.0];
    for &d in &displacements {
        for sign in [1.0, -1.0] {
            let q1 = sign * d;
            let p = plan(0.0, q1, 3.0, 2.0, 4.0);
            check_conservative(&p, 0.0, q1, 3.0, 2.0, 4.0, &format!("sweep D={q1}"));
        }
    }
}

#[test]
fn planner_is_bit_identical_across_calls() {
    let mut state = 0xDEAD_BEEF_CAFE_F00Du64;
    for _ in 0..64 {
        let q0 = spread(&mut state, -10.0, 10.0);
        let q1 = spread(&mut state, -10.0, 10.0);
        let vmax = 10f64.powf(spread(&mut state, -1.0, 1.0));
        let amax = 10f64.powf(spread(&mut state, -1.0, 1.0));
        let jmax = 10f64.powf(spread(&mut state, -1.0, 1.0));
        let first = plan(q0, q1, vmax, amax, jmax);
        let second = plan(q0, q1, vmax, amax, jmax);
        assert_bit_identical(&first, &second);
    }
}

fn assert_bit_identical(a: &Profile<f64>, b: &Profile<f64>) {
    assert_eq!(a.kind(), b.kind());
    assert_eq!(a.total_time().to_bits(), b.total_time().to_bits());
    assert_eq!(a.segments().len(), b.segments().len());
    for (i, (x, y)) in a.segments().iter().zip(b.segments()).enumerate() {
        assert_eq!(
            x.dur.to_bits(),
            y.dur.to_bits(),
            "segment {i} duration bits"
        );
        assert_eq!(x.jerk.to_bits(), y.jerk.to_bits(), "segment {i} jerk bits");
    }
    assert_state_bits(a.start(), b.start(), "start");
    assert_state_bits(a.end(), b.end(), "end");
    for i in 0..a.segments().len() {
        assert_state_bits(
            a.phase_start(i).unwrap(),
            b.phase_start(i).unwrap(),
            &format!("phase start {i}"),
        );
    }
}

fn assert_state_bits(a: State<f64>, b: State<f64>, what: &str) {
    assert_eq!(a.q.to_bits(), b.q.to_bits(), "{what} q bits");
    assert_eq!(a.v.to_bits(), b.v.to_bits(), "{what} v bits");
    assert_eq!(a.a.to_bits(), b.a.to_bits(), "{what} a bits");
}

// ---------------------------------------------------------------------------
// Negative cases.
// ---------------------------------------------------------------------------

#[test]
fn planner_rejects_non_finite_positions() {
    let lim = Limits::new(3.0, 2.0, 4.0).unwrap();
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(
            plan_rest_conservative(bad, 1.0, lim).unwrap_err(),
            PlanError::NonFiniteInput,
            "q0 = {bad}"
        );
        assert_eq!(
            plan_rest_conservative(0.0, bad, lim).unwrap_err(),
            PlanError::NonFiniteInput,
            "q1 = {bad}"
        );
    }
}

#[test]
fn limits_reject_non_positive_and_non_finite_values() {
    let zero = 0.0;
    let cases = [
        (zero, 1.0, 1.0),
        (-1.0, 1.0, 1.0),
        (1.0, zero, 1.0),
        (1.0, -1.0, 1.0),
        (1.0, 1.0, zero),
        (1.0, 1.0, -1.0),
        (f64::NAN, 1.0, 1.0),
        (1.0, f64::NAN, 1.0),
        (1.0, 1.0, f64::NAN),
        (f64::INFINITY, 1.0, 1.0),
        (1.0, f64::INFINITY, 1.0),
        (1.0, 1.0, f64::INFINITY),
        (f64::NEG_INFINITY, 1.0, 1.0),
    ];
    for (v, a, j) in cases {
        assert_eq!(
            Limits::new(v, a, j).unwrap_err(),
            PlanError::NonPositiveLimit,
            "Limits::new({v}, {a}, {j})"
        );
    }
}

#[test]
fn stretch_rejects_factors_below_one_and_non_finite() {
    let p = plan(0.0, 3.0, 3.0, 2.0, 4.0);
    for factor in [
        0.0,
        -0.0,
        -1.0,
        0.5,
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ] {
        assert_eq!(
            p.stretch(factor).unwrap_err(),
            ProfileError::InvalidStretch,
            "stretch({factor})"
        );
    }

    let stretched = p.stretch(2.0).unwrap();
    assert_eq!(stretched.kind(), PlanKind::Conservative);
    assert_eq!(stretched.total_time(), 2.0 * p.total_time());
    assert_eq!(stretched.start().q, p.start().q);
    assert_eq!(stretched.start().v, p.start().v / 2.0);
    assert_eq!(stretched.start().a, p.start().a / 4.0);
    for (i, (orig, scaled)) in p.segments().iter().zip(stretched.segments()).enumerate() {
        assert_eq!(scaled.dur, 2.0 * orig.dur, "segment {i} duration");
        assert_eq!(scaled.jerk, orig.jerk / 8.0, "segment {i} jerk");
    }
    // factor 1 is the identity of the accepted domain.
    let identity = p.stretch(1.0).unwrap();
    assert_eq!(identity.start(), p.start());
    assert_eq!(identity.end(), p.end());
    assert_eq!(identity.total_time(), p.total_time());
    assert_eq!(identity.segments(), p.segments());
}

#[test]
fn overflowing_displacement_is_a_typed_error() {
    let lim = Limits::new(1.0, 1.0, 1.0).unwrap();
    // q1 - q0 overflows to -inf, which the planner must report rather than propagate.
    assert_eq!(
        plan_rest_conservative(f64::MAX, -f64::MAX, lim).unwrap_err(),
        PlanError::NumericalFailure
    );
}

// ---------------------------------------------------------------------------
// Capacity and construction errors.
// ---------------------------------------------------------------------------

#[test]
fn capacity_is_enforced_at_max_phases() {
    let start = State::new(0.0, 0.0, 0.0);
    let seg = Segment {
        dur: 0.1,
        jerk: 0.0,
    };

    let full: [Segment<f64>; MAX_PHASES] = [seg; MAX_PHASES];
    let profile = Profile::from_parts(start, &full).unwrap();
    assert_eq!(profile.segments().len(), MAX_PHASES);

    // A constructed over-capacity array is rejected, not truncated.
    let over: [Segment<f64>; MAX_PHASES + 1] = [seg; MAX_PHASES + 1];
    assert_eq!(
        Profile::from_parts(start, &over).unwrap_err(),
        ProfileError::TooManySegments
    );

    let mut pushed = Profile::constant(start);
    for _ in 0..MAX_PHASES {
        pushed.try_push(seg).unwrap();
    }
    assert_eq!(
        pushed.try_push(seg).unwrap_err(),
        ProfileError::TooManySegments
    );
}

#[test]
fn profile_construction_rejects_bad_segments_and_states() {
    let start = State::new(0.0, 0.0, 0.0);
    assert_eq!(
        Profile::from_parts(
            start,
            &[Segment {
                dur: -0.5,
                jerk: 0.0
            }]
        )
        .unwrap_err(),
        ProfileError::NegativeDuration
    );
    assert_eq!(
        Profile::from_parts(
            start,
            &[Segment {
                dur: f64::NAN,
                jerk: 0.0
            }]
        )
        .unwrap_err(),
        ProfileError::NonFinite
    );
    assert_eq!(
        Profile::from_parts(
            start,
            &[Segment {
                dur: 1.0,
                jerk: f64::INFINITY
            }]
        )
        .unwrap_err(),
        ProfileError::NonFinite
    );
    assert_eq!(
        Profile::from_parts(State::new(f64::NAN, 0.0, 0.0), &[]).unwrap_err(),
        ProfileError::NonFinite
    );
    assert_eq!(
        Profile::from_parts(State::new(0.0, f64::INFINITY, 0.0), &[]).unwrap_err(),
        ProfileError::NonFinite
    );
}

#[test]
fn append_rejects_a_mismatched_junction() {
    let first = plan(0.0, 3.0, 3.0, 2.0, 4.0);
    let second = plan(4.0, 5.0, 3.0, 2.0, 4.0);
    assert_eq!(
        first.append(&first).unwrap_err(),
        ProfileError::JunctionMismatch
    );
    assert_eq!(
        first.append(&second).unwrap_err(),
        ProfileError::JunctionMismatch
    );
}

// ---------------------------------------------------------------------------
// proptest: magnitude coverage.
// ---------------------------------------------------------------------------

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 128, .. ProptestConfig::default() })]

    #[test]
    fn proptest_conservative_is_feasible(
        q0 in -1.0e4f64..1.0e4f64,
        dq in -1.0e4f64..1.0e4f64,
        vmax in 1.0e-3f64..1.0e3f64,
        amax in 1.0e-3f64..1.0e3f64,
        jmax in 1.0e-3f64..1.0e3f64,
    ) {
        let q1 = q0 + dq;
        let lim = Limits::new(vmax, amax, jmax).unwrap();
        let p = plan_rest_conservative(q0, q1, lim).unwrap();
        check_conservative(&p, q0, q1, vmax, amax, jmax, "proptest");
    }

    #[test]
    fn proptest_conservative_magnitudes(
        q0 in -1.0e6f64..1.0e6f64,
        dq in -1.0e6f64..1.0e6f64,
        vmax in 1.0e-6f64..1.0e6f64,
        amax in 1.0e-6f64..1.0e6f64,
        jmax in 1.0e-6f64..1.0e6f64,
    ) {
        let q1 = q0 + dq;
        let lim = Limits::new(vmax, amax, jmax).unwrap();
        let p = plan_rest_conservative(q0, q1, lim).unwrap();
        check_conservative(&p, q0, q1, vmax, amax, jmax, "proptest magnitudes");
    }
}
