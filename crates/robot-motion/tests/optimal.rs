//! The optimal 7-phase rest-to-rest planner: the doc's representative cases and its
//! feasibility, determinism and boundary properties.
//!
//! Covers `docs/motion_control.md` §3.3–§3.4 and the §6.2 representative table: case
//! selection, exact durations, total time, peak velocity/acceleration, endpoints, dense
//! sampling of the limits, and the case boundaries.

use robot_motion::{Limits, PlanError, PlanKind, Profile, plan_rest_to_rest};

fn limits(vmax: f64, amax: f64, jmax: f64) -> Limits<f64> {
    Limits::new(vmax, amax, jmax).expect("limits are positive and finite")
}

fn close(actual: f64, expected: f64, scale: f64) -> bool {
    (actual - expected).abs() <= 1e-9 * scale.abs().max(1.0) + 1e-12
}

#[track_caller]
fn assert_close(actual: f64, expected: f64, scale: f64, what: &str) {
    assert!(
        close(actual, expected, scale),
        "{what}: actual={actual:.17e}, expected={expected:.17e}, scale={scale:.1e}"
    );
}

#[track_caller]
fn assert_durations(profile: &Profile<f64>, expected: [f64; 7], what: &str) {
    let segments = profile.segments();
    assert_eq!(
        segments.len(),
        7,
        "{what}: expected the seven canonical slots"
    );
    for (i, (segment, want)) in segments.iter().zip(expected.iter()).enumerate() {
        assert_close(
            segment.dur,
            *want,
            want.abs(),
            &format!("{what}: slot {i} duration"),
        );
    }
}

/// Peak speed and acceleration, taken at phase boundaries where these piecewise
/// linear/quadratic quantities attain their extrema.
fn boundary_peaks(profile: &Profile<f64>) -> (f64, f64) {
    let mut peak_v: f64 = 0.0;
    let mut peak_a: f64 = 0.0;
    let n = profile.segments().len();
    for i in 0..=n {
        let state = if i == n {
            profile.end()
        } else {
            profile.phase_start(i).expect("phase index within length")
        };
        peak_v = peak_v.max(state.v.abs());
        peak_a = peak_a.max(state.a.abs());
    }
    (peak_v, peak_a)
}

/// Feasibility and shape checks common to every positive-displacement case.
#[track_caller]
fn check_feasible(
    profile: &Profile<f64>,
    q0: f64,
    q1: f64,
    vmax: f64,
    amax: f64,
    jmax: f64,
    label: &str,
) {
    let delta = q1 - q0;
    let scale = delta.abs().max(1.0);
    let total = profile.total_time();
    assert!(
        total.is_finite() && total >= 0.0,
        "{label}: bad total time {total:e}"
    );
    assert_eq!(profile.segments().len(), 7, "{label}: expected seven slots");

    let summed: f64 = profile.segments().iter().map(|s| s.dur).sum();
    assert_close(summed, total, total, &format!("{label}: durations sum"));

    assert_close(
        profile.start().q,
        q0,
        scale,
        &format!("{label}: start position"),
    );
    assert_close(
        profile.start().v,
        0.0,
        1.0,
        &format!("{label}: start velocity"),
    );
    assert_close(
        profile.start().a,
        0.0,
        1.0,
        &format!("{label}: start acceleration"),
    );
    assert_close(
        profile.end().q,
        q1,
        scale,
        &format!("{label}: end position"),
    );
    assert_close(profile.end().v, 0.0, 1.0, &format!("{label}: end velocity"));
    assert_close(
        profile.end().a,
        0.0,
        1.0,
        &format!("{label}: end acceleration"),
    );

    // Fixed 7-slot jerk pattern, signed by the direction of travel.
    let sign = if delta >= 0.0 { 1.0 } else { -1.0 };
    let pattern = [jmax, 0.0, -jmax, 0.0, -jmax, 0.0, jmax];
    for (i, segment) in profile.segments().iter().enumerate() {
        assert!(
            segment.dur.is_finite() && segment.dur >= 0.0,
            "{label}: slot {i} duration"
        );
        assert_close(
            segment.jerk,
            sign * pattern[i],
            jmax,
            &format!("{label}: slot {i} jerk"),
        );
        assert!(
            segment.jerk.abs() <= jmax * (1.0 + 1e-9),
            "{label}: slot {i} jerk {} exceeds {jmax}",
            segment.jerk
        );
    }

    // Bounds and finiteness at every phase boundary.
    let n = profile.segments().len();
    for i in 0..=n {
        let state = if i == n {
            profile.end()
        } else {
            profile.phase_start(i).expect("phase index within length")
        };
        assert!(state.is_finite(), "{label}: non-finite phase start {i}");
        assert!(
            state.v.abs() <= vmax * (1.0 + 1e-9) + 1e-12,
            "{label}: |v|={} exceeds V={vmax} at phase {i}",
            state.v.abs()
        );
        assert!(
            state.a.abs() <= amax * (1.0 + 1e-9) + 1e-12,
            "{label}: |a|={} exceeds A={amax} at phase {i}",
            state.a.abs()
        );
    }

    // Dense sampling: bounds, monotonicity, no NaN.
    let samples = 2048;
    let mut previous_q = profile.start().q;
    for k in 0..=samples {
        let t = total * (k as f64) / (samples as f64);
        let state = profile.eval(t);
        assert!(
            state.q.is_finite() && state.v.is_finite() && state.a.is_finite(),
            "{label}: non-finite sample at t={t:e}"
        );
        assert!(
            state.v.abs() <= vmax * (1.0 + 1e-9) + 1e-12,
            "{label}: sampled |v|={} exceeds V={vmax} at t={t:e}",
            state.v.abs()
        );
        assert!(
            state.a.abs() <= amax * (1.0 + 1e-9) + 1e-12,
            "{label}: sampled |a|={} exceeds A={amax} at t={t:e}",
            state.a.abs()
        );
        if delta >= 0.0 {
            assert!(
                state.v >= -1e-9 * vmax - 1e-12,
                "{label}: negative velocity {0:e} on a positive move at t={t:e}",
                state.v
            );
            assert!(
                state.q >= previous_q - (1e-9 * scale + 1e-12),
                "{label}: position decreased at t={t:e}"
            );
        } else {
            assert!(
                state.v <= 1e-9 * vmax + 1e-12,
                "{label}: positive velocity {0:e} on a negative move at t={t:e}",
                state.v
            );
            assert!(
                state.q <= previous_q + (1e-9 * scale + 1e-12),
                "{label}: position increased at t={t:e}"
            );
        }
        previous_q = state.q;
    }
}

#[track_caller]
#[allow(clippy::too_many_arguments)]
fn check_case(
    q0: f64,
    q1: f64,
    vmax: f64,
    amax: f64,
    jmax: f64,
    kind: PlanKind,
    durations: [f64; 7],
    v_peak: f64,
    a_peak: f64,
    label: &str,
) -> Profile<f64> {
    let profile = plan_rest_to_rest(q0, q1, limits(vmax, amax, jmax))
        .unwrap_or_else(|error| panic!("{label}: unexpected error {error:?}"));
    assert_eq!(profile.kind(), kind, "{label}: kind");
    assert_durations(&profile, durations, label);
    let expected_total: f64 = durations.iter().sum();
    assert_close(
        profile.total_time(),
        expected_total,
        expected_total,
        &format!("{label}: total time"),
    );
    let (peak_v, peak_a) = boundary_peaks(&profile);
    assert_close(peak_v, v_peak, v_peak, &format!("{label}: peak speed"));
    assert_close(
        peak_a,
        a_peak,
        a_peak,
        &format!("{label}: peak acceleration"),
    );
    check_feasible(&profile, q0, q1, vmax, amax, jmax, label);
    profile
}

// ---------------------------------------------------------------------------
// The §6.2 representative cases. Limits are `V, A, J = 3, 2, 4` unless noted.
// ---------------------------------------------------------------------------

#[test]
fn doc_case_a_cruise_at_v() {
    check_case(
        0.0,
        15.0 / 2.0,
        3.0,
        2.0,
        4.0,
        PlanKind::Cruise,
        [0.5, 1.0, 0.5, 0.5, 0.5, 1.0, 0.5],
        3.0,
        2.0,
        "case A (cruise)",
    );
}

#[test]
fn doc_case_a_b_boundary_zero_cruise() {
    check_case(
        0.0,
        6.0,
        3.0,
        2.0,
        4.0,
        PlanKind::Cruise,
        [0.5, 1.0, 0.5, 0.0, 0.5, 1.0, 0.5],
        3.0,
        2.0,
        "A/B boundary",
    );
}

#[test]
fn doc_case_b_peak_without_cruise() {
    check_case(
        0.0,
        3.0,
        3.0,
        2.0,
        4.0,
        PlanKind::PeakNoCruise,
        [0.5, 0.5, 0.5, 0.0, 0.5, 0.5, 0.5],
        2.0,
        2.0,
        "case B (peak, no cruise)",
    );
}

#[test]
fn doc_case_b_c_boundary_zero_constant_accel() {
    check_case(
        0.0,
        1.0,
        3.0,
        2.0,
        4.0,
        PlanKind::PeakNoCruise,
        [0.5, 0.0, 0.5, 0.0, 0.5, 0.0, 0.5],
        1.0,
        2.0,
        "B/C boundary",
    );
}

#[test]
fn doc_case_c_triangular() {
    check_case(
        0.0,
        1.0 / 8.0,
        3.0,
        2.0,
        4.0,
        PlanKind::Triangular,
        [0.25, 0.0, 0.25, 0.0, 0.25, 0.0, 0.25],
        0.25,
        1.0,
        "case C (triangular)",
    );
}

#[test]
fn doc_case_a_prime_triangular_cruise() {
    // V = 1/4 < v_A = 1: the cruise branch with triangular ramps.
    check_case(
        0.0,
        1.0 / 4.0,
        0.25,
        2.0,
        4.0,
        PlanKind::Cruise,
        [0.25, 0.0, 0.25, 0.5, 0.25, 0.0, 0.25],
        0.25,
        1.0,
        "case A' (triangular cruise)",
    );
}

#[test]
fn doc_threshold_v_equals_va() {
    check_case(
        0.0,
        1.0,
        1.0,
        2.0,
        4.0,
        PlanKind::Cruise,
        [0.5, 0.0, 0.5, 0.0, 0.5, 0.0, 0.5],
        1.0,
        2.0,
        "V = v_A threshold",
    );
}

#[test]
fn doc_case_b_negative_direction_is_mirrored() {
    let profile = check_case(
        0.0,
        -3.0,
        3.0,
        2.0,
        4.0,
        PlanKind::PeakNoCruise,
        [0.5, 0.5, 0.5, 0.0, 0.5, 0.5, 0.5],
        2.0,
        2.0,
        "case B (negative direction)",
    );
    // The mirrored profile is the positive one with its motion signs flipped.
    assert_close(profile.end().q, -3.0, 3.0, "mirrored end position");
    let total = profile.total_time();
    for k in 0..=16 {
        let v = profile.eval(total * k as f64 / 16.0).v;
        assert!(v <= 1e-9, "mirrored velocity {v:e} must not be positive");
    }
}

#[test]
fn zero_displacement_is_empty() {
    let profile = plan_rest_to_rest(1.25, 1.25, limits(3.0, 2.0, 4.0)).unwrap();
    assert_eq!(profile.kind(), PlanKind::ZeroMotion);
    assert!(profile.segments().is_empty());
    assert_eq!(profile.total_time(), 0.0);
    assert_eq!(profile.start().q, 1.25);
    assert_eq!(profile.end(), profile.start());
    assert!(profile.eval(0.0).q == 1.25);
}

// ---------------------------------------------------------------------------
// Properties: random cases, determinism, boundaries.
// ---------------------------------------------------------------------------

/// splitmix64: seeded, so a failure is reproducible without a dependency.
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

#[test]
fn random_cases_are_feasible() {
    let mut seed = 0x5EED_1234_5678_9ABC_u64;
    for case in 0..250 {
        let vmax = spread(&mut seed, 0.05, 8.0);
        let amax = spread(&mut seed, 0.05, 8.0);
        let jmax = spread(&mut seed, 0.05, 8.0);
        let q0 = spread(&mut seed, -50.0, 50.0);
        let q1 = q0 + spread(&mut seed, -20.0, 20.0);
        let label = format!("random case {case}");
        let profile = plan_rest_to_rest(q0, q1, limits(vmax, amax, jmax))
            .unwrap_or_else(|error| panic!("{label}: unexpected error {error:?}"));
        assert!(
            matches!(
                profile.kind(),
                PlanKind::Cruise
                    | PlanKind::PeakNoCruise
                    | PlanKind::Triangular
                    | PlanKind::ZeroMotion
            ),
            "{label}: unexpected kind {:?}",
            profile.kind()
        );
        if q0 == q1 {
            assert_eq!(profile.kind(), PlanKind::ZeroMotion);
            continue;
        }
        check_feasible(&profile, q0, q1, vmax, amax, jmax, &label);
    }
}

#[test]
fn planner_is_deterministic() {
    let cases = [
        (0.0, 7.5, 3.0, 2.0, 4.0),
        (1.0, -2.5, 1.25, 3.0, 5.0),
        (-4.0, 4.0, 0.25, 2.0, 4.0),
        (0.5, 0.5 + 1e-9, 2.0, 2.0, 2.0),
    ];
    for (q0, q1, vmax, amax, jmax) in cases {
        let first = plan_rest_to_rest(q0, q1, limits(vmax, amax, jmax)).unwrap();
        let second = plan_rest_to_rest(q0, q1, limits(vmax, amax, jmax)).unwrap();
        assert_eq!(first, second, "profiles must be bit-identical");
        assert_eq!(
            first.total_time().to_bits(),
            second.total_time().to_bits(),
            "total times must be bit-identical"
        );
        for (a, b) in first.segments().iter().zip(second.segments()) {
            assert_eq!(a.dur.to_bits(), b.dur.to_bits());
            assert_eq!(a.jerk.to_bits(), b.jerk.to_bits());
        }
    }
}

#[test]
fn case_boundaries_do_not_panic() {
    // For A = 2, J = 4, V = 3: D_full(V) = 6 and 2A^3/J^2 = 1.
    let (vmax, amax, jmax) = (3.0, 2.0, 4.0);
    let boundaries = [6.0, 1.0];
    for boundary in boundaries {
        for offset in [-1e-9, -1e-12, 0.0, 1e-12, 1e-9] {
            let target = boundary + offset;
            let label = format!("boundary D={boundary} offset={offset:e}");
            let profile = plan_rest_to_rest(0.0, target, limits(vmax, amax, jmax))
                .unwrap_or_else(|error| panic!("{label}: unexpected error {error:?}"));
            assert!(
                profile
                    .segments()
                    .iter()
                    .all(|s| s.dur >= 0.0 && s.dur.is_finite()),
                "{label}: negative or non-finite duration"
            );
            assert!(
                matches!(
                    profile.kind(),
                    PlanKind::Cruise | PlanKind::PeakNoCruise | PlanKind::Triangular
                ),
                "{label}: unexpected kind {:?}",
                profile.kind()
            );
            check_feasible(&profile, 0.0, target, vmax, amax, jmax, &label);
        }
    }

    // Sweep V across v_A = 1 at fixed D = 1, where the branch flips between the
    // A-reached and triangular cruise formulas.
    for factor in [1.0 - 1e-12, 1.0, 1.0 + 1e-12] {
        let v = 1.0 * factor;
        let profile = plan_rest_to_rest(0.0, 1.0, limits(v, amax, jmax)).unwrap();
        assert!(
            profile
                .segments()
                .iter()
                .all(|s| s.dur >= 0.0 && s.dur.is_finite()),
            "V sweep at factor {factor:e}: negative duration"
        );
        check_feasible(
            &profile,
            0.0,
            1.0,
            v,
            amax,
            jmax,
            &format!("V sweep {factor:e}"),
        );
    }

    // Zero and near-zero displacement.
    for target in [0.0, 1e-300, -1e-300] {
        let profile = plan_rest_to_rest(0.0, target, limits(vmax, amax, jmax)).unwrap();
        assert!(
            profile
                .segments()
                .iter()
                .all(|s| s.dur >= 0.0 && s.dur.is_finite())
        );
        if target == 0.0 {
            assert_eq!(profile.kind(), PlanKind::ZeroMotion);
            assert!(profile.segments().is_empty());
        }
    }
}

#[test]
fn triangular_cruise_never_has_negative_constant_accel_time() {
    // v_A = A^2/J = 1; every V below it takes the triangular cruise branch, whose
    // constant-acceleration slots are structural zeros, never a negative `V/A - t_j`.
    let (amax, jmax) = (2.0, 4.0);
    let v_a = amax * amax / jmax;
    for v in [0.05, 0.1, 0.25, 0.5, 0.9, 0.999_999, v_a * (1.0 - 1e-12)] {
        assert!(v < v_a);
        let target = 2.0_f64.max(4.0 * v);
        let label = format!("triangular cruise V={v:e}");
        let profile = plan_rest_to_rest(0.0, target, limits(v, amax, jmax))
            .unwrap_or_else(|error| panic!("{label}: unexpected error {error:?}"));
        assert_eq!(profile.kind(), PlanKind::Cruise, "{label}: kind");
        assert_eq!(profile.segments()[1].dur, 0.0, "{label}: t_a slot");
        assert_eq!(profile.segments()[5].dur, 0.0, "{label}: t_a slot");
        assert!(
            profile
                .segments()
                .iter()
                .all(|s| s.dur >= 0.0 && s.dur.is_finite()),
            "{label}: negative duration"
        );
        check_feasible(&profile, 0.0, target, v, amax, jmax, &label);
    }
}

#[test]
fn random_boundary_sweeps_are_safe() {
    // Sweep D across both case boundaries for random limits. The reference boundaries
    // are the doc's formulas; the planner's f64 comparison may flip a branch, but the
    // result must stay finite, non-negative and feasible.
    let mut seed = 0x0B0B_5EED_0000_0001_u64;
    for case in 0..100 {
        let a = spread(&mut seed, 0.2, 6.0);
        let j = spread(&mut seed, 0.2, 6.0);
        let v = spread(&mut seed, 0.2, 6.0);
        let t_j = a / j;
        let v_a = a * a / j;
        let d_v = if v <= v_a {
            v * (v / j).sqrt()
        } else {
            v * (t_j + v / a) / 2.0
        };
        let d_full = 2.0 * d_v;
        let d_bc = 2.0 * a * a * a / (j * j);
        for boundary in [d_full, d_bc] {
            for offset in [-1e-12, 0.0, 1e-12] {
                let target = boundary * (1.0 + offset);
                if !(target.is_finite() && target > 0.0) {
                    continue;
                }
                let label = format!("case {case} boundary={boundary:e} offset={offset:e}");
                let profile = plan_rest_to_rest(0.0, target, limits(v, a, j))
                    .unwrap_or_else(|error| panic!("{label}: unexpected error {error:?}"));
                assert!(
                    profile
                        .segments()
                        .iter()
                        .all(|s| s.dur >= 0.0 && s.dur.is_finite()),
                    "{label}: negative or non-finite duration"
                );
                check_feasible(&profile, 0.0, target, v, a, j, &label);
            }
        }
    }
}

#[test]
fn non_finite_inputs_are_rejected() {
    let lim = limits(3.0, 2.0, 4.0);
    assert_eq!(
        plan_rest_to_rest(f64::NAN, 0.0, lim),
        Err(PlanError::NonFiniteInput)
    );
    assert_eq!(
        plan_rest_to_rest(0.0, f64::INFINITY, lim),
        Err(PlanError::NonFiniteInput)
    );
    assert_eq!(
        plan_rest_to_rest(0.0, f64::NEG_INFINITY, lim),
        Err(PlanError::NonFiniteInput)
    );
    // Both endpoints finite, but their difference overflows.
    assert_eq!(
        plan_rest_to_rest(f64::MAX, -f64::MAX, lim),
        Err(PlanError::NumericalFailure)
    );
}
