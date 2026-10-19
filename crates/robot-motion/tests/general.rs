//! M2: stop–move–start general-boundary planner.

use robot_motion::general::{
    plan_general, rev, start_profile, stop_feasible, stop_profile, viable,
};
use robot_motion::{Limits, State};

fn lim(v: f64, a: f64, j: f64) -> Limits<f64> {
    Limits::new(v, a, j).unwrap()
}

fn sample_profile(profile: &robot_motion::Profile<f64>, points: usize, limits: Limits<f64>) {
    let t_total = profile.total_time();
    assert!(t_total.is_finite() && t_total >= 0.0);
    for k in 0..=points {
        let t = t_total * (k as f64) / (points as f64);
        let s = profile.eval(t);
        assert!(s.is_finite(), "state at t={t} is not finite: {s:?}");
        assert!(
            s.v.abs() <= limits.vmax() * (1.0 + 1e-12) + 1e-12,
            "velocity {} exceeds {} at t={t}",
            s.v,
            limits.vmax()
        );
        assert!(
            s.a.abs() <= limits.amax() * (1.0 + 1e-12) + 1e-12,
            "acceleration {} exceeds {} at t={t}",
            s.a,
            limits.amax()
        );
    }
    for seg in profile.segments() {
        assert!(
            seg.jerk.abs() <= limits.jmax() * (1.0 + 1e-12) + 1e-12,
            "jerk {} exceeds {}",
            seg.jerk,
            limits.jmax()
        );
    }
}

#[test]
fn stop_feasibility_is_the_ramp_condition() {
    let l = lim(1.0, 10.0, 1.0);
    // v_s = 1 + (-10 * 10) / 2 = -49, outside the band.
    assert!(!stop_feasible(State::new(0.0, 1.0, -10.0), l));
    // At rest with a small acceleration the ramp stays in the band.
    assert!(stop_feasible(State::new(0.0, 0.5, -1.0), l));
    // The box alone is not enough: v = V, a = A pushes v_s past V.
    let l2 = lim(2.0, 2.0, 4.0);
    assert!(stop_feasible(State::new(0.0, 1.0, 1.0), l2));
    assert!(!stop_feasible(State::new(0.0, 2.0, 2.0), l2));
}

#[test]
fn stop_profile_ends_at_rest() {
    let l = lim(3.0, 2.0, 4.0);
    for state in [
        State::new(0.0, 1.0, 1.0),
        State::new(0.0, -1.0, 1.0),
        State::new(0.0, 2.0, -1.0),
        State::new(0.0, 0.0, 0.0),
    ] {
        if !stop_feasible(state, l) {
            continue;
        }
        let p = stop_profile(state, l).unwrap();
        assert_eq!(p.start(), state);
        assert!(p.end().v.abs() < 1e-12);
        assert!(p.end().a.abs() < 1e-12);
        sample_profile(&p, 200, l);
    }
}

#[test]
fn start_profile_ends_at_the_target() {
    let l = lim(3.0, 2.0, 4.0);
    let target = State::new(1.25, 1.0, 0.5);
    let p = start_profile(target, l).unwrap();
    assert!(p.start().v.abs() < 1e-12);
    assert!(p.start().a.abs() < 1e-12);
    let end = p.end();
    assert!((end.q - target.q).abs() < 1e-12);
    assert!((end.v - target.v).abs() < 1e-12);
    assert!((end.a - target.a).abs() < 1e-12);
    sample_profile(&p, 200, l);
}

#[test]
fn general_planner_boundary_and_feasibility() {
    let l = lim(3.0, 2.0, 4.0);
    let cases = [
        (State::new(0.0, 1.0, 1.0), State::new(1.0, 0.0, 0.0)),
        (State::new(0.0, 0.0, 0.0), State::new(2.0, -1.0, 0.5)),
        (State::new(1.0, -1.0, -1.0), State::new(0.0, 1.0, 1.0)),
        (State::new(0.0, 0.5, 0.0), State::new(0.0, 0.5, 0.0)),
        (State::new(0.0, 0.0, 0.0), State::new(0.0, 0.0, 0.0)),
    ];
    for (s0, s1) in cases {
        if !viable(s0, s1, l) {
            continue;
        }
        let p = plan_general(s0, s1, l).unwrap();
        assert_eq!(p.start(), s0);
        let end = p.end();
        assert!((end.q - s1.q).abs() < 1e-12, "q end {:?}", end);
        assert!((end.v - s1.v).abs() < 1e-12, "v end {:?}", end);
        assert!((end.a - s1.a).abs() < 1e-12, "a end {:?}", end);
        assert!(p.segments().len() <= 15);
        sample_profile(&p, 500, l);
    }
}

#[test]
fn nonviable_states_are_rejected() {
    let l = lim(1.0, 10.0, 1.0);
    // The counterexample from the analysis: a direct profile exists, but the
    // stop-move-start decomposition cannot stop without leaving the band.
    let s0 = State::new(0.0, 1.0, -10.0);
    let s1 = State::new(0.05, 0.0, -10.0);
    assert!(!viable(s0, s1, l));
    assert_eq!(
        plan_general(s0, s1, l).unwrap_err(),
        robot_motion::PlanError::Infeasible
    );
    assert_eq!(
        stop_profile(s0, l).unwrap_err(),
        robot_motion::PlanError::Infeasible
    );
}

#[test]
fn rev_preserves_position_and_acceleration() {
    let s = State::new(2.0, -0.5, 0.25);
    assert_eq!(rev(s), State::new(2.0, 0.5, 0.25));
}

#[test]
fn general_planner_is_deterministic() {
    let l = lim(3.0, 2.0, 4.0);
    let s0 = State::new(0.0, 1.0, 1.0);
    let s1 = State::new(1.0, 0.0, 0.0);
    let a = plan_general(s0, s1, l).unwrap();
    let b = plan_general(s0, s1, l).unwrap();
    assert_eq!(a, b);
}
