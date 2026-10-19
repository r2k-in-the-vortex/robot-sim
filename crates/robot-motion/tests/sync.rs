//! M3: synchronization and the scalar MoveJ.

use robot_motion::Limits;
use robot_motion::conservative::plan_rest_conservative;
use robot_motion::sync::{plan_movej_scalar, plan_movej_scalar_optimal, synchronize};

fn lim(v: f64, a: f64, j: f64) -> Limits<f64> {
    Limits::new(v, a, j).unwrap()
}

fn sample_joint(profile: &robot_motion::Profile<f64>, points: usize, limits: Limits<f64>) {
    let t_total = profile.total_time();
    for k in 0..=points {
        let t = t_total * (k as f64) / (points as f64);
        let s = profile.eval(t);
        assert!(s.is_finite());
        assert!(s.v.abs() <= limits.vmax() * (1.0 + 1e-12) + 1e-12);
        assert!(s.a.abs() <= limits.amax() * (1.0 + 1e-12) + 1e-12);
    }
    for seg in profile.segments() {
        assert!(seg.jerk.abs() <= limits.jmax() * (1.0 + 1e-12) + 1e-12);
    }
}

#[test]
fn synchronized_profiles_share_a_duration() {
    let l = lim(3.0, 2.0, 4.0);
    let a = plan_rest_conservative(0.0, 1.0, l).unwrap();
    let b = plan_rest_conservative(0.0, 4.0, l).unwrap();
    let c = plan_rest_conservative(0.0, 0.0, l).unwrap();
    let joint = synchronize([a, b, c]).unwrap();
    let t = joint.total_time();
    assert!(t > 0.0);
    for profile in joint.joints() {
        assert!((profile.total_time() - t).abs() < 1e-12);
        assert_eq!(profile.start().v, 0.0);
        assert_eq!(profile.start().a, 0.0);
    }
    // The stationary joint is a constant hold for the common duration.
    let stationary = joint.joints()[2];
    for k in 0..=64 {
        let time = t * (k as f64) / 64.0;
        assert!((stationary.eval(time).q - 0.0).abs() < 1e-12);
    }
    sample_joint(&joint.joints()[0], 200, l);
    sample_joint(&joint.joints()[1], 200, l);
}

#[test]
fn all_stationary_synchronization_has_zero_duration() {
    let l = lim(1.0, 1.0, 1.0);
    let z = || plan_rest_conservative(0.0, 0.0, l).unwrap();
    let joint = synchronize([z(), z()]).unwrap();
    assert_eq!(joint.total_time(), 0.0);
    for profile in joint.joints() {
        assert_eq!(profile.total_time(), 0.0);
    }
}

#[test]
fn movej_scalar_is_a_joint_space_line() {
    let l = lim(3.0, 2.0, 4.0);
    let start = [0.0, 1.0, -2.0];
    let target = [1.0, 3.0, -1.0];
    let joint = plan_movej_scalar(start, target, [l, l, l]).unwrap();
    let t = joint.total_time();
    assert!(t > 0.0);
    for k in 0..=200 {
        let time = t * (k as f64) / 200.0;
        let states = joint.eval(time);
        let delta0 = states[0].q - start[0];
        let delta1 = states[1].q - start[1];
        let delta2 = states[2].q - start[2];
        let total0 = target[0] - start[0];
        let total1 = target[1] - start[1];
        let total2 = target[2] - start[2];
        assert!((delta1 * total0 - delta0 * total1).abs() < 1e-9);
        assert!((delta2 * total0 - delta0 * total2).abs() < 1e-9);
    }
    for (i, profile) in joint.joints().iter().enumerate() {
        assert!((profile.end().q - target[i]).abs() < 1e-12);
        sample_joint(profile, 200, l);
    }
}

#[test]
fn movej_scalar_holds_a_stationary_joint() {
    let l = lim(3.0, 2.0, 4.0);
    let start = [0.0, 1.0];
    let target = [2.0, 1.0];
    let joint = plan_movej_scalar(start, target, [l, l]).unwrap();
    let t = joint.total_time();
    assert!(t > 0.0);
    for k in 0..=64 {
        let time = t * (k as f64) / 64.0;
        assert!((joint.eval(time)[1].q - 1.0).abs() < 1e-12);
    }
    assert!((joint.joints()[1].total_time() - t).abs() < 1e-12);
}

#[test]
fn movej_scalar_all_stationary_is_empty() {
    let l = lim(1.0, 1.0, 1.0);
    let joint = plan_movej_scalar([1.0, 2.0], [1.0, 2.0], [l, l]).unwrap();
    assert_eq!(joint.total_time(), 0.0);
    let s = joint.eval(0.0);
    assert_eq!(s[0].q, 1.0);
    assert_eq!(s[1].q, 2.0);
}

#[test]
fn synchronization_is_deterministic() {
    let l = lim(3.0, 2.0, 4.0);
    let a = plan_rest_conservative(0.0, 1.0, l).unwrap();
    let b = plan_rest_conservative(0.0, 2.0, l).unwrap();
    let x = synchronize([a, b]).unwrap();
    let y = synchronize([a, b]).unwrap();
    assert_eq!(x, y);
}

/// The same check as [`sample_joint`], with the tolerance the optimal planner's
/// square/cube roots need at a limit boundary.
fn sample_joint_optimal(profile: &robot_motion::Profile<f64>, points: usize, limits: Limits<f64>) {
    const TOLERANCE: f64 = 1e-9;
    let t_total = profile.total_time();
    for k in 0..=points {
        let t = t_total * (k as f64) / (points as f64);
        let s = profile.eval(t);
        assert!(s.is_finite());
        assert!(s.v.abs() <= limits.vmax() * (1.0 + TOLERANCE) + TOLERANCE);
        assert!(s.a.abs() <= limits.amax() * (1.0 + TOLERANCE) + TOLERANCE);
    }
    for seg in profile.segments() {
        assert!(seg.jerk.abs() <= limits.jmax() * (1.0 + TOLERANCE) + TOLERANCE);
    }
}

#[test]
fn optimal_movej_is_a_joint_space_line() {
    let l = lim(3.0, 2.0, 4.0);
    let start = [0.0, 1.0, -2.0];
    let target = [1.0, 3.0, -1.0];
    let joint = plan_movej_scalar_optimal(start, target, [l, l, l]).unwrap();
    let t = joint.total_time();
    assert!(t > 0.0);
    for k in 0..=200 {
        let time = t * (k as f64) / 200.0;
        let states = joint.eval(time);
        let delta0 = states[0].q - start[0];
        let delta1 = states[1].q - start[1];
        let delta2 = states[2].q - start[2];
        let total0 = target[0] - start[0];
        let total1 = target[1] - start[1];
        let total2 = target[2] - start[2];
        assert!((delta1 * total0 - delta0 * total1).abs() < 1e-9);
        assert!((delta2 * total0 - delta0 * total2).abs() < 1e-9);
    }
    for (i, profile) in joint.joints().iter().enumerate() {
        assert!((profile.end().q - target[i]).abs() < 1e-9);
        sample_joint_optimal(profile, 200, l);
    }
}

#[test]
fn optimal_movej_uses_each_joints_own_limits() {
    // The middle joint is the slow one; the others have room to move faster but still
    // finish when it does.
    let limits = [lim(3.0, 2.0, 4.0), lim(1.0, 0.5, 1.0), lim(6.0, 4.0, 8.0)];
    let start = [0.0, 0.0, 0.0];
    let target = [2.0, 1.0, 4.0];
    let joint = plan_movej_scalar_optimal(start, target, limits).unwrap();
    assert!(joint.total_time() > 0.0);
    for (i, profile) in joint.joints().iter().enumerate() {
        assert!((profile.end().q - target[i]).abs() < 1e-9);
        sample_joint_optimal(profile, 400, limits[i]);
    }
}

#[test]
fn optimal_movej_holds_a_stationary_joint() {
    let l = lim(3.0, 2.0, 4.0);
    let joint = plan_movej_scalar_optimal([0.0, 1.0], [2.0, 1.0], [l, l]).unwrap();
    let t = joint.total_time();
    assert!(t > 0.0);
    for k in 0..=64 {
        let time = t * (k as f64) / 64.0;
        assert!((joint.eval(time)[1].q - 1.0).abs() < 1e-12);
    }
    assert!((joint.joints()[1].total_time() - t).abs() < 1e-12);
}

#[test]
fn optimal_movej_all_stationary_is_empty() {
    let l = lim(1.0, 1.0, 1.0);
    let joint = plan_movej_scalar_optimal([1.0, 2.0], [1.0, 2.0], [l, l]).unwrap();
    assert_eq!(joint.total_time(), 0.0);
    let s = joint.eval(0.0);
    assert_eq!(s[0].q, 1.0);
    assert_eq!(s[1].q, 2.0);
}

#[test]
fn optimal_movej_is_much_faster_than_the_conservative_one_for_a_small_move() {
    // The conservative template's duration has a floor of four times `min(1, A/J, V/J)`,
    // which this move is far below; the optimal planner's triangular case shrinks with it.
    let l = lim(3.0, 2.0, 4.0);
    let conservative = plan_movej_scalar([0.0], [0.01], [l]).unwrap();
    let optimal = plan_movej_scalar_optimal([0.0], [0.01], [l]).unwrap();
    assert!(
        optimal.total_time() < conservative.total_time() / 4.0,
        "optimal {} vs conservative {}",
        optimal.total_time(),
        conservative.total_time()
    );
}
