//! M4: tracker, supervisor and the headless plant harness.

use robot_motion::conservative::plan_rest_conservative;
use robot_motion::harness::{CycleConfig, CycleOutcome, run};
use robot_motion::plant::{JointPlant, PlantConfig};
use robot_motion::supervisor::{Decision, Supervisor, SupervisorConfig};
use robot_motion::tracker::{Command, Tracker, TrackingGains};
use robot_motion::{Limits, State};

fn limits() -> Limits<f64> {
    Limits::new(1.0, 2.0, 4.0).unwrap()
}

fn config() -> SupervisorConfig {
    SupervisorConfig {
        eps_1: 1e-3,
        eps_2: 1e-2,
        eps_abort: 0.5,
        abort_cycles: 10_000,
        stall_cycles: 10_000,
        stall_velocity: 1e-3,
        cycle: 1e-3,
    }
}

fn command(saturated: bool) -> Command {
    Command {
        accel: if saturated { 50.0 } else { 0.0 },
        saturated,
    }
}

#[test]
fn supervisor_slows_then_completes() {
    let mut s = Supervisor::<1>::new(config());
    let slow = s.step(&[0.005], &[0.0], &[command(false)], 1.0);
    assert_eq!(slow.decision, Decision::Slowing);
    assert!(slow.rate > 0.0 && slow.rate < 1.0);
    let mut step = slow;
    for _ in 0..2000 {
        step = s.step(&[0.0], &[0.0], &[command(false)], 1.0);
        if step.decision == Decision::Complete {
            break;
        }
    }
    assert_eq!(step.decision, Decision::Complete);
}

#[test]
fn supervisor_detects_a_stall() {
    let mut cfg = config();
    cfg.stall_cycles = 3;
    let mut s = Supervisor::<1>::new(cfg);
    let mut step = s.step(&[0.0], &[0.0], &[command(false)], 10.0);
    for k in 1..=3 {
        step = s.step(&[k as f64], &[0.0], &[command(true)], 10.0);
    }
    assert_eq!(step.decision, Decision::Stall);
}

#[test]
fn supervisor_requests_a_replan_on_persistent_error() {
    let mut cfg = config();
    cfg.abort_cycles = 2;
    cfg.stall_cycles = 10_000;
    cfg.eps_abort = 0.1;
    let mut s = Supervisor::<1>::new(cfg);
    let _ = s.step(&[1.0], &[0.0], &[command(false)], 10.0);
    let step = s.step(&[1.0], &[0.0], &[command(false)], 10.0);
    assert_eq!(step.decision, Decision::Replan);
}

#[test]
fn supervisor_aborts_on_non_finite_input() {
    let mut s = Supervisor::<1>::new(config());
    let step = s.step(&[f64::NAN], &[0.0], &[command(false)], 1.0);
    assert_eq!(step.decision, Decision::Abort);
}

#[test]
fn tracker_clamps_and_flags_saturation() {
    let t = Tracker::new(TrackingGains {
        kp: 100.0,
        kd: 10.0,
        max_accel: 5.0,
    });
    let c = t.command(State::new(1.0, 0.0, 0.0), State::new(0.0, 0.0, 0.0));
    assert!(c.saturated);
    assert_eq!(c.accel, 5.0);
    let c = t.command(State::new(0.0, 0.0, 0.0), State::new(0.0, 0.0, 0.0));
    assert!(!c.saturated);
    assert_eq!(c.accel, 0.0);
}

#[test]
fn the_plant_tracks_a_feasible_profile() {
    let profile = plan_rest_conservative(0.0, 1.0, limits()).unwrap();
    let mut plants = [JointPlant::new(PlantConfig {
        start: State::new(0.0, 0.0, 0.0),
        position_clamp: None,
    })
    .unwrap()];
    let tracker = Tracker::new(TrackingGains {
        kp: 200.0,
        kd: 40.0,
        max_accel: 50.0,
    });
    let mut supervisor = Supervisor::<1>::new(config());
    let report = run(
        &robot_motion::JointProfile::new([profile], profile.total_time()),
        &mut plants,
        &tracker,
        &mut supervisor,
        CycleConfig::new(1e-3, 20_000).unwrap(),
    );
    assert_eq!(report.outcome, CycleOutcome::Complete);
    assert!(report.last.measured[0].q.is_finite());
    assert!((report.last.measured[0].q - 1.0).abs() < 1e-2);
    assert!(report.max_abs_position_error.is_finite());
}

#[test]
fn a_position_clamp_raises_stall_detection() {
    let profile = plan_rest_conservative(0.0, 1.0, limits()).unwrap();
    let mut plants = [JointPlant::new(PlantConfig {
        start: State::new(0.0, 0.0, 0.0),
        position_clamp: Some((0.0, 0.2)),
    })
    .unwrap()];
    let tracker = Tracker::new(TrackingGains {
        kp: 200.0,
        kd: 40.0,
        max_accel: 0.1,
    });
    let mut cfg = config();
    cfg.stall_cycles = 5;
    cfg.abort_cycles = 100_000;
    let mut supervisor = Supervisor::<1>::new(cfg);
    let report = run(
        &robot_motion::JointProfile::new([profile], profile.total_time()),
        &mut plants,
        &tracker,
        &mut supervisor,
        CycleConfig::new(1e-3, 50_000).unwrap(),
    );
    assert_eq!(report.outcome, CycleOutcome::StallDetected);
    assert!(report.stall_cycle.is_some());
    assert!((plants[0].state().q - 0.2).abs() < 1e-9);
}

#[test]
fn the_harness_stops_at_the_first_replan() {
    let profile = plan_rest_conservative(0.0, 1.0, limits()).unwrap();
    let mut plants = [JointPlant::new(PlantConfig {
        start: State::new(0.0, 0.0, 0.0),
        position_clamp: Some((0.0, 0.0)),
    })
    .unwrap()];
    let tracker = Tracker::new(TrackingGains {
        kp: 200.0,
        kd: 40.0,
        max_accel: 50.0,
    });
    let mut cfg = config();
    cfg.abort_cycles = 5;
    cfg.stall_cycles = 100_000;
    cfg.eps_abort = 0.005;
    let mut supervisor = Supervisor::<1>::new(cfg);
    let report = run(
        &robot_motion::JointProfile::new([profile], profile.total_time()),
        &mut plants,
        &tracker,
        &mut supervisor,
        CycleConfig::new(1e-3, 50_000).unwrap(),
    );
    assert_eq!(report.outcome, CycleOutcome::ReplanRequested);
    assert!(report.replan_cycle.is_some());
    assert!(supervisor.reference_time().is_finite());
}

#[test]
fn the_harness_is_deterministic() {
    let make = || {
        let profile = plan_rest_conservative(0.0, 0.5, limits()).unwrap();
        let mut plants = [JointPlant::new(PlantConfig {
            start: State::new(0.0, 0.0, 0.0),
            position_clamp: None,
        })
        .unwrap()];
        let tracker = Tracker::new(TrackingGains {
            kp: 100.0,
            kd: 20.0,
            max_accel: 20.0,
        });
        let mut supervisor = Supervisor::<1>::new(config());
        run(
            &robot_motion::JointProfile::new([profile], profile.total_time()),
            &mut plants,
            &tracker,
            &mut supervisor,
            CycleConfig::new(1e-3, 10_000).unwrap(),
        )
    };
    assert_eq!(make(), make());
}

#[test]
fn a_zero_cycle_is_rejected() {
    assert!(CycleConfig::new(0.0, 10).is_err());
    assert!(CycleConfig::new(-1.0, 10).is_err());
    assert!(CycleConfig::new(1.0, 0).is_err());
}
