//! The fixed-cycle M4 harness.
//!
//! `run` stops at the first re-plan, stall, abort or completion and returns the plant and
//! supervisor state intact. It does not replace the profile; the caller builds the
//! replacement, calls [`crate::supervisor::Supervisor::reset`] and resumes. If the
//! replacement is infeasible, the caller holds position and reports `Abort`.

use crate::error::PlanError;
use crate::plant::JointPlant;
use crate::profile::{JointProfile, State};
use crate::supervisor::{Decision, Supervisor, SupervisorStep};
use crate::tracker::{Command, Tracker};

/// Loop limits.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CycleConfig {
    pub cycle: f64,
    pub max_cycles: u32,
}

impl CycleConfig {
    pub fn new(cycle: f64, max_cycles: u32) -> Result<Self, PlanError> {
        if !cycle.is_finite() || cycle <= 0.0 || max_cycles == 0 {
            return Err(PlanError::NumericalFailure);
        }
        Ok(Self { cycle, max_cycles })
    }
}

/// Why the run stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CycleOutcome {
    Tracking,
    Complete,
    StallDetected,
    ReplanRequested,
    Aborted,
    CycleLimit,
}

/// One cycle's full record.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CycleStep<const N: usize> {
    pub outcome: CycleOutcome,
    pub reference: [State<f64>; N],
    pub measured: [State<f64>; N],
    pub commands: [Command; N],
    pub supervisor: SupervisorStep,
}

/// The run summary.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RunReport<const N: usize> {
    pub cycles: u32,
    pub outcome: CycleOutcome,
    pub stall_cycle: Option<u32>,
    pub replan_cycle: Option<u32>,
    pub max_abs_position_error: f64,
    pub position_min: f64,
    pub position_max: f64,
    pub max_abs_velocity: f64,
    pub last: CycleStep<N>,
}

/// Advance one cycle.
pub fn step<const N: usize>(
    profile: &JointProfile<N, f64>,
    plants: &mut [JointPlant; N],
    tracker: &Tracker,
    supervisor: &mut Supervisor<N>,
    cycle: f64,
) -> CycleStep<N> {
    let reference: [State<f64>; N] =
        profile.eval_scaled(supervisor.reference_time(), supervisor.rate(), 0.0);
    let measured: [State<f64>; N] = core::array::from_fn(|i| plants[i].state());
    let commands: [Command; N] =
        core::array::from_fn(|i| tracker.command(reference[i], measured[i]));
    let errors: [f64; N] = core::array::from_fn(|i| reference[i].q - measured[i].q);
    let velocities: [f64; N] = core::array::from_fn(|i| measured[i].v);
    let supervisor_step = supervisor.step(&errors, &velocities, &commands, profile.total_time());

    for i in 0..N {
        let _ = plants[i].step(commands[i].accel, cycle);
    }

    let outcome = match supervisor_step.decision {
        Decision::Complete => CycleOutcome::Complete,
        Decision::Replan => CycleOutcome::ReplanRequested,
        Decision::Stall => CycleOutcome::StallDetected,
        Decision::Abort => CycleOutcome::Aborted,
        Decision::Tracking | Decision::Slowing | Decision::Holding => CycleOutcome::Tracking,
    };

    CycleStep {
        outcome,
        reference,
        measured,
        commands,
        supervisor: supervisor_step,
    }
}

/// Run until the supervisor asks to stop, or the cycle limit is reached.
pub fn run<const N: usize>(
    profile: &JointProfile<N, f64>,
    plants: &mut [JointPlant; N],
    tracker: &Tracker,
    supervisor: &mut Supervisor<N>,
    config: CycleConfig,
) -> RunReport<N> {
    let mut cycles = 0u32;
    let mut outcome = CycleOutcome::CycleLimit;
    let mut stall_cycle = None;
    let mut replan_cycle = None;
    let mut max_abs_position_error = 0.0f64;
    let mut position_min = f64::INFINITY;
    let mut position_max = f64::NEG_INFINITY;
    let mut max_abs_velocity = 0.0f64;
    let mut last = CycleStep {
        outcome,
        reference: core::array::from_fn(|_| State::new(0.0, 0.0, 0.0)),
        measured: core::array::from_fn(|_| State::new(0.0, 0.0, 0.0)),
        commands: core::array::from_fn(|_| Command {
            accel: 0.0,
            saturated: false,
        }),
        supervisor: SupervisorStep {
            decision: Decision::Tracking,
            rate: 1.0,
            reference_time: 0.0,
        },
    };

    while cycles < config.max_cycles {
        let cycle_step = step(profile, plants, tracker, supervisor, config.cycle);
        cycles += 1;
        for i in 0..N {
            let error = (cycle_step.reference[i].q - cycle_step.measured[i].q).abs();
            if error > max_abs_position_error {
                max_abs_position_error = error;
            }
            let q = cycle_step.measured[i].q;
            if q < position_min {
                position_min = q;
            }
            if q > position_max {
                position_max = q;
            }
            let v = cycle_step.measured[i].v.abs();
            if v > max_abs_velocity {
                max_abs_velocity = v;
            }
        }
        last = cycle_step;
        match cycle_step.outcome {
            CycleOutcome::Tracking => {}
            CycleOutcome::Complete => {
                outcome = CycleOutcome::Complete;
                break;
            }
            CycleOutcome::StallDetected => {
                outcome = CycleOutcome::StallDetected;
                stall_cycle = Some(cycles);
                break;
            }
            CycleOutcome::ReplanRequested => {
                outcome = CycleOutcome::ReplanRequested;
                replan_cycle = Some(cycles);
                break;
            }
            CycleOutcome::Aborted => {
                outcome = CycleOutcome::Aborted;
                break;
            }
            CycleOutcome::CycleLimit => {}
        }
    }

    RunReport {
        cycles,
        outcome,
        stall_cycle,
        replan_cycle,
        max_abs_position_error,
        position_min,
        position_max,
        max_abs_velocity,
        last,
    }
}
