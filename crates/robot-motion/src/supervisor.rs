//! Time scaling, re-plan and stall detection.
//!
//! The rate is held constant within a cycle and changed only at cycle boundaries. Between
//! changes the reference is an affine reparameterisation, so `stretch_feasible` applies;
//! the concatenated reference is not claimed to be `C²`.

use crate::tracker::Command;

/// Thresholds and streak lengths.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SupervisorConfig {
    /// No slowdown below this absolute error.
    pub eps_1: f64,
    /// Full stop at or above this absolute error.
    pub eps_2: f64,
    /// Persistent-error threshold that requests a re-plan.
    pub eps_abort: f64,
    pub abort_cycles: u32,
    pub stall_cycles: u32,
    pub stall_velocity: f64,
    pub cycle: f64,
}

/// The supervisor's verdict for one cycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    Tracking,
    Slowing,
    Holding,
    Replan,
    Stall,
    Complete,
    Abort,
}

/// The decision plus the rate and reference time after the step.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SupervisorStep {
    pub decision: Decision,
    pub rate: f64,
    pub reference_time: f64,
}

/// Per-joint streak state, fixed capacity.
#[derive(Clone, Copy, Debug)]
pub struct Supervisor<const N: usize> {
    config: SupervisorConfig,
    rate: f64,
    reference_time: f64,
    abort_streak: [u32; N],
    stall_streak: [u32; N],
    last_abs_error: [f64; N],
}

impl<const N: usize> Supervisor<N> {
    pub fn new(config: SupervisorConfig) -> Self {
        Self {
            config,
            rate: 1.0,
            reference_time: 0.0,
            abort_streak: [0; N],
            stall_streak: [0; N],
            last_abs_error: [0.0; N],
        }
    }

    pub fn config(&self) -> SupervisorConfig {
        self.config
    }

    pub fn rate(&self) -> f64 {
        self.rate
    }

    pub fn reference_time(&self) -> f64 {
        self.reference_time
    }

    /// Restart the clock and clear the streaks after a re-plan.
    pub fn reset(&mut self, reference_time: f64) {
        self.reference_time = reference_time;
        self.rate = 1.0;
        self.abort_streak = [0; N];
        self.stall_streak = [0; N];
        self.last_abs_error = [0.0; N];
    }

    pub fn step(
        &mut self,
        errors: &[f64; N],
        velocities: &[f64; N],
        commands: &[Command; N],
        total_time: f64,
    ) -> SupervisorStep {
        // Non-finite input is not a motion decision; fail closed.
        for ((error, velocity), cmd) in errors.iter().zip(velocities.iter()).zip(commands.iter()) {
            if !error.is_finite() || !velocity.is_finite() || !cmd.accel.is_finite() {
                return SupervisorStep {
                    decision: Decision::Abort,
                    rate: self.rate,
                    reference_time: self.reference_time,
                };
            }
        }
        if !self.config.cycle.is_finite() || self.config.cycle <= 0.0 {
            return SupervisorStep {
                decision: Decision::Abort,
                rate: self.rate,
                reference_time: self.reference_time,
            };
        }

        // Slowdown is the minimum per-joint rate (the largest error under a monotone law).
        let mut rate = 1.0_f64;
        for &error in errors.iter() {
            let e = error.abs();
            let r = if e <= self.config.eps_1 {
                1.0
            } else if e < self.config.eps_2 && self.config.eps_2 > self.config.eps_1 {
                1.0 - (e - self.config.eps_1) / (self.config.eps_2 - self.config.eps_1)
            } else {
                0.0
            };
            if r < rate {
                rate = r;
            }
        }
        self.rate = rate;
        self.reference_time += rate * self.config.cycle;
        if self.reference_time > total_time {
            self.reference_time = total_time;
        }
        if self.reference_time < 0.0 {
            self.reference_time = 0.0;
        }

        let mut stall = false;
        let mut replan = false;
        let mut all_small = true;
        for i in 0..N {
            let e = errors[i].abs();
            if e > self.config.eps_1 {
                all_small = false;
            }
            if e > self.config.eps_abort {
                self.abort_streak[i] = self.abort_streak[i].saturating_add(1);
            } else {
                self.abort_streak[i] = 0;
            }
            if commands[i].saturated
                && velocities[i].abs() <= self.config.stall_velocity
                && e >= self.last_abs_error[i]
            {
                self.stall_streak[i] = self.stall_streak[i].saturating_add(1);
            } else {
                self.stall_streak[i] = 0;
            }
            self.last_abs_error[i] = e;
            if self.stall_streak[i] >= self.config.stall_cycles.max(1) {
                stall = true;
            }
            if self.abort_streak[i] >= self.config.abort_cycles.max(1) {
                replan = true;
            }
        }

        let decision = if stall {
            Decision::Stall
        } else if replan {
            Decision::Replan
        } else if self.reference_time >= total_time && all_small {
            Decision::Complete
        } else if self.rate == 0.0 {
            Decision::Holding
        } else if self.rate < 1.0 {
            Decision::Slowing
        } else {
            Decision::Tracking
        };

        SupervisorStep {
            decision,
            rate: self.rate,
            reference_time: self.reference_time,
        }
    }
}
