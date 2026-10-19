//! A minimal simulated joint plant for the M4 harness.
//!
//! Semi-implicit Euler with an optional position clamp. A clamp sets the velocity to zero
//! and reports `clamped`; that is the obstacle model the stall test uses.

use crate::error::PlanError;
use crate::profile::State;

/// Plant construction parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PlantConfig {
    pub start: State<f64>,
    /// Inclusive position limits; hitting one clamps the joint.
    pub position_clamp: Option<(f64, f64)>,
}

/// One plant step's result.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PlantStep {
    pub state: State<f64>,
    pub clamped: bool,
}

/// A single simulated joint.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct JointPlant {
    state: State<f64>,
    position_clamp: Option<(f64, f64)>,
}

impl JointPlant {
    pub fn new(config: PlantConfig) -> Result<Self, PlanError> {
        if !config.start.is_finite() {
            return Err(PlanError::NonFiniteInput);
        }
        if let Some((lo, hi)) = config.position_clamp {
            if !lo.is_finite() || !hi.is_finite() || lo > hi {
                return Err(PlanError::NumericalFailure);
            }
        }
        Ok(Self {
            state: config.start,
            position_clamp: config.position_clamp,
        })
    }

    pub fn state(&self) -> State<f64> {
        self.state
    }

    pub fn step(&mut self, commanded_accel: f64, cycle: f64) -> PlantStep {
        if !commanded_accel.is_finite() || !cycle.is_finite() || cycle <= 0.0 {
            return PlantStep {
                state: self.state,
                clamped: true,
            };
        }
        let v = self.state.v + commanded_accel * cycle;
        let mut q = self.state.q + v * cycle;
        let mut clamped = false;
        if let Some((lo, hi)) = self.position_clamp {
            if q < lo {
                q = lo;
                clamped = true;
            } else if q > hi {
                q = hi;
                clamped = true;
            }
        }
        let velocity = if clamped { 0.0 } else { v };
        self.state = State {
            q,
            v: velocity,
            a: commanded_accel,
        };
        PlantStep {
            state: self.state,
            clamped,
        }
    }
}
