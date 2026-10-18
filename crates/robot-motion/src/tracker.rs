//! A plant-agnostic per-joint tracker.
//!
//! The output is an acceleration command (the plant decides what that means) plus a
//! saturation flag. The supervisor uses the flag for stall detection.

use crate::profile::State;

/// Feedback gains and the acceleration clamp.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TrackingGains {
    pub kp: f64,
    pub kd: f64,
    pub max_accel: f64,
}

/// One cycle's command.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Command {
    pub accel: f64,
    pub saturated: bool,
}

/// `a_cmd = a_ref + kp e + kd e_dot`, manually clamped.
#[derive(Clone, Copy, Debug)]
pub struct Tracker {
    gains: TrackingGains,
}

impl Tracker {
    pub fn new(gains: TrackingGains) -> Self {
        Self { gains }
    }

    pub fn gains(&self) -> TrackingGains {
        self.gains
    }

    pub fn command(&self, reference: State<f64>, measured: State<f64>) -> Command {
        let e = reference.q - measured.q;
        let e_dot = reference.v - measured.v;
        let raw = reference.a + self.gains.kp * e + self.gains.kd * e_dot;
        let max = self.gains.max_accel;

        // `f64::clamp` panics on NaN; this is the explicit, total version.
        if !raw.is_finite() || !max.is_finite() || max <= 0.0 {
            return Command {
                accel: 0.0,
                saturated: true,
            };
        }
        if raw > max {
            Command {
                accel: max,
                saturated: true,
            }
        } else if raw < -max {
            Command {
                accel: -max,
                saturated: true,
            }
        } else {
            Command {
                accel: raw,
                saturated: false,
            }
        }
    }
}
