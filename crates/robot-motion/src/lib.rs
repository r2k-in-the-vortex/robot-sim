//! Jerk-limited motion planning and tracking.
//!
//! This crate is the Rust counterpart of the Lean development under `lean/Motion/`.
//! The specification is the Lean one; `docs/lean-rust-map.md` records the mapping and
//! `docs/motion_control.md` is the execution plan.
//!
//! # Layers
//!
//! * [`profile`] is the polynomial layer: `State`, `Limits`, `Segment`, `Profile`,
//!   evaluation and the transforms (`stretch`, `translate`, `mirror`, `append`,
//!   `reverse`). It is generic over [`robot_kinematics::Field`], so the same code runs
//!   over `f64` in production and over `robot_golden::Ratio` in the exact tests.
//! * [`conservative`] is the verified default planner. It is radical-free and therefore
//!   also `Field`-generic: every duration and jerk is rational when the inputs are.
//! * [`plan`] is the optimal 7-phase planner (M1-opt). It needs `sqrt`/`cbrt` and is
//!   `f64`-only; it is tested against the exact golden corpus with a declared tolerance.
//!
//! Production instantiates `f64` and nothing else. The crate is `no_std`, allocates
//! nothing, and has a fixed-capacity `Profile`; `MAX_PHASES` is backed by the Lean
//! length theorems.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

pub mod conservative;
pub mod error;
pub mod general;
pub mod harness;
pub mod math;
pub mod plan;
pub mod plant;
pub mod profile;
pub mod supervisor;
pub mod sync;
pub mod tracker;

pub use conservative::plan_rest_conservative;
pub use error::{PlanError, ProfileError};
pub use general::{plan_general, stop_feasible, viable};
pub use harness::{CycleConfig, CycleOutcome, RunReport, run};
pub use plan::plan_rest_to_rest;
pub use plant::{JointPlant, PlantConfig};
pub use profile::{JointProfile, Limits, MAX_PHASES, PlanKind, Profile, Segment, State};
pub use supervisor::{Decision, Supervisor, SupervisorConfig};
pub use sync::{plan_movej_scalar, synchronize};
pub use tracker::{Command, Tracker, TrackingGains};
