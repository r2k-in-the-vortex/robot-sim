//! Force and torque: the wrench/twist frame algebra, and the model of what a sensor
//! between the wrist and the tool actually measures.
//!
//! This crate is the Rust counterpart of `lean/TorqueWrench.lean` and `lean/Dynamics.lean`,
//! which together are the specification. Function names are the Lean names in snake case, so
//! the correspondence stays greppable.
//!
//! # What the subject is, and what it is not
//!
//! "Torque wrench" is only the Lean module's filename: the subject is [`Wrench`], a force and
//! a moment, and the frame transforms that carry it between the sensor frame and the tool-tip
//! frame. The dynamics is a **single rigid body** — the payload distal to the sensor — in
//! Newton–Euler form written *algebraically*: acceleration is an independent datum and no
//! derivative is ever taken. There is no manipulator dynamics here: no mass matrix, no
//! Jacobian, no joint torques.
//!
//! The measurement model is
//!
//! ```text
//! measured = transport(contact) + inertial - gravity
//! ```
//!
//! and [`recovered_contact_wrench`] runs it backwards. It is exact in both directions
//! (`recoveredContactWrench_measuredWrench`): what is left in a real system is the accuracy of
//! the mass properties and the acceleration estimate, not the algebra.
//!
//! # Why it is generic, and what that buys
//!
//! Both Lean files are stated over an arbitrary `CommRing`, so everything in them is a
//! polynomial in the inputs. `TorqueWrench.lean` says why that matters: `ℝ` is a quotient of
//! Cauchy sequences with no computation rule, while `ℚ` arithmetic *computes*, so the Lean
//! generator can evaluate the model and emit exact numbers. This crate is generic for the same
//! reason — it is the strongest validation available in this project:
//! `test_data/force_torque_frames.json` holds 29 cases the Lean generator emitted, and the
//! test suite evaluates this same code over `robot_golden::Ratio` and compares with `==`, no
//! tolerance anywhere.
//!
//! # Conventions
//!
//! * `p` is the tip origin expressed in **sensor** coordinates, and a [`Rotation`] maps tip
//!   coordinates to sensor coordinates.
//! * `g` is the gravitational **acceleration**, pointing down. Gravity exerts the force `m g`
//!   on the body, so a sensor holding it at rest reads *minus* its gravity wrench — that single
//!   equation pins the sign convention of the whole model (`measuredWrench_at_rest`).
//! * No angle appears anywhere: a rotation enters as a [`Rotation`], checked from a matrix or
//!   built from a cosine/sine pair.
//!
//! # Invariants carried by types
//!
//! [`Rotation`] bundles orthogonality and determinant one because the algebra needs both. The
//! round trips need the first; `mulVec_cross` — a rotation commutes with a cross product —
//! needs the second, because orthogonality alone also admits reflections, and those
//! *anti*-commute instead. [`MassProperties`] bundles the symmetry of the inertia tensor, which
//! `dot_mulVec_self` needs to write the angular power as `α ⋅ (I ω)`.
//!
//! Where Lean discharges such an obligation with a proof inside a structure literal
//! (`Rotation.mul`'s `orth` and `det_eq_one`, `tipMassToSensor`'s `inertia_symm`), the Rust
//! constructor is private and unchecked and the proof is cited in place; every path in from
//! outside goes through a checked constructor, so a value of the type is only as sound as the
//! constructors are and nothing else has to re-check.

#![no_std]
#![forbid(unsafe_code)]

pub mod dynamics;
pub mod wrench;

pub use dynamics::{
    Accel, MassProperties, com_accel, first_moment, gravity_wrench, inertial_wrench,
    measured_wrench, origin_inertia, parallel_axis_inertia, recovered_contact_wrench,
    sensor_accel_to_tip, sensor_mass_to_tip, spatial_gravity_wrench, spatial_inertial_wrench,
    tip_accel_to_sensor, tip_mass_to_sensor,
};
pub use wrench::{
    Rotation, Twist, Wrench, sensor_to_tip, sensor_twist_to_tip, sensor_twist_to_tip_velocity,
    tip_to_sensor, tip_twist_to_sensor, virtual_work,
};
