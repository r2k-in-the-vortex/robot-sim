//! Kinematics of the supported six-axis arm.
//!
//! This crate is the Rust counterpart of the Lean development under `lean/`, which is
//! the specification: `Kinematics.lean` for the forward chain and `Zyz.lean`,
//! `Atan2.lean` and `InverseKinematics.lean` for the closed-form solver. The function
//! names mirror the Lean names so the correspondence stays greppable, and
//! `docs/lean-rust-map.md` records it definition by definition.
//!
//! # Conventions
//!
//! * Angles are **radians** and **total DH angles** — the joint's static theta offset is
//!   already folded in, exactly as `θ` appears in Lean. [`units`] carries the conversion
//!   to and from the degrees the configuration file uses.
//! * The DH transform is the standard one, `Rz θ · Tz d · Tx a · Rx α`. This is *not*
//!   modified/Craig DH.
//! * The arm's structure is fixed and [`Geometry`] is the evidence: `alpha` of
//!   `90, 0, 90, 90, -90, 0` degrees with `a3 = a4 = a5 = a6 = 0` and `d2 = d3 = d5 = 0`.
//!
//! # Precision
//!
//! The algorithms are generic over [`Scalar`], but production instantiates [`f64`] and
//! nothing else, so every operation monomorphises to a plain floating-point instruction.
//! The genericity exists so the test suite can re-run the same properties at higher
//! precision, where a failure at `f64` that disappears at 200 bits is a rounding
//! artefact and one that survives is an algorithmic mistake.
//!
//! Nothing in the Lean development is a proof *about* `f64`; what the theorems supply is
//! the exact property each function must satisfy, and — for the rational part of the
//! mathematics — vectors to check it against. See `docs/verification.md`.
//!
//! # Real-time use
//!
//! The crate is `no_std`-capable, allocates nothing, and contains no panicking operation
//! on any control path: the candidate buffer is a fixed array sized by a proved bound
//! ([`MAX_SOLUTIONS`]), and overflow is reported rather than raised.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

pub mod angle;
pub mod chain;
pub mod geometry;
pub mod mat3;
pub mod pose;
pub mod scalar;
pub mod solution;
pub mod units;
pub mod vec3;

pub use angle::{AnglesCosSin, CosSin};
pub use chain::{
    Angles, PlanarTarget, arm_pose, arm_pose_cs, arm_rotation, arm_rotation_cs, carrier_pose,
    carrier_pose_cs, elbow_cosine, fk, fk_cs, pairs, planar_target, wrist_center, wrist_pose,
    wrist_pose_cs, wrist_rotation, wrist_rotation_cs,
};
pub use geometry::{Geometry, GeometryError};
pub use mat3::Mat3;
pub use pose::Pose;
pub use scalar::{Field, Scalar};
pub use solution::{MAX_SOLUTIONS, Solution, SolutionSet};
pub use units::{FRAME_COUNT, JOINT_COUNT, deg_to_rad, rad_to_deg, runtime_angle, total_angle, wrap_angle};
pub use vec3::Vec3;
