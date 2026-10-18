//! The robot configuration document: the DH table and the per-frame mesh settings.
//!
//! This is the shape of `robot_parameters.json`, schema version 1, as types, plus the
//! conversions that boundary needs:
//!
//! * **degrees to radians, offset folded in.** The document stores a static theta offset
//!   in degrees because that is what the UI edits, while [`robot_kinematics`] works in
//!   radians and total DH angles. See [`DHParameters::total_angles_rad`].
//! * **a DH table to a [`robot_kinematics::Geometry`].** The kinematics core fixes the
//!   arm's structure rather than accepting a free table, so the table has to prove it is
//!   that arm by producing a `Geometry`. See [`DHParameters::geometry`].
//!
//! Reading and writing the file itself — the bytes, the validation, and the mesh paths
//! that are relative to the file — is [`persist`]'s job.
//!
//! Field names match the JSON keys exactly, so a `serde` derive added by the code that
//! owns the file I/O needs no rename attributes.

#![forbid(unsafe_code)]

pub mod dh;
pub mod document;
pub mod limits;
pub mod mesh;
pub mod persist;
pub mod table;

pub use dh::{DHParameters, DhRow};
pub use document::{Document, SCHEMA_VERSION};
pub use limits::{
    DEFAULT_ACCELERATION_DEG_S2, DEFAULT_JERK_DEG_S3, DEFAULT_VELOCITY_DEG_S, JointMotionLimits,
    MotionLimits,
};
pub use mesh::{MESH_COUNT, MeshSettings};
pub use persist::{DocumentError, FILE_NAME, LoadError, load, parse, save, to_json};
pub use robot_kinematics::{FRAME_COUNT, JOINT_COUNT};
pub use table::{STRUCTURE_TOLERANCE_RAD, TableError};

/// The seven settings rows, in the order `robot_parameters.json` lists `meshes` and the
/// base and joints are drawn: index 0 is the base, index `i` is joint `i`.
///
/// `MESH_FRAME_NAMES` in `simulator.py` line 38.
pub const MESH_FRAME_NAMES: [&str; FRAME_COUNT] = ["Base", "J1", "J2", "J3", "J4", "J5", "J6"];

/// The seven gizmo labels, in the same order.
///
/// The cumulative frame `i` carries joint `i + 1`'s axis, so the short names differ from
/// [`MESH_FRAME_NAMES`] by one and frame 6 is the flange. `AXIS_FRAME_NAMES` in
/// `simulator.py` lines 39-41, with the comment explaining exactly that shift.
pub const AXIS_FRAME_NAMES: [&str; FRAME_COUNT] =
    ["J1", "J2", "J3", "J4", "J5", "J6", "Tool/Flange"];
