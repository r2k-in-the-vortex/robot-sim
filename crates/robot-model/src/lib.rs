//! The robot configuration document: the DH table and the per-frame mesh settings.
//!
//! This is the shape of `robot_parameters.json`, schema version 1, as types. Reading and
//! writing the file is the Parameters tab's job; everything here is a plain data type
//! plus the conversions that boundary needs:
//!
//! * **degrees to radians, offset folded in.** The document stores a static theta offset
//!   in degrees because that is what the UI edits, while [`robot_kinematics`] works in
//!   radians and total DH angles. See [`DHParameters::total_angles_rad`].
//! * **a DH table to a [`robot_kinematics::Geometry`].** The kinematics core fixes the
//!   arm's structure rather than accepting a free table, so the table has to prove it is
//!   that arm by producing a `Geometry`. See [`DHParameters::geometry`].
//!
//! Field names match the JSON keys exactly, so a `serde` derive added by the code that
//! owns the file I/O needs no rename attributes.

#![forbid(unsafe_code)]

pub mod dh;
pub mod document;
pub mod mesh;

pub use dh::{DHParameters, DhRow};
pub use document::{Document, SCHEMA_VERSION};
pub use mesh::{MeshSettings, MESH_COUNT};
pub use robot_kinematics::{FRAME_COUNT, JOINT_COUNT};

/// The seven settings rows, in the order `robot_parameters.json` lists `meshes` and the
/// base and joints are drawn: index 0 is the base, index `i` is joint `i`.
///
/// `MESH_FRAME_NAMES` in `simulator.py` line 38.
pub const MESH_FRAME_NAMES: [&str; FRAME_COUNT] =
    ["Base", "J1", "J2", "J3", "J4", "J5", "J6"];

/// The seven gizmo labels, in the same order.
///
/// The cumulative frame `i` carries joint `i + 1`'s axis, so the short names differ from
/// [`MESH_FRAME_NAMES`] by one and frame 6 is the flange. `AXIS_FRAME_NAMES` in
/// `simulator.py` lines 39-41, with the comment explaining exactly that shift.
pub const AXIS_FRAME_NAMES: [&str; FRAME_COUNT] =
    ["J1", "J2", "J3", "J4", "J5", "J6", "Tool/Flange"];
