//! The whole configuration document, mirroring `robot_parameters.json`.

use crate::FRAME_COUNT;
use crate::dh::DHParameters;
use crate::mesh::MESH_COUNT;
use crate::mesh::MeshSettings;

/// The only `schema_version` this shape describes.
pub const SCHEMA_VERSION: u32 = 1;

/// The `units` block the JSON carries, as documentation rather than as data.
///
/// It exists so a reader can tell what the numbers mean without the source. Both strings
/// are what the shipped file says.
pub mod units {
    /// `units.angles`
    pub const ANGLES: &str = "degrees";
    /// `units.lengths`
    pub const LENGTHS: &str = "model_units";
}

/// Everything the Parameters tab edits and the 3D view draws.
#[derive(Clone, PartialEq, Debug)]
pub struct Document {
    /// Always [`SCHEMA_VERSION`] for a document this type can produce.
    pub schema_version: u32,
    /// Whether loaded meshes draw their triangle edges. Off by default.
    pub show_mesh_edges: bool,
    /// One visibility flag per frame, base first: `show_coordinate_gizmos` in the JSON.
    /// All visible by default.
    pub show_coordinate_gizmos: [bool; FRAME_COUNT],
    /// Whether the per-frame labels are drawn. Visible by default.
    pub show_joint_labels: bool,
    /// The DH table.
    pub parameters: DHParameters,
    /// One mesh setting per frame, base first.
    pub meshes: [MeshSettings; MESH_COUNT],
}

impl Default for Document {
    fn default() -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            show_mesh_edges: false,
            show_coordinate_gizmos: [true; FRAME_COUNT],
            show_joint_labels: true,
            parameters: DHParameters::shipped(),
            meshes: core::array::from_fn(|_| MeshSettings::default()),
        }
    }
}

impl Document {
    /// The document `robot_parameters.json` ships, which is also the state a fresh
    /// install starts in: the illustrative DH table, seven empty mesh slots, and every
    /// gizmo and label visible.
    pub fn shipped() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_default_document_has_seven_visible_gizmos_and_no_meshes() {
        let document = Document::shipped();
        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert!(!document.show_mesh_edges);
        assert!(document.show_joint_labels);
        assert!(
            document
                .show_coordinate_gizmos
                .iter()
                .all(|visible| *visible)
        );
        assert!(document.meshes.iter().all(|mesh| !mesh.is_drawn()));
    }

    #[test]
    fn the_default_dh_table_is_the_shipped_one() {
        assert_eq!(Document::shipped().parameters, DHParameters::shipped());
    }
}
