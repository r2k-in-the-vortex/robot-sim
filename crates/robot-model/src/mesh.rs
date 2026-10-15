//! Per-frame STL mesh settings.

use crate::FRAME_COUNT;

/// One frame's mesh setting: what to draw, where, and how transparently.
///
/// `rotation_deg` is applied in the order local X, then Y, then Z, which is
/// `Rz(rz) · Ry(ry) · Rx(rx)` — see [`MeshSettings::local_rotation`].
#[derive(Clone, PartialEq, Debug)]
pub struct MeshSettings {
    /// Path to the STL, empty for "no mesh". The document stores it relative to the
    /// configuration file where it can.
    pub path: String,
    /// Local translation, in model units, applied after the local rotation.
    pub offset: [f64; 3],
    /// Local Euler angles in degrees, applied in the order X, then Y, then Z.
    pub rotation_deg: [f64; 3],
    /// `0.0` is invisible, `1.0` is opaque.
    pub opacity: f64,
}

impl Default for MeshSettings {
    fn default() -> Self {
        Self {
            path: String::new(),
            offset: [0.0; 3],
            rotation_deg: [0.0; 3],
            opacity: 1.0,
        }
    }
}

impl MeshSettings {
    /// Whether this setting asks for anything to be drawn at all.
    ///
    /// `simulator.py` line 880 skips a mesh with no path, and one with zero opacity is
    /// equally invisible, so both count as "not configured" — including in the mesh
    /// status line's loaded count (line 964).
    pub fn is_drawn(&self) -> bool {
        !self.path.is_empty() && self.opacity > 0.0
    }

    /// The local rotation `Rz(rz) · Ry(ry) · Rx(rx)` as row-major rows.
    ///
    /// Transcribed from `simulator.py` lines 978-988 rather than composed from three
    /// axis rotations, so the entries match the Python's floating-point operations
    /// exactly. The order is X then Y then Z, which is what the README documents for the
    /// Parameters tab's mesh rotations.
    pub fn local_rotation(&self) -> [[f64; 3]; 3] {
        let [rx, ry, rz] = self.rotation_deg.map(f64::to_radians);
        let (sx, cx) = rx.sin_cos();
        let (sy, cy) = ry.sin_cos();
        let (sz, cz) = rz.sin_cos();
        [
            [cz * cy, cz * sy * sx - sz * cx, cz * sy * cx + sz * sx],
            [sz * cy, sz * sy * sx + cz * cx, sz * sy * cx - cz * sx],
            [-sy, cy * sx, cy * cx],
        ]
    }
}

/// The document's `meshes` array covers the base and the six joints, in this order.
pub const MESH_COUNT: usize = FRAME_COUNT;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MESH_FRAME_NAMES;

    /// Multiply a row-major 3x3 by a column vector.
    fn apply(m: [[f64; 3]; 3], v: [f64; 3]) -> [f64; 3] {
        core::array::from_fn(|row| m[row][0] * v[0] + m[row][1] * v[1] + m[row][2] * v[2])
    }

    /// `Rz(rz) · Ry(ry) · Rx(rx)` built from separate axis rotations, as the reference
    /// the closed form above is checked against.
    fn rz_ry_rx(rx: f64, ry: f64, rz: f64) -> [[f64; 3]; 3] {
        let (sx, cx) = rx.sin_cos();
        let (sy, cy) = ry.sin_cos();
        let (sz, cz) = rz.sin_cos();
        let rot_x = [[1.0, 0.0, 0.0], [0.0, cx, -sx], [0.0, sx, cx]];
        let rot_y = [[cy, 0.0, sy], [0.0, 1.0, 0.0], [-sy, 0.0, cy]];
        let rot_z = [[cz, -sz, 0.0], [sz, cz, 0.0], [0.0, 0.0, 1.0]];
        let mul = |a: [[f64; 3]; 3], b: [[f64; 3]; 3]| -> [[f64; 3]; 3] {
            core::array::from_fn(|i| {
                core::array::from_fn(|j| (0..3).map(|k| a[i][k] * b[k][j]).sum())
            })
        };
        mul(mul(rot_z, rot_y), rot_x)
    }

    #[test]
    fn the_local_rotation_is_z_after_y_after_x() {
        let settings = MeshSettings {
            rotation_deg: [23.0, -41.0, 7.5],
            ..MeshSettings::default()
        };
        let expected = rz_ry_rx(
            23.0_f64.to_radians(),
            -41.0_f64.to_radians(),
            7.5_f64.to_radians(),
        );
        let actual = settings.local_rotation();
        for row in 0..3 {
            for column in 0..3 {
                assert!(
                    (actual[row][column] - expected[row][column]).abs() < 1e-12,
                    "entry [{row}][{column}]"
                );
            }
        }
    }

    #[test]
    fn the_order_matters_so_the_test_would_catch_it() {
        // The previous test would also pass against a transposed or reordered
        // transcription that happened to agree at those angles, so this pins the
        // distinction the order actually makes: X then Y then Z is not Z then Y then X.
        let degrees = [30.0, 40.0, 50.0];
        let settings = MeshSettings {
            rotation_deg: degrees,
            ..MeshSettings::default()
        };
        let reversed = rz_ry_rx(
            degrees[2].to_radians(),
            degrees[1].to_radians(),
            degrees[0].to_radians(),
        );
        let actual = settings.local_rotation();
        let largest_difference = (0..3)
            .flat_map(|row| (0..3).map(move |column| (row, column)))
            .map(|(row, column)| (actual[row][column] - reversed[row][column]).abs())
            .fold(0.0_f64, f64::max);
        assert!(largest_difference > 0.1, "difference {largest_difference}");
    }

    #[test]
    fn identity_rotation_leaves_a_point_alone() {
        let identity = MeshSettings::default().local_rotation();
        let probe = [1.5, -2.25, 3.75];
        let moved = apply(identity, probe);
        for axis in 0..3 {
            assert!((moved[axis] - probe[axis]).abs() < 1e-15);
        }
    }

    #[test]
    fn a_mesh_with_no_path_or_no_opacity_is_not_drawn() {
        assert!(!MeshSettings::default().is_drawn());
        let configured = MeshSettings {
            path: "mesh/part.stl".into(),
            ..MeshSettings::default()
        };
        assert!(configured.is_drawn());
        let invisible = MeshSettings {
            opacity: 0.0,
            ..configured
        };
        assert!(!invisible.is_drawn());
    }

    #[test]
    fn there_is_one_mesh_setting_per_frame() {
        assert_eq!(MESH_COUNT, 7);
        assert_eq!(MESH_FRAME_NAMES.len(), MESH_COUNT);
    }
}
