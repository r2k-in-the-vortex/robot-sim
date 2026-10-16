//! STL loading and smooth, two-sided link shading.
//!
//! Stands in for the matplotlib path of `simulator.py`: [`parse_stl`] replaces
//! `stl_mesh.Mesh.from_file` (simulator.py:883) and [`build_link_mesh`] transcribes
//! `_two_sided_face_colors` (simulator.py:991-1040), including its crease handling and
//! its `mesh_scale`-relative vertex weld.
//!
//! Binary and ASCII STL are told apart by size and not by the header, because the header
//! lies: all seven shipped link meshes are binary, six of them open with the ASCII bytes
//! `solid ` and the seventh with `COLOR`. A binary file is exactly `84 + 50 * n` bytes
//! with its triangle count at offset 80, which is the only dependable discriminator.

use std::collections::HashMap;
use std::io::Cursor;
use std::path::Path;

use bevy::asset::RenderAssetUsages;
use bevy::mesh::{Indices, Mesh, PrimitiveTopology, VertexAttributeValues};

/// The ambient floor of `illumination` (simulator.py:1038).
const AMBIENT: f64 = 0.32;
/// The weight of the diffuse term (simulator.py:1038).
const DIFFUSE_WEIGHT: f64 = 0.68;
/// The headlight direction, normalized where it is used (simulator.py:1034-1035).
const LIGHT: [f64; 3] = [0.35, -0.45, 0.82];
/// Faces whose normals are within this angle of each other shade as one surface
/// (simulator.py:1016).
const CREASE_DEGREES: f64 = 50.0;

/// A box that contains nothing. This, rather than `Bounds::default()`, is the
/// accumulator seed: folding it into a union is the identity, and it is what an empty
/// mesh is left with.
const EMPTY_BOUNDS: Bounds = Bounds {
    min: [f32::INFINITY; 3],
    max: [f32::NEG_INFINITY; 3],
};

/// The axis-aligned bounds of a mesh in its own coordinate system.
#[derive(Copy, Clone, PartialEq, Debug, Default)]
pub struct Bounds {
    pub min: [f32; 3],
    pub max: [f32; 3],
}

impl Bounds {
    /// The midpoint of the box.
    pub fn center(&self) -> [f32; 3] {
        [
            (self.min[0] + self.max[0]) / 2.0,
            (self.min[1] + self.max[1]) / 2.0,
            (self.min[2] + self.max[2]) / 2.0,
        ]
    }

    /// The extent of the box along each axis.
    pub fn size(&self) -> [f32; 3] {
        [
            self.max[0] - self.min[0],
            self.max[1] - self.min[1],
            self.max[2] - self.min[2],
        ]
    }

    /// The smallest box containing both.
    pub fn union(self, other: Self) -> Self {
        Self {
            min: [
                self.min[0].min(other.min[0]),
                self.min[1].min(other.min[1]),
                self.min[2].min(other.min[2]),
            ],
            max: [
                self.max[0].max(other.max[0]),
                self.max[1].max(other.max[1]),
                self.max[2].max(other.max[2]),
            ],
        }
    }

    /// The bounds of this box after an axis-aligned transform: translate then
    /// rotate. `rotation` is row-major rows of a 3x3 matrix.
    pub fn transformed(self, rotation: [[f32; 3]; 3], translation: [f32; 3]) -> Self {
        // The bounds of nothing are still nothing, and the infinite seed would
        // otherwise turn into NaN through `0.0 * inf`.
        if self.is_empty() {
            return self;
        }
        let mut min = translation;
        let mut max = translation;
        for (axis, row) in rotation.iter().enumerate() {
            for (column, factor) in row.iter().enumerate() {
                // Whichever corner of the box lands low or high on this axis.
                let low = factor * self.min[column];
                let high = factor * self.max[column];
                min[axis] += low.min(high);
                max[axis] += low.max(high);
            }
        }
        Self { min, max }
    }

    /// True when the box is the [`EMPTY_BOUNDS`] seed, i.e. inverted on some axis.
    /// `Bounds::default()` is the degenerate box at the origin, not the empty one.
    pub fn is_empty(&self) -> bool {
        self.min[0] > self.max[0] || self.min[1] > self.max[1] || self.min[2] > self.max[2]
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct LinkMesh {
    pub positions: Vec<[f32; 3]>,
    pub normals: Vec<[f32; 3]>,
    pub colors: Vec<[f32; 4]>,
    pub indices: Vec<u32>,
    /// Bounds of the welded vertices, in the mesh's own units.
    pub bounds: Bounds,
    pub triangle_count: usize,
}

#[derive(Debug)]
pub enum MeshError {
    /// The file could not be read from disk.
    Io(std::io::Error),
    /// stl_io's parse failed on data we had classified as ASCII.
    Parse(std::io::Error),
    /// The file decoded but contained no triangles.
    Empty,
}

impl std::fmt::Display for MeshError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(f, "could not read the STL file: {error}"),
            Self::Parse(error) => write!(f, "could not parse the STL data: {error}"),
            Self::Empty => write!(f, "the STL file contains no triangles"),
        }
    }
}

impl std::error::Error for MeshError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) | Self::Parse(error) => Some(error),
            Self::Empty => None,
        }
    }
}

/// Read an STL file from disk. `base_color` is sRGB 0..1; `opacity` is 0..1.
pub fn load_link_mesh(
    path: &Path,
    base_color: [f32; 3],
    opacity: f32,
) -> Result<LinkMesh, MeshError> {
    let bytes = std::fs::read(path).map_err(MeshError::Io)?;
    let triangles = parse_stl(&bytes)?;
    if triangles.is_empty() {
        // simulator.py:884-886 rejects the same file with "STL contains no vertices".
        return Err(MeshError::Empty);
    }
    Ok(build_link_mesh(&triangles, base_color, opacity))
}

/// Parse STL bytes into raw triangles, handling the binary/ASCII trap described above.
pub fn parse_stl(bytes: &[u8]) -> Result<Vec<[[f32; 3]; 3]>, MeshError> {
    if binary_triangle_count(bytes).is_some() {
        return read_binary(bytes);
    }
    match read_ascii(bytes) {
        Ok(triangles) => Ok(triangles),
        // A binary file with trailing bytes fails the exact size test, so retry it
        // as binary by force before reporting a parse failure.
        Err(_) => read_binary(bytes),
    }
}

/// Weld, smooth-shade and two-sided-light a triangle soup.
pub fn build_link_mesh(
    triangles: &[[[f32; 3]; 3]],
    base_color: [f32; 3],
    opacity: f32,
) -> LinkMesh {
    if triangles.is_empty() {
        return LinkMesh {
            positions: Vec::new(),
            normals: Vec::new(),
            colors: Vec::new(),
            indices: Vec::new(),
            bounds: EMPTY_BOUNDS,
            triangle_count: 0,
        };
    }

    let (welded_positions, corner_vertex) = weld_coincident_vertices(triangles);
    let face_normals = smooth_face_normals(triangles, &corner_vertex, welded_positions.len());

    let light = normalize(LIGHT);
    let vertex_count = triangles.len() * 3;
    let mut positions = Vec::with_capacity(vertex_count);
    let mut normals = Vec::with_capacity(vertex_count);
    let mut colors = Vec::with_capacity(vertex_count);

    for (face, triangle) in triangles.iter().enumerate() {
        // The absolute value is the two-sided part: a face lit from behind is exactly
        // as bright as one lit from the front (simulator.py:1036).
        let diffuse = dot(face_normals[face], light).abs();
        let illumination = AMBIENT + DIFFUSE_WEIGHT * diffuse;
        let color = [
            (f64::from(base_color[0]) * illumination).clamp(0.0, 1.0) as f32,
            (f64::from(base_color[1]) * illumination).clamp(0.0, 1.0) as f32,
            (f64::from(base_color[2]) * illumination).clamp(0.0, 1.0) as f32,
            opacity,
        ];
        // The color varies per face, so the three corners share one normal but still
        // need their own copies of the vertex (simulator.py:1039-1040).
        let normal = face_normals[face].map(|component| component as f32);
        for corner in triangle {
            positions.push(*corner);
            normals.push(normal);
            colors.push(color);
        }
    }

    let bounds = welded_positions
        .iter()
        .fold(EMPTY_BOUNDS, |bounds, position| {
            bounds.union(Bounds {
                min: *position,
                max: *position,
            })
        });

    LinkMesh {
        positions,
        normals,
        colors,
        indices: (0..vertex_count as u32).collect(),
        bounds,
        triangle_count: triangles.len(),
    }
}

/// Convert to a Bevy render mesh with POSITION, NORMAL and COLOR attributes.
pub fn to_bevy_mesh(mesh: &LinkMesh) -> Mesh {
    let mut bevy_mesh = Mesh::new(
        PrimitiveTopology::TriangleList,
        RenderAssetUsages::default(),
    );
    // All three attributes every time: a mesh with fewer than two of them cannot be
    // rendered, and the color is what carries the pre-baked two-sided lighting.
    bevy_mesh.insert_attribute(
        Mesh::ATTRIBUTE_POSITION,
        VertexAttributeValues::Float32x3(mesh.positions.clone()),
    );
    bevy_mesh.insert_attribute(
        Mesh::ATTRIBUTE_NORMAL,
        VertexAttributeValues::Float32x3(mesh.normals.clone()),
    );
    // The baked colors are display-referred sRGB, because that is what the reference's
    // numpy facecolors are and what matplotlib writes (simulator.py:1039-1040): the
    // illumination multiply happens in sRGB and the values have to stay comparable with
    // it. Bevy's color attribute is not that: the fragment shader takes it as
    // `base_color` in linear light, and the non-HDR target only re-encodes on write, so
    // sRGB numbers fed straight in are used as if they were already linear and every
    // face comes out washed out. Convert here; alpha is already linear.
    let colors = mesh
        .colors
        .iter()
        .map(|color| {
            [
                srgb_to_linear(color[0]),
                srgb_to_linear(color[1]),
                srgb_to_linear(color[2]),
                color[3],
            ]
        })
        .collect();
    bevy_mesh.insert_attribute(
        Mesh::ATTRIBUTE_COLOR,
        VertexAttributeValues::Float32x4(colors),
    );
    bevy_mesh.insert_indices(Indices::U32(mesh.indices.clone()));
    bevy_mesh
}

/// The IEC 61966-2-1 transfer function, sRGB -> linear light.
fn srgb_to_linear(channel: f32) -> f32 {
    if channel <= 0.04045 {
        channel / 12.92
    } else {
        ((channel + 0.055) / 1.055).powf(2.4)
    }
}

/// The triangle count of a binary STL, or `None` when the bytes are not one.
///
/// Binary STL has no usable signature: six of the seven meshes in `mesh/` start with
/// `solid ` and the seventh starts with `COLOR`, yet all seven are binary, so a
/// `starts_with("solid")` sniff gets the shipped meshes exactly backwards. A binary
/// file is precisely `84 + 50 * n` bytes with `n` at offset 80, which is the only
/// reliable discriminator.
fn binary_triangle_count(bytes: &[u8]) -> Option<u32> {
    let count_bytes = bytes.get(80..84)?;
    let count = u32::from_le_bytes([
        count_bytes[0],
        count_bytes[1],
        count_bytes[2],
        count_bytes[3],
    ]);
    (84 + 50 * u64::from(count) == bytes.len() as u64).then_some(count)
}

fn read_ascii(bytes: &[u8]) -> Result<Vec<[[f32; 3]; 3]>, MeshError> {
    stl_io::read_stl(&mut Cursor::new(bytes))
        .map(into_triangles)
        .map_err(MeshError::Parse)
}

/// Read the bytes as binary STL no matter what the header claims.
fn read_binary(bytes: &[u8]) -> Result<Vec<[[f32; 3]; 3]>, MeshError> {
    let mut forced = bytes.to_vec();
    // stl_io picks its reader by probing whether the first line starts with `solid `
    // (ascii_reader.rs:29), and its binary reader reads the 80-byte header only to
    // discard it (binary_reader.rs: `reader.read_exact(&mut header)?;`). Overwriting
    // the header therefore forces the binary path without touching a single triangle.
    if forced.len() >= 6 {
        forced[..6].copy_from_slice(b"######");
    }
    stl_io::read_stl(&mut Cursor::new(forced.as_slice()))
        .map(into_triangles)
        .map_err(MeshError::Parse)
}

fn into_triangles(mesh: stl_io::IndexedMesh) -> Vec<[[f32; 3]; 3]> {
    mesh.into_triangle_vec()
        .into_iter()
        .map(|triangle| triangle.vertices.map(|vertex| vertex.0))
        .collect()
}

/// Weld coincident corners and return the representative position of each welded
/// vertex plus the corner -> welded vertex map, with corners in triangle order.
///
/// The representative is the first corner that mapped to the group, so the bounds are
/// real mesh coordinates rather than the quantized weld keys.
fn weld_coincident_vertices(triangles: &[[[f32; 3]; 3]]) -> (Vec<[f32; 3]>, Vec<usize>) {
    debug_assert!(!triangles.is_empty());

    // simulator.py:994-996: the weld quantum is relative to the mesh's own size, with
    // a floor of 1.0 so a sub-unit mesh does not collapse into a single point.
    let mut low = [f64::INFINITY; 3];
    let mut high = [f64::NEG_INFINITY; 3];
    for triangle in triangles {
        for corner in triangle {
            for (axis, value) in corner.iter().enumerate() {
                let value = f64::from(*value);
                low[axis] = low[axis].min(value);
                high[axis] = high[axis].max(value);
            }
        }
    }
    let mesh_scale = (high[0] - low[0])
        .max(high[1] - low[1])
        .max(high[2] - low[2])
        .max(1.0);
    let quantum = mesh_scale * 1e-7;

    // simulator.py:883 loads the STL as float64, so the whole pipeline runs in f64 to
    // keep the weld groups and the shading bit-comparable with the Python.
    let mut welded_index: HashMap<[i64; 3], usize> = HashMap::new();
    let mut welded_positions: Vec<[f32; 3]> = Vec::new();
    let mut corner_vertex = Vec::with_capacity(triangles.len() * 3);
    for triangle in triangles {
        for &position in triangle {
            // `np.rint` rounds halves to even, hence `round_ties_even` rather than `round`.
            let key =
                position.map(|component| (f64::from(component) / quantum).round_ties_even() as i64);
            let vertex = *welded_index.entry(key).or_insert_with(|| {
                welded_positions.push(position);
                welded_positions.len() - 1
            });
            corner_vertex.push(vertex);
        }
    }
    (welded_positions, corner_vertex)
}

/// The per-face shading normal: the three corner normals of each face, averaged.
///
/// A corner normal is the area-weighted sum of every incident face normal within
/// [`CREASE_DEGREES`] of that corner's own face (simulator.py:1016-1032), so a smooth
/// surface shades as a unit while a crease keeps its two sides apart.
fn smooth_face_normals(
    triangles: &[[[f32; 3]; 3]],
    corner_vertex: &[usize],
    welded_count: usize,
) -> Vec<[f64; 3]> {
    let mut face_normals = Vec::with_capacity(triangles.len());
    let mut face_areas = Vec::with_capacity(triangles.len());
    for triangle in triangles {
        let a = triangle[0].map(f64::from);
        let b = triangle[1].map(f64::from);
        let c = triangle[2].map(f64::from);
        let normal = cross(sub(b, a), sub(c, a));
        let area = length(normal);
        face_areas.push(area);
        // Zero-area faces keep a zero normal instead of dividing by zero.
        face_normals.push(if area > 0.0 {
            divide(normal, area)
        } else {
            [0.0; 3]
        });
    }

    let mut incident: Vec<Vec<usize>> = vec![Vec::new(); welded_count];
    for (corner, &vertex) in corner_vertex.iter().enumerate() {
        incident[vertex].push(corner);
    }

    let crease_cosine = CREASE_DEGREES.to_radians().cos();
    let mut corner_normals = vec![[0.0; 3]; corner_vertex.len()];
    for corners in &incident {
        for &corner in corners {
            let reference = face_normals[corner / 3];
            let mut sum = [0.0; 3];
            for &other in corners {
                let face = other / 3;
                // Degenerate faces have a zero normal, which dots to 0 with everything
                // and so never clears the crease threshold.
                if dot(reference, face_normals[face]) >= crease_cosine {
                    sum = add(sum, scale(face_normals[face], face_areas[face]));
                }
            }
            corner_normals[corner] = sum;
        }
    }

    let corner_normals: Vec<[f64; 3]> = corner_normals.into_iter().map(normalize).collect();
    (0..triangles.len())
        .map(|face| {
            let corners = &corner_normals[face * 3..face * 3 + 3];
            normalize(divide(add(add(corners[0], corners[1]), corners[2]), 3.0))
        })
        .collect()
}

fn add(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}

fn sub(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}

fn scale(v: [f64; 3], factor: f64) -> [f64; 3] {
    [v[0] * factor, v[1] * factor, v[2] * factor]
}

fn divide(v: [f64; 3], divisor: f64) -> [f64; 3] {
    [v[0] / divisor, v[1] / divisor, v[2] / divisor]
}

fn cross(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]
}

fn dot(a: [f64; 3], b: [f64; 3]) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}

fn length(v: [f64; 3]) -> f64 {
    dot(v, v).sqrt()
}

/// Unit length, or zero for a zero-length input.
fn normalize(v: [f64; 3]) -> [f64; 3] {
    let len = length(v);
    if len > 0.0 { divide(v, len) } else { v }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two triangles sharing the A-C edge, in the z = 0 plane.
    const QUAD: [[[f32; 3]; 3]; 2] = [
        [[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [1.0, 1.0, 0.0]],
        [[0.0, 0.0, 0.0], [1.0, 1.0, 0.0], [0.0, 1.0, 0.0]],
    ];

    /// Two triangles sharing the A-B edge, the second one's free corner at `apex`, so
    /// the angle between the two planes is the angle between (0, 1, 0) and `apex`.
    fn bent_pair(apex: [f32; 3]) -> [[[f32; 3]; 3]; 2] {
        [
            [[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]],
            [[1.0, 0.0, 0.0], [0.0, 0.0, 0.0], apex],
        ]
    }

    /// An `apex` point `degrees` off the first plane.
    fn tilted_apex(degrees: f64) -> [f32; 3] {
        let (sin, cos) = degrees.to_radians().sin_cos();
        [0.0, -(cos as f32), sin as f32]
    }

    /// The single face normal of a one-triangle mesh, unit length.
    fn only_face_normal(triangle: [[f32; 3]; 3]) -> [f64; 3] {
        let (_, corner_vertex) = weld_coincident_vertices(&[triangle]);
        let normals = smooth_face_normals(&[triangle], &corner_vertex, 3);
        assert_eq!(normals.len(), 1);
        normals[0]
    }

    fn only_face_color(triangle: [[f32; 3]; 3], base_color: [f32; 3]) -> [f32; 4] {
        let mesh = build_link_mesh(&[triangle], base_color, 1.0);
        assert_eq!(mesh.colors.len(), 3);
        assert_eq!(mesh.colors[0], mesh.colors[1]);
        assert_eq!(mesh.colors[1], mesh.colors[2]);
        mesh.colors[0]
    }

    const ASCII_STL: &str = "solid test
  facet normal 0 0 1
    outer loop
      vertex 0 0 0
      vertex 2 0 0
      vertex 0 2 0
    endloop
  endfacet
endsolid test
";

    const EMPTY_ASCII_STL: &str = "solid nothing
endsolid nothing
";

    /// The triangle [`synthetic_binary_stl`] holds: normal then three vertices, all
    /// distinct, so any misaligned record read shows up as the wrong number.
    const SYNTHETIC_TRIANGLE: [[f32; 3]; 3] = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];

    /// A binary STL whose 80-byte header is a valid UTF-8 first line starting with
    /// `solid ` — the exact shape that makes a header sniff misread it as ASCII.
    fn synthetic_binary_stl() -> Vec<u8> {
        let mut bytes = Vec::new();
        let mut header = b"solid synthetic binary mesh\n".to_vec();
        header.resize(80, b' ');
        bytes.extend_from_slice(&header);
        bytes.extend_from_slice(&1u32.to_le_bytes());
        let normal = [0.0f32, 0.0, 1.0];
        for vertex in [
            normal,
            SYNTHETIC_TRIANGLE[0],
            SYNTHETIC_TRIANGLE[1],
            SYNTHETIC_TRIANGLE[2],
        ] {
            for component in vertex {
                bytes.extend_from_slice(&component.to_le_bytes());
            }
        }
        bytes.extend_from_slice(&0u16.to_le_bytes());
        assert_eq!(bytes.len(), 84 + 50);
        bytes
    }

    #[test]
    fn shipped_meshes_parse_shade_and_bound() {
        let directory = concat!(env!("CARGO_MANIFEST_DIR"), "/../../mesh");
        let mut checked = 0;
        for entry in std::fs::read_dir(directory).expect("the mesh directory must exist") {
            let path = entry.expect("directory entry").path();
            if !path
                .extension()
                .is_some_and(|extension| extension.eq_ignore_ascii_case("STL"))
            {
                continue;
            }
            let bytes = std::fs::read(&path).expect("mesh file must be readable");
            let triangles = parse_stl(&bytes).unwrap_or_else(|error| panic!("{path:?}: {error}"));
            let declared =
                u32::from_le_bytes([bytes[80], bytes[81], bytes[82], bytes[83]]) as usize;
            assert_eq!(triangles.len(), declared, "{path:?}");
            assert!(declared > 0, "{path:?}");

            let base = [0.8f32, 0.25, 0.25];
            let opacity = 0.9f32;
            let mesh = build_link_mesh(&triangles, base, opacity);
            assert_eq!(mesh.positions.len(), declared * 3, "{path:?}");
            assert_eq!(mesh.normals.len(), declared * 3, "{path:?}");
            assert_eq!(mesh.colors.len(), declared * 3, "{path:?}");
            assert_eq!(mesh.indices.len(), declared * 3, "{path:?}");
            assert_eq!(mesh.triangle_count, declared, "{path:?}");
            assert_eq!(mesh.indices[declared * 3 - 1] as usize, declared * 3 - 1);
            assert!(!mesh.bounds.is_empty(), "{path:?}");
            assert!(
                mesh.bounds.size().iter().all(|extent| *extent > 0.0),
                "{path:?}"
            );
            assert!(
                mesh.bounds.transformed(
                    [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
                    [0.0; 3]
                ) == mesh.bounds,
                "{path:?}"
            );
            // Every face with area shades as a unit normal, and every color sits between
            // the ambient floor and the full base color of its face.
            //
            // A face *without* area is a collapsed CAD sliver, which the reference
            // defines rather than forbids: all three divides in `_two_sided_face_colors`
            // are guarded by `where=area > 0` (simulator.py:1000-1032), so a sliver keeps
            // a zero normal, adds nothing to any neighbour's smoothing — a zero normal
            // never clears the crease cosine — and shades at the ambient floor. It
            // covers no pixels, so the rendered mesh is what it would be with the sliver
            // deleted. Mesh 04 ships exactly one (face 44527, corners 133581-133583: a
            // 0.0045-unit sliver whose third corner is the midpoint of the other two),
            // and a re-export can add or remove more.
            let mut slivers = 0;
            for face in 0..declared {
                let corners = &mesh.positions[face * 3..face * 3 + 3];
                let a = corners[0].map(f64::from);
                let b = corners[1].map(f64::from);
                let c = corners[2].map(f64::from);
                let normals = &mesh.normals[face * 3..face * 3 + 3];
                if length(cross(sub(b, a), sub(c, a))) > 0.0 {
                    for (offset, normal) in normals.iter().enumerate() {
                        let len = length(normal.map(f64::from));
                        assert!(
                            (len - 1.0).abs() < 1e-4,
                            "{path:?} corner {} has a non-unit normal {normal:?}",
                            face * 3 + offset
                        );
                    }
                    continue;
                }
                slivers += 1;
                assert!(
                    normals.iter().all(|normal| *normal == [0.0; 3]),
                    "{path:?} zero-area face {face} should shade with a zero normal, \
                     not {normals:?}"
                );
                for (offset, color) in mesh.colors[face * 3..face * 3 + 3].iter().enumerate() {
                    for (channel, channel_base) in color.iter().zip(base) {
                        let floor = AMBIENT as f32 * channel_base;
                        assert!(
                            (channel - floor).abs() < 1e-6,
                            "{path:?} corner {} of zero-area face {face} should shade at \
                             the ambient floor {floor}, not {color:?}",
                            face * 3 + offset
                        );
                    }
                }
            }
            // Tolerated, not ignored: one collapsed face in 57,000 is a tessellation
            // artifact, while a mesh that is a measurable fraction slivers is an export
            // that went wrong and its shading means nothing.
            assert!(
                slivers * 1000 <= declared,
                "{path:?} is {slivers} zero-area faces out of {declared}"
            );
            for (corner, color) in mesh.colors.iter().enumerate() {
                for (channel, base) in color.iter().zip(base) {
                    assert!(
                        (AMBIENT as f32 * base - 1e-6..=base + 1e-6).contains(channel),
                        "{path:?} corner {corner} has an out of range color {color:?}"
                    );
                }
                assert_eq!(color[3], opacity, "{path:?} corner {corner}");
            }
            checked += 1;
        }
        assert_eq!(checked, 7, "the seven shipped meshes must all be covered");
    }

    #[test]
    fn binary_with_a_solid_header_is_parsed_as_binary() {
        let bytes = synthetic_binary_stl();
        // The trap is live: the header really does look like ASCII.
        assert!(bytes.starts_with(b"solid "));
        assert!(std::str::from_utf8(&bytes[..80]).is_ok());
        assert_eq!(binary_triangle_count(&bytes), Some(1));
        // A header sniff would take the ASCII path here and never find the triangle.
        let naive = match stl_io::read_stl(&mut Cursor::new(bytes.as_slice())) {
            Ok(mesh) => mesh.faces.len() != 1,
            Err(_) => true,
        };
        assert!(
            naive,
            "the sniffing path must not be able to read this file"
        );

        let triangles = parse_stl(&bytes).expect("binary parse");
        assert_eq!(triangles, vec![SYNTHETIC_TRIANGLE]);
    }

    #[test]
    fn binary_with_trailing_bytes_falls_back_to_binary() {
        let mut bytes = synthetic_binary_stl();
        bytes.extend_from_slice(b"junk");
        // Trailing bytes break the exact size test, so this is not classified as
        // binary; the ASCII attempt fails and the forced binary retry rescues it.
        assert_eq!(binary_triangle_count(&bytes), None);
        let triangles = parse_stl(&bytes).expect("binary fallback");
        assert_eq!(triangles, vec![SYNTHETIC_TRIANGLE]);
    }

    #[test]
    fn ascii_stl_is_parsed_as_ascii() {
        let bytes = ASCII_STL.as_bytes();
        // Not 84 + 50 * n, so it must take the ASCII branch.
        assert_eq!(binary_triangle_count(bytes), None);
        let triangles = parse_stl(bytes).expect("ascii parse");
        assert_eq!(triangles.len(), 1);
        assert_eq!(
            triangles[0],
            [[0.0, 0.0, 0.0], [2.0, 0.0, 0.0], [0.0, 2.0, 0.0]]
        );
    }

    #[test]
    fn welding_merges_coincident_corners() {
        let (positions, corner_vertex) = weld_coincident_vertices(&QUAD);
        // Four distinct corners, not the six corners of the soup.
        assert_eq!(positions.len(), 4);
        assert_eq!(positions[0], [0.0, 0.0, 0.0]);
        assert_eq!(positions[1], [1.0, 0.0, 0.0]);
        assert_eq!(positions[2], [1.0, 1.0, 0.0]);
        assert_eq!(positions[3], [0.0, 1.0, 0.0]);
        // Corners 0 and 3 are the same welded vertex, as are 2 and 4.
        assert_eq!(corner_vertex, vec![0, 1, 2, 0, 2, 3]);

        // A flat quad therefore shades as one surface: every face normal is the plane
        // normal, which only holds because the shared corners are welded.
        let normals = smooth_face_normals(&QUAD, &corner_vertex, positions.len());
        assert_eq!(normals.len(), 2);
        assert_eq!(normals[0], [0.0, 0.0, 1.0]);
        assert_eq!(normals[1], [0.0, 0.0, 1.0]);
    }

    #[test]
    fn a_shared_edge_is_smoothed_but_a_crease_is_not() {
        // The free corner stands straight up, so the two planes are exactly 90 apart.
        let sharp = bent_pair([0.0, 0.0, 1.0]);
        let (positions, corner_vertex) = weld_coincident_vertices(&sharp);
        assert_eq!(positions.len(), 4);
        let normals = smooth_face_normals(&sharp, &corner_vertex, positions.len());
        let face_a = only_face_normal(sharp[0]);
        let face_b = only_face_normal(sharp[1]);
        assert_eq!(face_a, [0.0, 0.0, 1.0]);
        assert_eq!(face_b, [0.0, 1.0, 0.0]);
        // 90 degrees apart is well past the 50 degree threshold, so neither face is
        // pulled toward the other: each keeps its own plane.
        assert_eq!(normals[0], face_a);
        assert_eq!(normals[1], face_b);

        let shallow = bent_pair(tilted_apex(8.0));
        let (positions, corner_vertex) = weld_coincident_vertices(&shallow);
        let normals = smooth_face_normals(&shallow, &corner_vertex, positions.len());
        let face_a = only_face_normal(shallow[0]);
        let face_b = only_face_normal(shallow[1]);
        // 8 degrees apart is inside the threshold, so each face leans toward the
        // other one — impossible unless the shared corners were welded.
        assert!(dot(normals[0], face_b) > dot(face_a, face_b));
        assert!(dot(normals[1], face_a) > dot(face_a, face_b));
        assert!(dot(normals[0], face_a) < 1.0);
        assert!(dot(normals[0], face_a) > dot(face_a, face_b));
        assert!(dot(normals[1], face_b) < 1.0);
        assert!(dot(normals[1], face_b) > dot(face_a, face_b));
        // The two faces stay distinct rather than collapsing into one average.
        assert!(dot(normals[0], normals[1]) < 1.0);
    }

    #[test]
    fn flipping_the_winding_keeps_the_illumination() {
        let triangle = [[0.0f32, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.5]];
        let flipped = [triangle[0], triangle[2], triangle[1]];
        let base = [0.8, 0.25, 0.1];

        let forward = build_link_mesh(&[triangle], base, 1.0);
        let backward = build_link_mesh(&[flipped], base, 1.0);
        // `|n . L|` again: the flipped face is lit identically, bit for bit.
        assert_eq!(backward.colors, forward.colors);
        assert_eq!(forward.normals[0], backward.normals[0].map(|c| -c));
        assert!(
            dot(
                only_face_normal(triangle).map(f64::from),
                only_face_normal(flipped).map(f64::from)
            ) < 0.0
        );
    }

    #[test]
    fn a_face_perpendicular_to_the_light_gets_the_ambient_floor() {
        // The normal is (0.45, 0.35, 0), which is exactly perpendicular to the light
        // direction (0.35, -0.45, 0.82): 0.45 * 0.35 - 0.35 * 0.45 = 0.
        let triangle = [[0.0f32, 0.0, 0.0], [0.0, 0.0, 1.0], [0.35, -0.45, 0.0]];
        let base = [0.8, 0.5, 0.2];
        let color = only_face_color(triangle, base);
        for (channel, base) in color.iter().zip(base) {
            assert!(
                (channel - 0.32 * base).abs() < 1e-6,
                "{channel} should be the ambient floor of {base}"
            );
        }
        assert_eq!(color[3], 1.0);
    }

    #[test]
    fn a_face_aligned_with_the_light_gets_the_full_base_color() {
        // Both corners are perpendicular to the light, so the face normal is parallel
        // to it: cross(B, cross(L, B)) = L * |B|^2.
        let triangle = [
            [0.0f32, 0.0, 0.0],
            [0.45, 0.35, 0.0],
            [-0.287, 0.369, 0.325],
        ];
        let base = [0.8, 0.5, 0.2];
        let normal = only_face_normal(triangle);
        assert!(dot(normal, normalize(LIGHT)) > 1.0 - 1e-9, "{normal:?}");
        let color = only_face_color(triangle, base);
        for (channel, base) in color.iter().zip(base) {
            assert!(
                (channel - base).abs() < 1e-6,
                "{channel} should be the full base color {base}"
            );
        }
    }

    #[test]
    fn bounds_union_transform_and_extent() {
        let a = Bounds {
            min: [0.0, 0.0, 0.0],
            max: [2.0, 1.0, 1.0],
        };
        let b = Bounds {
            min: [-1.0, 0.5, 0.0],
            max: [1.0, 3.0, 1.0],
        };
        assert!(!a.is_empty());
        assert!(
            a.union(b)
                == Bounds {
                    min: [-1.0, 0.0, 0.0],
                    max: [2.0, 3.0, 1.0]
                }
        );
        assert_eq!(a.union(b).center(), [0.5, 1.5, 0.5]);
        assert_eq!(a.union(b).size(), [3.0, 3.0, 1.0]);

        // Quarter turn about z, then translate by +5 in x: (x, y, z) -> (5 - y, x, z).
        let rotation = [[0.0, -1.0, 0.0], [1.0, 0.0, 0.0], [0.0, 0.0, 1.0]];
        let turned = a.transformed(rotation, [5.0, 0.0, 0.0]);
        assert_eq!(
            turned,
            Bounds {
                min: [4.0, 0.0, 0.0],
                max: [5.0, 2.0, 1.0]
            }
        );
        assert_eq!(turned.center(), [4.5, 1.0, 0.5]);
        assert_eq!(turned.size(), [1.0, 2.0, 1.0]);

        // The seed is empty, is the identity of `union`, and survives a transform, but
        // the derived `Default` is the degenerate box at the origin.
        assert!(EMPTY_BOUNDS.is_empty());
        assert!(EMPTY_BOUNDS.union(a) == a);
        assert!(
            EMPTY_BOUNDS
                .transformed(rotation, [5.0, 0.0, 0.0])
                .is_empty()
        );
        assert!(!Bounds::default().is_empty());
    }

    #[test]
    fn a_mesh_without_triangles_is_reported_as_empty() {
        // `parse_stl` reports the empty soup, `build_link_mesh` the empty mesh, and
        // `load_link_mesh` the error the caller actually has to handle.
        let triangles = parse_stl(EMPTY_ASCII_STL.as_bytes()).expect("empty soup parses");
        assert!(triangles.is_empty());

        let mesh = build_link_mesh(&[], [1.0, 0.5, 0.25], 1.0);
        assert_eq!(mesh.triangle_count, 0);
        assert!(mesh.positions.is_empty());
        assert!(mesh.normals.is_empty());
        assert!(mesh.colors.is_empty());
        assert!(mesh.indices.is_empty());
        assert!(mesh.bounds.is_empty());

        let path =
            std::env::temp_dir().join(format!("robot_app_mesh_empty_{}.stl", std::process::id()));
        std::fs::write(&path, EMPTY_ASCII_STL).expect("temp file");
        let loaded = load_link_mesh(&path, [1.0, 0.5, 0.25], 1.0);
        let _ = std::fs::remove_file(&path);
        assert!(matches!(loaded, Err(MeshError::Empty)));
    }

    #[test]
    fn a_missing_file_is_an_io_error() {
        let loaded = load_link_mesh(Path::new("robot-app-mesh-missing-file.stl"), [1.0; 3], 1.0);
        assert!(matches!(loaded, Err(MeshError::Io(_))));
    }

    /// The inverse of the transfer function `to_bevy_mesh` applies, which nothing in the
    /// module needs.
    fn linear_to_srgb(channel: f32) -> f32 {
        if channel <= 0.003_130_8 {
            channel * 12.92
        } else {
            1.055 * channel.powf(1.0 / 2.4) - 0.055
        }
    }

    #[test]
    fn bevy_colors_are_linear_light_not_srgb() {
        // One base color above the transfer function's knee and one below it, so both
        // branches are covered.
        for base in [[0.5f32, 0.25, 0.125], [0.02, 0.03, 0.01]] {
            let mesh = build_link_mesh(&QUAD, base, 0.75);
            let bevy_mesh = to_bevy_mesh(&mesh);
            let Some(VertexAttributeValues::Float32x4(colors)) =
                bevy_mesh.attribute(Mesh::ATTRIBUTE_COLOR)
            else {
                panic!("expected float32x4 colors");
            };
            assert_eq!(colors.len(), mesh.colors.len());
            for (converted, baked) in colors.iter().zip(&mesh.colors) {
                // The baked color stays sRGB, so the attribute is a real conversion ...
                assert!((converted[0] - baked[0]).abs() > 1e-3, "{converted:?}");
                for channel in 0..3 {
                    assert!(
                        (linear_to_srgb(converted[channel]) - baked[channel]).abs() < 1e-5,
                        "{converted:?} should round-trip back to {baked:?}"
                    );
                }
                // ... and the alpha passes through untouched.
                assert_eq!(converted[3], baked[3]);
            }
        }
    }

    #[test]
    fn to_bevy_mesh_carries_all_three_attributes() {
        let mesh = build_link_mesh(&QUAD, [0.8, 0.25, 0.25], 0.75);
        let bevy_mesh = to_bevy_mesh(&mesh);
        assert_eq!(
            bevy_mesh.primitive_topology(),
            PrimitiveTopology::TriangleList
        );
        assert_eq!(
            bevy_mesh.attribute(Mesh::ATTRIBUTE_POSITION).unwrap().len(),
            6
        );
        assert_eq!(
            bevy_mesh.attribute(Mesh::ATTRIBUTE_NORMAL).unwrap().len(),
            6
        );
        assert_eq!(bevy_mesh.attribute(Mesh::ATTRIBUTE_COLOR).unwrap().len(), 6);
        assert_eq!(bevy_mesh.count_vertices(), 6);
        match bevy_mesh.indices().unwrap() {
            Indices::U32(indices) => assert_eq!(indices.len(), 6),
            Indices::U16(indices) => panic!("expected u32 indices, got {indices:?}"),
        }
    }
}
