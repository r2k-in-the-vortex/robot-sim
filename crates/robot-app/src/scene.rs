//! The 3D scene: the six-joint frame hierarchy, the link overlays and the reference grid.
//!
//! The entity tree is the DH chain. Frame 0 is the base at the world origin, and joint
//! `i`'s entity is a child of frame `i - 1` carrying the standard-DH transform
//! `Rz θ · Tz d · Tx a · Rx α` as its local [`Transform`]. Bevy's transform propagation
//! then composes the same cumulative tower `carrier_pose` returns, which is what makes a
//! joint jiggle a single write rather than a rebuild of the whole arm.
//!
//! The world is Z-up, matching the DH model, the STL meshes and `simulator.py`'s grid on
//! Z=0 (line 827). See [`crate::camera`] for why Bevy's Y-up habit is not followed.

use bevy::pbr::wireframe::{Wireframe, WireframeColor};
use bevy::prelude::*;
use robot_kinematics::{Pose, units};
use robot_model::{FRAME_COUNT, MeshSettings};

use crate::camera::{self, OrbitCamera};
use crate::mesh::{self, Bounds};
use crate::{RobotState, ViewState};

/// The palette of `simulator.py` line 42, one entry per frame, base first.
const MESH_COLORS: [u32; FRAME_COUNT] = [
    0x536d7a, 0xd94a45, 0x31845b, 0x3978c5, 0xd18b2c, 0x7655a5, 0x278b8b,
];

/// The coordinate-gizmo axis colors, `simulator.py:935`: X red, Y green, Z blue.
const AXIS_COLORS: [u32; 3] = [0xd94a45, 0x31845b, 0x3978c5];

/// The link polyline color, `simulator.py:931`.
const LINK_COLOR: u32 = 0x5c6872;

/// The grid's line color and the mesh edge color, `simulator.py:850` and `:900`.
pub const GRID_COLOR: u32 = 0xcbd5da;
const EDGE_COLOR: u32 = 0x25343b;

/// The color a joint label is painted in, `simulator.py:957`.
pub const LABEL_COLOR: u32 = 0x26323b;

/// The background `simulator.py:872` paints behind the view.
pub const BACKGROUND_COLOR: u32 = 0xf4f6f7;

/// The gizmo length as a fraction of the fitted radius, `simulator.py:936`.
pub const GIZMO_LENGTH_FRACTION: f64 = 0.14;

/// How far above its frame origin a label sits, as a fraction of the gizmo length
/// (`simulator.py:956`: `marker_length * 0.2`).
pub const LABEL_LIFT_FRACTION: f64 = 0.2;

/// A ceiling on how many grid lines one axis may draw.
///
/// `simulator.py:847` has no such guard because matplotlib merely slows down once the
/// range dwarfs the spacing. A gizmo buffer that size stalls the frame instead, and the
/// spacing is fixed by the model's radius while the extent follows the zoom, so a hard
/// zoom-out is enough to reach it.
const MAX_GRID_LINES_PER_AXIS: i64 = 400;

/// One of the seven cumulative frames. Index 0 is the base.
#[derive(Component, Copy, Clone, PartialEq, Eq, Debug)]
pub struct FrameIndex(pub usize);

/// The render entity for one row of the document's `meshes` array.
#[derive(Component, Copy, Clone, PartialEq, Eq, Debug)]
pub struct MeshSlot(pub usize);

/// The render assets behind one configured mesh row, plus the local bounds the view fit
/// needs before the entity has been placed.
pub struct LinkAssets {
    pub mesh: Handle<Mesh>,
    pub material: Handle<StandardMaterial>,
    /// Bounds in the mesh's own units, before the per-frame scale, rotation and offset.
    pub bounds: Bounds,
}

/// The loaded link meshes, re-derived only when a row's asset-affecting fields change.
///
/// `offset` and `rotation_deg` are deliberately absent from the signature: they move the
/// entity, they do not change the asset, so editing either must not reload a
/// multi-megabyte STL.
#[derive(Resource, Default)]
pub struct LinkMeshes {
    slots: Vec<Option<LinkAssets>>,
    signature: Option<u64>,
    /// The status `simulator.py:962-965` shows under the view.
    pub status: String,
}

impl LinkMeshes {
    pub fn get(&self, slot: usize) -> Option<&LinkAssets> {
        self.slots.get(slot).and_then(Option::as_ref)
    }
}

/// The uniform scale applied to a loaded STL.
///
/// The document carries no scale field, but the shipped meshes are not in the model's own
/// units: measured over `mesh/`, they span up to 640 units, while the shipped DH table puts
/// the whole arm inside roughly 80. `simulator.py` places the raw STL coordinates and lets
/// the camera fit absorb the difference (lines 908-919), which is why the reference view
/// frames a bounding box several times larger than the arm. A tenth brings a mesh into the
/// model's range, and is the millimetre-to-model-unit ratio the part numbering implies.
///
/// The placement is still `p_world = R_frame · (R_local · (s·p) + offset) + origin`; only
/// `offset` is in model units, because the README documents the mesh offsets alongside `d`
/// and `a`.
pub const MESH_UNIT_SCALE: f32 = 0.1;

/// Spawn the seven frame entities and their mesh children, once at startup.
///
/// Frame 0 carries no joint: the base frame *is* the base, so it sits at the world origin
/// and never moves. That is the `(None,) + transforms` pairing of `simulator.py:866-867`.
pub fn build_scene(mut commands: Commands) {
    let mut parent = Entity::PLACEHOLDER;
    for frame in 0..FRAME_COUNT {
        let entity = commands
            .spawn((
                FrameIndex(frame),
                Transform::default(),
                Visibility::default(),
                Name::new(format!("frame {frame}")),
            ))
            .id();
        if frame > 0 {
            commands.entity(entity).insert(ChildOf(parent));
        }
        parent = entity;

        commands.spawn((
            MeshSlot(frame),
            ChildOf(entity),
            Transform::default(),
            Visibility::default(),
            Name::new(format!("mesh {frame}")),
        ));
    }
}

/// Drive the six joint entities from the runtime angles.
///
/// Each joint writes only its own local transform, so the whole arm follows from Bevy's
/// propagation. The static theta offset is folded in here, which is the
/// `compose_dh_parameters` boundary `kinematics.py` draws: the kinematics core only ever
/// sees total DH angles.
pub fn sync_joints(robot: Res<RobotState>, mut frames: Query<(&FrameIndex, &mut Transform)>) {
    for (index, mut transform) in &mut frames {
        let FrameIndex(frame) = *index;
        if frame == 0 {
            // The base frame is the world origin, so there is no joint transform to apply.
            continue;
        }
        let row = robot.document.parameters.joints[frame - 1];
        let pose = Pose::dh(
            units::total_angle(row.theta_offset_deg, robot.runtime_angles_deg[frame - 1]),
            row.d,
            row.a,
            units::deg_to_rad(row.alpha_deg),
        );
        *transform = pose_to_transform(pose);
    }
}

/// Place each configured mesh under its frame, loading the ones whose assets changed.
pub fn sync_meshes(
    mut commands: Commands,
    robot: Res<RobotState>,
    mut link_meshes: ResMut<LinkMeshes>,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<StandardMaterial>>,
    mut slots: Query<(
        Entity,
        &MeshSlot,
        &mut Transform,
        &mut Visibility,
        Option<&Mesh3d>,
    )>,
) {
    if let Some(signature) = mesh_signature(&robot.document.meshes)
        && link_meshes.signature != Some(signature)
    {
        let (loaded, errors) = load_all(&robot.document.meshes, &mut meshes, &mut materials);
        link_meshes.slots = loaded;
        link_meshes.signature = Some(signature);
        link_meshes.status = status_line(&robot.document.meshes, &errors);
    }

    for (entity, slot, mut transform, mut visibility, existing) in &mut slots {
        let Some(setting) = robot.document.meshes.get(slot.0) else {
            continue;
        };
        *transform = mesh_transform(setting);
        match link_meshes.get(slot.0) {
            Some(assets) => {
                *visibility = Visibility::Visible;
                if existing.is_none() {
                    commands.entity(entity).insert((
                        Mesh3d(assets.mesh.clone()),
                        MeshMaterial3d(assets.material.clone()),
                    ));
                }
            }
            None => *visibility = Visibility::Hidden,
        }
    }
}

/// Track `show_mesh_edges` on the mesh entities.
///
/// The wireframe pass is Bevy's, added explicitly in `main.rs` because `DefaultPlugins`
/// does not include it. `simulator.py:900` draws the same thing as a 0.25-pixel
/// `edgecolors` overlay; the color and the triangle topology match, the width is Bevy's
/// screen-space one.
pub fn sync_mesh_edges(
    robot: Res<RobotState>,
    mut commands: Commands,
    slots: Query<(Entity, &MeshSlot, Option<&Wireframe>)>,
) {
    if !robot.is_changed() {
        return;
    }
    for (entity, slot, wireframe) in &slots {
        let wanted = robot.document.show_mesh_edges
            && robot
                .document
                .meshes
                .get(slot.0)
                .is_some_and(MeshSettings::is_drawn);
        let mut entity_commands = commands.entity(entity);
        match (wanted, wireframe.is_some()) {
            (true, false) => {
                entity_commands.insert((
                    Wireframe,
                    WireframeColor {
                        color: color(EDGE_COLOR),
                    },
                ));
            }
            (false, true) => {
                entity_commands.remove::<Wireframe>();
            }
            _ => {}
        }
    }
}

/// Draw everything that is not a mesh: the link polyline, the per-frame coordinate gizmos
/// and the scale-adaptive XY grid.
pub fn draw_overlays(
    robot: Res<RobotState>,
    view: Res<ViewState>,
    frames: Query<(&FrameIndex, &GlobalTransform)>,
    mut gizmos: Gizmos,
) {
    let Some((origins, rotations)) = frame_poses(&frames) else {
        // `build_scene` spawns the frame entities; until it has run there is nothing to
        // draw.
        return;
    };

    // The fitted radius, not the current half-span: `simulator.py:836` derives the grid
    // step from the model's size, so zooming moves the grid's extent without
    // retessellating it.
    draw_grid(&mut gizmos, &view.camera, view.grid_radius);

    gizmos.linestrip(origins, color(LINK_COLOR));

    let marker_length = (view.grid_radius * GIZMO_LENGTH_FRACTION) as f32;
    for (frame, origin) in origins.iter().enumerate() {
        if !robot
            .document
            .show_coordinate_gizmos
            .get(frame)
            .copied()
            .unwrap_or(false)
        {
            continue;
        }
        let basis = rotations[frame];
        for (axis, axis_color) in AXIS_COLORS.iter().enumerate() {
            gizmos.line(
                *origin,
                *origin + basis[axis] * marker_length,
                color(*axis_color),
            );
        }
    }
}

/// The union of every frame origin and every placed mesh box, which is what
/// `simulator.py:908-913` frames.
///
/// The meshes contribute their *placed* boxes: `Bounds::transformed` puts a link's local
/// box through the mesh entity's whole `GlobalTransform`, which already carries its
/// parent frame's pose, so a rotated link is framed by what it covers rather than by the
/// box it started from.
///
/// Frame origins are in the union unconditionally, because `build_scene` always spawns
/// them; the base at the world origin is `simulator.py:908`'s hard-coded `(0, 0, 0)`.
pub fn scene_bounds(
    frames: &Query<(&FrameIndex, &GlobalTransform)>,
    slots: &Query<(&MeshSlot, &GlobalTransform)>,
    link_meshes: &LinkMeshes,
) -> Bounds {
    let mut bounds = empty_bounds();
    for (_, transform) in frames {
        bounds = bounds.union(point_bounds(transform.translation().to_array()));
    }
    for (slot, transform) in slots {
        let Some(assets) = link_meshes.get(slot.0) else {
            continue;
        };
        bounds = bounds.union(placed_bounds(assets.bounds, transform));
    }
    bounds
}

/// The scene's current extents, recomputed once a frame after transform propagation.
#[derive(Resource)]
pub struct SceneBounds(pub Bounds);

impl Default for SceneBounds {
    /// The empty box, not `Bounds::default()`'s degenerate box at the origin: a fit that
    /// somehow ran before the first measurement then frames nothing, rather than framing a
    /// speck at the world origin and throwing the view somewhere unrelated.
    fn default() -> Self {
        Self(empty_bounds())
    }
}

/// Measure the scene. Runs after propagation, so the mesh entities have their real world
/// transforms, and after [`sync_meshes`], so a freshly loaded mesh is already in
/// [`LinkMeshes`].
pub fn refresh_scene_bounds(
    frames: Query<(&FrameIndex, &GlobalTransform)>,
    slots: Query<(&MeshSlot, &GlobalTransform)>,
    link_meshes: Res<LinkMeshes>,
    mut bounds: ResMut<SceneBounds>,
) {
    bounds.0 = scene_bounds(&frames, &slots, &link_meshes);
}

/// Apply a pending fit request.
///
/// The request is a flag rather than a direct call because the scene's size is only known
/// a frame in: the frame entities come from startup commands and the meshes are loaded the
/// first time [`sync_meshes`] sees them, both after startup itself. `grid_radius` is
/// updated with it so the grid and the view volume always describe the same scene
/// (`simulator.py:920-926` feeds the grid from the same fitted radius as the span).
pub fn apply_fit(mut view: ResMut<ViewState>, bounds: Res<SceneBounds>) {
    if !view.fit_requested {
        return;
    }
    view.fit_requested = false;
    view.camera.fit(bounds.0);
    view.grid_radius = camera::fit_radius(bounds.0);
}

// ---------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------

/// The frame origins and their rotation columns, ordered by frame index.
///
/// Returns `None` until every frame entity exists, so a caller cannot silently draw a
/// half-built arm.
#[allow(clippy::type_complexity)]
fn frame_poses(
    frames: &Query<(&FrameIndex, &GlobalTransform)>,
) -> Option<([Vec3; FRAME_COUNT], [[Vec3; 3]; FRAME_COUNT])> {
    let mut origins = [Vec3::ZERO; FRAME_COUNT];
    let mut rotations = [[Vec3::X, Vec3::Y, Vec3::Z]; FRAME_COUNT];
    let mut seen = [false; FRAME_COUNT];
    for (index, transform) in frames {
        let FrameIndex(frame) = *index;
        if frame >= FRAME_COUNT {
            continue;
        }
        origins[frame] = transform.translation();
        let rotation = transform.rotation();
        // The frame's own axes, which are the columns of its rotation. `Transform::forward`
        // would be the *negated* z axis, and the reference draws the z column
        // (`simulator.py:940-944`), so the columns are read directly.
        rotations[frame] = [rotation * Vec3::X, rotation * Vec3::Y, rotation * Vec3::Z];
        seen[frame] = true;
    }
    seen.iter()
        .all(|present| *present)
        .then_some((origins, rotations))
}

/// The scale-adaptive XY grid on the Z=0 plane, `simulator.py:827-856`.
fn draw_grid(gizmos: &mut Gizmos, camera: &OrbitCamera, radius: f64) {
    let spacing = camera::grid_spacing(radius);
    if !spacing.is_finite() || spacing <= 0.0 {
        return;
    }
    let half = camera.half_span;
    for axis in 0..2 {
        let from = camera.target[axis] - half;
        let to = camera.target[axis] + half;
        let (mut first, mut last) = camera::grid_line_indices(from, to, spacing);
        if last - first > MAX_GRID_LINES_PER_AXIS {
            // Keep the lines around the view center rather than the low end of the range.
            let middle = first / 2 + last / 2;
            first = middle - MAX_GRID_LINES_PER_AXIS / 2;
            last = first + MAX_GRID_LINES_PER_AXIS;
        }
        for index in first..=last {
            let value = index as f64 * spacing;
            let (start, end) = if axis == 0 {
                // A line of constant x, running the full y extent.
                (
                    Vec3::new(value as f32, from as f32, 0.0),
                    Vec3::new(value as f32, to as f32, 0.0),
                )
            } else {
                // A line of constant y, running the full x extent.
                (
                    Vec3::new(from as f32, value as f32, 0.0),
                    Vec3::new(to as f32, value as f32, 0.0),
                )
            };
            gizmos.line(start, end, color(GRID_COLOR));
        }
    }
}

/// The local transform of a mesh under its frame, per [`MESH_UNIT_SCALE`].
fn mesh_transform(setting: &MeshSettings) -> Transform {
    let rotation = setting.local_rotation();
    let column = |j: usize| {
        Vec3::new(
            rotation[0][j] as f32,
            rotation[1][j] as f32,
            rotation[2][j] as f32,
        )
    };
    Transform::from_rotation(Quat::from_mat3(&Mat3::from_cols(
        column(0),
        column(1),
        column(2),
    )))
    .with_translation(Vec3::new(
        setting.offset[0] as f32,
        setting.offset[1] as f32,
        setting.offset[2] as f32,
    ))
    .with_scale(Vec3::splat(MESH_UNIT_SCALE))
}

/// A mesh entity's local box placed in the world.
///
/// `Bounds::transformed` models rotation and translation but not the uniform
/// [`MESH_UNIT_SCALE`], so the scale is folded into the box first. Every mesh transform
/// this module builds uses a splat scale, so one component carries it.
fn placed_bounds(local: Bounds, global: &GlobalTransform) -> Bounds {
    if local.is_empty() {
        return local;
    }
    let (scale, rotation, translation) = global.to_scale_rotation_translation();
    let scaled = Bounds {
        min: local.min.map(|axis| axis * scale.x),
        max: local.max.map(|axis| axis * scale.x),
    };
    scaled.transformed(rotation_rows(rotation), translation.to_array())
}

/// A rotation as the row-major rows `Bounds::transformed` wants.
///
/// The columns come free from the basis vectors; the rows are their transposition, so
/// building them out of `q * basis` keeps the convention from being a guess.
fn rotation_rows(rotation: Quat) -> [[f32; 3]; 3] {
    let x = (rotation * Vec3::X).to_array();
    let y = (rotation * Vec3::Y).to_array();
    let z = (rotation * Vec3::Z).to_array();
    [[x[0], y[0], z[0]], [x[1], y[1], z[1]], [x[2], y[2], z[2]]]
}

/// The empty box, the identity for `Bounds::union`. `Bounds::default()` is the degenerate
/// box at the origin instead, which would drag every union toward the origin.
fn empty_bounds() -> Bounds {
    Bounds {
        min: [f32::INFINITY; 3],
        max: [f32::NEG_INFINITY; 3],
    }
}

/// A degenerate box around one point.
fn point_bounds(point: [f32; 3]) -> Bounds {
    Bounds {
        min: point,
        max: point,
    }
}

/// A `Pose<f64>` as a Bevy transform. The rotation block is orthonormal by construction
/// (`fk_R_orth`), which is what `Quat::from_mat3` requires.
fn pose_to_transform(pose: Pose<f64>) -> Transform {
    let r = pose.r;
    let column = |j: usize| Vec3::new(r.at(0, j) as f32, r.at(1, j) as f32, r.at(2, j) as f32);
    Transform::from_rotation(Quat::from_mat3(&Mat3::from_cols(
        column(0),
        column(1),
        column(2),
    )))
    .with_translation(Vec3::new(
        pose.p.x() as f32,
        pose.p.y() as f32,
        pose.p.z() as f32,
    ))
}

/// Load every configured row, keeping the ones that failed out of the result and
/// collecting their errors for the status line.
fn load_all(
    settings: &[MeshSettings],
    meshes: &mut Assets<Mesh>,
    materials: &mut Assets<StandardMaterial>,
) -> (Vec<Option<LinkAssets>>, Vec<String>) {
    let mut slots = Vec::with_capacity(settings.len());
    let mut errors = Vec::new();
    for (index, setting) in settings.iter().enumerate() {
        if !setting.is_drawn() {
            slots.push(None);
            continue;
        }
        match mesh::load_link_mesh(
            std::path::Path::new(&setting.path),
            srgb_floats(MESH_COLORS[index % MESH_COLORS.len()]),
            setting.opacity as f32,
        ) {
            Ok(loaded) => {
                slots.push(Some(LinkAssets {
                    mesh: meshes.add(mesh::to_bevy_mesh(&loaded)),
                    material: materials.add(link_material(setting.opacity as f32)),
                    bounds: loaded.bounds,
                }));
            }
            Err(error) => {
                errors.push(format!(
                    "{}: {error}",
                    robot_model::MESH_FRAME_NAMES
                        .get(index)
                        .copied()
                        .unwrap_or("?")
                ));
                slots.push(None);
            }
        }
    }
    (slots, errors)
}

/// The material every link shares, apart from the baked vertex colors.
///
/// `bevy_pbr`'s fragment shader *replaces* the base color with the vertex color when the
/// mesh carries `ATTRIBUTE_COLOR`, so the per-face two-sided Lambert of
/// `_two_sided_face_colors` is baked into the mesh and the material only has to not fight
/// it: `unlit` keeps the renderer's own lighting out of the result, and the camera's
/// `Tonemapping::None` keeps the tone curve out of it, so what reaches the screen is the
/// color the Python computed.
fn link_material(opacity: f32) -> StandardMaterial {
    StandardMaterial {
        base_color: Color::WHITE,
        unlit: true,
        // `cull_mode: None` is the two-sided half of the shading; the `|n·L|` half is
        // already baked per face.
        cull_mode: None,
        double_sided: true,
        alpha_mode: if opacity >= 1.0 {
            AlphaMode::Opaque
        } else {
            AlphaMode::Blend
        },
        ..default()
    }
}

/// `simulator.py:962-965`: either the failed rows by name, or how many are configured.
fn status_line(settings: &[MeshSettings], errors: &[String]) -> String {
    if errors.is_empty() {
        let loaded = settings.iter().filter(|setting| setting.is_drawn()).count();
        format!("{loaded} mesh(es) configured.")
    } else {
        format!("Mesh load issue: {}", errors.join("; "))
    }
}

/// A hash of the row fields that change the loaded assets.
fn mesh_signature(settings: &[MeshSettings]) -> Option<u64> {
    if settings.is_empty() {
        return None;
    }
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for setting in settings {
        setting.path.hash(&mut hasher);
        setting.opacity.to_bits().hash(&mut hasher);
    }
    Some(hasher.finish())
}

/// A hex literal as a Bevy color.
pub fn color(hex: u32) -> Color {
    let (r, g, b) = rgb(hex);
    Color::srgb_u8(r, g, b)
}

/// A hex literal as the sRGB triple the shading math wants.
const fn srgb_floats(hex: u32) -> [f32; 3] {
    let (r, g, b) = rgb(hex);
    [r as f32 / 255.0, g as f32 / 255.0, b as f32 / 255.0]
}

/// A hex literal as its sRGB channels, for the consumers that are not Bevy colors — the
/// egui labels take a `Color32`.
pub const fn rgb(hex: u32) -> (u8, u8, u8) {
    (
        ((hex >> 16) & 0xff) as u8,
        ((hex >> 8) & 0xff) as u8,
        (hex & 0xff) as u8,
    )
}
