//! The 6-axis robot simulator: a Bevy window with an orthographic 3D view of the DH chain
//! and an egui shell around it.
//!
//! The window is the reference's (`simulator.py:168-170`): "6-Axis Robot Simulator",
//! 1120x760, no smaller than 820x600. Inside it are the reference's two tabs
//! (`simulator.py:186-189`) — the 3D view and the parameter pages — plus the Motion tab,
//! which keeps the 3D view in its central rect and adds the command editor, queue and
//! planned-motion graphs around it. The UI itself lives in [`ui`]; this module is the
//! wiring — the resources the view and the shell share, the two cameras, and the order the
//! systems run in.
//!
//! # The two cameras
//!
//! egui's own camera and the robot's camera are deliberately separate. bevy_egui sizes
//! egui's `screen_rect` from the viewport of whichever camera carries
//! [`PrimaryEguiContext`], and the egui render pass scissors to that same rect, so a
//! camera whose viewport is the 3D view's rect would clip the UI to it. Instead the 3D
//! camera takes the UI's leftover rect as its viewport and the egui camera spans the whole
//! window, rendering nothing but the UI (`RenderLayers::none()`) on top of it. That is the
//! arrangement of bevy_egui's own `side_panel` example.

mod camera;
mod dialogs;
mod jog;
mod mesh;
mod motion;
mod motion_linear;
mod motion_ui;
mod pyformat;
mod scene;
mod session;
mod solve;
mod ui;

use bevy::camera::visibility::RenderLayers;
use bevy::camera::{CameraOutputMode, ScalingMode, Viewport as CameraViewport};
use bevy::input::mouse::{MouseScrollUnit, MouseWheel};
use bevy::pbr::wireframe::WireframePlugin;
use bevy::prelude::*;
use bevy::render::render_resource::BlendState;
use bevy::render::view::{DebandDither, Tonemapping};
use bevy::window::{PrimaryWindow, WindowResolution};
use bevy_egui::{
    EguiGlobalSettings, EguiPlugin, EguiPostUpdateSet, EguiPrimaryContextPass, PrimaryEguiContext,
    egui,
};

use camera::OrbitCamera;
use mesh::Bounds;
use robot_kinematics::JOINT_COUNT;
use robot_model::Document;
use scene::{LinkMeshes, SceneBounds};
use ui::{ParameterTab, Tab, Viewport};

/// How far the camera stands from its target, in half-spans of the view volume.
///
/// An orthographic camera's distance only decides where its clip slab sits, so this is not
/// a framing choice: it is the offset that puts the whole scene in front of the near
/// plane. Keeping it proportional to the half-span means zooming never changes the
/// framing.
const CAMERA_DISTANCE_SPANS: f64 = 4.0;

/// How far the clip slab reaches either side of the camera, in half-spans.
///
/// The fitted scene is bounded by `camera::fit_radius`, which [`OrbitCamera::fit`] turns
/// into a half-span with a 45% margin, so nothing the fit can frame extends more than
/// about 0.7 half-spans along the view axis from the target — comfortably inside the slab.
const CAMERA_CLIP_SPANS: f64 = 8.0;

/// Scroll units in one wheel notch, for the platforms that report lines rather than the
/// 120-unit deltas `simulator.py:1094` divides by.
const WHEEL_UNITS_PER_LINE: f64 = 120.0;

/// A nominal line height for precision-touchpad scrolls, which report pixels.
const PIXELS_PER_WHEEL_LINE: f64 = 50.0;

/// Everything the scene draws: the parameter document and the six runtime joint angles.
///
/// The angles are the editable half — the jog controls write them — and they start at zero,
/// the pose the reference opens in. Writing the resource is what drives the arm;
/// [`scene::sync_joints`] reads it every frame.
///
/// The angles are **continuous**, not folded into a single turn. A joint jog accumulates
/// (`joint_angles[joint_index] += direction * step`, `simulator.py:335`) and the joint keeps
/// what it wound, so J6 can sit at 400°: that really is a whole turn further round than 40°,
/// a Cartesian jog from there moves it a little instead of spinning it back, and the turn
/// count is what the UI annotates beside the angle ([`session::wound_turns`]).
///
/// The angles are held at **full precision**; the DH page's angle fields only ever render
/// them at display precision, and [`session::Session::read_joint_angles`] decides whether a
/// field still means the stored angle or a typed-in one. Saving never writes them: see
/// [`session::Session::save_json`].
#[derive(Resource)]
pub struct RobotState {
    pub document: Document,
    pub runtime_angles_deg: [f64; JOINT_COUNT],
}

impl Default for RobotState {
    fn default() -> Self {
        Self {
            document: Document::shipped(),
            runtime_angles_deg: [0.0; JOINT_COUNT],
        }
    }
}

/// Where the 3D view is looking, and what it framed the last time it fit.
///
/// `grid_radius` is the fitted radius rather than the half-span, because the grid takes its
/// spacing from it (`simulator.py:920-926`) and the two have to describe the same scene.
/// `fit_requested` is a flag rather than a call because the scene's size is only known a
/// frame after its entities exist; see [`scene::apply_fit`].
#[derive(Resource)]
pub struct ViewState {
    pub camera: OrbitCamera,
    pub grid_radius: f64,
    pub fit_requested: bool,
}

impl Default for ViewState {
    fn default() -> Self {
        Self {
            camera: OrbitCamera::isometric(),
            // The degenerate scene: what a fit of "nothing measured yet" produces. The
            // startup fit overwrites it before the first frame is drawn.
            grid_radius: camera::fit_radius(Bounds::default()),
            fit_requested: true,
        }
    }
}

/// The camera that renders the robot, as opposed to the one that renders the UI.
#[derive(Component)]
struct SceneCamera;

/// The drag being held, mirroring `simulator.py`'s `_drag_button` and
/// `_last_mouse_position` (`:1042-1050`).
#[derive(Default)]
struct DragState {
    button: Option<MouseButton>,
    last: Option<Vec2>,
}

fn main() -> AppExit {
    let mut app = App::new();

    app.add_plugins((
        DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "6-Axis Robot Simulator".into(),
                // tkinter's `geometry("1120x760")` is in logical pixels and
                // `WindowResolution` is in physical ones; the two agree at the reference's
                // 100% display scale, and the minimum size below is logical either way.
                resolution: WindowResolution::new(1120, 760),
                resize_constraints: WindowResizeConstraints {
                    min_width: 820.0,
                    min_height: 600.0,
                    ..default()
                },
                ..default()
            }),
            ..default()
        }),
        // The link edges of `show_mesh_edges`. Only entities carrying a `Wireframe`
        // component are drawn, which is what `scene::sync_mesh_edges` toggles.
        WireframePlugin::default(),
        EguiPlugin::default(),
    ));

    // Must precede `setup_primary_egui_context_system`, which runs in `PreStartup` and
    // again in the first `PreUpdate` and claims the first camera it finds. Setting it
    // inside a startup system would race that first run: `PreStartup` goes first.
    app.world_mut()
        .resource_mut::<EguiGlobalSettings>()
        .auto_create_primary_context = false;

    // The startup configuration load (`simulator.py:211-223`). It happens here rather than in
    // a startup system because the scene's first frame already needs the document, and
    // because a file the reference would have refused is reported through the same messagebox
    // the UI draws ([`session::Session::notice`]) instead of being raised into a handler.
    let (session, document, angles) = session::Session::start();

    app.insert_resource(ClearColor(scene::color(scene::BACKGROUND_COLOR)))
        .insert_resource(RobotState {
            document,
            runtime_angles_deg: angles,
        })
        .insert_resource(session)
        .init_resource::<ViewState>()
        .init_resource::<Tab>()
        .init_resource::<ParameterTab>()
        .init_resource::<Viewport>()
        .init_resource::<LinkMeshes>()
        .init_resource::<SceneBounds>()
        .init_resource::<motion::MotionRuntime>();

    app.add_systems(Startup, (setup_cameras, scene::build_scene));

    app.add_systems(
        Update,
        (
            camera_input,
            // Playback writes the runtime angles; the scene has to read them in the same
            // frame or the arm trails its graph cursor by one.
            motion::advance_motion.before(scene::sync_joints),
            scene::sync_joints,
            scene::sync_meshes,
            scene::sync_mesh_edges,
        ),
    );

    // The camera and the overlays read the frame origins, which only exist once Bevy has
    // propagated the joint transforms. `Propagate` runs in `PostUpdate`, so everything
    // downstream of it does too — and `draw_overlays` still lands well before the gizmos
    // are collected in `Last`.
    app.add_systems(
        PostUpdate,
        (
            scene::refresh_scene_bounds,
            scene::apply_fit,
            update_camera,
            scene::draw_overlays,
        )
            .chain()
            .after(TransformSystems::Propagate)
            // Published by the egui pass, one frame behind the layout that produced it.
            // Running first means the camera always reads the current frame's panels.
            .before(EguiPostUpdateSet::EndPass),
    );

    // `EguiPrimaryContextPass` is not a schedule of its own: bevy_egui runs it from
    // `PostUpdate`, inside `EguiPostUpdateSet::EndPass`.
    app.add_systems(EguiPrimaryContextPass, ui::draw_shell);

    app.run()
}

/// Spawn the robot's camera and the UI's, once.
fn setup_cameras(mut commands: Commands) {
    commands.spawn((
        Name::new("robot camera"),
        SceneCamera,
        Camera3d::default(),
        Camera {
            // Drawn first, then the UI over it.
            order: 0,
            ..default()
        },
        Projection::Orthographic(OrthographicProjection {
            scaling_mode: ScalingMode::FixedVertical {
                viewport_height: (2.0 * OrbitCamera::isometric().half_span) as f32,
            },
            ..OrthographicProjection::default_3d()
        }),
        // The face colors are baked as display-referred sRGB (`mesh.rs`), so the tone
        // curve has to stay out of the way for them to reach the screen unchanged.
        // Dithering is the one thing `None` cannot do, and `Camera3d` turns it on by
        // default; leaving it on would only draw noise into a flat-shaded picture.
        Tonemapping::None,
        DebandDither::Disabled,
        Transform::from_translation(Vec3::new(10.0, -10.0, 10.0)).looking_at(Vec3::ZERO, Vec3::Z),
    ));

    // The UI camera covers the whole window and draws nothing but the UI, so egui's
    // screen rect is the window even while the robot camera renders a sub-rect of it.
    commands.spawn((
        Name::new("ui camera"),
        PrimaryEguiContext,
        Camera2d,
        RenderLayers::none(),
        Camera {
            order: 1,
            output_mode: CameraOutputMode::Write {
                blend_state: Some(BlendState::ALPHA_BLENDING),
                clear_color: ClearColorConfig::None,
            },
            clear_color: ClearColorConfig::Custom(Color::NONE),
            ..default()
        },
    ));
}

/// Place the robot camera and size its view volume.
///
/// The projection does the framing and the camera only sits on the orbit sphere, so a
/// zoom changes the volume rather than the camera's distance and a pan moves the scene
/// under a camera that keeps pointing at it. The window is centered on the target by
/// default, which is what makes those two agree with the reference's axis-limit edits
/// (`simulator.py:1069-1116`).
///
/// The viewport is the leftover rect the UI pass measured ([`Viewport`]), held inside the
/// window's own physical size on the way in: wgpu validates a camera viewport against the
/// render target rather than clipping it, and this rect is a frame old by the time it gets
/// here.
fn update_camera(
    view: Res<ViewState>,
    viewport: Res<Viewport>,
    window: Single<&Window, With<PrimaryWindow>>,
    mut camera: Single<(&mut Transform, &mut Projection, &mut Camera), With<SceneCamera>>,
) {
    let (transform, projection, camera) = &mut *camera;
    let orbit = view.camera;

    // A zero size is the first frame, before the UI has measured its panels: the camera
    // keeps the window-sized viewport it started with rather than a degenerate rect.
    if viewport.physical_size.x > 0 && viewport.physical_size.y > 0 {
        // The rect was measured against the window as it stood when the UI pass laid its
        // panels out, so a resize since then — a maximize, a restore, a drag — leaves it
        // describing the old window for this frame. wgpu validates the viewport against
        // the target this frame actually renders into and rejects a rect that overhangs it
        // rather than clipping it, which quits the app; holding the rect inside the
        // window's own size is what makes the stale frame harmless.
        let target = window.physical_size();
        let position = viewport.physical_position.min(target);
        let far = viewport
            .physical_position
            .saturating_add(viewport.physical_size)
            .min(target);
        let size = far.saturating_sub(position);
        // A rect the window holds none of — panels taller than a very small window — leaves
        // the camera on the whole target rather than handing the renderer an empty viewport.
        camera.viewport = (size.x > 0 && size.y > 0).then_some(CameraViewport {
            physical_position: position,
            physical_size: size,
            ..default()
        });
    }

    let direction = Vec3::from_array(orbit.view_direction().map(|component| component as f32));
    let eye = Vec3::from_array(
        orbit
            .eye(CAMERA_DISTANCE_SPANS * orbit.half_span)
            .map(|c| c as f32),
    );
    **transform = Transform::from_translation(eye);
    // `look_to` aims the camera's forward axis (-Z) along the direction it is given; the
    // world's +Z is the reference's up (`simulator.py:863-864`, matplotlib's `view_init`
    // default), so the horizon stays level however far the elevation is dragged.
    transform.look_to(-direction, Vec3::Z);

    if let Projection::Orthographic(orthographic) = &mut **projection {
        orthographic.scaling_mode = ScalingMode::FixedVertical {
            viewport_height: (2.0 * orbit.half_span) as f32,
        };
        // An orthographic camera has no perspective divide, so `near` and `far` are plain
        // view-space depths and a negative `near` is legal — it is what lets geometry
        // behind the camera's position still be inside the volume.
        orthographic.near = ((CAMERA_DISTANCE_SPANS - CAMERA_CLIP_SPANS) * orbit.half_span) as f32;
        orthographic.far = ((CAMERA_DISTANCE_SPANS + CAMERA_CLIP_SPANS) * orbit.half_span) as f32;
    }
}

/// Orbit, pan and zoom from the mouse.
///
/// The reference binds these to the 3D axes (`simulator.py:1042-1103`): a press only starts
/// a drag inside it, the drag then survives leaving it, and the release ends it whether or
/// not the button is still over the view. The one substitution is the wheel denominator: a
/// drag's pixel is a pixel in both, but the reference divides the pan by
/// `min(bbox.width, bbox.height)` (`:1072`) while an orthographic projection with a fixed
/// vertical span pins the *height* to the view volume, so the height is what keeps a drag
/// matched to the scene under it.
///
/// The parameter pages cover the 3D view without resizing it, so a drag there would
/// otherwise spin a camera nobody can see: the reference's canvas is unmapped on the
/// Parameters tab and gets no events at all, which is the behavior reproduced by the
/// [`Tab`] guard.
fn camera_input(
    buttons: Res<ButtonInput<MouseButton>>,
    mut wheel: MessageReader<MouseWheel>,
    window: Single<&Window, With<PrimaryWindow>>,
    viewport: Res<Viewport>,
    tab: Res<Tab>,
    mut view: ResMut<ViewState>,
    mut drag: Local<DragState>,
) {
    let cursor = window.cursor_position();
    // The Motion tab keeps the 3D view in its central rect, so its camera is draggable
    // too. Parameters covers the view and still refuses input.
    let in_view = |point: Vec2| {
        matches!(*tab, Tab::View | Tab::Motion)
            && viewport.points.contains(egui::pos2(point.x, point.y))
    };

    match drag.button {
        // The button is what ends the drag, not the position: `_on_mouse_release`
        // (`simulator.py:1047-1049`) never looks at where the cursor was.
        Some(button) if !buttons.pressed(button) => {
            *drag = DragState::default();
        }
        Some(_) => {}
        None => {
            for button in [MouseButton::Left, MouseButton::Right] {
                if buttons.just_pressed(button) && cursor.is_some_and(in_view) {
                    drag.button = Some(button);
                    drag.last = cursor;
                    break;
                }
            }
        }
    }

    if let (Some(button), Some(last), Some(now)) = (drag.button, drag.last, cursor) {
        drag.last = Some(now);
        let delta = now - last;
        if delta != Vec2::ZERO {
            let delta_x = f64::from(delta.x);
            let delta_y = f64::from(delta.y);
            match button {
                MouseButton::Left => view.camera.orbit(delta_x, delta_y),
                MouseButton::Right => {
                    view.camera
                        .pan(delta_x, delta_y, f64::from(viewport.points.height()))
                }
                _ => {}
            }
        }
    }

    // The reference's wheel handler is bound to the canvas, not to the axes, but zooming
    // while the pointer is off the view would fight the side panel's own scrolling.
    let mut delta = 0.0;
    for event in wheel.read() {
        if !cursor.is_some_and(in_view) {
            continue;
        }
        delta += f64::from(event.y)
            * match event.unit {
                // winit reports lines where tkinter reports deltas 120 apart.
                MouseScrollUnit::Line => WHEEL_UNITS_PER_LINE,
                MouseScrollUnit::Pixel => WHEEL_UNITS_PER_LINE / PIXELS_PER_WHEEL_LINE,
            };
    }
    // A zero delta is the empty wheel event `simulator.py:1093` drops.
    view.camera.wheel_zoom(delta);
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::{Mat3 as KinMat3, Pose};
    use robot_model::FRAME_COUNT;

    /// The Bevy rotation whose columns are the kinematics core's.
    fn rotation(kin: &KinMat3<f64>) -> Mat3 {
        let column = |index: usize| {
            Vec3::new(
                kin.at(0, index) as f32,
                kin.at(1, index) as f32,
                kin.at(2, index) as f32,
            )
        };
        Mat3::from_cols(column(0), column(1), column(2))
    }

    /// The angles the tree test drives the arm to, chosen off a joint limit and off zero
    /// on every axis so a transposed or dropped joint cannot pass by symmetry.
    const TEST_ANGLES: [f64; JOINT_COUNT] = [17.0, -42.5, 63.25, 91.0, -128.75, 179.5];

    /// The frame entities compose to the cumulative tower `carrier_pose` returns.
    ///
    /// This is the substitution the ECS scene graph makes for `simulator.py`'s direct
    /// tower (`:866-899`), and the only place the two could silently disagree: Bevy's
    /// propagation would happily compose a wrong chain, and the picture would look almost
    /// right. Testing it against the kinematics core is what makes it a claim rather than
    /// an assumption.
    #[test]
    fn the_entity_tree_composes_to_carrier_pose() {
        let mut app = App::new();
        app.add_plugins((MinimalPlugins, TransformPlugin));
        app.insert_resource(RobotState {
            document: Document::shipped(),
            runtime_angles_deg: TEST_ANGLES,
        });
        app.add_systems(Startup, scene::build_scene);
        app.add_systems(Update, scene::sync_joints);

        // One update to run startup, one to drive the joints, one to propagate the
        // result: `sync_joints` writes the locals in `Update` and `Propagate` composes
        // them in `PostUpdate` of the same frame.
        for _ in 0..3 {
            app.update();
        }

        let expected: [Pose<f64>; FRAME_COUNT] = Document::shipped()
            .parameters
            .carrier_pose(&TEST_ANGLES)
            .expect("the shipped table is the arm the kinematics core models");

        let world = app.world_mut();
        let mut query = world.query::<(&scene::FrameIndex, &GlobalTransform)>();
        let mut actual = [None; FRAME_COUNT];
        for (index, transform) in query.iter(world) {
            actual[index.0] = Some(*transform);
        }

        for (frame, pose) in expected.iter().enumerate() {
            let transform = actual[frame].expect("build_scene spawns every frame");
            let (scale, rotation_quat, translation) = transform.to_scale_rotation_translation();
            assert!(
                (scale - Vec3::ONE).abs().max_element() < 1e-6,
                "frame {frame} carries a scale: {scale:?}"
            );

            let want = Vec3::new(pose.p.x() as f32, pose.p.y() as f32, pose.p.z() as f32);
            // The arm is tens of units across, where `f32` still resolves a few
            // millionths; a millimetre is far tighter than any placement error and far
            // looser than the conversion.
            assert!(
                (translation - want).abs().max_element() < 1e-3,
                "frame {frame} sits at {translation:?}, expected {want:?}"
            );

            let angle = rotation_quat
                .angle_between(Quat::from_mat3(&rotation(&pose.r)))
                .to_degrees();
            assert!(
                angle < 0.01,
                "frame {frame} is rotated {angle} degrees off, expected {:?}",
                pose.r
            );
        }
    }
}
