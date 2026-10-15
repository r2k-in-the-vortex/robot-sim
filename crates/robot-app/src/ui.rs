//! The egui shell: the tab strip, the 3D view's side panel and the parameter pages.
//!
//! The two top-level tabs and the parameter sub-tabs are the reference layout
//! (`simulator.py:186-188` for the tabs, `:438-441` for the sub-tabs). The tables here
//! display the document read-only: editing, validation, file load/save and the jog
//! controls are WS5's, and each one is marked where it goes.
//!
//! The 3D view is not an egui widget. This module measures the rect the renderer leaves
//! free and publishes it in [`Viewport`]; `main.rs` points the camera at that rect and
//! this module paints the joint labels into it, projected through the same camera. Doing
//! the labels here rather than with `Text2d` keeps them screen-aligned and unscaled, as
//! matplotlib's `axes.text` is (`simulator.py:955-959`).

use bevy::prelude::*;
use bevy::window::PrimaryWindow;
use bevy_egui::{EguiContexts, egui};
use robot_kinematics::Pose;
use robot_model::{AXIS_FRAME_NAMES, FRAME_COUNT, MESH_FRAME_NAMES};

use crate::camera::OrbitCamera;
use crate::scene::{GIZMO_LENGTH_FRACTION, LABEL_COLOR, LABEL_LIFT_FRACTION, LinkMeshes};
use crate::{RobotState, ViewState};

/// The two tabs of `simulator.py:188-189`.
#[derive(Resource, Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Tab {
    #[default]
    View,
    Parameters,
}

/// The two sub-tabs of `simulator.py:440-441`.
#[derive(Resource, Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum ParameterTab {
    #[default]
    Dh,
    Meshes,
}

/// The rect the 3D renderer owns, as measured by the UI pass.
///
/// Two units, because the two consumers disagree: `Camera::viewport` is in physical
/// pixels, while egui — and so the label projection and the cursor — works in logical
/// points.
#[derive(Resource, Clone, Copy, Debug)]
pub struct Viewport {
    /// The 3D view's rect in logical points, in window coordinates.
    pub points: egui::Rect,
    /// The same rect's top-left corner in physical pixels.
    pub physical_position: UVec2,
    /// The same rect's size in physical pixels. A zero size means "do not touch the
    /// camera viewport yet", so the first frames render full-window.
    pub physical_size: UVec2,
}

impl Default for Viewport {
    fn default() -> Self {
        Self {
            points: egui::Rect::ZERO,
            physical_position: UVec2::ZERO,
            physical_size: UVec2::ZERO,
        }
    }
}

/// Draw the shell and publish the 3D view's rect.
#[allow(clippy::too_many_arguments)]
pub fn draw_shell(
    mut contexts: EguiContexts,
    window: Single<&Window, With<PrimaryWindow>>,
    mut tab: ResMut<Tab>,
    mut parameter_tab: ResMut<ParameterTab>,
    mut view: ResMut<ViewState>,
    mut robot: ResMut<RobotState>,
    link_meshes: Res<LinkMeshes>,
    mut viewport: ResMut<Viewport>,
) -> Result {
    let ctx = contexts.ctx_mut()?;
    if ctx.theme() == egui::Theme::Dark {
        // The reference is a light UI (`simulator.py:190` paints the figure #f4f6f7), and
        // egui follows the system theme by default. Setting the preference is enough: the
        // default style for the light theme is the one we want, and it survives the user
        // switching the system theme mid-run.
        ctx.set_theme(egui::ThemePreference::Light);
    }

    let screen = ctx.viewport_rect();
    let mut root = egui::Ui::new(
        ctx.clone(),
        egui::Id::new("shell_root"),
        egui::UiBuilder::new()
            .layer_id(egui::LayerId::background())
            .max_rect(screen),
    );

    let strip = egui::Panel::top("tab_strip")
        .show(&mut root, |ui| {
            ui.horizontal(|ui| {
                ui.heading("6-Axis Robot");
                ui.separator();
                ui.selectable_value(&mut *tab, Tab::View, "3D View");
                ui.selectable_value(&mut *tab, Tab::Parameters, "Parameters");
            });
            ui.add_space(2.0);
        })
        .response
        .rect;

    // The central rect is assembled from the panels' own rects rather than from a
    // `CentralPanel`, because the camera needs it exactly: a viewport that overlaps a
    // panel would put the render under the widgets.
    let mut central = egui::Rect::from_min_max(egui::pos2(screen.min.x, strip.max.y), screen.max);

    match *tab {
        Tab::View => {
            let controls = egui::Panel::left("view_controls")
                .default_size(240.0)
                .show(&mut root, |ui| view_controls(ui, &mut view))
                .response
                .rect;
            let readout = egui::Panel::bottom("pose_readout")
                .show(&mut root, |ui| pose_readout(ui, &robot, &link_meshes))
                .response
                .rect;
            central.min.x = controls.max.x;
            central.max.y = readout.min.y;

            if robot.document.show_joint_labels {
                draw_labels(&root, central, &robot, &view.camera, view.grid_radius);
            }
        }
        Tab::Parameters => {
            let mut page = root.new_child(
                egui::UiBuilder::new()
                    .max_rect(central)
                    .layout(egui::Layout::top_down(egui::Align::Min)),
            );
            // Opaque, so the 3D render behind it is covered rather than showing through:
            // the reference swaps tabs, it does not overlay them.
            page.painter()
                .rect_filled(central, 0.0, page.style().visuals.panel_fill);
            page.add_space(8.0);
            parameter_page(&mut page, &mut parameter_tab, &mut robot, &link_meshes);
        }
    }

    let scale = window.scale_factor();
    viewport.points = central;
    viewport.physical_position = UVec2::new(
        (central.min.x * scale).round().max(0.0) as u32,
        (central.min.y * scale).round().max(0.0) as u32,
    );
    viewport.physical_size = UVec2::new(
        (central.width() * scale).round().max(0.0) as u32,
        (central.height() * scale).round().max(0.0) as u32,
    );

    Ok(())
}

/// The 3D view's side panel.
///
/// Only the view's own controls are here. `simulator.py:230-277` puts the jog controls in
/// the same place, which is WS5's half; the placeholder keeps the layout stable until
/// then.
fn view_controls(ui: &mut egui::Ui, view: &mut ViewState) {
    ui.add_space(4.0);
    ui.heading("View");
    ui.label("Left-drag orbits, right-drag pans, the wheel zooms.");
    if ui.button("Fit view").clicked() {
        view.fit_requested = true;
    }
    ui.add_space(6.0);
    ui.label(format!(
        "Elevation {:.1}°, azimuth {:.1}°",
        view.camera.elev_deg, view.camera.azim_deg
    ));
    ui.separator();

    ui.heading("Jog");
    ui.add_enabled(false, egui::Button::new("Joint jogs"));
    ui.add_enabled(false, egui::Button::new("Base frame"));
    ui.add_enabled(false, egui::Button::new("Tool frame"));
    ui.label(egui::RichText::new("Jog controls land with WS5.").small());
}

/// The pose and mesh status under the view (`simulator.py:969-976`).
fn pose_readout(ui: &mut egui::Ui, robot: &RobotState, link_meshes: &LinkMeshes) {
    ui.add_space(2.0);
    match robot
        .document
        .parameters
        .carrier_pose(&robot.runtime_angles_deg)
    {
        Ok(poses) => {
            let tool = poses[FRAME_COUNT - 1];
            let (roll, pitch, yaw) = rpy_degrees(&tool);
            ui.label(format!(
                "T6 position: X {:.3}   Y {:.3}   Z {:.3}",
                tool.p.x(),
                tool.p.y(),
                tool.p.z()
            ));
            ui.label(format!(
                "Orientation RPY (ZYX, deg): roll {roll:.1}   pitch {pitch:.1}   yaw {yaw:.1}"
            ));
        }
        Err(error) => {
            ui.colored_label(egui::Color32::from_rgb(0xc0, 0x39, 0x2b), error.to_string());
        }
    }
    // `simulator.py:962-965`.
    ui.label(link_meshes.status.as_str());
    ui.add_space(2.0);
}

/// The Parameters tab: its sub-tabs and their pages.
fn parameter_page(
    ui: &mut egui::Ui,
    parameter_tab: &mut ParameterTab,
    robot: &mut RobotState,
    link_meshes: &LinkMeshes,
) {
    ui.horizontal(|ui| {
        ui.selectable_value(parameter_tab, ParameterTab::Dh, "DH Parameters");
        ui.selectable_value(parameter_tab, ParameterTab::Meshes, "Meshes");
    });
    ui.separator();
    egui::ScrollArea::vertical().show(ui, |ui| match parameter_tab {
        ParameterTab::Dh => dh_page(ui, robot),
        ParameterTab::Meshes => mesh_page(ui, robot, link_meshes),
    });
}

/// `simulator.py:443-508`.
fn dh_page(ui: &mut egui::Ui, robot: &mut RobotState) {
    ui.add_space(4.0);
    ui.heading("Denavit–Hartenberg parameters");
    ui.label("Theta offset and joint angle are in degrees; d and a use consistent length units.");
    ui.add_space(8.0);

    egui::Grid::new("dh_table")
        .num_columns(6)
        .spacing([16.0, 6.0])
        .show(ui, |ui| {
            for heading in [
                "Joint",
                "Theta offset (deg)",
                "Joint angle (deg)",
                "d",
                "a",
                "Alpha (deg)",
            ] {
                ui.label(egui::RichText::new(heading).strong());
            }
            ui.end_row();

            for (joint, row) in robot.document.parameters.joints.iter().enumerate() {
                ui.label(format!("J{}", joint + 1));
                ui.label(format!("{}", row.theta_offset_deg));
                // The runtime angle is the one editable value the reference writes back
                // (`simulator.py:466-470`); WS5 replaces this label with its spinbox.
                ui.label(format!("{}", robot.runtime_angles_deg[joint]));
                ui.label(format!("{}", row.d));
                ui.label(format!("{}", row.a));
                ui.label(format!("{}", row.alpha_deg));
                ui.end_row();
            }
        });

    ui.add_space(12.0);
    ui.horizontal(|ui| {
        ui.add_enabled(false, egui::Button::new("Apply to View"));
        ui.add_enabled(false, egui::Button::new("Save JSON"));
        ui.add_enabled(false, egui::Button::new("Load JSON"));
    });
    ui.label(
        egui::RichText::new(
            "Joint angles start at zero and are not saved. The buttons land with WS5.",
        )
        .small(),
    );
    ui.add_space(10.0);

    ui.separator();
    show_joint_labels(ui, robot);
    ui.add_space(4.0);
    ui.label("Coordinate gizmos");
    ui.horizontal_wrapped(|ui| {
        for (frame, name) in AXIS_FRAME_NAMES.iter().enumerate() {
            ui.checkbox(&mut robot.document.show_coordinate_gizmos[frame], *name);
        }
    });
}

/// "Show joint labels in 3D View" (`simulator.py:490-495`).
///
/// Split out so the mutable borrow of the document is taken only when the box is clicked:
/// [`ResMut`](bevy::prelude::ResMut) marks a resource changed on `DerefMut`, and a
/// resource that is "changed" every frame drags the mesh-edge system along with it.
fn show_joint_labels(ui: &mut egui::Ui, robot: &mut RobotState) {
    let mut show = robot.document.show_joint_labels;
    if ui
        .checkbox(&mut show, "Show joint labels in 3D View")
        .clicked()
    {
        robot.document.show_joint_labels = show;
    }
}

/// `simulator.py:510-573`.
fn mesh_page(ui: &mut egui::Ui, robot: &mut RobotState, link_meshes: &LinkMeshes) {
    ui.add_space(4.0);
    ui.heading("Frame-attached STL meshes");
    ui.label("Offsets use model length units. Rotations are local X, then Y, then Z, in degrees.");
    ui.add_space(8.0);

    let mut show_edges = robot.document.show_mesh_edges;
    if ui
        .checkbox(&mut show_edges, "Show triangle edges")
        .clicked()
    {
        robot.document.show_mesh_edges = show_edges;
    }
    ui.add_space(6.0);

    egui::Grid::new("mesh_table")
        .num_columns(9)
        .spacing([10.0, 4.0])
        .show(ui, |ui| {
            for heading in [
                "Frame", "STL file", "Offset X", "Offset Y", "Offset Z", "Rot X", "Rot Y", "Rot Z",
                "Opacity",
            ] {
                ui.label(egui::RichText::new(heading).strong());
            }
            ui.end_row();

            for (frame, setting) in robot.document.meshes.iter().enumerate() {
                ui.label(MESH_FRAME_NAMES[frame]);
                let path = if setting.path.is_empty() {
                    "—"
                } else {
                    setting.path.as_str()
                };
                ui.label(path);
                for axis in setting.offset {
                    ui.label(format!("{axis}"));
                }
                for angle in setting.rotation_deg {
                    ui.label(format!("{angle}"));
                }
                ui.label(format!("{}", setting.opacity));
                ui.end_row();
            }
        });

    ui.add_space(10.0);
    // `simulator.py:962-965` shows this same line under the view.
    ui.label(link_meshes.status.as_str());
    ui.add_space(6.0);
    ui.horizontal(|ui| {
        ui.add_enabled(false, egui::Button::new("Apply Meshes"));
        ui.add_enabled(false, egui::Button::new("Save JSON"));
    });
    ui.label(egui::RichText::new("Editing meshes lands with WS5.").small());
}

/// Paint the per-frame names over the 3D view, lifted off each origin as
/// `simulator.py:955-959` does.
///
/// The anchors come from the kinematics rather than from the entities' world transforms,
/// so a label lands on the frame the next render draws regardless of which schedule ran
/// first this frame.
fn draw_labels(
    root: &egui::Ui,
    viewport: egui::Rect,
    robot: &RobotState,
    camera: &OrbitCamera,
    radius: f64,
) {
    let Ok(poses) = robot
        .document
        .parameters
        .carrier_pose(&robot.runtime_angles_deg)
    else {
        return;
    };
    // The same marker length the gizmos use, so a label tracks the frame it belongs to.
    let lift = radius * GIZMO_LENGTH_FRACTION * LABEL_LIFT_FRACTION;
    let painter = root.painter_at(viewport);
    let (red, green, blue) = crate::scene::rgb(LABEL_COLOR);
    let color = egui::Color32::from_rgb(red, green, blue);
    for (frame, pose) in poses.iter().enumerate() {
        let anchor = [pose.p.x(), pose.p.y(), pose.p.z() + lift];
        let screen = project(camera, viewport, anchor);
        if !viewport.contains(screen) {
            continue;
        }
        painter.text(
            screen,
            egui::Align2::CENTER_CENTER,
            AXIS_FRAME_NAMES[frame],
            egui::FontId::proportional(11.0),
            color,
        );
    }
}

/// Where a world point lands inside the viewport, in egui points.
///
/// Mirrors the orthographic camera `main.rs` builds from the same [`OrbitCamera`]: the
/// visible world height is `2 · half_span` (`ScalingMode::FixedVertical`), the visible
/// width is that times the viewport's aspect ratio, and the screen basis is
/// [`OrbitCamera::right`] and [`OrbitCamera::up`] — which is also the basis `pan` moves
/// along, so a drag and a label agree about which way is which.
pub fn project(camera: &OrbitCamera, viewport: egui::Rect, point: [f64; 3]) -> egui::Pos2 {
    let offset = [0, 1, 2].map(|axis| point[axis] - camera.target[axis]);
    let right = camera.right();
    let up = camera.up();
    let across = dot(offset, right);
    let above = dot(offset, up);

    let height = f64::from(viewport.height()).max(1.0);
    let half_height = camera.half_span.max(f64::MIN_POSITIVE);
    let half_width = half_height * f64::from(viewport.width()) / height;

    egui::pos2(
        viewport.center().x + (across / half_width * f64::from(viewport.width()) / 2.0) as f32,
        viewport.center().y - (above / half_height * (height / 2.0)) as f32,
    )
}

/// Roll, pitch, yaw for `R = Rz(yaw) · Ry(pitch) · Rx(roll)`, in degrees.
///
/// Transcribed from `simulator.py:45-57`, including its gimbal-lock branch: at pitch
/// ±90° the roll and yaw axes coincide, the yaw is taken from the second row instead and
/// the roll is reported as zero.
pub fn rpy_degrees(pose: &Pose<f64>) -> (f64, f64, f64) {
    let at = |row: usize, column: usize| pose.r.at(row, column);
    let pitch = (-at(2, 0)).atan2(at(0, 0).hypot(at(1, 0)));
    let (roll, yaw) = if at(0, 0).hypot(at(1, 0)) > 1e-9 {
        (at(2, 1).atan2(at(2, 2)), at(1, 0).atan2(at(0, 0)))
    } else {
        (0.0, (-at(0, 1)).atan2(at(1, 1)))
    };
    (roll.to_degrees(), pitch.to_degrees(), yaw.to_degrees())
}

fn dot(left: [f64; 3], right: [f64; 3]) -> f64 {
    left[0] * right[0] + left[1] * right[1] + left[2] * right[2]
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::{Mat3, Vec3};

    /// The reference's rotation builder, `simulator.py:978-988`: `Rz(rz) · Ry(ry) · Rx(rx)`,
    /// written as rows because that is how the Python's nested tuples are indexed.
    fn rz_ry_rx(rx_deg: f64, ry_deg: f64, rz_deg: f64) -> Mat3<f64> {
        let rx = rx_deg.to_radians();
        let ry = ry_deg.to_radians();
        let rz = rz_deg.to_radians();
        let rot_x = Mat3::from_rows([
            [1.0, 0.0, 0.0],
            [0.0, rx.cos(), -rx.sin()],
            [0.0, rx.sin(), rx.cos()],
        ]);
        let rot_y = Mat3::from_rows([
            [ry.cos(), 0.0, ry.sin()],
            [0.0, 1.0, 0.0],
            [-ry.sin(), 0.0, ry.cos()],
        ]);
        let rot_z = Mat3::from_rows([
            [rz.cos(), -rz.sin(), 0.0],
            [rz.sin(), rz.cos(), 0.0],
            [0.0, 0.0, 1.0],
        ]);
        rot_z * rot_y * rot_x
    }

    fn pose_of(rx: f64, ry: f64, rz: f64) -> Pose<f64> {
        Pose::new(rz_ry_rx(rx, ry, rz), Vec3::zero())
    }

    #[test]
    fn rpy_round_trips_a_composed_rotation() {
        for (rx, ry, rz) in [
            (0.0, 0.0, 0.0),
            (10.0, 20.0, 30.0),
            (-45.0, 15.5, 170.0),
            (80.0, -30.0, -120.0),
        ] {
            let (roll, pitch, yaw) = rpy_degrees(&pose_of(rx, ry, rz));
            assert!((roll - rx).abs() < 1e-9, "roll {roll} for {rx}");
            assert!((pitch - ry).abs() < 1e-9, "pitch {pitch} for {ry}");
            assert!((yaw - rz).abs() < 1e-9, "yaw {yaw} for {rz}");
        }
    }

    #[test]
    fn rpy_uses_the_gimbal_lock_branch_at_pitch_ninety() {
        // At pitch 90° the first column vanishes, so the yaw has to come from the second
        // row and the roll is reported as zero (`simulator.py:54-56`). The pitch and roll
        // axes have coincided by then, and the two angles are only ever recoverable as
        // their difference: `Rz(20) · Ry(90) · Rx(35)` is the same rotation as
        // `Rz(-15) · Ry(90)`, so `-15` is the answer, not `20`.
        let (roll, pitch, yaw) = rpy_degrees(&pose_of(35.0, 90.0, 20.0));
        assert!(roll.abs() < 1e-9, "roll {roll}");
        assert!((pitch - 90.0).abs() < 1e-9, "pitch {pitch}");
        assert!((yaw + 15.0).abs() < 1e-9, "yaw {yaw}");
    }

    #[test]
    fn project_puts_the_target_at_the_viewport_center() {
        let camera = OrbitCamera::isometric();
        let viewport = egui::Rect::from_min_size(egui::pos2(100.0, 50.0), egui::vec2(400.0, 300.0));
        let center = project(&camera, viewport, camera.target);
        assert!((center.x - viewport.center().x).abs() < 1e-3, "{center:?}");
        assert!((center.y - viewport.center().y).abs() < 1e-3, "{center:?}");
    }

    #[test]
    fn project_follows_the_camera_basis() {
        let mut camera = OrbitCamera::isometric();
        camera.half_span = 10.0; // a 20-unit-tall view volume
        let viewport = egui::Rect::from_min_size(egui::pos2(0.0, 0.0), egui::vec2(200.0, 100.0));

        // 20 world units over 100 points is five per point, on both axes: the view volume
        // is 40 units wide, which is 200 points.
        let right = camera.right();
        let along_right = [0, 1, 2].map(|axis| right[axis] * 5.0);
        let screen = project(&camera, viewport, along_right);
        assert!(
            (screen.x - (viewport.center().x + 25.0)).abs() < 1e-3,
            "{screen:?}"
        );
        assert!((screen.y - viewport.center().y).abs() < 1e-3, "{screen:?}");

        // Up in the world is up on the screen, and screen y counts downward.
        let up = camera.up();
        let along_up = [0, 1, 2].map(|axis| up[axis] * 5.0);
        let screen = project(&camera, viewport, along_up);
        assert!((screen.x - viewport.center().x).abs() < 1e-3, "{screen:?}");
        assert!(
            (screen.y - (viewport.center().y - 25.0)).abs() < 1e-3,
            "{screen:?}"
        );
    }

    #[test]
    fn project_pins_the_world_height_to_the_viewport_height() {
        let mut camera = OrbitCamera::isometric();
        camera.half_span = 1.0; // a two-unit-tall view volume
        let right = camera.right();

        // `FixedVertical` puts those two units across the viewport's height whatever the
        // aspect, so the scale follows the *height*: 100 points per unit at 200 points
        // tall, and the width only decides how much more of the world is on show.
        let wide = egui::Rect::from_min_size(egui::pos2(0.0, 0.0), egui::vec2(400.0, 200.0));
        let screen = project(&camera, wide, [right[0], right[1], right[2]]);
        assert!(
            (screen.x - (wide.center().x + 100.0)).abs() < 1e-3,
            "{screen:?}"
        );

        let tall = egui::Rect::from_min_size(egui::pos2(0.0, 0.0), egui::vec2(200.0, 400.0));
        let screen = project(&camera, tall, [right[0], right[1], right[2]]);
        assert!(
            (screen.x - (tall.center().x + 200.0)).abs() < 1e-3,
            "{screen:?}"
        );
    }
}
