//! The egui shell: the tab strip, the 3D view's side panel and the parameter pages.
//!
//! The two top-level tabs and the parameter sub-tabs are the reference layout
//! (`simulator.py:186-188` for the tabs, `:438-441` for the sub-tabs). The tables here are
//! editable and every button is wired: the fields live in [`crate::session`], which owns the
//! operations they drive and the rules about which of them take effect when, and this module
//! only lays them out and calls across.
//!
//! The 3D view is not an egui widget. This module measures the rect the renderer leaves
//! free and publishes it in [`Viewport`]; `main.rs` points the camera at that rect and
//! this module paints the joint labels into it, projected through the same camera. Doing
//! the labels here rather than with `Text2d` keeps them screen-aligned and unscaled, as
//! matplotlib's `axes.text` is (`simulator.py:955-959`).

use bevy::prelude::*;
use bevy::window::PrimaryWindow;
use bevy_egui::{EguiContexts, egui};
use robot_kinematics::{JOINT_COUNT, Pose};
use robot_model::Document;
use robot_model::{AXIS_FRAME_NAMES, FRAME_COUNT, MESH_FRAME_NAMES};

use crate::camera::OrbitCamera;
use crate::dialogs;
use crate::jog::Axis;
use crate::scene::{GIZMO_LENGTH_FRACTION, LABEL_COLOR, LABEL_LIFT_FRACTION, LinkMeshes};
use crate::session::{self, INVALID_PARAMETERS_TITLE, Session, rotation_to_rpy_degrees};
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
    mut session: ResMut<Session>,
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
                .show(&mut root, |ui| {
                    view_controls(ui, &mut view, &mut robot, &mut session)
                })
                .response
                .rect;
            let readout = egui::Panel::bottom("pose_readout")
                .show(&mut root, |ui| {
                    pose_readout(ui, &robot, &link_meshes, &mut session)
                })
                .response
                .rect;
            central.min.x = controls.max.x;
            central.max.y = readout.min.y;

            if robot.document.show_joint_labels {
                draw_labels(&root, central, &robot, &view.camera, view.grid_radius);
            }
        }
        Tab::Parameters => {
            // The fill is drawn on the root, over the whole central rect, so the page stays
            // opaque edge to edge; the content is inset from it by the margin the View tab's
            // panels use (`Frame::side_top_panel`), so the tables do not run into the window
            // edge and the two tabs agree about where their widgets start.
            root.painter()
                .rect_filled(central, 0.0, root.style().visuals.panel_fill);
            let margin = egui::Frame::side_top_panel(root.style())
                .inner_margin
                .leftf();
            let mut page = root.new_child(
                egui::UiBuilder::new()
                    .max_rect(central.shrink2(egui::vec2(margin, 0.0)))
                    .layout(egui::Layout::top_down(egui::Align::Min)),
            );
            page.add_space(8.0);
            parameter_page(
                &mut page,
                &mut parameter_tab,
                &mut robot,
                &mut session,
                &link_meshes,
            );
        }
    }

    // The messagebox the reference raises inside its handlers (`simulator.py:673, 708, 821`).
    draw_notice(&mut root, &mut session);

    viewport.points = central;
    let (physical_position, physical_size) =
        physical_viewport(central, window.scale_factor(), window.physical_size());
    viewport.physical_position = physical_position;
    viewport.physical_size = physical_size;

    Ok(())
}

/// The [`Camera::viewport`] rect for a logical one: both corners rounded into physical
/// pixels, each held inside `target` — the window's own physical size, which is the size
/// the frame renders into.
///
/// Rounding the origin and the size separately, as this used to, cannot promise that the
/// rect fits: each rounding can carry an edge half a pixel outward, and the logical rect
/// egui lays out is measured against the window as Bevy last handed it to egui, which after
/// a resize is a frame behind the size the frame renders into. Either one leaves the rect
/// hanging off the render target by a pixel, and wgpu validates a camera viewport against
/// the target's extent rather than clipping it — the frame is aborted and Bevy quits the
/// app. `main.rs` clamps again where the viewport is applied, for the frames the UI pass
/// has not measured yet.
///
/// [`Camera::viewport`]: bevy::camera::Camera::viewport
fn physical_viewport(points: egui::Rect, scale: f32, target: UVec2) -> (UVec2, UVec2) {
    // A NaN or a negative coordinate floors to zero rather than wrapping, and the clamp
    // also catches the `as u32` saturation a wild coordinate would hit.
    let corner = |x: f32, y: f32| {
        UVec2::new(
            (x * scale).round().max(0.0) as u32,
            (y * scale).round().max(0.0) as u32,
        )
        .min(target)
    };
    let origin = corner(points.min.x, points.min.y);
    let far = corner(points.max.x, points.max.y);
    // An inverted rect, or one the target holds none of, comes back with a zero size, which
    // `main.rs` reads as "leave the camera viewport alone".
    (origin, far.saturating_sub(origin))
}

/// The 3D view's side panel: the camera controls, then `simulator.py:229-277`'s jog panel.
///
/// # Text fields, not drag values
///
/// The reference's step boxes and angle boxes are `ttk.Spinbox` widgets, which are editable
/// text with arrows. egui has no spinbox, and a [`egui::DragValue`] would be a different
/// interaction *and* a different failure model: it cannot hold `"abc"`, so the reference's
/// own complaints — "Joint step must be a finite positive angle." — would become unreachable.
/// Keeping the fields as text keeps the validation the port is supposed to reproduce.
fn view_controls(
    ui: &mut egui::Ui,
    view: &mut ViewState,
    robot: &mut RobotState,
    session: &mut Session,
) {
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
    ui.add_space(2.0);
    egui::Grid::new("jog_steps")
        .num_columns(2)
        .spacing([8.0, 4.0])
        .show(ui, |ui| {
            ui.label("Jog step");
            step_field(ui, &mut session.jog_step);
            ui.end_row();
            ui.label("Rotation step");
            step_field(ui, &mut session.rotation_step);
            ui.end_row();
        });
    ui.add_space(6.0);

    // `simulator.py:251-256`'s two frame groups, in its order.
    egui::Frame::group(ui.style()).show(ui, |ui| {
        frame_jog_buttons(
            ui,
            "Base frame",
            session,
            robot,
            Session::jog_cartesian,
            Session::jog_rotation_world,
        );
    });
    egui::Frame::group(ui.style()).show(ui, |ui| {
        frame_jog_buttons(
            ui,
            "Tool frame",
            session,
            robot,
            Session::jog_tool_translation,
            Session::jog_rotation_tool,
        );
    });
    ui.add_space(6.0);

    egui::Frame::group(ui.style()).show(ui, |ui| {
        ui.label(egui::RichText::new("Joint jogs").strong());
        ui.horizontal(|ui| {
            ui.label("Joint step");
            step_field(ui, &mut session.joint_step);
            ui.separator();
            for joint in 0..JOINT_COUNT {
                ui.vertical(|ui| {
                    ui.label(format!("J{}", joint + 1));
                    ui.horizontal(|ui| {
                        if ui.small_button("-").clicked() {
                            session.jog_joint(
                                joint,
                                -1,
                                &mut robot.document,
                                &mut robot.runtime_angles_deg,
                            );
                        }
                        if ui.small_button("+").clicked() {
                            session.jog_joint(
                                joint,
                                1,
                                &mut robot.document,
                                &mut robot.runtime_angles_deg,
                            );
                        }
                    });
                    // `_sync_joint_angle_views`'s front readout (`simulator.py:325`).
                    ui.label(
                        egui::RichText::new(format!("{:.1}°", robot.runtime_angles_deg[joint]))
                            .small(),
                    );
                });
            }
        });
    });

    ui.add_space(4.0);
    ui.label(session.status.as_str());
}

/// One step box, sized like the reference's `width=6` spinboxes.
fn step_field(ui: &mut egui::Ui, text: &mut String) {
    ui.add(egui::TextEdit::singleline(text).desired_width(56.0));
}

/// One frame group's six translation buttons and six rotation buttons,
/// `_build_frame_jog_buttons` (`simulator.py:278-296`).
///
/// The reference's column arithmetic — `axis * 2 + (1 if direction > 0 else 0)` over
/// `((-1, "-"), (1, "+"))` — is a grid layout; the order it produces is what matters here,
/// so the row reads X−, X+, Y−, Y+, Z−, Z+.
fn frame_jog_buttons(
    ui: &mut egui::Ui,
    title: &str,
    session: &mut Session,
    robot: &mut RobotState,
    translate: fn(&mut Session, Axis, i32, &mut Document, &mut [f64; JOINT_COUNT]),
    rotate: fn(&mut Session, Axis, i32, &mut Document, &mut [f64; JOINT_COUNT]),
) {
    ui.label(egui::RichText::new(title).strong());
    // The translation row first, then the rotation one, which is the reference's row order.
    for rotating in [false, true] {
        ui.horizontal(|ui| {
            for axis in Axis::ALL {
                for direction in [-1, 1] {
                    let label = jog_button_label(axis, direction, rotating);
                    if ui.small_button(label).clicked() {
                        if rotating {
                            rotate(
                                session,
                                axis,
                                direction,
                                &mut robot.document,
                                &mut robot.runtime_angles_deg,
                            );
                        } else {
                            translate(
                                session,
                                axis,
                                direction,
                                &mut robot.document,
                                &mut robot.runtime_angles_deg,
                            );
                        }
                    }
                }
            }
        });
    }
}

/// One jog button's label: the axis letter, an `R` when the button turns the pose rather
/// than moving it, and the sign of the direction it carries — `X-`, `X+`, `RX-`, `RX+`.
///
/// The label and the direction the click hands to the handler are both built from the one
/// `direction` argument, so the sign a button advertises and the sign it jogs with cannot
/// drift apart. The reference writes the same two spellings out of its `((-1, "-"), (1, "+"))`
/// pairs (`simulator.py:280-296`).
///
/// `pub(crate)` for `session`'s tests, which name the buttons they click the way the panel
/// spells them rather than paraphrasing the suffix.
pub(crate) fn jog_button_label(axis: Axis, direction: i32, rotating: bool) -> String {
    let suffix = if direction < 0 { "-" } else { "+" };
    if rotating {
        format!("R{}{suffix}", axis.letter())
    } else {
        format!("{}{suffix}", axis.letter())
    }
}

/// The pose and mesh status under the view (`simulator.py:969-976`), plus `Copy XYZ`.
fn pose_readout(
    ui: &mut egui::Ui,
    robot: &RobotState,
    link_meshes: &LinkMeshes,
    session: &mut Session,
) {
    ui.add_space(2.0);
    ui.horizontal(|ui| {
        ui.vertical(|ui| {
            let pose = robot
                .document
                .parameters
                .carrier_pose(&robot.runtime_angles_deg);
            match pose {
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
        });

        // Right-aligned, as the reference packs it (`simulator.py:205-207`).
        ui.with_layout(egui::Layout::right_to_left(egui::Align::TOP), |ui| {
            if ui.button("Copy XYZ").clicked() {
                copy_xyz(ui, robot, session);
            }
        });
    });
    ui.add_space(2.0);
}

/// Put the T6 pose on the clipboard, `_copy_t6_position` (`simulator.py:297-316`).
///
/// egui's clipboard is enough: bevy_egui manages it through `arboard` by default, so
/// `Context::copy_text` needs no dependency of its own.
fn copy_xyz(ui: &egui::Ui, robot: &RobotState, session: &mut Session) {
    match Session::copy_xyz_text(&robot.document.parameters, &robot.runtime_angles_deg) {
        Ok(text) => {
            ui.ctx().copy_text(text);
            session.status = String::from(session::COPIED);
        }
        // The reference has nothing to say here: `forward_kinematics` in Python accepts any
        // table, so its `Copy XYZ` cannot fail the way a table with no geometry does here.
        Err(message) => session.show_notice(INVALID_PARAMETERS_TITLE, message),
    }
}

/// The pending messagebox, if any.
///
/// A modal window with one button, which is as close as an immediate-mode frame gets to
/// `messagebox.showerror`: the reference's handler blocks until it is dismissed, and this one
/// keeps the notice up until the user presses OK.
fn draw_notice(root: &mut egui::Ui, session: &mut Session) {
    let Some(failure) = session.notice.clone() else {
        return;
    };
    let mut dismissed = false;
    egui::Window::new(failure.title)
        .collapsible(false)
        .resizable(false)
        .anchor(egui::Align2::CENTER_CENTER, [0.0, 0.0])
        .show(root.ctx(), |ui| {
            ui.label(failure.message.as_str());
            ui.add_space(6.0);
            ui.vertical_centered(|ui| {
                if ui.button("OK").clicked() {
                    dismissed = true;
                }
            });
        });
    if dismissed {
        session.notice = None;
    }
}

/// The Parameters tab: its sub-tabs and their pages.
fn parameter_page(
    ui: &mut egui::Ui,
    parameter_tab: &mut ParameterTab,
    robot: &mut RobotState,
    session: &mut Session,
    link_meshes: &LinkMeshes,
) {
    ui.horizontal(|ui| {
        ui.selectable_value(parameter_tab, ParameterTab::Dh, "DH Parameters");
        ui.selectable_value(parameter_tab, ParameterTab::Meshes, "Meshes");
    });
    ui.separator();
    egui::ScrollArea::vertical().show(ui, |ui| match parameter_tab {
        ParameterTab::Dh => dh_page(ui, robot, session),
        ParameterTab::Meshes => mesh_page(ui, robot, session, link_meshes),
    });
}

/// `simulator.py:443-508`.
fn dh_page(ui: &mut egui::Ui, robot: &mut RobotState, session: &mut Session) {
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

            for joint in 0..JOINT_COUNT {
                ui.label(format!("J{}", joint + 1));
                // The columns are theta, joint angle, d, a, alpha, in that order, while the
                // stored row is (theta, d, a, alpha): the runtime angle sits in the middle
                // of the row on screen but is not one of the DH values. It is kept in its
                // own field list, which is what the display-precision split in
                // [`Session::read_joint_angles`] turns on — an edited angle field must not
                // round the five it was not asked about.
                let [theta, d, a, alpha] = &mut session.dh[joint];
                ui.add(egui::TextEdit::singleline(theta).desired_width(96.0));
                ui.add(
                    egui::TextEdit::singleline(&mut session.joint_angles[joint])
                        .desired_width(96.0),
                );
                ui.add(egui::TextEdit::singleline(d).desired_width(96.0));
                ui.add(egui::TextEdit::singleline(a).desired_width(96.0));
                ui.add(egui::TextEdit::singleline(alpha).desired_width(96.0));
                ui.end_row();
            }
        });

    ui.add_space(12.0);
    ui.horizontal(|ui| {
        if ui.button("Apply to View").clicked() {
            if let Err(failure) =
                session.apply_from_entries(&mut robot.document, &mut robot.runtime_angles_deg)
            {
                session.notice = Some(failure);
            }
        }
        if ui.button("Save JSON").clicked() {
            save_json(session, robot);
        }
        if ui.button("Load JSON").clicked() {
            load_json(session, robot);
        }
    });
    ui.label(
        egui::RichText::new(format!(
            "File: {} · Joint angles start at zero and are not saved.",
            session
                .config_path
                .file_name()
                .map_or_else(String::new, |name| name.to_string_lossy().into_owned())
        ))
        .small(),
    );
    ui.add_space(10.0);

    ui.separator();
    show_joint_labels(ui, robot);
    ui.add_space(4.0);
    gizmo_checkboxes(ui, robot);
}

/// "Coordinate gizmos", `simulator.py:496-508`.
///
/// **Deviation.** The reference labels these seven boxes from `AXIS_FRAME_NAMES` —
/// `("J1", …, "J6", "Tool/Flange")`, the names of the *axes* each frame carries — while the
/// list it zips over is indexed in render order, which is `("Base", "J1", …, "J6")`, the
/// names of the *bodies* each frame holds. The two lists are shifted by one and disagree at
/// both ends, so the box the reference labels "J1" is the one that shows and hides the
/// **base** gizmo, and the box labelled "Tool/Flange" is J6's. The boxes here are labelled
/// with [`MESH_FRAME_NAMES`], so each one names the frame whose gizmo it actually toggles.
///
/// The drawn labels over the 3D view keep the reference's axis naming, which is correct
/// there: the gizmo at frame `i` draws frame `i`'s axes, and frame `i` carries joint `i+1`'s
/// axis, which is exactly what `simulator.py:39-41` says the list is for.
fn gizmo_checkboxes(ui: &mut egui::Ui, robot: &mut RobotState) {
    ui.label("Coordinate gizmos");
    let mut visibility = robot.document.show_coordinate_gizmos;
    let mut changed = false;
    ui.horizontal_wrapped(|ui| {
        for (frame, name) in MESH_FRAME_NAMES.iter().enumerate() {
            if ui.checkbox(&mut visibility[frame], *name).changed() {
                changed = true;
            }
        }
    });
    // Written back only on a click, so the resource is not marked changed every frame and
    // the mesh-edge system is not dragged along with it. See [`show_joint_labels`].
    if changed {
        robot.document.show_coordinate_gizmos = visibility;
    }
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

/// Save through a chooser, then report the way `_save_json` does.
fn save_json(session: &mut Session, robot: &mut RobotState) {
    let Some(path) = dialogs::save_config(&session.config_path) else {
        return;
    };
    match session.save_json(&mut robot.document, &path) {
        Ok(message) => session.show_notice("Parameters saved", message),
        Err(failure) => session.notice = Some(failure),
    }
}

/// Load through a chooser, then report the way `_load_json` does.
fn load_json(session: &mut Session, robot: &mut RobotState) {
    let Some(path) = dialogs::load_config(&session.config_path) else {
        return;
    };
    let angles = robot.runtime_angles_deg;
    if let Err(failure) = session.load_json(&mut robot.document, &angles, &path) {
        session.notice = Some(failure);
    }
}

/// `simulator.py:510-573`.
fn mesh_page(
    ui: &mut egui::Ui,
    robot: &mut RobotState,
    session: &mut Session,
    link_meshes: &LinkMeshes,
) {
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
        .num_columns(10)
        .spacing([8.0, 4.0])
        .show(ui, |ui| {
            for heading in [
                "Frame", "STL file", "", "Offset X", "Offset Y", "Offset Z", "Rot X", "Rot Y",
                "Rot Z", "Opacity",
            ] {
                ui.label(egui::RichText::new(heading).strong());
            }
            ui.end_row();

            for (frame, form) in session.meshes.iter_mut().enumerate() {
                ui.label(MESH_FRAME_NAMES[frame]);
                ui.add(egui::TextEdit::singleline(&mut form.path).desired_width(220.0));
                if ui.button("Browse…").clicked() {
                    if let Some(path) = dialogs::pick_stl(&form.path) {
                        form.path = path.to_string_lossy().into_owned();
                    }
                }
                for field in form.offset.iter_mut().chain(form.rotation.iter_mut()) {
                    ui.add(egui::TextEdit::singleline(field).desired_width(56.0));
                }
                ui.add(egui::TextEdit::singleline(&mut form.opacity).desired_width(48.0));
                ui.end_row();
            }
        });

    ui.add_space(10.0);
    // `simulator.py:962-965` shows this same line under the view.
    ui.label(link_meshes.status.as_str());
    ui.add_space(6.0);
    ui.horizontal(|ui| {
        if ui.button("Apply Meshes").clicked() {
            if let Err(failure) =
                session.apply_from_entries(&mut robot.document, &mut robot.runtime_angles_deg)
            {
                session.notice = Some(failure);
            }
        }
        if ui.button("Save JSON").clicked() {
            save_json(session, robot);
        }
    });
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
/// The extraction itself lives in [`crate::session`], beside the `Copy XYZ` button that also
/// needs it; this is the readout's spelling of the same answer.
pub fn rpy_degrees(pose: &Pose<f64>) -> (f64, f64, f64) {
    let [roll, pitch, yaw] = rotation_to_rpy_degrees(pose);
    (roll, pitch, yaw)
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
    fn physical_viewport_rounds_both_corners_at_a_whole_scale() {
        // At 100% display scale a point is a pixel: the rect comes back as written.
        let points = egui::Rect::from_min_max(egui::pos2(240.0, 39.0), egui::pos2(1120.0, 699.0));
        let (position, size) = physical_viewport(points, 1.0, UVec2::new(1120, 760));
        assert_eq!(position, UVec2::new(240, 39));
        assert_eq!(size, UVec2::new(880, 660));
    }

    #[test]
    fn physical_viewport_holds_a_fractional_scale_inside_the_window() {
        // The crash this was written for. A maximized 1920x1111 window at 125%, a top strip
        // 31.2 points tall, and a 3D view reaching to 889.6 — the last row of a layout
        // measured against the window as it stood a frame earlier, one row past the 1111
        // this frame renders into. Both edges land exactly (31.2 and 858.4 points are 39
        // and 1073 pixels), so the viewport asks for row 1112 of a target 1111 rows tall.
        let points = egui::Rect::from_min_max(egui::pos2(0.0, 31.2), egui::pos2(1536.0, 889.6));
        let (position, size) = physical_viewport(points, 1.25, UVec2::new(1920, 1111));
        assert_eq!(position, UVec2::new(0, 39));
        assert_eq!(size, UVec2::new(1920, 1072));
        assert_eq!(position.y + size.y, 1111);

        // The same layout against the window it was restored to: a rect overhanging both
        // axes comes back trimmed on each one, which is the shape the live crash took.
        let (position, size) = physical_viewport(points, 1.25, UVec2::new(1400, 950));
        assert_eq!(position, UVec2::new(0, 39));
        assert_eq!(size, UVec2::new(1400, 911));
        assert_eq!(position.y + size.y, 950);
    }

    #[test]
    fn physical_viewport_comes_back_empty_when_the_target_holds_none_of_it() {
        // Panels stacked taller than a small window, an inverted rect, and a rect entirely
        // past the window all have to read as "no viewport", which is what `main.rs` checks
        // before it touches the camera.
        let target = UVec2::new(1025, 750); // the reference's 820x600 minimum, at 125%
        let cases = [
            // Panels stacked taller than the window: the leftover rect starts below it.
            egui::Rect::from_min_max(egui::pos2(0.0, 620.0), egui::pos2(800.0, 700.0)),
            // An inverted rect, which `Rect` is free to hold and a caller could hand over.
            egui::Rect::from_min_max(egui::pos2(0.0, 500.0), egui::pos2(0.0, 400.0)),
            // A rect entirely past the window's right edge.
            egui::Rect::from_min_max(egui::pos2(900.0, 0.0), egui::pos2(1200.0, 100.0)),
        ];
        for points in cases {
            let (position, size) = physical_viewport(points, 1.25, target);
            assert!(
                size.x == 0 || size.y == 0,
                "{points:?} -> {position:?} + {size:?}"
            );
        }
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

    /// The two button rows exactly as they read in the panel, left to right, and what each
    /// button carries with it: the `-` spelling goes with `direction == -1` and the `+`
    /// spelling with `1`, which is the direction the click hands the handler.
    ///
    /// The ways to get this wrong are a suffix taken from the other branch of the sign test,
    /// a letter taken from the other axis, and an `R` on the row that moves the tool rather
    /// than turning it — the panel's two nested loops put all three next to each other.
    #[test]
    fn a_jog_button_is_labelled_with_the_axis_and_direction_it_carries() {
        let rows = [
            (false, ["X-", "X+", "Y-", "Y+", "Z-", "Z+"]),
            (true, ["RX-", "RX+", "RY-", "RY+", "RZ-", "RZ+"]),
        ];
        for (rotating, expected) in rows {
            let rendered: Vec<String> = Axis::ALL
                .iter()
                .flat_map(|axis| {
                    [-1, 1].map(|direction| jog_button_label(*axis, direction, rotating))
                })
                .collect();
            let row = if rotating { "rotation" } else { "translation" };
            assert_eq!(rendered, expected, "the {row} row");
        }
    }
}
