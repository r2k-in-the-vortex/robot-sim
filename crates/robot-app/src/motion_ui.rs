//! The Motion tab: the editor and queue on the left, the planned-motion graphs below.
//!
//! The panels are laid out in [`crate::ui`]; this module only draws their contents and
//! calls into [`crate::motion`], which owns every rule about what a command means. The
//! plots show the whole planned trajectory and a cursor at the playback time: the arm in
//! the central 3D view and the cursor therefore describe the same instant.

use bevy_egui::egui::{self, Color32, RichText, Stroke};
use egui_plot::{Corner, Legend, Line, LineStyle, Plot, VLine};
use robot_kinematics::JOINT_COUNT;
use robot_model::{DHParameters, FRAME_COUNT, MotionLimits};

use crate::RobotState;
use crate::motion::{
    CommandLimits, MotionCommand, MotionRuntime, PlanSource, PlaybackPlan, command_from_json,
    command_to_json, queue_to_json,
};
use crate::session;

/// Status: something is capped by a physical limit, which is a warning rather than a
/// failure. Paired with the star and the explanatory line, never color alone.
const CAP_COLOR: Color32 = Color32::from_rgb(0xb8, 0x6e, 0x00);
/// Status: a refusal. Paired with the word "Error".
const CRITICAL: Color32 = Color32::from_rgb(0xd0, 0x3b, 0x3b);
/// The plot grid, the same recessive gray the reference charts use.
const GRID: Color32 = Color32::from_rgb(0xe1, 0xe0, 0xd9);
/// The cursor is the one loud mark on the plots.
const CURSOR: Color32 = Color32::from_rgb(0x0b, 0x0b, 0x0b);

/// The six joint series. The order is fixed so a joint keeps its color in the legend, the
/// live-value swatches and every plot.
const JOINT_COLORS: [Color32; JOINT_COUNT] = [
    Color32::from_rgb(0x2a, 0x78, 0xd6),
    Color32::from_rgb(0xeb, 0x68, 0x34),
    Color32::from_rgb(0x1b, 0xaf, 0x7a),
    Color32::from_rgb(0xed, 0xa1, 0x00),
    Color32::from_rgb(0xe8, 0x7b, 0xa4),
    Color32::from_rgb(0x00, 0x83, 0x00),
];

/// X, Y, Z in the gizmo colors the 3D view uses.
const XYZ_COLORS: [Color32; 3] = [
    Color32::from_rgb(0xd9, 0x4a, 0x45),
    Color32::from_rgb(0x31, 0x84, 0x5b),
    Color32::from_rgb(0x39, 0x78, 0xc5),
];

/// The Motion tab's left panel.
pub fn controls(ui: &mut egui::Ui, motion: &mut MotionRuntime, robot: &RobotState) {
    let parameters = robot.document.parameters;
    let physical = robot.document.motion_limits;
    let current = robot.runtime_angles_deg;

    ui.add_space(4.0);
    ui.heading("Motion");
    ui.label(
        RichText::new(
            "MoveJ: one joint-space S-curve, so every joint starts and stops together \
             and the slowest one sets the pace.",
        )
        .small(),
    );
    ui.add_space(4.0);
    status_line(ui, motion);

    ui.separator();
    live_values(ui, robot);
    ui.separator();
    editor_section(ui, motion, &parameters, &physical, current);
    ui.separator();
    queue_section(ui, motion, &parameters, &physical, current);
    ui.separator();
    json_section(ui, motion, &parameters, &physical, current);
}

fn status_line(ui: &mut egui::Ui, motion: &MotionRuntime) {
    if motion.status_is_error {
        ui.colored_label(CRITICAL, format!("Error: {}", motion.status));
    } else {
        ui.label(motion.status.as_str());
    }
}

/// The arm's current joint angles and tool pose.
///
/// The swatches carry the same color as the plot line, and the numbers stay in plain ink:
/// four of the categorical hues are below 3:1 on the light surface, so color is a locator
/// here, never the only way to read the value.
fn live_values(ui: &mut egui::Ui, robot: &RobotState) {
    ui.label(RichText::new("Current pose").strong());
    egui::Grid::new("motion_live_joints")
        .num_columns(3)
        .spacing([10.0, 2.0])
        .show(ui, |ui| {
            for (joint, angle) in robot.runtime_angles_deg.iter().enumerate() {
                ui.horizontal(|ui| {
                    swatch(ui, JOINT_COLORS[joint]);
                    ui.label(
                        RichText::new(format!("J{} {:.2}°", joint + 1, angle))
                            .monospace()
                            .small(),
                    );
                });
                if (joint + 1) % 3 == 0 {
                    ui.end_row();
                }
            }
        });

    match robot
        .document
        .parameters
        .carrier_pose(&robot.runtime_angles_deg)
    {
        Ok(poses) => {
            let tool = poses[FRAME_COUNT - 1];
            ui.horizontal_wrapped(|ui| {
                for (index, (axis, value)) in
                    [("X", tool.p.x()), ("Y", tool.p.y()), ("Z", tool.p.z())]
                        .into_iter()
                        .enumerate()
                {
                    swatch(ui, XYZ_COLORS[index]);
                    ui.label(
                        RichText::new(format!("{axis} {value:.2}"))
                            .monospace()
                            .small(),
                    );
                    ui.add_space(6.0);
                }
            });
            let [roll, pitch, yaw] = session::rotation_to_rpy_degrees(&tool);
            ui.label(
                RichText::new(format!("RPY {roll:.1}° / {pitch:.1}° / {yaw:.1}°"))
                    .monospace()
                    .small(),
            );
        }
        Err(error) => {
            ui.label(
                RichText::new(format!("Tool pose unavailable: {error}"))
                    .small()
                    .color(ui.visuals().weak_text_color()),
            );
        }
    }
}

fn swatch(ui: &mut egui::Ui, color: Color32) {
    let (rect, _) = ui.allocate_exact_size(egui::vec2(8.0, 8.0), egui::Sense::hover());
    ui.painter().rect_filled(rect, 2.0, color);
}

fn editor_section(
    ui: &mut egui::Ui,
    motion: &mut MotionRuntime,
    parameters: &DHParameters,
    physical: &MotionLimits,
    current: [f64; JOINT_COUNT],
) {
    egui::CollapsingHeader::new("Joint move (MoveJ)")
        .default_open(true)
        .show(ui, |ui| {
            ui.label(RichText::new("Start (deg)").small());
            joint_fields(ui, "motion_start", &mut motion.editor.start_deg);
            ui.horizontal_wrapped(|ui| {
                if ui
                    .add_enabled(!motion.active, egui::Button::new("From current"))
                    .on_hover_text("Fill the start from the arm's current joint angles")
                    .clicked()
                {
                    motion.fill_start_from_current(current);
                }
                if ui
                    .add_enabled(
                        !motion.active && !motion.commands.is_empty(),
                        egui::Button::new("From last queued"),
                    )
                    .on_hover_text("Fill the start from the last queued move's stop")
                    .clicked()
                    && let Err(error) = motion.fill_start_from_last()
                {
                    motion.status = error;
                    motion.status_is_error = true;
                }
            });

            ui.add_space(4.0);
            ui.label(RichText::new("Stop (deg)").small());
            joint_fields(ui, "motion_stop", &mut motion.editor.stop_deg);
            ui.add_space(4.0);
            limit_fields(ui, &mut motion.editor.limits);

            let draft = motion.editor.command();
            let draft_plan = draft.plan(physical);
            match &draft_plan {
                Ok(profile) => {
                    ui.label(
                        RichText::new(format!("Duration: {:.2} s", profile.total_time()))
                            .monospace()
                            .small(),
                    );
                }
                Err(error) => {
                    ui.colored_label(CRITICAL, format!("Error: {error}"));
                }
            }

            let capped = motion.editor.limits.exceeds_physical(physical);
            effective_limits(ui, motion.editor.limits, physical, capped);
            if capped {
                ui.label(
                    RichText::new(cap_summary(motion.editor.limits, physical))
                        .small()
                        .color(CAP_COLOR),
                );
            }

            ui.add_space(4.0);
            if ui
                .add_enabled(
                    !motion.active && draft_plan.is_ok(),
                    egui::Button::new("Add to queue"),
                )
                .clicked()
                && let Err(error) = motion.add_command(parameters, physical, current)
            {
                motion.status = error;
                motion.status_is_error = true;
            }
        });
}

fn joint_fields(ui: &mut egui::Ui, id: &str, values: &mut [f64; JOINT_COUNT]) {
    egui::Grid::new(id)
        .num_columns(JOINT_COUNT)
        .spacing([4.0, 2.0])
        .show(ui, |ui| {
            for joint in 0..JOINT_COUNT {
                ui.label(RichText::new(format!("J{}", joint + 1)).small());
            }
            ui.end_row();
            for value in values.iter_mut() {
                ui.add_sized(
                    [44.0, 18.0],
                    egui::DragValue::new(value).speed(0.5).max_decimals(3),
                );
            }
            ui.end_row();
        });
}

fn limit_fields(ui: &mut egui::Ui, limits: &mut CommandLimits) {
    egui::Grid::new("motion_command_limits")
        .num_columns(3)
        .spacing([8.0, 2.0])
        .show(ui, |ui| {
            ui.label(RichText::new("V (deg/s)").small());
            ui.label(RichText::new("A (deg/s²)").small());
            ui.label(RichText::new("J (deg/s³)").small());
            ui.end_row();
            for value in [
                &mut limits.velocity_deg_s,
                &mut limits.acceleration_deg_s2,
                &mut limits.jerk_deg_s3,
            ] {
                ui.add(
                    egui::DragValue::new(value)
                        .range(0.001..=1.0e6)
                        .speed(1.0)
                        .max_decimals(3),
                );
            }
            ui.end_row();
        });
}

/// The effective per-joint table: the command's request after the document's ceilings.
fn effective_limits(
    ui: &mut egui::Ui,
    command: CommandLimits,
    physical: &MotionLimits,
    capped: bool,
) {
    egui::CollapsingHeader::new("Effective joint limits")
        .default_open(capped)
        .show(ui, |ui| {
            if capped {
                ui.label(
                    RichText::new(
                        "Effective values, in the same units as the fields above. A star \
                         marks a component the joint's physical limit caps.",
                    )
                    .small()
                    .color(ui.visuals().weak_text_color()),
                );
            } else {
                ui.label(
                    RichText::new(
                        "The command is below every joint's physical limits; nothing is \
                         capped.",
                    )
                    .small()
                    .color(ui.visuals().weak_text_color()),
                );
            }

            let effective = command.effective_per_joint(physical);
            egui::Grid::new("motion_effective_limits")
                .num_columns(4)
                .spacing([10.0, 2.0])
                .striped(true)
                .show(ui, |ui| {
                    for heading in ["Joint", "V", "A", "J"] {
                        ui.label(RichText::new(heading).small());
                    }
                    ui.end_row();
                    for (joint, limits) in effective.iter().enumerate() {
                        ui.label(RichText::new(format!("J{}", joint + 1)).small());
                        cap_cell(
                            ui,
                            limits.velocity_deg_s,
                            command.velocity_deg_s,
                            physical.joints[joint].velocity_deg_s,
                        );
                        cap_cell(
                            ui,
                            limits.acceleration_deg_s2,
                            command.acceleration_deg_s2,
                            physical.joints[joint].acceleration_deg_s2,
                        );
                        cap_cell(
                            ui,
                            limits.jerk_deg_s3,
                            command.jerk_deg_s3,
                            physical.joints[joint].jerk_deg_s3,
                        );
                        ui.end_row();
                    }
                });
        });
}

/// One line naming every component the physical limits cap, so the warning is useful
/// without opening the table. The table itself has the full effective values.
fn cap_summary(command: CommandLimits, physical: &MotionLimits) -> String {
    let mut parts = Vec::new();
    for (joint, limits) in physical.joints.iter().enumerate() {
        if command.velocity_deg_s > limits.velocity_deg_s {
            parts.push(format!("J{} V {:.1}", joint + 1, limits.velocity_deg_s));
        }
        if command.acceleration_deg_s2 > limits.acceleration_deg_s2 {
            parts.push(format!(
                "J{} A {:.1}",
                joint + 1,
                limits.acceleration_deg_s2
            ));
        }
        if command.jerk_deg_s3 > limits.jerk_deg_s3 {
            parts.push(format!("J{} J {:.1}", joint + 1, limits.jerk_deg_s3));
        }
    }
    format!("Capped by joint limits: {}.", parts.join(", "))
}

fn cap_cell(ui: &mut egui::Ui, effective: f64, requested: f64, physical: f64) {
    let capped = requested > physical;
    let text = if capped {
        format!("{effective:.1}*")
    } else {
        format!("{effective:.1}")
    };
    let color = if capped {
        CAP_COLOR
    } else {
        ui.visuals().weak_text_color()
    };
    ui.label(RichText::new(text).monospace().small().color(color));
}

fn queue_section(
    ui: &mut egui::Ui,
    motion: &mut MotionRuntime,
    parameters: &DHParameters,
    physical: &MotionLimits,
    current: [f64; JOINT_COUNT],
) {
    ui.horizontal(|ui| {
        ui.label(RichText::new(format!("Queue ({})", motion.commands.len())).strong());
        if let Some(plan) = &motion.plan {
            ui.label(
                RichText::new(format!(
                    "Plan: {} transition(s), {:.2} s",
                    plan.transitions(),
                    plan.total_time()
                ))
                .small()
                .color(ui.visuals().weak_text_color()),
            );
        }
    });

    if motion.commands.is_empty() {
        ui.label(
            RichText::new("No commands yet. The queue JSON below is the way to move one.")
                .small()
                .color(ui.visuals().weak_text_color()),
        );
    }

    // Removal is collected and applied after the loop: the list cannot be mutated while it
    // is being iterated.
    let mut remove = None;
    for (index, command) in motion.commands.iter().enumerate() {
        ui.horizontal(|ui| {
            let duration = command.plan(physical).map(|profile| profile.total_time());
            let text = match duration {
                Ok(duration) => {
                    format!("#{} {}  {:.2} s", index + 1, command.kind_name(), duration)
                }
                Err(_) => format!("#{} {}  invalid", index + 1, command.kind_name()),
            };
            ui.label(RichText::new(text).small());
            if ui
                .add_enabled(!motion.active, egui::Button::new("Remove").small())
                .clicked()
            {
                remove = Some(index);
            }
        });
        ui.label(
            RichText::new(format!(
                "  S {}   E {}",
                vector_text(command.start_deg()),
                vector_text(command.stop_deg())
            ))
            .monospace()
            .small()
            .color(ui.visuals().weak_text_color()),
        );
    }
    if let Some(index) = remove {
        motion.remove_command(index, parameters, physical, current);
    }

    ui.add_space(4.0);
    ui.horizontal_wrapped(|ui| {
        let can_play = !motion.active && !motion.commands.is_empty();
        if ui
            .add_enabled(can_play, egui::Button::new("▶ Play all"))
            .clicked()
            && let Err(error) = motion.play_all(parameters, physical, current)
        {
            motion.status = error;
            motion.status_is_error = true;
        }

        if motion.active {
            if ui
                .button(if motion.playing {
                    "⏸ Pause"
                } else {
                    "▶ Resume"
                })
                .clicked()
            {
                if motion.playing {
                    motion.pause();
                } else {
                    motion.resume();
                }
            }
            if ui.button("⏹ Stop").clicked() {
                motion.stop();
            }
        }

        if ui
            .add_enabled(!motion.active, egui::Button::new("Refresh preview"))
            .on_hover_text("Rebuild the plan from the arm's current pose")
            .clicked()
        {
            motion.preview_dirty = true;
            motion.plan_source = Some(PlanSource::Preview);
            motion.ensure_preview(parameters, physical, current);
        }
        if ui
            .add_enabled(
                !motion.active && !motion.commands.is_empty(),
                egui::Button::new("Clear queue"),
            )
            .clicked()
        {
            motion.clear_queue(parameters, physical, current);
        }
    });

    if let Some(plan) = &motion.plan {
        let total = plan.total_time();
        if total > 0.0 {
            let t = motion.time.clamp(0.0, total);
            ui.label(
                RichText::new(format!("t = {:.2} / {:.2} s", t, total))
                    .monospace()
                    .small(),
            );
            ui.add(egui::ProgressBar::new((t / total) as f32).show_percentage());
            if let Some(label) = motion.current_segment_label() {
                ui.label(RichText::new(label).small());
            }
        } else {
            ui.label(
                RichText::new("The queue has no motion.")
                    .small()
                    .color(ui.visuals().weak_text_color()),
            );
        }
    }
    if let Some(error) = &motion.plan_error {
        ui.colored_label(CRITICAL, format!("Plan error: {error}"));
    }
}

fn json_section(
    ui: &mut egui::Ui,
    motion: &mut MotionRuntime,
    parameters: &DHParameters,
    physical: &MotionLimits,
    current: [f64; JOINT_COUNT],
) {
    egui::CollapsingHeader::new("Command JSON")
        .default_open(false)
        .show(ui, |ui| {
            match command_to_json(&motion.editor.command()) {
                Ok(json) => {
                    if ui.button("Copy command JSON").clicked() {
                        ui.ctx().copy_text(json.clone());
                        motion.status = String::from("Copied command JSON.");
                        motion.status_is_error = false;
                    }
                    ui.add(
                        egui::Label::new(RichText::new(json).monospace().small()).selectable(true),
                    );
                }
                Err(error) => {
                    ui.colored_label(CRITICAL, format!("Error: {error}"));
                }
            }
            ui.add_space(4.0);
            ui.label(RichText::new("Paste a command, then load it into the editor:").small());
            ui.add(
                egui::TextEdit::multiline(&mut motion.command_import)
                    .desired_rows(4)
                    .code_editor(),
            );
            if ui
                .add_enabled(!motion.active, egui::Button::new("Load command"))
                .clicked()
            {
                match command_from_json(&motion.command_import) {
                    Ok(MotionCommand::MoveJ(command)) => {
                        motion.editor.start_deg = command.start_deg;
                        motion.editor.stop_deg = command.stop_deg;
                        motion.editor.limits = command.limits;
                        motion.command_import.clear();
                        motion.status = String::from("Loaded the command into the editor.");
                        motion.status_is_error = false;
                    }
                    Err(error) => {
                        motion.status = error;
                        motion.status_is_error = true;
                    }
                }
            }
        });

    egui::CollapsingHeader::new("Queue JSON")
        .default_open(false)
        .show(ui, |ui| {
            match queue_to_json(&motion.commands) {
                Ok(json) => {
                    if ui.button("Copy queue JSON").clicked() {
                        ui.ctx().copy_text(json.clone());
                        motion.status = String::from("Copied queue JSON.");
                        motion.status_is_error = false;
                    }
                    ui.add(
                        egui::Label::new(RichText::new(json).monospace().small()).selectable(true),
                    );
                }
                Err(error) => {
                    ui.colored_label(CRITICAL, format!("Error: {error}"));
                }
            }
            ui.add_space(4.0);
            ui.label(RichText::new("Paste a queue, then load it:").small());
            ui.add(
                egui::TextEdit::multiline(&mut motion.queue_import)
                    .desired_rows(6)
                    .code_editor(),
            );
            if ui
                .add_enabled(!motion.active, egui::Button::new("Load queue"))
                .clicked()
            {
                // Cloned because `import_queue` needs the runtime mutably while it reads
                // the text.
                let text = motion.queue_import.clone();
                match motion.import_queue(&text, parameters, physical, current) {
                    Ok(()) => {
                        motion.queue_import.clear();
                        motion.status = String::from("Loaded the queue.");
                        motion.status_is_error = false;
                    }
                    Err(error) => {
                        motion.status = error;
                        motion.status_is_error = true;
                    }
                }
            }
        });
}

fn vector_text(values: [f64; JOINT_COUNT]) -> String {
    values
        .iter()
        .map(|value| format!("{value:.1}"))
        .collect::<Vec<String>>()
        .join(" ")
}

/// The bottom panel: the whole planned trajectory plus the playback cursor.
pub fn plots(ui: &mut egui::Ui, motion: &MotionRuntime) {
    ui.add_space(2.0);
    if let Some(error) = &motion.plan_error {
        ui.colored_label(CRITICAL, format!("Plan error: {error}"));
        return;
    }
    let Some(plan) = &motion.plan else {
        ui.label(
            RichText::new("Add a command to see the planned joint and Cartesian graphs.")
                .color(ui.visuals().weak_text_color()),
        );
        return;
    };
    if plan.total_time() <= 0.0 {
        ui.label(
            RichText::new("The queue has no motion to graph.")
                .color(ui.visuals().weak_text_color()),
        );
        return;
    }

    let cursor = motion.time.clamp(0.0, plan.total_time());
    let reset = motion.reset_plots;
    let available = ui.available_size();
    let height = available.y.max(120.0);
    let gutter = 8.0;
    let left_width = (available.x * 0.5).max(220.0);
    let right_width = (available.x - left_width - gutter).max(160.0);

    ui.horizontal(|ui| {
        ui.allocate_ui_with_layout(
            egui::vec2(left_width, height),
            egui::Layout::top_down(egui::Align::Min),
            |ui| joint_plot(ui, plan, cursor, height, reset),
        );
        ui.allocate_ui_with_layout(
            egui::vec2(right_width, height),
            egui::Layout::top_down(egui::Align::Min),
            |ui| {
                if let Some(error) = plan.cartesian_error() {
                    ui.label(RichText::new("Cartesian graphs unavailable").strong());
                    ui.colored_label(CRITICAL, error);
                } else {
                    let lane = (height - 18.0) / 2.0;
                    xyz_plot(ui, plan, cursor, lane, reset);
                    rpy_plot(ui, plan, cursor, lane, reset);
                }
            },
        );
    });
}

fn joint_plot(ui: &mut egui::Ui, plan: &PlaybackPlan, cursor: f64, height: f32, reset: bool) {
    ui.label(RichText::new("Joint angles [deg]").strong());
    let plot = base_plot("motion-joint-plot", (height - 22.0).max(60.0), reset, true)
        .y_axis_label("angle [deg]");
    plot.show(ui, |plot_ui| {
        boundaries(plot_ui, plan);
        for (joint, series) in plan.joint_series().iter().enumerate() {
            plot_ui.line(
                Line::new(format!("J{}", joint + 1), series.clone())
                    .color(JOINT_COLORS[joint])
                    .width(2.0),
            );
        }
        cursor_line(plot_ui, cursor);
    });
}

fn xyz_plot(ui: &mut egui::Ui, plan: &PlaybackPlan, cursor: f64, height: f32, reset: bool) {
    ui.label(RichText::new("Tool position [model units]: X, Y, Z").strong());
    let plot = base_plot("motion-xyz-plot", (height - 22.0).max(50.0), reset, false)
        .y_axis_label("position");
    plot.show(ui, |plot_ui| {
        boundaries(plot_ui, plan);
        for (axis, series) in plan.xyz_series().iter().enumerate() {
            plot_ui.line(
                Line::new(["X", "Y", "Z"][axis], series.clone())
                    .color(XYZ_COLORS[axis])
                    .width(2.0),
            );
        }
        cursor_line(plot_ui, cursor);
    });
}

fn rpy_plot(ui: &mut egui::Ui, plan: &PlaybackPlan, cursor: f64, height: f32, reset: bool) {
    ui.label(RichText::new("Tool orientation ZYX [deg], unwrapped: Roll, Pitch, Yaw").strong());
    let plot = base_plot("motion-rpy-plot", (height - 22.0).max(50.0), reset, false)
        .y_axis_label("angle [deg]");
    plot.show(ui, |plot_ui| {
        boundaries(plot_ui, plan);
        for (axis, series) in plan.rpy_series().iter().enumerate() {
            plot_ui.line(
                Line::new(["Roll", "Pitch", "Yaw"][axis], series.clone())
                    .color(XYZ_COLORS[axis])
                    .width(2.0),
            );
        }
        cursor_line(plot_ui, cursor);
    });
}

fn base_plot(id: &'static str, height: f32, reset: bool, legend: bool) -> Plot<'static> {
    let plot = Plot::new(id)
        .height(height)
        .show_axes([true, true])
        .show_grid(true)
        .grid_color(GRID)
        .link_axis("motion-time-axis", egui::Vec2b::new(true, false))
        .x_axis_label("time [s]");
    // The right-hand plots are too narrow for a legend box and name their three series
    // in the title instead; the joint plot has room and six series to identify.
    let plot = if legend {
        plot.legend(
            Legend::default()
                .position(Corner::LeftTop)
                .text_style(egui::TextStyle::Small),
        )
    } else {
        plot
    };
    if reset { plot.reset() } else { plot }
}

fn boundaries(plot_ui: &mut egui_plot::PlotUi<'_>, plan: &PlaybackPlan) {
    for (index, segment) in plan.segments().iter().enumerate().skip(1) {
        plot_ui.vline(
            VLine::new(format!("segment boundary {index}"), segment.start_time)
                .stroke(Stroke::new(1.0, GRID))
                .style(LineStyle::dashed_dense()),
        );
    }
}

fn cursor_line(plot_ui: &mut egui_plot::PlotUi<'_>, cursor: f64) {
    plot_ui.vline(VLine::new("cursor", cursor).stroke(Stroke::new(1.5, CURSOR)));
}
