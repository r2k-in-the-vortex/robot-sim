//! The demo window: controls on the left, four linked planned-output lanes, and a
//! timeline that scrubs through the profile.

use eframe::egui::{self, Align, DragValue, Grid, Layout, RichText, Slider};
use robot_motion::{Limits, PlanError, PlanKind};

use crate::plan::{DemoParams, DemoPlan, Planner, StopCheck, Viability, thresholds, viability};
use crate::plot::{self, Lane, Overlays};
use crate::style::{CRITICAL, GOOD, Palette, number, short};

/// Everything the window keeps between frames. The plan itself is rebuilt from the
/// parameters every frame: it is cheap, and it can never be stale while a slider moves.
pub struct DemoApp {
    params: DemoParams,
    cursor_t: f64,
    playing: bool,
    looping: bool,
    show_limits: bool,
    show_phase_lines: bool,
    show_phase_table: bool,
}

impl Default for DemoApp {
    fn default() -> Self {
        Self {
            params: DemoParams::default(),
            cursor_t: 0.0,
            playing: false,
            looping: true,
            show_limits: true,
            show_phase_lines: true,
            show_phase_table: true,
        }
    }
}

impl eframe::App for DemoApp {
    fn ui(&mut self, ui: &mut egui::Ui, _frame: &mut eframe::Frame) {
        // A non-rest boundary is only handled by the general planner.
        if self.params.non_rest {
            self.params.planner = Planner::General;
        }

        self.header(ui);

        let mut planned = None;
        egui::Panel::left("motion-controls")
            .resizable(true)
            .default_size(360.0)
            .min_size(320.0)
            .max_size(540.0)
            .show(ui, |ui| {
                egui::ScrollArea::vertical()
                    .auto_shrink([false, false])
                    .show(ui, |ui| {
                        self.controls(ui);
                        let result = self.params.plan();
                        self.status(ui, &result);
                        self.overlays(ui);
                        if let Ok(plan) = &result {
                            self.phase_table(ui, plan);
                        }
                        self.how_to_read(ui);
                        planned = Some(result);
                    });
            });

        let planned = planned.expect("the side panel is always shown");
        match planned {
            Ok(plan) => {
                let ctx = ui.ctx().clone();
                self.advance_playback(&ctx, plan.total_time);
                self.timeline(ui, Some(&plan));
                egui::CentralPanel::default().show(ui, |ui| self.graphs(ui, &plan));
            }
            Err(error) => {
                self.playing = false;
                self.timeline(ui, None);
                egui::CentralPanel::default().show(ui, |ui| self.error_page(ui, error));
            }
        }
    }
}

impl DemoApp {
    fn header(&self, ui: &mut egui::Ui) {
        egui::Panel::top("motion-header").show(ui, |ui| {
            let palette = Palette::new(ui);
            ui.add_space(4.0);
            ui.horizontal(|ui| {
                ui.heading("1-DOF motion planner");
                ui.label(
                    RichText::new("robot-motion · jerk-limited S-curves").color(palette.muted),
                );
            });
            ui.label(
                "Edit the limits and boundary states. Every curve is evaluated from the \
                 planner's piecewise-cubic profile, and the timeline scrubs through it.",
            );
            ui.add_space(4.0);
        });
    }

    fn controls(&mut self, ui: &mut egui::Ui) {
        let palette = Palette::new(ui);
        ui.add_space(4.0);

        ui.label(RichText::new("Planner").strong());
        let mut planner = self.params.planner;
        let non_rest = self.params.non_rest;
        ui.add_enabled_ui(!non_rest, |ui| {
            ui.radio_value(&mut planner, Planner::Optimal, Planner::Optimal.title());
            ui.radio_value(
                &mut planner,
                Planner::Conservative,
                Planner::Conservative.title(),
            );
        });
        ui.radio_value(&mut planner, Planner::General, Planner::General.title());
        self.params.planner = planner;
        ui.label(RichText::new(planner.note()).small().color(palette.muted));

        ui.add_space(8.0);
        ui.separator();
        ui.label(RichText::new("Limits").strong());
        ui.scope(|ui| {
            ui.spacing_mut().slider_width = (ui.available_width() - 6.0).max(120.0);
            limit_control(
                ui,
                "Velocity limit  V",
                &mut self.params.vmax,
                0.001..=100.0,
                0.01,
                " u/s",
            );
            limit_control(
                ui,
                "Acceleration limit  A",
                &mut self.params.amax,
                0.001..=500.0,
                0.05,
                " u/s²",
            );
            limit_control(
                ui,
                "Jerk limit  J",
                &mut self.params.jmax,
                0.001..=5000.0,
                0.5,
                " u/s³",
            );
        });
        self.thresholds_section(ui);

        ui.add_space(8.0);
        ui.separator();
        ui.label(RichText::new("Boundary states").strong());
        state_control(ui, "Start position  q0", &mut self.params.q0, " u");
        state_control(
            ui,
            if self.params.non_rest {
                "End position  q1"
            } else {
                "Stop position  q1"
            },
            &mut self.params.q1,
            " u",
        );
        ui.checkbox(&mut self.params.non_rest, "Non-rest boundaries  (v, a ≠ 0)");
        if self.params.non_rest {
            ui.label(
                RichText::new(
                    "The general planner is required: it brakes to rest, moves, then \
                     time-reverses a stop to reach the target vector.",
                )
                .small()
                .color(palette.muted),
            );
            ui.add_space(2.0);
            state_control(ui, "Start velocity  v0", &mut self.params.v0, " u/s");
            state_control(ui, "Start acceleration  a0", &mut self.params.a0, " u/s²");
            state_control(ui, "End velocity  v1", &mut self.params.v1, " u/s");
            state_control(ui, "End acceleration  a1", &mut self.params.a1, " u/s²");
        }

        if self.params.effective_planner() == Planner::General
            && let Ok(limits) = self.params.limits()
        {
            let check = viability(&self.params, limits);
            self.viability_section(ui, check, limits);
        }
    }

    fn overlays(&mut self, ui: &mut egui::Ui) {
        ui.add_space(8.0);
        ui.separator();
        ui.label(RichText::new("Overlays").strong());
        ui.checkbox(&mut self.show_limits, "Show limit lines");
        ui.checkbox(&mut self.show_phase_lines, "Show phase boundaries");
        ui.checkbox(&mut self.show_phase_table, "Show phase table");
        ui.add_space(4.0);
        if ui
            .button("Reset inputs")
            .on_hover_text("Restore the demo's starting limits and boundary states")
            .clicked()
        {
            *self = Self::default();
        }
    }

    fn thresholds_section(&self, ui: &mut egui::Ui) {
        let Ok(limits) = self.params.limits() else {
            return;
        };
        let thresholds = thresholds(limits);
        egui::CollapsingHeader::new("Derived thresholds")
            .default_open(false)
            .show(ui, |ui| {
                Grid::new("threshold-grid")
                    .num_columns(2)
                    .spacing([10.0, 2.0])
                    .show(ui, |ui| {
                        kv(ui, "t_j = A/J", format!("{} s", number(thresholds.t_j)));
                        kv(ui, "v_A = A²/J", format!("{} u/s", number(thresholds.v_a)));
                        match self.params.effective_planner() {
                            Planner::Optimal => {
                                kv(
                                    ui,
                                    "cruise when |Δq| ≥ d_full",
                                    format!("{} u", number(thresholds.d_full)),
                                );
                            }
                            Planner::Conservative | Planner::General => {
                                kv(
                                    ui,
                                    "τ = min(1, A/J, V/J)",
                                    format!("{} s", number(thresholds.tau)),
                                );
                                kv(
                                    ui,
                                    "cruise when |Δq| ≥ Δ_min",
                                    format!("{} u", number(thresholds.d_min)),
                                );
                            }
                        }
                    });
            });
    }

    fn viability_section(&self, ui: &mut egui::Ui, check: Viability, limits: Limits) {
        let palette = Palette::new(ui);
        ui.add_space(6.0);
        ui.horizontal(|ui| {
            ui.label(RichText::new("Boundary viability").strong());
            if check.is_viable() {
                ui.colored_label(GOOD, "viable");
            } else {
                ui.colored_label(CRITICAL, "not viable");
            }
        });
        ui.label(
            RichText::new(
                "The exact stop–move–start test. Outside it this decomposition cannot \
                 stop or restart without leaving the velocity band.",
            )
            .small()
            .color(palette.muted),
        );
        Grid::new("viability-grid")
            .num_columns(4)
            .spacing([8.0, 3.0])
            .striped(true)
            .show(ui, |ui| {
                for heading in ["", "|v| ≤ V", "|a| ≤ A", "|v_s|, |v_e| ≤ V"] {
                    ui.label(RichText::new(heading).small().color(palette.muted));
                }
                ui.end_row();
                check_row(ui, "start", check.start, limits);
                check_row(ui, "target", check.target, limits);
            });
        ui.label(
            RichText::new("v_s = v + a|a|/(2J),  v_e = v − a|a|/(2J).")
                .small()
                .color(palette.muted),
        );
    }

    fn status(&self, ui: &mut egui::Ui, result: &Result<DemoPlan, PlanError>) {
        let palette = Palette::new(ui);
        ui.add_space(8.0);
        ui.separator();
        ui.label(RichText::new("Plan output").strong());
        match result {
            Ok(plan) => {
                Grid::new("status-grid")
                    .num_columns(2)
                    .spacing([12.0, 2.0])
                    .show(ui, |ui| {
                        kv(ui, "shape", kind_name(plan.kind));
                        kv(ui, "duration", format!("{} s", number(plan.total_time)));
                        kv(ui, "phases", plan.phases.len().to_string());
                        kv(
                            ui,
                            "displacement",
                            format!(
                                "{} u",
                                number(plan.profile.end().q - plan.profile.start().q)
                            ),
                        );
                        kv(ui, "peak |v|", format!("{} u/s", number(plan.peaks.v)));
                        kv(ui, "peak |a|", format!("{} u/s²", number(plan.peaks.a)));
                        kv(ui, "peak |j|", format!("{} u/s³", number(plan.peaks.j)));
                    });
            }
            Err(error) => {
                ui.colored_label(CRITICAL, format!("Error: {error}"));
                ui.label(
                    RichText::new(
                        "No curve is drawn from a rejected plan; adjust the boundary \
                         states or the limits.",
                    )
                    .small()
                    .color(palette.muted),
                );
            }
        }
    }

    fn phase_table(&self, ui: &mut egui::Ui, plan: &DemoPlan) {
        if !self.show_phase_table {
            return;
        }
        let palette = Palette::new(ui);
        ui.add_space(6.0);
        egui::CollapsingHeader::new(format!("Phases ({})", plan.phases.len()))
            .default_open(true)
            .show(ui, |ui| {
                if plan.phases.is_empty() {
                    ui.label(RichText::new("No phases — zero motion.").small());
                    return;
                }
                Grid::new("phase-grid")
                    .num_columns(5)
                    .spacing([8.0, 2.0])
                    .striped(true)
                    .show(ui, |ui| {
                        for heading in ["#", "Δt s", "jerk", "q in", "q out"] {
                            ui.label(RichText::new(heading).small().color(palette.muted));
                        }
                        ui.end_row();
                        for phase in &plan.phases {
                            ui.label(
                                RichText::new((phase.index + 1).to_string())
                                    .monospace()
                                    .small(),
                            );
                            ui.label(RichText::new(short(phase.dur)).monospace().small());
                            ui.label(RichText::new(short(phase.jerk)).monospace().small());
                            ui.label(RichText::new(short(phase.entry.q)).monospace().small());
                            ui.label(RichText::new(short(phase.exit.q)).monospace().small());
                            ui.end_row();
                        }
                    });
            });
    }

    fn how_to_read(&self, ui: &mut egui::Ui) {
        let palette = Palette::new(ui);
        ui.add_space(6.0);
        egui::CollapsingHeader::new("How to read this")
            .default_open(false)
            .show(ui, |ui| {
                for line in [
                    "The planner emits a sequence of constant-jerk phases. Position, \
                     velocity and acceleration are continuous; jerk jumps at every \
                     phase boundary.",
                    "Dashed horizontal lines are the active velocity, acceleration and \
                     jerk limits. The faint vertical lines are interior phase boundaries.",
                    "The timeline cursor is the same instant on all four lanes. The dot \
                     marks the planned state at that instant.",
                    "The optimal and conservative planners are rest-to-rest. The general \
                     planner accepts a full (q, v, a) vector at each boundary but is not \
                     time-optimal.",
                ] {
                    ui.label(RichText::new(line).small().color(palette.muted));
                }
            });
    }

    fn advance_playback(&mut self, ctx: &egui::Context, total_time: f64) {
        if total_time <= 0.0 {
            self.cursor_t = 0.0;
            self.playing = false;
            return;
        }
        self.cursor_t = self.cursor_t.clamp(0.0, total_time);
        if self.playing {
            let dt = ctx.input(|input| input.stable_dt).min(0.1) as f64;
            self.cursor_t += dt;
            if self.cursor_t >= total_time {
                if self.looping {
                    self.cursor_t = 0.0;
                } else {
                    self.cursor_t = total_time;
                    self.playing = false;
                }
            }
            ctx.request_repaint();
        }
    }

    fn timeline(&mut self, ui: &mut egui::Ui, plan: Option<&DemoPlan>) {
        egui::Panel::bottom("motion-timeline").show(ui, |ui| {
            let palette = Palette::new(ui);
            ui.add_space(3.0);
            let can_play = plan.is_some_and(|plan| plan.total_time > 0.0);
            ui.horizontal(|ui| {
                if ui
                    .add_enabled(
                        can_play,
                        egui::Button::new(if self.playing {
                            "⏸ Pause"
                        } else {
                            "▶ Play"
                        }),
                    )
                    .clicked()
                {
                    self.playing = !self.playing;
                }
                if ui
                    .add_enabled(can_play, egui::Button::new("⏮ Reset"))
                    .clicked()
                {
                    self.cursor_t = 0.0;
                    self.playing = false;
                }
                match plan {
                    Some(plan) if plan.total_time > 0.0 => {
                        let width = (ui.available_width() - 210.0).max(120.0);
                        ui.spacing_mut().slider_width = width;
                        ui.scope(|ui| {
                            let palette = Palette::new(ui);
                            ui.style_mut().visuals.widgets.inactive.bg_fill = palette.rail;
                            ui.style_mut().visuals.selection.bg_fill = palette.series;
                            ui.add(
                                Slider::new(&mut self.cursor_t, 0.0..=plan.total_time)
                                    .trailing_fill(true)
                                    .show_value(false),
                            );
                        });
                        ui.label(
                            RichText::new(format!(
                                "t = {:.3} / {:.3} s",
                                self.cursor_t, plan.total_time
                            ))
                            .monospace()
                            .small(),
                        );
                    }
                    Some(_) => {
                        ui.label(RichText::new("zero motion").color(palette.muted));
                    }
                    None => {
                        ui.label(RichText::new("plan rejected").color(CRITICAL));
                    }
                }
                ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                    ui.checkbox(&mut self.looping, "Loop");
                });
            });
            if let Some(plan) = plan {
                let state = plan.state_at(self.cursor_t);
                let jerk = plan.jerk_at(self.cursor_t);
                ui.horizontal_wrapped(|ui| {
                    readout(ui, "q", state.q, "u");
                    readout(ui, "v", state.v, "u/s");
                    readout(ui, "a", state.a, "u/s²");
                    readout(ui, "j", jerk, "u/s³");
                });
            }
            ui.add_space(3.0);
        });
    }

    fn graphs(&self, ui: &mut egui::Ui, plan: &DemoPlan) {
        let lanes = [
            Lane::position(),
            Lane::velocity(plan.limits.vmax()),
            Lane::acceleration(plan.limits.amax()),
            Lane::jerk(plan.limits.jmax()),
        ];

        let spacing = ui.spacing().item_spacing.y;
        let heading = ui.spacing().interact_size.y;
        let reserved = lanes.len() as f32 * (heading + 2.0 * spacing);
        let plot_height = ((ui.available_height() - reserved) / lanes.len() as f32).max(90.0);

        let overlays = Overlays {
            show_limits: self.show_limits,
            show_phase_lines: self.show_phase_lines,
            cursor_t: self.cursor_t,
        };
        ui.add_space(2.0);
        for lane in &lanes {
            plot::lane(ui, plan, lane, plot_height, &overlays);
        }
    }

    fn error_page(&self, ui: &mut egui::Ui, error: PlanError) {
        ui.vertical_centered(|ui| {
            ui.add_space(48.0);
            ui.heading("No plan for these inputs");
            ui.colored_label(CRITICAL, format!("Error: {error}"));
            ui.add_space(8.0);
            if matches!(error, PlanError::Infeasible) {
                ui.label(
                    "The general planner's viability test is exact for its \
                     stop–move–start decomposition. Check the boundary-vector table in \
                     the side panel: the adjusted velocities v_s and v_e must stay inside \
                     the velocity band.",
                );
            } else {
                ui.label(
                    "The planner never emits a partial or infeasible profile; adjust the \
                     inputs until it accepts them.",
                );
            }
        });
    }
}

fn limit_control(
    ui: &mut egui::Ui,
    label: &str,
    value: &mut f64,
    range: std::ops::RangeInclusive<f64>,
    speed: f64,
    suffix: &str,
) {
    ui.horizontal(|ui| {
        ui.label(label);
        ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
            ui.add(
                DragValue::new(value)
                    .range(range.clone())
                    .speed(speed)
                    .max_decimals(4)
                    .suffix(suffix),
            );
        });
    });
    ui.scope(|ui| {
        let palette = Palette::new(ui);
        ui.style_mut().visuals.widgets.inactive.bg_fill = palette.rail;
        ui.add(
            Slider::new(value, range)
                .logarithmic(true)
                .show_value(false),
        );
    });
}

fn state_control(ui: &mut egui::Ui, label: &str, value: &mut f64, suffix: &str) {
    ui.horizontal(|ui| {
        ui.label(label);
        ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
            ui.add(
                DragValue::new(value)
                    .speed(0.02)
                    .max_decimals(4)
                    .suffix(suffix),
            );
        });
    });
}

fn check_row(ui: &mut egui::Ui, title: &str, check: StopCheck, limits: Limits) {
    let palette = Palette::new(ui);
    ui.label(RichText::new(title).small().color(palette.muted));
    check_cell(ui, check.v_ok, check.v, limits.vmax());
    check_cell(ui, check.a_ok, check.a, limits.amax());
    check_cell(ui, check.adjusted_ok, check.adjusted, limits.vmax());
    debug_assert!(check.feasible == (check.v_ok && check.a_ok && check.adjusted_ok));
    ui.end_row();
}

fn check_cell(ui: &mut egui::Ui, ok: bool, value: f64, limit: f64) {
    let (label, color) = if ok { ("ok", GOOD) } else { ("no", CRITICAL) };
    ui.label(
        RichText::new(format!("{label} {}/{}", short(value.abs()), short(limit)))
            .monospace()
            .small()
            .color(color),
    );
}

fn readout(ui: &mut egui::Ui, symbol: &str, value: f64, unit: &str) {
    ui.label(
        RichText::new(format!("{symbol} = {} {unit}", number(value)))
            .monospace()
            .small(),
    );
    ui.add_space(10.0);
}

fn kv(ui: &mut egui::Ui, key: &str, value: impl Into<String>) {
    let palette = Palette::new(ui);
    ui.label(RichText::new(key).small().color(palette.muted));
    ui.label(RichText::new(value.into()).monospace().small());
    ui.end_row();
}

fn kind_name(kind: PlanKind) -> &'static str {
    match kind {
        PlanKind::ZeroMotion => "zero motion",
        PlanKind::Conservative => "conservative template",
        PlanKind::Cruise => "cruise at V",
        PlanKind::PeakNoCruise => "peak without cruise",
        PlanKind::Triangular => "triangular",
        PlanKind::General => "stop–move–start",
    }
}
