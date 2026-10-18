//! The four linked time-series lanes: position, velocity, acceleration and jerk.
//!
//! Each lane is a single-series small multiple, so it carries no legend box — the lane
//! heading names the quantity. The x axis is shared (`link_axis`), grid and limit lines
//! are recessive, and the cursor is the one loud mark on top of the series.

use eframe::egui::{self, Align, Layout, RichText, Stroke};
use egui_plot::{HLine, HoverPosition, Line, LineStyle, Plot, PlotPoints, Points, VLine};
use robot_motion::State;

use crate::plan::DemoPlan;
use crate::style::{Palette, number};

/// Samples per lane for the smooth quantities. The profile is piecewise cubic, so this
/// is far more than enough for a 1500 px plot; phase boundaries are drawn separately.
const SAMPLES: usize = 900;

/// Where a lane's y values come from.
#[derive(Clone, Copy)]
pub enum Values {
    /// Evaluate the profile and pick one component.
    Eval(fn(State<f64>) -> f64),
    /// The piecewise-constant jerk, drawn as a step series.
    Jerk,
}

/// One small multiple: a quantity, its unit, and the limit line to draw.
pub struct Lane {
    pub title: &'static str,
    pub symbol: &'static str,
    pub unit: &'static str,
    pub limit: Option<f64>,
    pub values: Values,
    pub bottom: bool,
}

impl Lane {
    pub fn position() -> Self {
        Self {
            title: "Position",
            symbol: "q",
            unit: "u",
            limit: None,
            values: Values::Eval(|state| state.q),
            bottom: false,
        }
    }

    pub fn velocity(limit: f64) -> Self {
        Self {
            title: "Velocity",
            symbol: "v",
            unit: "u/s",
            limit: Some(limit),
            values: Values::Eval(|state| state.v),
            bottom: false,
        }
    }

    pub fn acceleration(limit: f64) -> Self {
        Self {
            title: "Acceleration",
            symbol: "a",
            unit: "u/s²",
            limit: Some(limit),
            values: Values::Eval(|state| state.a),
            bottom: false,
        }
    }

    pub fn jerk(limit: f64) -> Self {
        Self {
            title: "Jerk",
            symbol: "j",
            unit: "u/s³",
            limit: Some(limit),
            values: Values::Jerk,
            bottom: true,
        }
    }
}

/// What the plots should overlay.
pub struct Overlays {
    pub show_limits: bool,
    pub show_phase_lines: bool,
    pub cursor_t: f64,
}

/// Draw one lane, heading included. `plot_height` excludes the heading row.
pub fn lane(
    ui: &mut egui::Ui,
    plan: &DemoPlan,
    spec: &Lane,
    plot_height: f32,
    overlays: &Overlays,
) {
    let palette = Palette::new(ui);
    let total_time = plan.total_time;
    let profile = plan.profile;
    let cursor_t = overlays.cursor_t.clamp(0.0, total_time.max(0.0));

    ui.horizontal(|ui| {
        ui.label(RichText::new(format!("{}  {}", spec.title, spec.symbol)).strong());
        ui.label(RichText::new(format!("[{}]", spec.unit)).color(palette.muted));
        ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
            if overlays.show_limits
                && let Some(limit) = spec.limit
            {
                ui.label(
                    RichText::new(format!("limit ±{} {}", number(limit), spec.unit))
                        .color(palette.muted)
                        .small(),
                );
            }
        });
    });

    let data = match spec.values {
        Values::Eval(value) => PlotPoints::from_explicit_callback(
            move |t| value(profile.eval(t)),
            0.0..=total_time,
            SAMPLES,
        ),
        Values::Jerk => PlotPoints::new(plan.jerk_steps.clone()),
    };
    let cursor_value = match spec.values {
        Values::Eval(value) => value(plan.state_at(cursor_t)),
        Values::Jerk => plan.jerk_at(cursor_t),
    };

    let symbol = spec.symbol;
    let unit = spec.unit;
    let mut plot = Plot::new(format!("motion-lane-{}", spec.symbol))
        .height(plot_height)
        .show_axes([spec.bottom, true])
        .show_grid(true)
        .grid_color(palette.grid)
        .link_axis("motion-time-axis", egui::Vec2b::new(true, false))
        .label_formatter(move |position| {
            let position = match position {
                HoverPosition::NearDataPoint { position, .. }
                | HoverPosition::Elsewhere { position } => *position,
            };
            Some(format!(
                "t = {:.4} s\n{} = {:.4} {}",
                position.x, symbol, position.y, unit
            ))
        });
    if spec.bottom {
        plot = plot.x_axis_label("time [s]");
    }

    plot.show(ui, |plot_ui| {
        if overlays.show_limits
            && let Some(limit) = spec.limit
        {
            for (name, y) in [("upper limit", limit), ("lower limit", -limit)] {
                plot_ui.hline(
                    HLine::new(format!("{} {name}", spec.symbol), y)
                        .stroke(Stroke::new(1.0, palette.limit))
                        .style(LineStyle::dashed_dense()),
                );
            }
        }

        if overlays.show_phase_lines {
            for (index, &x) in plan.boundaries.iter().enumerate() {
                plot_ui.vline(
                    VLine::new(format!("phase boundary {index}"), x)
                        .stroke(Stroke::new(1.0, palette.phase)),
                );
            }
        }

        plot_ui.line(
            Line::new(spec.symbol, data)
                .color(palette.series)
                .width(2.0),
        );

        if total_time > 0.0 {
            // At either endpoint the cursor would sit on the axis/boundary and read as a
            // frame line; the dot alone still marks the planned state there.
            if cursor_t > 0.0 && cursor_t < total_time {
                plot_ui
                    .vline(VLine::new("cursor", cursor_t).stroke(Stroke::new(1.5, palette.series)));
            }
            // A 2 px surface ring keeps the dot legible where it crosses the series.
            plot_ui.points(
                Points::new("cursor ring", vec![[cursor_t, cursor_value]])
                    .radius(6.0)
                    .color(palette.surface)
                    .allow_hover(false),
            );
            plot_ui.points(
                Points::new("cursor dot", vec![[cursor_t, cursor_value]])
                    .radius(4.0)
                    .color(palette.series)
                    .allow_hover(false),
            );
        }
    });
}
