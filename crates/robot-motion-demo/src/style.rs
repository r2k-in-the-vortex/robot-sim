//! Colors and number formatting shared by the panels and the plots.
//!
//! The chart palette follows the repository's data-visualization reference: one blue
//! series hue stepped per theme, recessive gray chrome, and status colors reserved for
//! pass/fail states (always paired with an icon and a word, never color alone).

use eframe::egui::{self, Color32};

/// Status: a condition holds. Mode-invariant; always paired with the word "ok" or
/// "viable", never color alone.
pub const GOOD: Color32 = Color32::from_rgb(0x0c, 0xa3, 0x0c);
/// Status: a condition fails. Mode-invariant; always paired with the word "no" or
/// "not viable", never color alone.
pub const CRITICAL: Color32 = Color32::from_rgb(0xd0, 0x3b, 0x3b);

/// Theme-dependent chart colors.
#[derive(Clone, Copy, Debug)]
pub struct Palette {
    /// The one data series in every lane.
    pub series: Color32,
    /// Limit lines; a reference, not data.
    pub limit: Color32,
    /// Interior phase boundaries.
    pub phase: Color32,
    /// Grid hairlines.
    pub grid: Color32,
    /// Slider rails and other control tracks.
    pub rail: Color32,
    /// The fill behind the plot, used for the cursor dot's ring.
    pub surface: Color32,
    /// Axis labels and secondary text.
    pub muted: Color32,
}

impl Palette {
    pub fn new(ui: &egui::Ui) -> Self {
        if ui.visuals().dark_mode {
            Self {
                series: Color32::from_rgb(0x39, 0x87, 0xe5),
                limit: Color32::from_rgb(0x89, 0x87, 0x81),
                phase: Color32::from_rgba_unmultiplied(0x89, 0x87, 0x81, 90),
                grid: Color32::from_rgb(0x2c, 0x2c, 0x2a),
                rail: Color32::from_rgb(0x38, 0x38, 0x35),
                surface: ui.visuals().panel_fill,
                muted: Color32::from_rgb(0x89, 0x87, 0x81),
            }
        } else {
            Self {
                series: Color32::from_rgb(0x2a, 0x78, 0xd6),
                limit: Color32::from_rgb(0x89, 0x87, 0x81),
                phase: Color32::from_rgba_unmultiplied(0x89, 0x87, 0x81, 90),
                grid: Color32::from_rgb(0xe1, 0xe0, 0xd9),
                rail: Color32::from_rgb(0xc3, 0xc2, 0xb7),
                surface: ui.visuals().panel_fill,
                muted: Color32::from_rgb(0x89, 0x87, 0x81),
            }
        }
    }
}

/// Four decimals, switching to exponent form for very large or very small magnitudes.
pub fn number(value: f64) -> String {
    if !value.is_finite() {
        return "—".to_owned();
    }
    let magnitude = value.abs();
    if magnitude != 0.0 && (magnitude < 1e-3 || magnitude >= 1e5) {
        format!("{value:.3e}")
    } else {
        format!("{value:.4}")
    }
}

/// Three decimals for compact table cells.
pub fn short(value: f64) -> String {
    if !value.is_finite() {
        return "—".to_owned();
    }
    let magnitude = value.abs();
    if magnitude != 0.0 && (magnitude < 1e-3 || magnitude >= 1e5) {
        format!("{value:.2e}")
    } else {
        format!("{value:.3}")
    }
}
