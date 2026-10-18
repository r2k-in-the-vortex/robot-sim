//! Interactive 1-DOF motion-planner demo.
//!
//! The window exposes the limits and boundary states of the planners in
//! [`robot_motion`], and plots the planned position, velocity, acceleration and jerk
//! over time. It is a manual test bench for understanding the controller's output, not
//! a controller itself: every curve is the planner's own [`robot_motion::Profile`].

#![forbid(unsafe_code)]

mod app;
mod plan;
mod plot;
mod style;

fn main() -> eframe::Result {
    let options = eframe::NativeOptions {
        viewport: eframe::egui::ViewportBuilder::default()
            .with_inner_size([1280.0, 860.0])
            .with_min_inner_size([1000.0, 720.0])
            .with_title("robot-motion demo — 1-DOF planner"),
        ..Default::default()
    };
    eframe::run_native(
        "robot-motion-demo",
        options,
        Box::new(|_cc| Ok(Box::new(app::DemoApp::default()))),
    )
}
