//! The demo's adapter between UI parameters and `robot-motion`.
//!
//! It calls the same planner entry points a controller would use — the optimal
//! rest-to-rest planner, the conservative rational template, and the general
//! stop–move–start planner — and adds only what the UI needs: phase rows, exact peaks
//! and the general planner's boundary viability values. The plots evaluate the real
//! [`Profile`]; there is no duplicate trajectory mathematics here.

use robot_motion::general::{plan_general, rev, stop_feasible};
use robot_motion::{
    Limits, PlanError, PlanKind, Profile, State, plan_rest_conservative, plan_rest_to_rest,
};

/// Which planner the demo drives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Planner {
    /// The time-optimal 7-phase planner (`plan_rest_to_rest`).
    Optimal,
    /// The radical-free rational template (`plan_rest_conservative`).
    Conservative,
    /// Stop–move–start boundary planner (`plan_general`); the only mode that accepts
    /// nonzero boundary velocities and accelerations.
    General,
}

impl Planner {
    pub fn title(self) -> &'static str {
        match self {
            Self::Optimal => "Optimal 7-phase (rest to rest)",
            Self::Conservative => "Conservative template (rest to rest)",
            Self::General => "General stop–move–start",
        }
    }

    pub fn note(self) -> &'static str {
        match self {
            Self::Optimal => {
                "Time-optimal rest-to-rest S-curve. Uses sqrt/cbrt case analysis \
                 (cruise, peak without cruise, or triangular)."
            }
            Self::Conservative => {
                "Deliberately conservative rational template. Slower than optimal, \
                 but every duration and jerk is rational."
            }
            Self::General => {
                "Brakes from the start state to rest, plans a conservative rest-to-rest \
                 move, then time-reverses a stop profile to reach the target state."
            }
        }
    }
}

/// Everything the side panel's controls edit.
#[derive(Clone, Copy, Debug)]
pub struct DemoParams {
    pub planner: Planner,
    /// When false the boundary velocities and accelerations are forced to zero and the
    /// rest-to-rest planners are available. When true the general planner is used.
    pub non_rest: bool,
    pub vmax: f64,
    pub amax: f64,
    pub jmax: f64,
    pub q0: f64,
    pub q1: f64,
    pub v0: f64,
    pub a0: f64,
    pub v1: f64,
    pub a1: f64,
}

impl Default for DemoParams {
    fn default() -> Self {
        Self {
            planner: Planner::Optimal,
            non_rest: false,
            vmax: 1.0,
            amax: 2.0,
            jmax: 10.0,
            q0: 0.0,
            q1: 1.0,
            v0: 0.0,
            a0: 0.0,
            v1: 0.0,
            a1: 0.0,
        }
    }
}

impl DemoParams {
    /// A nonzero boundary velocity/acceleration forces the general planner.
    pub fn effective_planner(&self) -> Planner {
        if self.non_rest {
            Planner::General
        } else {
            self.planner
        }
    }

    pub fn limits(&self) -> Result<Limits<f64>, PlanError> {
        Limits::new(self.vmax, self.amax, self.jmax)
    }

    pub fn start_state(&self) -> State<f64> {
        if self.non_rest {
            State::new(self.q0, self.v0, self.a0)
        } else {
            State::new(self.q0, 0.0, 0.0)
        }
    }

    pub fn end_state(&self) -> State<f64> {
        if self.non_rest {
            State::new(self.q1, self.v1, self.a1)
        } else {
            State::new(self.q1, 0.0, 0.0)
        }
    }

    /// Run the selected planner.
    pub fn plan(&self) -> Result<DemoPlan, PlanError> {
        let limits = self.limits()?;
        let start = self.start_state();
        let end = self.end_state();
        let profile = match self.effective_planner() {
            Planner::Optimal => plan_rest_to_rest(start.q, end.q, limits)?,
            Planner::Conservative => plan_rest_conservative(start.q, end.q, limits)?,
            Planner::General => plan_general(start, end, limits)?,
        };
        // All finite segments can still sum to an infinite duration for extreme typed
        // positions; the UI's time axis and playback need a finite horizon.
        if !profile.total_time().is_finite() {
            return Err(PlanError::NumericalFailure);
        }
        Ok(DemoPlan::new(profile, limits))
    }
}

/// One constant-jerk phase, with its exact boundary states.
#[derive(Clone, Copy, Debug)]
pub struct PhaseRow {
    pub index: usize,
    pub dur: f64,
    pub jerk: f64,
    pub entry: State<f64>,
    pub exit: State<f64>,
}

/// Largest magnitudes reached by the profile.
#[derive(Clone, Copy, Debug, Default)]
pub struct Peaks {
    pub v: f64,
    pub a: f64,
    pub j: f64,
}

/// A planned profile plus the derived facts the UI displays.
#[derive(Clone, Debug)]
pub struct DemoPlan {
    pub profile: Profile<f64>,
    pub limits: Limits<f64>,
    pub kind: PlanKind,
    pub total_time: f64,
    pub phases: Vec<PhaseRow>,
    /// Interior phase-boundary times (excluding 0 and `total_time`).
    pub boundaries: Vec<f64>,
    /// Step points for the jerk graph: two points per non-empty phase.
    pub jerk_steps: Vec<[f64; 2]>,
    pub peaks: Peaks,
}

impl DemoPlan {
    fn new(profile: Profile<f64>, limits: Limits<f64>) -> Self {
        let total_time = profile.total_time();
        let mut phases = Vec::with_capacity(profile.segments().len());
        let mut boundaries = Vec::new();
        let mut jerk_steps = Vec::new();
        let mut peaks = Peaks::default();
        let mut cursor = 0.0;

        for (index, segment) in profile.segments().iter().enumerate() {
            let entry = profile.phase_start(index).unwrap_or(profile.start());
            let exit = entry.advance(segment.jerk, segment.dur);
            phases.push(PhaseRow {
                index,
                dur: segment.dur,
                jerk: segment.jerk,
                entry,
                exit,
            });
            cursor += segment.dur;
            if index + 1 < profile.segments().len() && boundaries.last() != Some(&cursor) {
                // Zero-duration phases keep the canonical slot list but contribute no
                // boundary of their own; adjacent slots can share a time.
                boundaries.push(cursor);
            }
            if segment.dur > 0.0 {
                jerk_steps.push([cursor - segment.dur, segment.jerk]);
                jerk_steps.push([cursor, segment.jerk]);
            }

            peaks.j = peaks.j.max(segment.jerk.abs());
            peaks.a = peaks
                .a
                .max(entry.a.abs())
                .max(exit.a.abs())
                .max(segment_jerk_peak_acceleration(entry, *segment));
            peaks.v = peaks
                .v
                .max(entry.v.abs())
                .max(exit.v.abs())
                .max(segment_peak_velocity(entry, *segment));
        }

        Self {
            profile,
            limits,
            kind: profile.kind(),
            total_time,
            phases,
            boundaries,
            jerk_steps,
            peaks,
        }
    }

    pub fn state_at(&self, t: f64) -> State<f64> {
        self.profile.eval(t)
    }

    /// Jerk at `t`, following the profile's later-segment convention; zero after the end.
    pub fn jerk_at(&self, t: f64) -> f64 {
        let mut acc = 0.0;
        for segment in self.profile.segments() {
            acc += segment.dur;
            if t < acc {
                return segment.jerk;
            }
        }
        0.0
    }
}

/// Maximum of the piecewise-linear acceleration on one segment.
fn segment_jerk_peak_acceleration(entry: State<f64>, segment: robot_motion::Segment<f64>) -> f64 {
    let end = entry.a + segment.jerk * segment.dur;
    entry.a.abs().max(end.abs())
}

/// Maximum of the quadratic velocity on one segment (endpoints or the interior
/// stationary point where `a = 0`).
fn segment_peak_velocity(entry: State<f64>, segment: robot_motion::Segment<f64>) -> f64 {
    let (v0, a0, j, d) = (entry.v, entry.a, segment.jerk, segment.dur);
    let mut peak = v0.abs().max((v0 + a0 * d + j * d * d / 2.0).abs());
    if j != 0.0 && d > 0.0 {
        let t = -a0 / j;
        if t > 0.0 && t < d {
            peak = peak.max((v0 + a0 * t + j * t * t / 2.0).abs());
        }
    }
    peak
}

/// One boundary state's part of the stop–move–start viability test.
#[derive(Clone, Copy, Debug)]
pub struct StopCheck {
    pub v: f64,
    pub a: f64,
    /// `v_s` for the start (`v + a|a|/(2J)`) or `v_e` for the target
    /// (`v - a|a|/(2J)`): the velocity after the fastest legal acceleration-removal ramp.
    pub adjusted: f64,
    pub v_ok: bool,
    pub a_ok: bool,
    pub adjusted_ok: bool,
    pub feasible: bool,
}

/// The exact viability predicate of the stop–move–start decomposition, with the
/// intermediate values shown so the UI can explain a rejection.
#[derive(Clone, Copy, Debug)]
pub struct Viability {
    pub start: StopCheck,
    pub target: StopCheck,
}

impl Viability {
    pub fn is_viable(self) -> bool {
        self.start.feasible && self.target.feasible
    }
}

pub fn viability(params: &DemoParams, limits: Limits<f64>) -> Viability {
    let start = params.start_state();
    let target = params.end_state();
    let start_adjusted = start.v + start.a * start.a.abs() / (2.0 * limits.jmax());
    let target_adjusted = target.v - target.a * target.a.abs() / (2.0 * limits.jmax());
    Viability {
        start: StopCheck {
            v: start.v,
            a: start.a,
            adjusted: start_adjusted,
            v_ok: start.v.abs() <= limits.vmax(),
            a_ok: start.a.abs() <= limits.amax(),
            adjusted_ok: start_adjusted.abs() <= limits.vmax(),
            feasible: stop_feasible(start, limits),
        },
        target: StopCheck {
            v: target.v,
            a: target.a,
            adjusted: target_adjusted,
            v_ok: target.v.abs() <= limits.vmax(),
            a_ok: target.a.abs() <= limits.amax(),
            adjusted_ok: target_adjusted.abs() <= limits.vmax(),
            feasible: stop_feasible(rev(target), limits),
        },
    }
}

/// Classification thresholds the two rest-to-rest planners use.
#[derive(Clone, Copy, Debug)]
pub struct Thresholds {
    /// An acceleration ramp takes this long: `A/J`.
    pub t_j: f64,
    /// Smallest peak velocity a complete A-ramp can reach: `A²/J`.
    pub v_a: f64,
    /// Optimal planner: cruise if `|Δq| ≥ d_full`; `d_full = 2 d(V)`.
    pub d_full: f64,
    /// Conservative template: `τ = min(1, A/J, V/J)`.
    pub tau: f64,
    /// Conservative template: cruise if `|Δq| ≥ d_min`; `d_min = 2Jτ³`.
    pub d_min: f64,
}

pub fn thresholds(limits: Limits<f64>) -> Thresholds {
    let tj = limits.amax() / limits.jmax();
    let va = limits.amax() * limits.amax() / limits.jmax();
    let half = if limits.vmax() <= va {
        limits.vmax() * (limits.vmax() / limits.jmax()).sqrt()
    } else {
        limits.vmax() * (tj + limits.vmax() / limits.amax()) / 2.0
    };
    let tau = 1.0_f64
        .min(limits.amax() / limits.jmax())
        .min(limits.vmax() / limits.jmax());
    Thresholds {
        t_j: tj,
        v_a: va,
        d_full: 2.0 * half,
        tau,
        d_min: 2.0 * limits.jmax() * tau * tau * tau,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn close(actual: f64, expected: f64) {
        assert!(
            (actual - expected).abs() < 1e-9,
            "expected {expected}, got {actual}"
        );
    }

    #[test]
    fn default_optimal_plan_is_a_cruise() {
        let plan = DemoParams::default().plan().unwrap();
        assert_eq!(plan.kind, PlanKind::Cruise);
        close(plan.total_time, 1.7);
        close(plan.peaks.v, 1.0);
        close(plan.peaks.a, 2.0);
        close(plan.peaks.j, 10.0);
        assert_eq!(plan.phases.len(), 7);
    }

    #[test]
    fn conservative_plan_ends_at_rest_at_the_target() {
        let params = DemoParams {
            planner: Planner::Conservative,
            ..DemoParams::default()
        };
        let plan = params.plan().unwrap();
        assert_eq!(plan.kind, PlanKind::Conservative);
        close(plan.total_time, 10.2);
        close(plan.profile.end().q, 1.0);
        close(plan.profile.end().v, 0.0);
        close(plan.profile.end().a, 0.0);
        close(plan.peaks.v, 0.1);
        // Slots 2 and 6 have zero duration, so two boundary times are shared.
        assert_eq!(plan.boundaries.len(), 4);
    }

    #[test]
    fn general_plan_accepts_a_moving_start() {
        let params = DemoParams {
            non_rest: true,
            v0: 0.5,
            ..DemoParams::default()
        };
        let plan = params.plan().unwrap();
        assert_eq!(plan.kind, PlanKind::General);
        close(plan.profile.start().v, 0.5);
        close(plan.profile.end().q, 1.0);
        close(plan.profile.end().v, 0.0);
        let viability = viability(&params, params.limits().unwrap());
        assert!(viability.is_viable());
    }

    #[test]
    fn general_plan_rejects_a_state_that_cannot_stop() {
        let params = DemoParams {
            non_rest: true,
            v0: 1.0,
            a0: 2.0,
            ..DemoParams::default()
        };
        let viability = viability(&params, params.limits().unwrap());
        assert!(!viability.start.feasible);
        assert!(matches!(params.plan(), Err(PlanError::Infeasible)));
    }

    #[test]
    fn zero_motion_has_no_phases() {
        let params = DemoParams {
            q1: 0.0,
            ..DemoParams::default()
        };
        let plan = params.plan().unwrap();
        assert_eq!(plan.kind, PlanKind::ZeroMotion);
        close(plan.total_time, 0.0);
        assert!(plan.phases.is_empty());
        assert_eq!(plan.jerk_at(0.0), 0.0);
    }

    #[test]
    fn jerk_at_a_boundary_is_the_later_segment() {
        let plan = DemoParams::default().plan().unwrap();
        close(plan.jerk_at(0.2), 0.0);
        close(plan.jerk_at(0.1), 10.0);
    }

    #[test]
    fn thresholds_match_the_documented_formulas() {
        let limits = DemoParams::default().limits().unwrap();
        let t = thresholds(limits);
        close(t.t_j, 0.2);
        close(t.v_a, 0.4);
        close(t.d_full, 0.7);
        close(t.tau, 0.1);
        close(t.d_min, 0.02);
    }

    #[test]
    fn velocity_peak_finds_an_interior_stationary_point() {
        // v(t) = -4t + t² on [0, 3]: the interior minimum at t = 2 is -4, larger in
        // magnitude than either endpoint (0 and -3).
        let segment = robot_motion::Segment {
            dur: 3.0,
            jerk: 2.0,
        };
        let entry = State::new(0.0, 0.0, -4.0);
        close(segment_peak_velocity(entry, segment), 4.0);
    }

    #[test]
    fn target_viability_uses_the_time_reversed_condition() {
        let params = DemoParams {
            non_rest: true,
            v1: 0.9,
            a1: 2.0,
            ..DemoParams::default()
        };
        let limits = params.limits().unwrap();
        let check = viability(&params, limits);
        // v_e = 0.9 - 2*2/(2*10) = 0.7, inside the band.
        close(check.target.adjusted, 0.7);
        assert!(check.target.feasible);
        assert!(check.is_viable());
        let plan = params.plan().unwrap();
        close(plan.profile.end().v, 0.9);
        close(plan.profile.end().a, 2.0);
    }
}
