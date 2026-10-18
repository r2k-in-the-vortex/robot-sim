//! The Motion tab's `lin` (MoveL) command: a Cartesian straight line, timed and sampled.
//!
//! # What the command means
//!
//! The tool position moves along the affine segment between the command's start and stop
//! positions, and the orientation follows a spherical linear interpolation of the two
//! endpoint rotations. The path itself is `robot_motion::linear::LinearPath`; this module
//! supplies the timing and the application boundary.
//!
//! # Timing
//!
//! `robot-motion`'s Lean counterpart (`Motion.Linear`) is a sampled **vocabulary**: it
//! has no time law. This module adds one that matches the rest of the Motion tab:
//!
//! 1. Sample the path uniformly in its parameter `s ∈ [0, 1]` and solve each pose with
//!    the closed-form IK, choosing the branch nearest the previous sample.
//! 2. Estimate per-joint `M1/M2/M3` bounds for `q'(s)`, `q''(s)` and `q'''(s)` from those
//!    samples.
//! 3. Choose conservative scalar limits by the M5 inequalities and plan `s(t)` as a
//!    rest-to-rest S-curve with [`robot_motion::plan_rest_to_rest`].
//! 4. Re-solve `path.pose(s(t))` at a uniform time step and check the sampled V/A/J
//!    bounds and branch continuity.
//!
//! That is a **numerical certifier**, not the `cartesian_path_feasible` theorem: the
//! derivative bounds are sampled, and the error is a typed error rather than a slower
//! path when no positive limits exist. The Lean module's own vocabulary (slerp, samples,
//! branch continuity, sampled limits) lives in `robot-motion::linear`.
//!
//! # Units
//!
//! The command boundary is runtime joint degrees, like MoveJ. The planner core works in
//! total DH radians, so this module converts at the boundary: `theta_offset` is folded in
//! on the way in and subtracted, without wrapping, on the way out. The no-wrap half is
//! deliberate: a joint at 400° stays at 400° when the line's solution is expressed beside
//! it, exactly as [`crate::solve::solve_nearest_deg`] and the pose jogs already promise.
//!
//! # Sampling
//!
//! The output is uniform in **time**, at [`SAMPLES_PER_SECOND`], capped by
//! [`MAX_SAMPLES`]. Playback interpolates linearly between samples; the sample density is
//! chosen so the interpolation error is far below a display pixel and the finite-
//! difference limit check has the same shape as `Motion.WithinSampledLimits`.

use robot_kinematics::{JOINT_COUNT, Pose, Solution, units};
use robot_model::DHParameters;
use robot_motion::Limits;
use robot_motion::linear::{self, LinearPath, LinearSample};

/// Path samples used to estimate the joint-space derivative bounds. Odd and comfortably
/// above the third-difference minimum; the cost is one IK solve each.
pub const CERTIFICATION_SAMPLES: usize = 257;
/// Output samples per second of planned motion.
pub const SAMPLES_PER_SECOND: f64 = 200.0;
/// A ceiling on an output trajectory, so a very long Cartesian line cannot grow without
/// bound. At 200 Hz this is 100 seconds.
pub const MAX_SAMPLES: usize = 20_000;
/// The minimum output count the third-difference limit check needs.
pub const MIN_SAMPLES: usize = 4;
/// The branch-continuity bound: a legitimate line's per-sample step is far below this,
/// and a shoulder/elbow or wrist flip is far above it.
pub const MAX_STEP_DEG: f64 = 30.0;

/// A timed Cartesian straight-line trajectory in runtime joint degrees.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearPlan {
    duration: f64,
    dt: f64,
    angles_deg: Vec<[f64; JOINT_COUNT]>,
}

impl LinearPlan {
    pub fn total_time(&self) -> f64 {
        self.duration
    }

    /// The uniform time step between stored samples.
    ///
    /// The playback path evaluates through [`Self::eval_deg`]; the getter is the tests'
    /// and the graph layer's route to the same grid.
    #[allow(dead_code)]
    pub fn dt(&self) -> f64 {
        self.dt
    }

    /// The stored samples, in runtime joint degrees.
    #[allow(dead_code)]
    pub fn samples_deg(&self) -> &[[f64; JOINT_COUNT]] {
        &self.angles_deg
    }

    pub fn end_deg(&self) -> [f64; JOINT_COUNT] {
        self.angles_deg[self.angles_deg.len() - 1]
    }

    /// The joint angles at `t`, linearly interpolated between samples and clamped to the
    /// planned interval. A zero-duration plan holds its one sample.
    pub fn eval_deg(&self, t: f64) -> [f64; JOINT_COUNT] {
        if self.angles_deg.len() == 1 || self.dt <= 0.0 || !t.is_finite() {
            return self.angles_deg[0];
        }
        let last = self.angles_deg.len() - 1;
        let position = (t / self.dt).clamp(0.0, last as f64);
        let index = position.floor() as usize;
        if index >= last {
            return self.angles_deg[last];
        }
        let fraction = position - index as f64;
        let first = self.angles_deg[index];
        let second = self.angles_deg[index + 1];
        core::array::from_fn(|joint| first[joint] + (second[joint] - first[joint]) * fraction)
    }
}

/// Plan a Cartesian straight line from `start` to `stop`.
///
/// `reference_deg` is the configuration the arm holds; the line's first sample is the IK
/// candidate nearest it, so the command begins where a transition to the same pose would
/// leave the arm. `limits_deg` are the per-joint effective limits in degrees and seconds.
///
/// Returns a typed message rather than a plan when the line is unreachable, crosses a
/// shoulder/elbow branch, has no positive conservative scalar limits, or exceeds the
/// sampled V/A/J bounds.
pub fn plan(
    parameters: &DHParameters,
    start: &Pose<f64>,
    stop: &Pose<f64>,
    reference_deg: &[f64; JOINT_COUNT],
    limits_deg: &[Limits<f64>; JOINT_COUNT],
) -> Result<LinearPlan, String> {
    let geometry = parameters.geometry().map_err(|error| error.to_string())?;
    let path = LinearPath::slerp(*start, *stop).map_err(|error| error.to_string())?;
    let reference = Solution {
        angles: parameters.total_angles_rad(reference_deg),
        shoulder: 1,
        elbow: 1,
    };

    let mut limits_rad =
        [Limits::new(1.0, 1.0, 1.0).map_err(|error| error.to_string())?; JOINT_COUNT];
    for (target, source) in limits_rad.iter_mut().zip(limits_deg) {
        *target = Limits::new(
            source.vmax().to_radians(),
            source.amax().to_radians(),
            source.jmax().to_radians(),
        )
        .map_err(|error| error.to_string())?;
    }

    let mut path_samples = vec![LinearSample::default(); CERTIFICATION_SAMPLES];
    let certificate = linear::certify_linear_path(
        &geometry,
        &path,
        &reference,
        &limits_rad,
        MAX_STEP_DEG.to_radians(),
        &mut path_samples,
    )
    .map_err(path_error)?;

    let duration = certificate.duration();
    if duration <= 0.0 {
        return Ok(LinearPlan {
            duration: 0.0,
            dt: 0.0,
            angles_deg: vec![to_runtime_deg(parameters, &certificate.start)],
        });
    }

    let count =
        ((duration * SAMPLES_PER_SECOND).ceil() as usize + 1).clamp(MIN_SAMPLES, MAX_SAMPLES);
    let mut output = vec![LinearSample::default(); count];
    let filled = linear::sample_linear_certificate(&geometry, &path, &certificate, &mut output)
        .map_err(|error| format!("linear sampling: {error}"))?;
    output.truncate(filled);

    let dt = if filled > 1 {
        duration / (filled - 1) as f64
    } else {
        0.0
    };
    Ok(LinearPlan {
        duration,
        dt,
        angles_deg: output
            .iter()
            .map(|sample| to_runtime_deg(parameters, sample))
            .collect(),
    })
}

/// The configuration a linear command starts from, chosen nearest `reference_deg`.
///
/// The queue uses this to decide whether a transition MoveJ is needed and where it ends.
/// It goes through the same [`robot_motion::linear::solve_sample`] as the plan, so the
/// transition and the linear segment cannot disagree about the start configuration.
pub fn start_configuration(
    parameters: &DHParameters,
    start: &Pose<f64>,
    reference_deg: &[f64; JOINT_COUNT],
) -> Result<[f64; JOINT_COUNT], String> {
    let geometry = parameters.geometry().map_err(|error| error.to_string())?;
    let reference = Solution {
        angles: parameters.total_angles_rad(reference_deg),
        shoulder: 1,
        elbow: 1,
    };
    let sample = linear::solve_sample(&geometry, start, &reference)
        .map_err(|error| format!("linear start pose: {error}"))?;
    Ok(to_runtime_deg(parameters, &sample))
}

/// A linear certificate's duration without materialising the output samples.
///
/// The editor's live duration readout uses this so typing in a pose field does not plan
/// and solve a whole trajectory per frame.
pub fn estimate_duration(
    parameters: &DHParameters,
    start: &Pose<f64>,
    stop: &Pose<f64>,
    reference_deg: &[f64; JOINT_COUNT],
    limits_deg: &[Limits<f64>; JOINT_COUNT],
) -> Result<f64, String> {
    let geometry = parameters.geometry().map_err(|error| error.to_string())?;
    let path = LinearPath::slerp(*start, *stop).map_err(|error| error.to_string())?;
    let reference = Solution {
        angles: parameters.total_angles_rad(reference_deg),
        shoulder: 1,
        elbow: 1,
    };
    let mut limits_rad =
        [Limits::new(1.0, 1.0, 1.0).map_err(|error| error.to_string())?; JOINT_COUNT];
    for (target, source) in limits_rad.iter_mut().zip(limits_deg) {
        *target = Limits::new(
            source.vmax().to_radians(),
            source.amax().to_radians(),
            source.jmax().to_radians(),
        )
        .map_err(|error| error.to_string())?;
    }
    let mut path_samples = vec![LinearSample::default(); CERTIFICATION_SAMPLES];
    let certificate = linear::certify_linear_path(
        &geometry,
        &path,
        &reference,
        &limits_rad,
        MAX_STEP_DEG.to_radians(),
        &mut path_samples,
    )
    .map_err(path_error)?;
    Ok(certificate.duration())
}

/// Turn a certification failure into the app's sentence, with a hint for the one case
/// that is both common and easily actionable: a path whose first sample jumps because it
/// starts at a wrist singularity and its direction forces a wrist split.
fn path_error(error: linear::LinearError) -> String {
    match error {
        linear::LinearError::StepTooLarge { sample: 1 } => format!(
            "linear path: the start pose has no continuous joint-space branch along this \
             line; it is likely a wrist singularity (joint 5 at zero), so jog joint 5 away \
             from zero first ({error})"
        ),
        other => format!("linear path: {other}"),
    }
}

/// Convert a total-radian sample to runtime degrees without wrapping.
fn to_runtime_deg(parameters: &DHParameters, sample: &LinearSample) -> [f64; JOINT_COUNT] {
    core::array::from_fn(|joint| {
        units::rad_to_deg(
            sample.angles[joint] - units::deg_to_rad(parameters.joints[joint].theta_offset_deg),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::{JOINT_COUNT, Vec3, fk};

    fn parameters() -> DHParameters {
        DHParameters::shipped()
    }

    fn limits() -> [Limits<f64>; JOINT_COUNT] {
        [Limits::new(30.0, 60.0, 120.0).expect("positive"); JOINT_COUNT]
    }

    fn zero_pose(parameters: &DHParameters) -> Pose<f64> {
        let geometry = parameters.geometry().expect("shipped table");
        fk(&geometry, &parameters.total_angles_rad(&[0.0; JOINT_COUNT]))
    }

    /// A configuration off every singularity. The shipped zero pose has joint 5 at zero,
    /// which is the wrist singularity; a Cartesian line leaving it can require a
    /// discontinuous wrist split depending on its direction, and the planner rejects that
    /// case.
    fn open_reference() -> [f64; JOINT_COUNT] {
        [0.3, 0.2, -0.4, 0.1, 28.6, -0.3]
    }

    fn pose_at(parameters: &DHParameters, reference: &[f64; JOINT_COUNT]) -> Pose<f64> {
        let geometry = parameters.geometry().expect("shipped table");
        fk(&geometry, &parameters.total_angles_rad(reference))
    }

    #[test]
    fn a_short_line_moves_along_the_segment_and_respects_the_sampled_limits() {
        let parameters = parameters();
        let reference = open_reference();
        let start = pose_at(&parameters, &reference);
        let mut stop = start;
        stop.p = stop.p + Vec3::new(5.0, -3.0, 1.0);
        let plan =
            plan(&parameters, &start, &stop, &reference, &limits()).expect("the line is feasible");
        assert!(plan.total_time() > 0.0);
        assert!(plan.dt() > 0.0);
        assert!(plan.samples_deg().len() >= MIN_SAMPLES);

        let geometry = parameters.geometry().expect("shipped table");
        let direction = stop.p - start.p;
        let length_squared = direction.dot(direction);
        for fraction in [0.0, 0.1, 0.5, 0.9, 1.0] {
            let t = plan.total_time() * fraction;
            let angles = plan.eval_deg(t);
            let pose = fk(&geometry, &parameters.total_angles_rad(&angles));
            let offset = pose.p - start.p;
            // The distance from the sample to the infinite line is `|offset × dir| / |dir|`.
            let distance = offset.cross(direction).norm() / length_squared.sqrt();
            assert!(
                distance < 1e-6,
                "t = {t}: the tool is {distance} off the line"
            );
            // ... and it is between the endpoints, not on the extension.
            let along = offset.dot(direction) / length_squared;
            assert!(
                (-1e-9..=1.0 + 1e-9).contains(&along),
                "t = {t}: along = {along}"
            );
        }
        let end = plan.eval_deg(plan.total_time());
        let end_pose = fk(&geometry, &parameters.total_angles_rad(&end));
        assert!(
            end_pose.p.distance(stop.p) < 1e-6,
            "the line ends {} away",
            end_pose.p.distance(stop.p)
        );

        // The sampled finite differences are the same check the core performs.
        let samples: Vec<[f64; JOINT_COUNT]> = plan.samples_deg().to_vec();
        // Both the samples and these limits are in degrees, so the check is unit-consistent.
        let trajectory =
            robot_motion::linear::SampledTrajectory::new(plan.dt(), &samples).expect("valid");
        robot_motion::linear::check_within_sampled_limits(&limits(), &trajectory)
            .expect("the output respects the sampled bounds");
    }

    #[test]
    fn a_zero_length_line_has_no_duration() {
        let parameters = parameters();
        let pose = zero_pose(&parameters);
        let plan = plan(&parameters, &pose, &pose, &[0.0; JOINT_COUNT], &limits())
            .expect("a stationary line is feasible");
        assert_eq!(plan.total_time(), 0.0);
        assert_eq!(plan.eval_deg(5.0), [0.0; JOINT_COUNT]);
    }

    #[test]
    fn an_unreachable_stop_is_an_error() {
        let parameters = parameters();
        let reference = open_reference();
        let start = pose_at(&parameters, &reference);
        let stop = Pose::new(start.r, Vec3::new(10_000.0, 0.0, 0.0));
        let error = plan(&parameters, &start, &stop, &reference, &limits())
            .expect_err("the stop is unreachable");
        assert!(error.contains("IK solution"), "{error}");
    }

    #[test]
    fn the_start_configuration_keeps_the_reference_winding() {
        let parameters = parameters();
        let geometry = parameters.geometry().expect("shipped table");
        let reference = [0.0, 0.0, 0.0, 0.0, 0.0, 400.0];
        let pose = fk(&geometry, &parameters.total_angles_rad(&reference));
        let start = start_configuration(&parameters, &pose, &reference).expect("reachable");
        // The candidate is placed beside the wound reference rather than wrapped to 40°.
        assert!(
            (start[5] - 400.0).abs() < 1e-6,
            "joint 6 started at {} degrees",
            start[5]
        );
    }

    #[test]
    fn a_line_from_the_rpy_rounded_zero_pose_can_be_planned() {
        // The command boundary stores RPY, so the shipped zero pose is round-tripped
        // through the gimbal-lock representative before planning. The exact solver sees a
        // pose an ulp off the singularity and jumps between wrist splits; the
        // tolerance-widened solver keeps the continuous branch, which is what makes the
        // default MoveL editor usable for a pure X move.
        use crate::motion::CommandPose;
        let parameters = parameters();
        let rounded = CommandPose::from_pose(&zero_pose(&parameters)).to_pose();
        let mut stop = rounded;
        stop.p = stop.p + Vec3::new(4.0, 0.0, 0.0);
        let plan = plan(&parameters, &rounded, &stop, &[0.0; JOINT_COUNT], &limits())
            .expect("the tolerance-widened solver finds a continuous branch");
        assert!(plan.total_time() > 0.0);
    }

    #[test]
    fn a_line_leaving_the_wrist_singularity_is_refused_with_a_hint() {
        // The shipped zero pose has joint 5 at zero. The IK has no continuous branch off
        // the singularity, so the first sample step is large; the message says what to do.
        let parameters = parameters();
        let start = zero_pose(&parameters);
        let mut stop = start;
        stop.p = stop.p + Vec3::new(5.0, -3.0, 1.0);
        let error = plan(&parameters, &start, &stop, &[0.0; JOINT_COUNT], &limits())
            .expect_err("the singular start has no continuous branch");
        assert!(
            error.contains("wrist singularity"),
            "unhelpful message: {error}"
        );
    }

    #[test]
    fn a_plan_keeps_a_wound_joint_where_it_is() {
        let parameters = parameters();
        let mut reference = open_reference();
        reference[5] = 400.0;
        let start = pose_at(&parameters, &reference);
        let mut stop = start;
        stop.p = stop.p + Vec3::new(1.0, 0.0, 0.0);
        let plan = plan(&parameters, &start, &stop, &reference, &limits())
            .expect("the wound start is feasible");
        let first = plan.samples_deg()[0][5];
        assert!(
            (first - 400.0).abs() < 1e-6,
            "joint 6 starts at {first} degrees instead of 400"
        );
    }

    #[test]
    fn the_estimate_is_the_materialised_duration() {
        let parameters = parameters();
        let reference = open_reference();
        let start = pose_at(&parameters, &reference);
        let mut stop = start;
        stop.p = stop.p + Vec3::new(2.0, 1.0, 0.0);
        let materialised =
            plan(&parameters, &start, &stop, &reference, &limits()).expect("feasible");
        let estimate =
            estimate_duration(&parameters, &start, &stop, &reference, &limits()).expect("feasible");
        assert!((estimate - materialised.total_time()).abs() < 1e-12);
    }
}
