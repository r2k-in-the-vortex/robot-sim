//! Linear (Cartesian straight-line) motion: the Rust counterpart of `Motion.Linear`.
//!
//! `lean/Motion/Linear.lean` is a **sampled specification**, not a theorem: a Cartesian
//! straight line, a uniformly sampled joint trajectory, one closed-form IK candidate per
//! sample, and four checks. This module mirrors that vocabulary and adds the numerical
//! planner the application needs:
//!
//! * [`LinearPath`] is `Motion.LinearPath`: the position is affine in the path parameter
//!   `s`, and the orientation is a supplied function. The Lean structure leaves slerp vs
//!   axis-angle open; [`LinearPath::slerp`] is the supplied rotation path this
//!   implementation uses, while [`LinearPath::with_rotation`] accepts another one.
//! * [`LinearSample`] is one row of `Motion.SampledSolutions`: the placed total joint
//!   angles (radians) plus the shoulder/elbow labels of the candidate they came from.
//! * [`SampledTrajectory`] is `Motion.SampledTrajectory`: `count`, `dt`, finite
//!   differences, and `parameter k = k / (count - 1)`.
//! * [`check_branch_continuous`] and [`check_within_sampled_limits`] are
//!   `BranchContinuous` and `WithinSampledLimits`.
//! * [`solve_sample`] is the per-sample `SamplesAreSolutions` / `SamplesOnPath` step:
//!   take the closed form's candidates through the application's tolerance-widened
//!   solver, keep those whose forward kinematics reproduces the sampled pose, and choose
//!   the one nearest the previous configuration in the wrapped metric.
//!
//! # The numerical planner
//!
//! [`certify_linear_path`] and [`sample_linear_certificate`] are the application-facing
//! extension. The Lean module has no time law; the planner supplies one that is
//! rest-to-rest and jerk-limited by reusing [`crate::plan::plan_rest_to_rest`] on the path
//! parameter `s ∈ [0, 1]`:
//!
//! 1. sample the path uniformly in `s` and solve each sample's IK, choosing branches
//!    continuously;
//! 2. estimate per-joint bounds `M1, M2, M3` for the path derivatives `q'(s)`, `q''(s)`
//!    and `q'''(s)` by finite differences;
//! 3. choose scalar limits by the conservative inequalities of
//!    `docs/motion_control.md` §4.4 (the M5 certificate, sampled rather than proved):
//!    `M1·V ≤ v`, `M2·V² + M1·A ≤ a`, `M3·V³ + 3·M2·V·A + M1·J ≤ j`, with the component
//!    minimum over the moving joints and a safety margin;
//! 4. plan `s(t)` as a rest-to-rest S-curve with those limits;
//! 5. resample `q(s(t))` at a uniform time step and check the sampled V/A/J bounds and
//!    branch continuity on the output.
//!
//! This is a **numerical certificate**, not `cartesian_path_feasible`: the derivative
//! bounds are sampled, so the guarantee is only over the sample grid, and the planner
//! fails closed with a typed error when no positive scalar limits exist. Beyond the
//! sample grid, only the S-curve's own smoothness and the sampling density stand between
//! the output and the limits. That is exactly the boundary §5.6 draws.
//!
//! # Units
//!
//! Angles are **total DH radians**, as everywhere in `robot-kinematics` and the Lean
//! development. The caller converts runtime degrees at the boundary; the application
//! layer does so with `units::total_angle` and its inverse. Positions are in the model's
//! own length unit. Limits are radians and seconds.
//!
//! # `no_std`
//!
//! The module allocates nothing. The path/certificate routines fill caller-provided
//! slices, so the application chooses the sample counts and the crate stays usable on a
//! real-time control loop.

use robot_kinematics::{
    Geometry, JOINT_COUNT, Mat3, Pose, Scalar, Solution, SolutionSet, Tolerances, Vec3, fk, solve,
    units::wrap_angle,
};

use crate::error::PlanError;
use crate::plan::plan_rest_to_rest;
use crate::profile::{Limits, Profile, State};

/// The pose tolerance used by the `SamplesOnPath` re-check. The Lean development has no
/// tolerance; this is the numerical boundary that makes its `fk (q(s)) = pose(s)`
/// hypothesis testable in `f64`.
pub const POSE_TOLERANCE: f64 = 1e-7;

/// The fraction of the sampled limit bounds the scalar planner is allowed to use.
///
/// The `M1/M2/M3` bounds are finite differences over a finite grid, so the true maximum
/// between samples can be larger. Reserving headroom keeps the sampled check meaningful
/// instead of firing on the grid's own discretisation error.
const LIMIT_MARGIN: f64 = 0.8;

/// Joints whose sampled path derivative is below this (radians per unit path parameter)
/// are treated as stationary for limit certification. The path itself still samples
/// them; this only keeps finite-difference noise from dominating a `0 / 0` ratio.
const STATIONARY_BOUND: f64 = 1e-9;

/// The rotation tolerance for [`LinearPath`]'s `IsRotation` checks.
const ROTATION_TOLERANCE: f64 = 1e-9;

/// Why a linear-path request failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinearError {
    /// An input pose, angle or limit was NaN or infinite.
    NonFiniteInput,
    /// A rotation supplied by the caller is not orthogonal with determinant one.
    NotARotation { sample: usize },
    /// The supplied rotation path does not meet `start.R` at `s = 0` or `stop.R` at
    /// `s = 1` (Lean's `rotation_zero` / `rotation_one`).
    RotationEndpointMismatch,
    /// A sampled path or trajectory buffer had fewer points than the finite differences
    /// need.
    TooFewSamples,
    /// The closed form produced no candidate for the sampled pose.
    UnreachableSample { sample: usize },
    /// Candidates existed, but none reproduced the sampled pose within
    /// [`POSE_TOLERANCE`] — Lean's `SamplesOnPath` failing numerically.
    SamplesOnPath { sample: usize },
    /// Consecutive samples changed shoulder or elbow branch (Lean's `BranchContinuous`).
    BranchDiscontinuity { sample: usize },
    /// A joint moved more than `maxStep` (modulo a full turn) between samples.
    StepTooLarge { sample: usize },
    /// A sampled finite-difference velocity, acceleration or jerk exceeded its limit.
    LimitExceeded { sample: usize, joint: usize },
    /// No positive scalar `(V, A, J)` satisfies the conservative sampled bounds.
    CertificationFailed,
    /// A derived quantity overflowed to a non-finite value.
    NumericalFailure,
}

impl core::fmt::Display for LinearError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NonFiniteInput => formatter.write_str("a linear-path input is not finite"),
            Self::NotARotation { sample } => {
                write!(
                    formatter,
                    "the rotation at sample {sample} is not a rotation"
                )
            }
            Self::RotationEndpointMismatch => {
                formatter.write_str("the rotation path does not meet the endpoint rotations")
            }
            Self::TooFewSamples => {
                formatter.write_str("a sampled linear trajectory has too few samples")
            }
            Self::UnreachableSample { sample } => {
                write!(formatter, "no IK solution for the pose at sample {sample}")
            }
            Self::SamplesOnPath { sample } => {
                write!(
                    formatter,
                    "no IK candidate reproduces the path pose at sample {sample}"
                )
            }
            Self::BranchDiscontinuity { sample } => {
                write!(
                    formatter,
                    "the shoulder/elbow branch changes at sample {sample}"
                )
            }
            Self::StepTooLarge { sample } => {
                write!(
                    formatter,
                    "a joint step at sample {sample} exceeds the branch-continuity bound"
                )
            }
            Self::LimitExceeded { sample, joint } => {
                write!(
                    formatter,
                    "joint {} exceeds its sampled limit at sample {sample}",
                    joint + 1
                )
            }
            Self::CertificationFailed => formatter.write_str(
                "the sampled path has no positive conservative scalar velocity, acceleration \
                 and jerk limits",
            ),
            Self::NumericalFailure => {
                formatter.write_str("a derived linear-path quantity is not finite")
            }
        }
    }
}

impl core::error::Error for LinearError {}

/// The rotation path a [`LinearPath`] carries.
///
/// A function pointer rather than a trait object: the module is `no_std` and must not
/// allocate, and the Lean structure's `rotation` is supplied data that cannot capture
/// state either. [`slerp_rotation`] is the implementation [`LinearPath::slerp`] installs.
pub type RotationPath = fn(&Pose<f64>, &Pose<f64>, f64) -> Mat3<f64>;

/// A Cartesian straight line: `Motion.LinearPath`.
///
/// Position is `(1 - s) start.p + s stop.p`; orientation is the supplied [`RotationPath`].
/// The Lean structure also carries the two endpoint laws and the pointwise `IsRotation`
/// hypothesis. Over `f64` those are checked at the endpoints and on a fixed interior
/// grid, never over all of `ℝ`.
#[derive(Clone, Copy, Debug)]
pub struct LinearPath {
    start: Pose<f64>,
    stop: Pose<f64>,
    rotation: RotationPath,
}

impl LinearPath {
    /// The standard path: affine position and spherical linear interpolation of the
    /// orientation.
    pub fn slerp(start: Pose<f64>, stop: Pose<f64>) -> Result<Self, LinearError> {
        Self::with_rotation(start, stop, slerp_rotation)
    }

    /// A path with a caller-supplied rotation interpolation.
    ///
    /// The Lean development deliberately leaves slerp vs axis-angle open, so the Rust
    /// counterpart does too: the choice is the function passed here. The endpoint laws
    /// and the interior `IsRotation` checks are this constructor's responsibility.
    pub fn with_rotation(
        start: Pose<f64>,
        stop: Pose<f64>,
        rotation: RotationPath,
    ) -> Result<Self, LinearError> {
        if !start.is_finite() || !stop.is_finite() {
            return Err(LinearError::NonFiniteInput);
        }
        if !matrix_is_rotation(start.r) {
            return Err(LinearError::NotARotation { sample: 0 });
        }
        if !matrix_is_rotation(stop.r) {
            return Err(LinearError::NotARotation { sample: 1 });
        }

        let path = Self {
            start,
            stop,
            rotation,
        };
        // Check the *supplied* function, not `rotation_at`: the latter returns the endpoint
        // matrices exactly and would hide a rotation path that violates the Lean endpoint
        // laws.
        if rotation(&start, &stop, 0.0).frobenius_distance(start.r) > ROTATION_TOLERANCE {
            return Err(LinearError::RotationEndpointMismatch);
        }
        if rotation(&start, &stop, 1.0).frobenius_distance(stop.r) > ROTATION_TOLERANCE {
            return Err(LinearError::RotationEndpointMismatch);
        }
        // `∀ s, IsRotation (rotation s)` cannot be decided; sample the open interval.
        const INTERIOR_SAMPLES: usize = 8;
        for index in 1..INTERIOR_SAMPLES {
            let s = index as f64 / INTERIOR_SAMPLES as f64;
            if !matrix_is_rotation(path.rotation_at(s)) {
                return Err(LinearError::NotARotation { sample: index });
            }
        }
        Ok(path)
    }

    pub fn start(&self) -> Pose<f64> {
        self.start
    }

    pub fn stop(&self) -> Pose<f64> {
        self.stop
    }

    /// `Motion.LinearPath.position`: the affine interpolation.
    pub fn position(&self, s: f64) -> Vec3<f64> {
        let start = self.start.p;
        let stop = self.stop.p;
        Vec3::new(
            (1.0 - s) * start.x() + s * stop.x(),
            (1.0 - s) * start.y() + s * stop.y(),
            (1.0 - s) * start.z() + s * stop.z(),
        )
    }

    /// The supplied orientation at `s`. The endpoints are returned exactly, which is what
    /// makes the Lean `rotation_zero` / `rotation_one` fields hold bit for bit.
    pub fn rotation_at(&self, s: f64) -> Mat3<f64> {
        if s <= 0.0 {
            return self.start.r;
        }
        if s >= 1.0 {
            return self.stop.r;
        }
        (self.rotation)(&self.start, &self.stop, s)
    }

    /// `Motion.LinearPath.pose`.
    pub fn pose(&self, s: f64) -> Pose<f64> {
        Pose::new(self.rotation_at(s), self.position(s))
    }
}

/// One sampled solution: the placed total joint angles in radians, plus the branch labels
/// of the candidate they came from.
///
/// `angles` is a continuous representative, exactly the `SampledSolutions.angles` field:
/// it is the candidate's angles placed beside the previous sample by
/// [`Solution::representative_near`], so a wound joint keeps its whole turns.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LinearSample {
    pub angles: [f64; JOINT_COUNT],
    /// `+1` or `-1`, Lean's `Solution.shoulder`.
    pub shoulder: i8,
    /// `+1` or `-1`, Lean's `Solution.elbow`.
    pub elbow: i8,
}

impl Default for LinearSample {
    fn default() -> Self {
        Self {
            angles: [0.0; JOINT_COUNT],
            shoulder: 1,
            elbow: 1,
        }
    }
}

impl LinearSample {
    pub fn is_finite(self) -> bool {
        self.angles.iter().all(|angle| angle.is_finite())
    }

    fn reference(self) -> Solution<f64> {
        Solution {
            angles: self.angles,
            shoulder: self.shoulder,
            elbow: self.elbow,
        }
    }
}

/// `Motion.SampledTrajectory`: a uniformly timed sequence of configurations.
///
/// `parameter k = k / (count - 1)`, exactly the Lean definition. The velocity,
/// acceleration and jerk are **forward finite differences**, as in the specification —
/// this is a sampled contract, not an analytic derivative.
#[derive(Clone, Copy, Debug)]
pub struct SampledTrajectory<'a> {
    dt: f64,
    angles: &'a [[f64; JOINT_COUNT]],
}

impl<'a> SampledTrajectory<'a> {
    pub fn new(dt: f64, angles: &'a [[f64; JOINT_COUNT]]) -> Result<Self, LinearError> {
        if angles.len() < 2 {
            return Err(LinearError::TooFewSamples);
        }
        if !dt.is_finite() || dt <= 0.0 {
            return Err(LinearError::NonFiniteInput);
        }
        if angles
            .iter()
            .any(|row| row.iter().any(|angle| !angle.is_finite()))
        {
            return Err(LinearError::NonFiniteInput);
        }
        Ok(Self { dt, angles })
    }

    pub fn dt(&self) -> f64 {
        self.dt
    }

    pub fn count(&self) -> usize {
        self.angles.len()
    }

    /// `time(k) = k · dt`.
    pub fn time(&self, k: usize) -> f64 {
        k as f64 * self.dt
    }

    /// `parameter(k) = k / (count - 1)`.
    pub fn parameter(&self, k: usize) -> f64 {
        k as f64 / (self.count() - 1) as f64
    }

    pub fn angles(&self, k: usize) -> [f64; JOINT_COUNT] {
        self.angles[k]
    }

    pub fn angle(&self, k: usize, joint: usize) -> f64 {
        self.angles[k][joint]
    }

    /// Forward finite-difference velocity between samples `k` and `k + 1`.
    pub fn velocity(&self, k: usize, joint: usize) -> Option<f64> {
        (k + 1 < self.count()).then(|| (self.angle(k + 1, joint) - self.angle(k, joint)) / self.dt)
    }

    /// Forward finite-difference acceleration between velocities `k` and `k + 1`.
    pub fn acceleration(&self, k: usize, joint: usize) -> Option<f64> {
        if k + 2 >= self.count() {
            return None;
        }
        let next = self.velocity(k + 1, joint)?;
        let current = self.velocity(k, joint)?;
        Some((next - current) / self.dt)
    }

    /// Forward finite-difference jerk between accelerations `k` and `k + 1`.
    pub fn jerk(&self, k: usize, joint: usize) -> Option<f64> {
        if k + 3 >= self.count() {
            return None;
        }
        let next = self.acceleration(k + 1, joint)?;
        let current = self.acceleration(k, joint)?;
        Some((next - current) / self.dt)
    }
}

/// `Motion.BranchContinuous`: consecutive shoulder/elbow labels agree and every wrapped
/// joint step is at most `max_step` radians.
pub fn check_branch_continuous(samples: &[LinearSample], max_step: f64) -> Result<(), LinearError> {
    if !max_step.is_finite() || max_step < 0.0 {
        return Err(LinearError::NonFiniteInput);
    }
    for k in 0..samples.len().saturating_sub(1) {
        if samples[k + 1].shoulder != samples[k].shoulder
            || samples[k + 1].elbow != samples[k].elbow
        {
            return Err(LinearError::BranchDiscontinuity { sample: k + 1 });
        }
        for joint in 0..JOINT_COUNT {
            let step = wrap_angle(samples[k + 1].angles[joint] - samples[k].angles[joint]).abs();
            if step > max_step {
                return Err(LinearError::StepTooLarge { sample: k + 1 });
            }
        }
    }
    Ok(())
}

/// `Motion.WithinSampledLimits`: the finite-difference V/A/J samples respect the limits.
pub fn check_within_sampled_limits(
    limits: &[Limits<f64>; JOINT_COUNT],
    trajectory: &SampledTrajectory<'_>,
) -> Result<(), LinearError> {
    check_limits(limits, trajectory.dt(), trajectory.count(), |k, joint| {
        trajectory.angle(k, joint)
    })
}

/// The shared body of the two limit checks: one over a [`SampledTrajectory`], one over
/// planner output that carries branch labels beside the angles.
fn check_limits<F>(
    limits: &[Limits<f64>; JOINT_COUNT],
    dt: f64,
    count: usize,
    angle: F,
) -> Result<(), LinearError>
where
    F: Fn(usize, usize) -> f64,
{
    if count < 2 || !dt.is_finite() || dt <= 0.0 {
        return Err(LinearError::TooFewSamples);
    }

    // Velocity: k + 1 < count.
    for k in 0..count - 1 {
        for (joint, limit) in limits.iter().enumerate() {
            let velocity = (angle(k + 1, joint) - angle(k, joint)) / dt;
            if !velocity.is_finite() || velocity.abs() > limit.vmax() {
                return Err(LinearError::LimitExceeded { sample: k, joint });
            }
        }
    }
    // Acceleration: k + 2 < count.
    for k in 0..count.saturating_sub(2) {
        for (joint, limit) in limits.iter().enumerate() {
            let v0 = (angle(k + 1, joint) - angle(k, joint)) / dt;
            let v1 = (angle(k + 2, joint) - angle(k + 1, joint)) / dt;
            let acceleration = (v1 - v0) / dt;
            if !acceleration.is_finite() || acceleration.abs() > limit.amax() {
                return Err(LinearError::LimitExceeded { sample: k, joint });
            }
        }
    }
    // Jerk: k + 3 < count.
    for k in 0..count.saturating_sub(3) {
        for (joint, limit) in limits.iter().enumerate() {
            let v0 = (angle(k + 1, joint) - angle(k, joint)) / dt;
            let v1 = (angle(k + 2, joint) - angle(k + 1, joint)) / dt;
            let v2 = (angle(k + 3, joint) - angle(k + 2, joint)) / dt;
            let a0 = (v1 - v0) / dt;
            let a1 = (v2 - v1) / dt;
            let jerk = (a1 - a0) / dt;
            if !jerk.is_finite() || jerk.abs() > limit.jmax() {
                return Err(LinearError::LimitExceeded { sample: k, joint });
            }
        }
    }
    Ok(())
}

/// Solve one sampled pose with the closed form and place the chosen candidate beside
/// `reference`.
///
/// This is the numerical form of `SamplesAreSolutions` and `SamplesOnPath` together.
/// Every candidate comes from [`robot_kinematics::solve`] with `Tolerances::python()` —
/// the same tolerance-widened solver the pose jogs use. That matters at a wrist
/// singularity: a command pose that has been through the RPY boundary can differ from the
/// exact configuration by an ulp, and the unfiltered exact [`robot_kinematics::solutions`]
/// candidates can then jump between wrist splits while `solve`'s pose filter keeps the
/// continuous flat split. The candidates that survive are re-checked against `target`
/// within [`POSE_TOLERANCE`] (Lean's `SamplesOnPath`), and the nearest one is placed with
/// [`Solution::representative_near`], which preserves winding. An empty candidate set is
/// [`LinearError::UnreachableSample`]; a non-empty set with no survivor is
/// [`LinearError::SamplesOnPath`].
pub fn solve_sample(
    geometry: &Geometry<f64>,
    target: &Pose<f64>,
    reference: &Solution<f64>,
) -> Result<LinearSample, LinearError> {
    if !target.is_finite() {
        return Err(LinearError::NonFiniteInput);
    }
    let mut candidates = SolutionSet::<f64>::new();
    solve(geometry, target, &Tolerances::python(), &mut candidates);
    if candidates.is_empty() {
        return Err(LinearError::UnreachableSample { sample: 0 });
    }

    let mut best: Option<(LinearSample, f64)> = None;
    for candidate in candidates.iter() {
        let placed = candidate.representative_near(reference);
        let reconstructed = fk(geometry, &placed.angles);
        if reconstructed.p.distance(target.p) > POSE_TOLERANCE
            || reconstructed.r.frobenius_distance(target.r) > POSE_TOLERANCE
        {
            continue;
        }
        let distance = placed.wrapped_distance_sq(reference);
        if best.is_none_or(|(_, best_distance)| distance < best_distance) {
            best = Some((
                LinearSample {
                    angles: placed.angles,
                    shoulder: candidate.shoulder,
                    elbow: candidate.elbow,
                },
                distance,
            ));
        }
    }
    best.map(|(sample, _)| sample)
        .ok_or(LinearError::SamplesOnPath { sample: 0 })
}

/// A conservative scalar time law for a linear path, plus its start sample.
///
/// The `profile` is `s(t)`, `s ∈ [0, 1]`, from [`plan_rest_to_rest`]; its total time is
/// the duration of the Cartesian move. It is deliberately not a Lean object: the Lean
/// `SampledTrajectory` has no timing law, and this is the application's numerical
/// extension (see the module docs).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LinearCertificate {
    /// The rest-to-rest scalar profile in the path parameter.
    pub profile: Profile<f64>,
    /// The `s = 0` solution, chosen nearest the caller's reference.
    pub start: LinearSample,
    /// The limits the certificate was built against.
    pub limits: [Limits<f64>; JOINT_COUNT],
    /// The branch-continuity bound the samples were checked against.
    pub max_step: f64,
}

impl LinearCertificate {
    pub fn duration(&self) -> f64 {
        self.profile.total_time()
    }
}

/// Certify a linear path and build its rest-to-rest scalar time law.
///
/// `samples` is scratch storage whose length selects the path-sampling density: the
/// longer the slice, the tighter the finite-difference bounds. Four samples is the
/// minimum the third difference needs. The slice is filled with the uniform-parameter
/// solutions and is not needed by the caller afterwards.
///
/// The returned certificate's duration is zero when the path does not move any joint;
/// [`sample_linear_certificate`] then returns a single sample.
pub fn certify_linear_path(
    geometry: &Geometry<f64>,
    path: &LinearPath,
    reference: &Solution<f64>,
    limits: &[Limits<f64>; JOINT_COUNT],
    max_step: f64,
    samples: &mut [LinearSample],
) -> Result<LinearCertificate, LinearError> {
    let count = samples.len();
    if count < 4 {
        return Err(LinearError::TooFewSamples);
    }
    if !max_step.is_finite() || max_step < 0.0 {
        return Err(LinearError::NonFiniteInput);
    }
    if limits.iter().any(|limit| {
        !limit.vmax().is_finite() || !limit.amax().is_finite() || !limit.jmax().is_finite()
    }) {
        return Err(LinearError::NonFiniteInput);
    }

    // An exactly stationary path is a zero-duration move, not a dense sampling of a
    // point. Solving it sample by sample near a wrist singularity can turn ulp-sized
    // quaternion differences into a large wrist split; the endpoints say there is no
    // motion, so resolve the start once and stop.
    if path.start() == path.stop() {
        let start = solve_sample(geometry, &path.pose(0.0), reference)
            .map_err(|error| at_sample(error, 0))?;
        return Ok(LinearCertificate {
            profile: Profile::constant(State::new(0.0, 0.0, 0.0)),
            start,
            limits: *limits,
            max_step,
        });
    }

    // The uniform-parameter solve. The first sample is the reference's nearest candidate;
    // each later sample is the previous sample's nearest, which is the selection half of
    // `BranchContinuous`.
    samples[0] =
        solve_sample(geometry, &path.pose(0.0), reference).map_err(|error| at_sample(error, 0))?;
    for index in 1..count {
        let s = index as f64 / (count - 1) as f64;
        let previous = samples[index - 1].reference();
        samples[index] = solve_sample(geometry, &path.pose(s), &previous)
            .map_err(|error| at_sample(error, index))?;
    }
    check_branch_continuous(samples, max_step)?;

    let step = 1.0 / (count - 1) as f64;
    let (m1, m2, m3) = derivative_bounds(samples, step);

    let moving = (0..JOINT_COUNT).any(|joint| m1[joint] > STATIONARY_BOUND);
    if !moving {
        return Ok(LinearCertificate {
            profile: Profile::constant(State::new(0.0, 0.0, 0.0)),
            start: samples[0],
            limits: *limits,
            max_step,
        });
    }

    let scalar = scalar_limits(&m1, &m2, &m3, limits).ok_or(LinearError::CertificationFailed)?;
    let profile = plan_rest_to_rest(0.0, 1.0, scalar).map_err(map_plan_error)?;
    Ok(LinearCertificate {
        profile,
        start: samples[0],
        limits: *limits,
        max_step,
    })
}

/// Sample a certified path at uniform time.
///
/// `out.len()` is the output sample count; the time step is `duration / (out.len() - 1)`.
/// Each output is solved fresh at `path.pose(profile.eval(t).q)`, so `SamplesOnPath` holds
/// pointwise rather than by interpolation, and the branch is selected from the previous
/// output sample. `out` is checked against `BranchContinuous` and
/// `WithinSampledLimits` before it is returned.
///
/// A zero-duration certificate fills `out[0]` with its start sample and returns `1`.
pub fn sample_linear_certificate(
    geometry: &Geometry<f64>,
    path: &LinearPath,
    certificate: &LinearCertificate,
    out: &mut [LinearSample],
) -> Result<usize, LinearError> {
    let count = out.len();
    let duration = certificate.duration();
    if duration <= 0.0 {
        if out.is_empty() {
            return Err(LinearError::TooFewSamples);
        }
        out[0] = certificate.start;
        return Ok(1);
    }
    if count < 2 {
        return Err(LinearError::TooFewSamples);
    }
    let dt = duration / (count - 1) as f64;
    if !dt.is_finite() || dt <= 0.0 {
        return Err(LinearError::NumericalFailure);
    }

    out[0] = certificate.start;
    for index in 1..count {
        let t = if index + 1 == count {
            duration
        } else {
            index as f64 * dt
        };
        let s = certificate.profile.eval(t).q;
        // The profile is finite for finite limits; the check keeps `clamp` total, since
        // `f64::clamp` would panic on a NaN it cannot see through the profile.
        if !s.is_finite() {
            return Err(LinearError::NumericalFailure);
        }
        let s = s.clamp(0.0, 1.0);
        let previous = out[index - 1].reference();
        out[index] = solve_sample(geometry, &path.pose(s), &previous)
            .map_err(|error| at_sample(error, index))?;
    }

    check_branch_continuous(out, certificate.max_step)?;
    check_limits(&certificate.limits, dt, count, |k, joint| {
        out[k].angles[joint]
    })?;
    Ok(count)
}

/// Solve the conservative M5 inequalities for one scalar `(V, A, J)`.
///
/// `V` starts at the tightest `vmax / M1` ratio and is then reduced through the listed
/// scales until `A` and `J` are positive for every moving joint. The reduction is what
/// handles a joint that barely moves but is curved: its `M2 · V²` term can exceed `amax`
/// at the first `V`, even though a slower path is perfectly feasible. `none` means no
/// tested scale produced positive limits; that is the certifier's honest failure, not a
/// licence to emit a faster profile.
fn scalar_limits(
    m1: &[f64; JOINT_COUNT],
    m2: &[f64; JOINT_COUNT],
    m3: &[f64; JOINT_COUNT],
    limits: &[Limits<f64>; JOINT_COUNT],
) -> Option<Limits<f64>> {
    let mut base = f64::INFINITY;
    for joint in 0..JOINT_COUNT {
        if m1[joint] > STATIONARY_BOUND {
            base = base.min(limits[joint].vmax() / m1[joint]);
        }
    }
    if !base.is_finite() || base <= 0.0 {
        return None;
    }

    const SCALES: [f64; 9] = [LIMIT_MARGIN, 0.4, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.001];
    for scale in SCALES {
        let vmax = base * scale;
        if !vmax.is_finite() || vmax <= 0.0 {
            continue;
        }

        let mut acceleration = f64::INFINITY;
        for joint in 0..JOINT_COUNT {
            if m1[joint] > STATIONARY_BOUND {
                acceleration =
                    acceleration.min((limits[joint].amax() - m2[joint] * vmax * vmax) / m1[joint]);
            }
        }
        if !acceleration.is_finite() || acceleration <= 0.0 {
            continue;
        }

        // The jerk inequality also contains the chosen acceleration (`3 M2 V A`), so a
        // path can have a feasible A but still no positive J. Trading acceleration for
        // jerk is the remaining degree of freedom, and a slower profile beats a refusal.
        const ACCELERATION_SCALES: [f64; 6] = [LIMIT_MARGIN, 0.4, 0.2, 0.1, 0.05, 0.02];
        for acceleration_scale in ACCELERATION_SCALES {
            let amax = acceleration * acceleration_scale;
            let mut jmax = f64::INFINITY;
            for joint in 0..JOINT_COUNT {
                if m1[joint] > STATIONARY_BOUND {
                    let used = m3[joint] * vmax * vmax * vmax + 3.0 * m2[joint] * vmax * amax;
                    jmax = jmax.min((limits[joint].jmax() - used) / m1[joint]);
                }
            }
            if !jmax.is_finite() || jmax <= 0.0 {
                continue;
            }
            let jmax = jmax * LIMIT_MARGIN;

            if let Ok(limits) = Limits::new(vmax, amax, jmax) {
                return Some(limits);
            }
        }
    }
    None
}

/// Per-joint sampled bounds for `q'(s)`, `q''(s)` and `q'''(s)`.
///
/// Forward differences at index `k`; the absolute maximum over the grid. This is the
/// numerical substitute for the `M1/M2/M3` hypotheses of `cartesian_path_feasible`, and
/// the module docs are explicit that it is sampled, not proved.
fn derivative_bounds(
    samples: &[LinearSample],
    step: f64,
) -> ([f64; JOINT_COUNT], [f64; JOINT_COUNT], [f64; JOINT_COUNT]) {
    let count = samples.len();
    let mut m1: [f64; JOINT_COUNT] = [0.0; JOINT_COUNT];
    let mut m2: [f64; JOINT_COUNT] = [0.0; JOINT_COUNT];
    let mut m3: [f64; JOINT_COUNT] = [0.0; JOINT_COUNT];
    for joint in 0..JOINT_COUNT {
        for k in 0..count - 1 {
            let first = (samples[k + 1].angles[joint] - samples[k].angles[joint]) / step;
            m1[joint] = m1[joint].max(first.abs());
        }
        for k in 0..count - 2 {
            let second = (samples[k + 2].angles[joint] - 2.0 * samples[k + 1].angles[joint]
                + samples[k].angles[joint])
                / (step * step);
            m2[joint] = m2[joint].max(second.abs());
        }
        for k in 0..count - 3 {
            let third = (samples[k + 3].angles[joint] - 3.0 * samples[k + 2].angles[joint]
                + 3.0 * samples[k + 1].angles[joint]
                - samples[k].angles[joint])
                / (step * step * step);
            m3[joint] = m3[joint].max(third.abs());
        }
    }
    (m1, m2, m3)
}

/// Replace the sample index of a [`solve_sample`] error, which does not know where the
/// caller placed the pose.
fn at_sample(error: LinearError, sample: usize) -> LinearError {
    match error {
        LinearError::UnreachableSample { .. } => LinearError::UnreachableSample { sample },
        LinearError::SamplesOnPath { .. } => LinearError::SamplesOnPath { sample },
        other => other,
    }
}

fn map_plan_error(_: PlanError) -> LinearError {
    LinearError::NumericalFailure
}

/// Whether a matrix is orthogonal with determinant one — Lean's `Linear.IsRotation`, the
/// hypothesis `LinearPath.rotation_isRotation` carries pointwise.
fn matrix_is_rotation(matrix: Mat3<f64>) -> bool {
    let identity = Mat3::identity();
    (matrix.transpose() * matrix).frobenius_distance(identity) <= ROTATION_TOLERANCE
        && (matrix.det() - 1.0).abs() <= ROTATION_TOLERANCE
}

/// Spherical linear interpolation of two rotations, supplied as a [`RotationPath`].
///
/// The shortest arc is chosen (`q` and `-q` are the same rotation), and nearly parallel
/// quaternions fall back to a normalised linear interpolation. The endpoints are exact.
pub fn slerp_rotation(start: &Pose<f64>, stop: &Pose<f64>, s: f64) -> Mat3<f64> {
    if s <= 0.0 {
        return start.r;
    }
    if s >= 1.0 {
        return stop.r;
    }
    // Identical rotations interpolate to themselves. Without this, the quaternion
    // round trip below changes the matrix by an ulp or two; near a wrist singularity that
    // is enough to make the IK read-back jump between wrist splits, which turns a stationary
    // path into a fictitious long move.
    if start.r == stop.r {
        return start.r;
    }

    let q0 = quaternion_from_rotation(start.r);
    let mut q1 = quaternion_from_rotation(stop.r);
    let mut cosine = dot4(q0, q1);
    if cosine < 0.0 {
        for value in &mut q1 {
            *value = -*value;
        }
        cosine = -cosine;
    }
    if cosine > 1.0 {
        cosine = 1.0;
    }

    let quaternion = if cosine > 0.9995 {
        let mut linear = [0.0; 4];
        for index in 0..4 {
            linear[index] = q0[index] + (q1[index] - q0[index]) * s;
        }
        normalize4(linear)
    } else {
        let theta = Scalar::acos(cosine);
        let sine = Scalar::sin(theta);
        let angle = theta * s;
        let weight0 = Scalar::sin(theta - angle) / sine;
        let weight1 = Scalar::sin(angle) / sine;
        let mut blended = [0.0; 4];
        for index in 0..4 {
            blended[index] = q0[index] * weight0 + q1[index] * weight1;
        }
        normalize4(blended)
    };
    rotation_from_quaternion(quaternion)
}

/// The quaternion of a rotation matrix, by the branchwise trace formulas.
fn quaternion_from_rotation(matrix: Mat3<f64>) -> [f64; 4] {
    let m00 = matrix.at(0, 0);
    let m01 = matrix.at(0, 1);
    let m02 = matrix.at(0, 2);
    let m10 = matrix.at(1, 0);
    let m11 = matrix.at(1, 1);
    let m12 = matrix.at(1, 2);
    let m20 = matrix.at(2, 0);
    let m21 = matrix.at(2, 1);
    let m22 = matrix.at(2, 2);
    let trace = m00 + m11 + m22;

    let quaternion = if trace > 0.0 {
        let s = Scalar::sqrt(trace + 1.0) * 2.0;
        [0.25 * s, (m21 - m12) / s, (m02 - m20) / s, (m10 - m01) / s]
    } else if m00 > m11 && m00 > m22 {
        let s = Scalar::sqrt(1.0 + m00 - m11 - m22) * 2.0;
        [(m21 - m12) / s, 0.25 * s, (m01 + m10) / s, (m02 + m20) / s]
    } else if m11 > m22 {
        let s = Scalar::sqrt(1.0 + m11 - m00 - m22) * 2.0;
        [(m02 - m20) / s, (m01 + m10) / s, 0.25 * s, (m12 + m21) / s]
    } else {
        let s = Scalar::sqrt(1.0 + m22 - m00 - m11) * 2.0;
        [(m10 - m01) / s, (m02 + m20) / s, (m12 + m21) / s, 0.25 * s]
    };
    normalize4(quaternion)
}

/// The rotation matrix of a unit quaternion.
fn rotation_from_quaternion(quaternion: [f64; 4]) -> Mat3<f64> {
    let [w, x, y, z] = normalize4(quaternion);
    let xx = x * x;
    let yy = y * y;
    let zz = z * z;
    let xy = x * y;
    let xz = x * z;
    let yz = y * z;
    let wx = w * x;
    let wy = w * y;
    let wz = w * z;
    Mat3::from_rows([
        [1.0 - 2.0 * (yy + zz), 2.0 * (xy - wz), 2.0 * (xz + wy)],
        [2.0 * (xy + wz), 1.0 - 2.0 * (xx + zz), 2.0 * (yz - wx)],
        [2.0 * (xz - wy), 2.0 * (yz + wx), 1.0 - 2.0 * (xx + yy)],
    ])
}

fn dot4(left: [f64; 4], right: [f64; 4]) -> f64 {
    left[0] * right[0] + left[1] * right[1] + left[2] * right[2] + left[3] * right[3]
}

fn normalize4(quaternion: [f64; 4]) -> [f64; 4] {
    let norm = Scalar::sqrt(dot4(quaternion, quaternion));
    if !norm.is_finite() || norm == 0.0 {
        return [1.0, 0.0, 0.0, 0.0];
    }
    [
        quaternion[0] / norm,
        quaternion[1] / norm,
        quaternion[2] / norm,
        quaternion[3] / norm,
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::units::deg_to_rad;

    fn rotation(axis: usize, angle: f64) -> Mat3<f64> {
        match axis {
            0 => Mat3::rot_x(angle),
            1 => Mat3::rot_y(angle),
            _ => Mat3::rot_z(angle),
        }
    }

    #[test]
    fn slerp_endpoints_are_the_input_rotations_bit_for_bit() {
        let start = Pose::new(rotation(2, 0.3), Vec3::new(1.0, 2.0, 3.0));
        let stop = Pose::new(
            rotation(1, -1.1) * rotation(0, 0.4),
            Vec3::new(-4.0, 5.0, 6.0),
        );
        let path = LinearPath::slerp(start, stop).expect("finite rotations");
        assert_eq!(path.pose(0.0).r, start.r);
        assert_eq!(path.pose(1.0).r, stop.r);
        assert_eq!(path.pose(0.0).p, start.p);
        assert_eq!(path.pose(1.0).p, stop.p);
    }

    #[test]
    fn the_quaternion_bridge_rebuilds_the_rotation() {
        for matrix in [
            Mat3::rot_x(0.3),
            Mat3::rot_y(-1.2) * Mat3::rot_z(0.7),
            Mat3::rot_z(2.9) * Mat3::rot_x(-0.4) * Mat3::rot_y(1.1),
            Mat3::from_rows([[-1.0, 0.0, 0.0], [0.0, -1.0, 0.0], [0.0, 0.0, 1.0]]),
        ] {
            let rebuilt = rotation_from_quaternion(quaternion_from_rotation(matrix));
            assert!(
                rebuilt.frobenius_distance(matrix) < 1e-12,
                "round trip missed by {}",
                rebuilt.frobenius_distance(matrix)
            );
        }
    }

    #[test]
    fn slerp_midpoint_of_a_quarter_turn_is_an_eighth_turn() {
        let start = Pose::new(Mat3::identity(), Vec3::zero());
        let stop = Pose::new(Mat3::rot_z(core::f64::consts::FRAC_PI_2), Vec3::zero());
        let path = LinearPath::slerp(start, stop).expect("rotations");
        let midpoint = path.pose(0.5).r;
        let expected = Mat3::rot_z(core::f64::consts::FRAC_PI_4);
        assert!(
            midpoint.frobenius_distance(expected) < 1e-12,
            "midpoint is {:?}",
            midpoint
        );
    }

    #[test]
    fn position_is_affine() {
        let start = Pose::new(Mat3::identity(), Vec3::new(1.0, -2.0, 3.0));
        let stop = Pose::new(Mat3::identity(), Vec3::new(5.0, 6.0, -7.0));
        let path = LinearPath::slerp(start, stop).expect("rotations");
        for s in [0.0, 0.25, 0.5, 0.75, 1.0] {
            let p = path.position(s);
            assert!((p.x() - ((1.0 - s) * 1.0 + s * 5.0)).abs() < 1e-15);
            assert!((p.y() - ((1.0 - s) * -2.0 + s * 6.0)).abs() < 1e-15);
            assert!((p.z() - ((1.0 - s) * 3.0 + s * -7.0)).abs() < 1e-15);
        }
    }

    #[test]
    fn a_supplied_rotation_path_is_accepted_and_its_endpoints_checked() {
        fn axis_angle(start: &Pose<f64>, _stop: &Pose<f64>, s: f64) -> Mat3<f64> {
            start.r * Mat3::rot_z(core::f64::consts::FRAC_PI_2 * s)
        }
        let start = Pose::new(Mat3::identity(), Vec3::zero());
        let stop = Pose::new(Mat3::rot_z(core::f64::consts::FRAC_PI_2), Vec3::zero());
        let path = LinearPath::with_rotation(start, stop, axis_angle).expect("valid path");
        assert!(matrix_is_rotation(path.pose(0.37).r));

        fn wrong_endpoint(_: &Pose<f64>, _: &Pose<f64>, _: f64) -> Mat3<f64> {
            Mat3::rot_x(0.1)
        }
        assert_eq!(
            LinearPath::with_rotation(start, stop, wrong_endpoint).unwrap_err(),
            LinearError::RotationEndpointMismatch
        );
    }

    #[test]
    fn a_non_rotation_endpoint_is_rejected() {
        let mut start = Pose::new(Mat3::identity(), Vec3::zero());
        start.r.set(0, 0, 2.0);
        assert_eq!(
            LinearPath::slerp(start, Pose::identity()).unwrap_err(),
            LinearError::NotARotation { sample: 0 }
        );
    }

    #[test]
    fn sampled_trajectory_uses_the_lean_parameter_and_forward_differences() {
        let angles = [
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [1.0, -1.0, 2.0, 0.0, 0.0, 0.0],
            [3.0, -2.0, 5.0, 0.0, 0.0, 0.0],
            [6.0, -2.0, 9.0, 0.0, 0.0, 0.0],
        ];
        let trajectory = SampledTrajectory::new(0.5, &angles).expect("valid");
        assert_eq!(trajectory.count(), 4);
        assert!((trajectory.parameter(1) - 1.0 / 3.0).abs() < 1e-15);
        assert!((trajectory.time(2) - 1.0).abs() < 1e-15);
        assert_eq!(trajectory.velocity(0, 0), Some(2.0));
        assert_eq!(trajectory.velocity(1, 0), Some(4.0));
        assert_eq!(trajectory.acceleration(0, 0), Some(4.0));
        assert_eq!(trajectory.jerk(0, 0), Some(0.0));
        assert_eq!(trajectory.jerk(0, 1), Some(8.0));
        assert_eq!(trajectory.jerk(1, 0), None);
    }

    #[test]
    fn sampled_limits_reject_a_velocity_and_a_jerk_violation() {
        let angles = [
            [0.0; JOINT_COUNT],
            [1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [2.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [3.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        ];
        let trajectory = SampledTrajectory::new(0.5, &angles).expect("valid");
        let good = [
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
        ];
        assert_eq!(check_within_sampled_limits(&good, &trajectory), Ok(()));

        let tight = [
            Limits::new(1.5, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
            Limits::new(10.0, 10.0, 10.0).expect("positive"),
        ];
        assert_eq!(
            check_within_sampled_limits(&tight, &trajectory),
            Err(LinearError::LimitExceeded {
                sample: 0,
                joint: 0
            })
        );
    }

    #[test]
    fn branch_continuity_checks_labels_and_wrapped_steps() {
        let base = LinearSample {
            angles: [0.0; JOINT_COUNT],
            shoulder: 1,
            elbow: 1,
        };
        let mut turned = base;
        turned.angles[0] = 0.2;
        assert_eq!(check_branch_continuous(&[base, turned], 0.3), Ok(()));
        assert_eq!(
            check_branch_continuous(&[base, turned], 0.1),
            Err(LinearError::StepTooLarge { sample: 1 })
        );

        let mut flipped = turned;
        flipped.shoulder = -1;
        assert_eq!(
            check_branch_continuous(&[base, flipped], 1.0),
            Err(LinearError::BranchDiscontinuity { sample: 1 })
        );
    }

    /// A known configuration and the pose it produces, with the shipped arm.
    fn known_configuration() -> (Geometry<f64>, Solution<f64>) {
        let geometry = Geometry::<f64>::shipped();
        let angles = [0.3, deg_to_rad(90.0) + 0.2, -0.4, 0.1, 0.5, -0.3];
        let solution = Solution {
            angles,
            shoulder: 1,
            elbow: 1,
        };
        (geometry, solution)
    }

    #[test]
    fn a_short_cartesian_move_certifies_and_samples_on_the_path() {
        let (geometry, reference) = known_configuration();
        let start = fk(&geometry, &reference.angles);
        let mut stop = start;
        stop.p = stop.p + Vec3::new(2.0, -1.0, 0.5);
        let path = LinearPath::slerp(start, stop).expect("the poses are rotations");
        let limits = [Limits::new(10.0, 20.0, 40.0).expect("positive"); JOINT_COUNT];

        let mut path_samples = [LinearSample::default(); 65];
        let certificate = certify_linear_path(
            &geometry,
            &path,
            &reference,
            &limits,
            0.5,
            &mut path_samples,
        )
        .expect("the move is feasible");
        assert!(certificate.duration() > 0.0);

        let mut output = [LinearSample::default(); 201];
        let count = sample_linear_certificate(&geometry, &path, &certificate, &mut output)
            .expect("the sampled path is feasible");
        assert_eq!(count, output.len());
        assert!(output[0].is_finite());
        for sample in &output[..count] {
            let reconstructed = fk(&geometry, &sample.angles);
            assert!(
                reconstructed.p.is_finite() && reconstructed.r.is_finite(),
                "the forward chain produced a non-finite pose"
            );
        }
        // The first sample is the reference, placed.
        for joint in 0..JOINT_COUNT {
            assert!((output[0].angles[joint] - reference.angles[joint]).abs() < 1e-9);
        }
    }

    #[test]
    fn an_unreachable_path_is_reported() {
        let (geometry, reference) = known_configuration();
        let start = fk(&geometry, &reference.angles);
        let stop = Pose::new(Mat3::identity(), Vec3::new(10_000.0, 0.0, 0.0));
        let path = LinearPath::slerp(start, stop).expect("rotations");
        let limits = [Limits::new(10.0, 20.0, 40.0).expect("positive"); JOINT_COUNT];
        let mut samples = [LinearSample::default(); 65];
        let error = certify_linear_path(&geometry, &path, &reference, &limits, 0.5, &mut samples)
            .expect_err("the far pose is unreachable");
        assert!(
            matches!(error, LinearError::UnreachableSample { .. }),
            "{error}"
        );
    }

    #[test]
    fn a_zero_motion_path_has_a_zero_duration_certificate() {
        let (geometry, reference) = known_configuration();
        let start = fk(&geometry, &reference.angles);
        let path = LinearPath::slerp(start, start).expect("rotations");
        let limits = [Limits::new(10.0, 20.0, 40.0).expect("positive"); JOINT_COUNT];
        let mut samples = [LinearSample::default(); 17];
        let certificate =
            certify_linear_path(&geometry, &path, &reference, &limits, 0.5, &mut samples)
                .expect("zero motion is trivially feasible");
        assert_eq!(certificate.duration(), 0.0);
        let mut output = [LinearSample::default(); 4];
        assert_eq!(
            sample_linear_certificate(&geometry, &path, &certificate, &mut output),
            Ok(1)
        );
    }
}
