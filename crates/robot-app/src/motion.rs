//! Motion commands, the queue, and playback.
//!
//! # What a command is
//!
//! The first command type is `movej`: a straight line in joint space, one scalar S-curve
//! shared by all six joints so they start and stop together and the slowest joint sets the
//! pace. Its start and stop are runtime joint angles in degrees, the app's own unit; the
//! planner's arithmetic is unit-agnostic, so the degrees go in unchanged.
//!
//! A command carries its own velocity, acceleration and jerk request. The *physical* limits
//! live in `robot_parameters.json` and belong to the robot, one row per joint. The
//! effective limit is the tighter of the two, component by component: a command that asks
//! for less than a joint allows runs exactly as written, and one that asks for more is
//! capped. This module never rejects a command merely for exceeding a physical limit; the
//! cap happens silently in the plan and the UI shows where it applied.
//!
//! # The queue and the plan
//!
//! The queue is what the user builds and copies as JSON. The playback plan is what will
//! actually run: when the next command starts away from the pose the arm is in, a
//! transition MoveJ is inserted from the current pose to that start, using the command's
//! own (capped) limits. This is what makes the first command reach its start location and
//! what bridges gaps after a queue edit or import. Transitions are **not** written back
//! into the queue: a materialized transition would be tied to the pose at authoring time,
//! and replaying from somewhere else would stack another one in front of it.
//!
//! Every command is rest-to-rest, so the arm reaches zero velocity at each junction.
//! Blending across junctions is the future waypoint command type.
//!
//! # Playback
//!
//! [`MotionRuntime::advance`] runs in `Update` before the scene's joint sync and writes
//! `RobotState::runtime_angles_deg`; the 3D view and the Parameters fields follow. It is an
//! open-loop replay of the planned profiles, not the `robot-motion` plant/supervisor
//! harness: this app is a kinematic simulator, and the planned trajectory is exactly what
//! the graph cursor shows. The frame delta is capped so a long stall (a focus loss, a
//! breakpoint) cannot teleport the arm.

use bevy::prelude::{Res, ResMut, Resource, Time};
use robot_kinematics::JOINT_COUNT;
use robot_model::{DHParameters, FRAME_COUNT, JointMotionLimits, MotionLimits};
use robot_motion::{JointProfile, Limits, plan_movej_scalar_optimal};
use serde::{Deserialize, Serialize};

use crate::RobotState;
use crate::session::{self, Session};

/// The queue envelope's schema string.
pub const QUEUE_SCHEMA: &str = "robot-app.motion-queue";
/// The queue envelope's version. A file from a future version is refused by name rather
/// than guessed at.
pub const QUEUE_VERSION: u32 = 1;
/// A start this close to the cursor is the same place; it does not earn a transition.
pub const CHAIN_EPSILON_DEG: f64 = 1e-9;
/// The largest frame step playback takes. Anything longer is a stall, not motion.
pub const MAX_FRAME_DELTA_SECS: f64 = 0.1;
/// Graph samples per second of planned motion, before the clamps below.
pub const GRAPH_SAMPLE_HZ: f64 = 60.0;
/// A ceiling on one segment's samples.
pub const MAX_SAMPLES_PER_SEGMENT: usize = 400;
/// A ceiling on the samples in one plotted series.
pub const MAX_SAMPLES_PER_SERIES: usize = 2000;

/// A command's own velocity, acceleration and jerk request, in degrees and seconds.
///
/// One triple for the command rather than one per joint: this is the speed the user asked
/// the move to happen at. The per-joint physical ceilings are in the document and cap
/// these values; see [`MotionLimits`](robot_model::MotionLimits).
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommandLimits {
    pub velocity_deg_s: f64,
    pub acceleration_deg_s2: f64,
    pub jerk_deg_s3: f64,
}

impl Default for CommandLimits {
    fn default() -> Self {
        Self {
            velocity_deg_s: 90.0,
            acceleration_deg_s2: 180.0,
            jerk_deg_s3: 360.0,
        }
    }
}

impl CommandLimits {
    /// Whether every component is a finite positive number.
    pub fn is_valid(self) -> bool {
        [
            self.velocity_deg_s,
            self.acceleration_deg_s2,
            self.jerk_deg_s3,
        ]
        .iter()
        .all(|value| value.is_finite() && *value > 0.0)
    }

    /// The tighter of the command's request and each joint's physical ceiling.
    pub fn effective_per_joint(self, physical: &MotionLimits) -> [JointMotionLimits; JOINT_COUNT] {
        physical.joints.map(|joint| {
            JointMotionLimits::new(
                self.velocity_deg_s.min(joint.velocity_deg_s),
                self.acceleration_deg_s2.min(joint.acceleration_deg_s2),
                self.jerk_deg_s3.min(joint.jerk_deg_s3),
            )
        })
    }

    /// Whether any joint's physical ceiling is below what this command asks for.
    ///
    /// When this is false the command is below every ceiling and the plan is exactly what
    /// the user asked for; the UI has nothing to report.
    pub fn exceeds_physical(self, physical: &MotionLimits) -> bool {
        physical.joints.iter().any(|joint| {
            self.velocity_deg_s > joint.velocity_deg_s
                || self.acceleration_deg_s2 > joint.acceleration_deg_s2
                || self.jerk_deg_s3 > joint.jerk_deg_s3
        })
    }

    /// The six `robot-motion` limit bundles the planner takes.
    pub fn joint_limits(
        self,
        physical: &MotionLimits,
    ) -> Result<[Limits<f64>; JOINT_COUNT], String> {
        let one = Limits::new(1.0, 1.0, 1.0).map_err(|error| error.to_string())?;
        let mut limits = [one; JOINT_COUNT];
        for (slot, joint) in limits.iter_mut().zip(self.effective_per_joint(physical)) {
            *slot = Limits::new(
                joint.velocity_deg_s,
                joint.acceleration_deg_s2,
                joint.jerk_deg_s3,
            )
            .map_err(|error| format!("effective joint limits are invalid: {error}"))?;
        }
        Ok(limits)
    }
}

/// One joint-space move.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MoveJCommand {
    /// Runtime joint angles in degrees, one per joint.
    pub start_deg: [f64; JOINT_COUNT],
    /// Runtime joint angles in degrees, one per joint.
    pub stop_deg: [f64; JOINT_COUNT],
    pub limits: CommandLimits,
}

/// A queued motion command.
///
/// One variant today. The tag is explicit (`"movej"`) rather than derived: `rename_all`
/// would spell `MoveJ` as `move_j`, and the JSON is a compatibility surface once a user
/// copies it out.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum MotionCommand {
    #[serde(rename = "movej")]
    MoveJ(MoveJCommand),
}

impl MotionCommand {
    pub fn movej(
        start_deg: [f64; JOINT_COUNT],
        stop_deg: [f64; JOINT_COUNT],
        limits: CommandLimits,
    ) -> Self {
        Self::MoveJ(MoveJCommand {
            start_deg,
            stop_deg,
            limits,
        })
    }

    pub fn start_deg(&self) -> [f64; JOINT_COUNT] {
        match self {
            Self::MoveJ(command) => command.start_deg,
        }
    }

    pub fn stop_deg(&self) -> [f64; JOINT_COUNT] {
        match self {
            Self::MoveJ(command) => command.stop_deg,
        }
    }

    pub fn limits(&self) -> CommandLimits {
        match self {
            Self::MoveJ(command) => command.limits,
        }
    }

    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::MoveJ(_) => "MoveJ",
        }
    }

    /// Check the command's own data: every angle finite and every limit positive finite.
    ///
    /// A physical-limit cap cannot fail here; it only narrows a valid request.
    pub fn validate(&self) -> Result<(), String> {
        match self {
            Self::MoveJ(command) => {
                for (joint, value) in command.start_deg.iter().enumerate() {
                    if !value.is_finite() {
                        return Err(format!("start angle J{} is not finite", joint + 1));
                    }
                }
                for (joint, value) in command.stop_deg.iter().enumerate() {
                    if !value.is_finite() {
                        return Err(format!("stop angle J{} is not finite", joint + 1));
                    }
                }
                if !command.limits.is_valid() {
                    return Err(String::from(
                        "velocity, acceleration and jerk limits must be finite positive numbers",
                    ));
                }
                Ok(())
            }
        }
    }

    /// Plan the command against the robot's physical limits.
    pub fn plan(&self, physical: &MotionLimits) -> Result<JointProfile<JOINT_COUNT, f64>, String> {
        self.validate()?;
        plan_movej_scalar_optimal(
            self.start_deg(),
            self.stop_deg(),
            self.limits().joint_limits(physical)?,
        )
        .map_err(|error| error.to_string())
    }
}

/// One command as pretty JSON, ready to copy.
pub fn command_to_json(command: &MotionCommand) -> Result<String, String> {
    command.validate()?;
    serde_json::to_string_pretty(command).map_err(|error| error.to_string())
}

/// Parse one command and validate it.
pub fn command_from_json(text: &str) -> Result<MotionCommand, String> {
    let command: MotionCommand = serde_json::from_str(text).map_err(|error| error.to_string())?;
    command.validate()?;
    Ok(command)
}

/// The queue file's envelope.
#[derive(Serialize, Deserialize)]
struct QueueDocument {
    schema: String,
    version: u32,
    commands: Vec<MotionCommand>,
}

/// The whole queue as pretty JSON, ready to copy.
pub fn queue_to_json(commands: &[MotionCommand]) -> Result<String, String> {
    for (index, command) in commands.iter().enumerate() {
        command
            .validate()
            .map_err(|error| format!("command {}: {error}", index + 1))?;
    }
    let document = QueueDocument {
        schema: String::from(QUEUE_SCHEMA),
        version: QUEUE_VERSION,
        commands: commands.to_vec(),
    };
    serde_json::to_string_pretty(&document).map_err(|error| error.to_string())
}

/// Parse a queue.
///
/// The envelope and a bare array are both accepted; the bare array is what a user gets by
/// copying the command list out of some other tool. Parsing and validation happen on a
/// local vector, so a caller can replace its queue only on `Ok`.
pub fn queue_from_json(text: &str) -> Result<Vec<MotionCommand>, String> {
    let value: serde_json::Value = serde_json::from_str(text).map_err(|error| error.to_string())?;
    let commands: Vec<MotionCommand> = if value.is_array() {
        serde_json::from_value(value).map_err(|error| error.to_string())?
    } else {
        let document: QueueDocument =
            serde_json::from_value(value).map_err(|error| error.to_string())?;
        if document.schema != QUEUE_SCHEMA {
            return Err(format!("unsupported queue schema {:?}", document.schema));
        }
        if document.version != QUEUE_VERSION {
            return Err(format!("unsupported queue version {}", document.version));
        }
        document.commands
    };
    for (index, command) in commands.iter().enumerate() {
        command
            .validate()
            .map_err(|error| format!("command {}: {error}", index + 1))?;
    }
    Ok(commands)
}

/// The Motion tab's draft command.
#[derive(Clone, Debug, PartialEq)]
pub struct MotionEditor {
    pub start_deg: [f64; JOINT_COUNT],
    pub stop_deg: [f64; JOINT_COUNT],
    pub limits: CommandLimits,
}

impl Default for MotionEditor {
    fn default() -> Self {
        Self {
            start_deg: [0.0; JOINT_COUNT],
            stop_deg: [0.0; JOINT_COUNT],
            limits: CommandLimits::default(),
        }
    }
}

impl MotionEditor {
    pub fn command(&self) -> MotionCommand {
        MotionCommand::movej(self.start_deg, self.stop_deg, self.limits)
    }
}

/// Where a planned segment came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SegmentKind {
    /// Inserted to reach a command's start from wherever the arm is.
    Transition,
    /// The command at this queue index.
    Command(usize),
}

/// One row of the executed plan.
#[derive(Clone, Debug, PartialEq)]
pub struct PlanSegment {
    pub label: String,
    pub kind: SegmentKind,
    pub start_time: f64,
    pub duration: f64,
}

impl PlanSegment {
    pub fn end_time(&self) -> f64 {
        self.start_time + self.duration
    }
}

/// The precomputed plot series. `[t, value]` pairs, one series per line.
#[derive(Clone, Debug, PartialEq, Default)]
struct GraphData {
    joints: [Vec<[f64; 2]>; JOINT_COUNT],
    xyz: [Vec<[f64; 2]>; 3],
    rpy: [Vec<[f64; 2]>; 3],
    cartesian_error: Option<String>,
}

/// Every command in the queue, plus the transitions that make it runnable from `origin`.
#[derive(Clone, Debug, PartialEq)]
pub struct PlaybackPlan {
    origin_deg: [f64; JOINT_COUNT],
    segments: Vec<PlanSegment>,
    profiles: Vec<JointProfile<JOINT_COUNT, f64>>,
    total_time: f64,
    transitions: usize,
    graphs: GraphData,
}

impl PlaybackPlan {
    /// Build the executable plan from `origin_deg`.
    ///
    /// This is the only place transitions are created. A command's own limits shape its
    /// transition as well, so a slow command is reached slowly.
    pub fn build(
        commands: &[MotionCommand],
        origin_deg: [f64; JOINT_COUNT],
        parameters: &DHParameters,
        physical: &MotionLimits,
    ) -> Result<Self, String> {
        if commands.is_empty() {
            return Err(String::from("the queue is empty"));
        }

        let mut cursor = origin_deg;
        let mut segments = Vec::new();
        let mut profiles = Vec::new();
        let mut time = 0.0;
        let mut transitions = 0;

        for (index, command) in commands.iter().enumerate() {
            let start = command.start_deg();
            if max_difference(start, cursor) > CHAIN_EPSILON_DEG {
                let transition = MotionCommand::movej(cursor, start, command.limits())
                    .plan(physical)
                    .map_err(|error| format!("transition to move {}: {error}", index + 1))?;
                let duration = transition.total_time();
                if duration > 0.0 {
                    segments.push(PlanSegment {
                        label: format!("Transition to move {}", index + 1),
                        kind: SegmentKind::Transition,
                        start_time: time,
                        duration,
                    });
                    profiles.push(transition);
                    time += duration;
                    transitions += 1;
                }
            }

            let profile = command
                .plan(physical)
                .map_err(|error| format!("move {}: {error}", index + 1))?;
            let duration = profile.total_time();
            if duration > 0.0 {
                segments.push(PlanSegment {
                    label: format!("Move {} ({})", index + 1, command.kind_name()),
                    kind: SegmentKind::Command(index),
                    start_time: time,
                    duration,
                });
                profiles.push(profile);
                time += duration;
            }
            cursor = command.stop_deg();
        }

        let graphs = sample_graphs(&segments, &profiles, parameters);
        Ok(Self {
            origin_deg,
            segments,
            profiles,
            total_time: time,
            transitions,
            graphs,
        })
    }

    pub fn total_time(&self) -> f64 {
        self.total_time
    }

    pub fn transitions(&self) -> usize {
        self.transitions
    }

    pub fn segments(&self) -> &[PlanSegment] {
        &self.segments
    }

    pub fn joint_series(&self) -> &[Vec<[f64; 2]>; JOINT_COUNT] {
        &self.graphs.joints
    }

    pub fn xyz_series(&self) -> &[Vec<[f64; 2]>; 3] {
        &self.graphs.xyz
    }

    pub fn rpy_series(&self) -> &[Vec<[f64; 2]>; 3] {
        &self.graphs.rpy
    }

    pub fn cartesian_error(&self) -> Option<&str> {
        self.graphs.cartesian_error.as_deref()
    }

    /// The segment covering `t`, following the later-segment rule at a boundary.
    pub fn segment_at(&self, t: f64) -> Option<&PlanSegment> {
        self.segment_index(t).map(|index| &self.segments[index])
    }

    /// The joint angles at `t`, in degrees. Outside `[0, total]` the endpoints hold.
    pub fn eval_deg(&self, t: f64) -> [f64; JOINT_COUNT] {
        let Some(index) = self.segment_index(t) else {
            return self.origin_deg;
        };
        let segment = &self.segments[index];
        let local =
            (t.clamp(0.0, self.total_time) - segment.start_time).clamp(0.0, segment.duration);
        let states = self.profiles[index].eval(local);
        core::array::from_fn(|joint| states[joint].q)
    }

    fn segment_index(&self, t: f64) -> Option<usize> {
        if self.segments.is_empty() {
            return None;
        }
        let t = t.clamp(0.0, self.total_time);
        let index = self
            .segments
            .partition_point(|segment| segment.end_time() <= t);
        Some(index.min(self.segments.len() - 1))
    }
}

fn max_difference(left: [f64; JOINT_COUNT], right: [f64; JOINT_COUNT]) -> f64 {
    left.iter()
        .zip(right)
        .map(|(left, right)| (left - right).abs())
        .fold(0.0, f64::max)
}

/// Keep a displayed angle within half a turn of the previous one.
///
/// `rotation_to_rpy_degrees` reports roll and yaw inside `(-180°, 180°]`, so a continuous
/// rotation crosses the branch cut as a 360° cliff. The plotted series is a display aid;
/// the adjustment is not fed back into any state.
fn unwrap_degrees(value: f64, previous: Option<f64>) -> f64 {
    let Some(previous) = previous else {
        return value;
    };
    value + 360.0 * ((previous - value) / 360.0).round()
}

fn sample_graphs(
    segments: &[PlanSegment],
    profiles: &[JointProfile<JOINT_COUNT, f64>],
    parameters: &DHParameters,
) -> GraphData {
    let mut graphs = GraphData::default();
    if profiles.is_empty() {
        return graphs;
    }

    // Every segment gets a share of the budget; short moves still get enough points to be
    // legible, and a long queue lowers the per-segment rate rather than growing without
    // bound.
    let cap = (MAX_SAMPLES_PER_SERIES / profiles.len()).clamp(2, MAX_SAMPLES_PER_SEGMENT);
    let mut previous_roll = None;
    let mut previous_yaw = None;

    for (index, (segment, profile)) in segments.iter().zip(profiles).enumerate() {
        let count = ((segment.duration * GRAPH_SAMPLE_HZ).ceil() as usize).clamp(2, cap);
        for step in 0..=count {
            // The first segment supplies t = 0; a later segment's t = 0 sample would
            // duplicate its predecessor's last point.
            if index > 0 && step == 0 {
                continue;
            }
            let local = segment.duration * (step as f64) / (count as f64);
            let t = segment.start_time + local;
            let states = profile.eval(local);

            for (series, state) in graphs.joints.iter_mut().zip(states) {
                series.push([t, state.q]);
            }

            if graphs.cartesian_error.is_some() {
                continue;
            }
            let angles: [f64; JOINT_COUNT] = core::array::from_fn(|joint| states[joint].q);
            let tool = match parameters.carrier_pose(&angles) {
                Ok(poses) => poses[FRAME_COUNT - 1],
                Err(error) => {
                    graphs.cartesian_error = Some(error.to_string());
                    graphs.xyz = core::array::from_fn(|_| Vec::new());
                    graphs.rpy = core::array::from_fn(|_| Vec::new());
                    continue;
                }
            };

            let [roll, pitch, yaw] = session::rotation_to_rpy_degrees(&tool);
            let roll = unwrap_degrees(roll, previous_roll);
            let yaw = unwrap_degrees(yaw, previous_yaw);
            previous_roll = Some(roll);
            previous_yaw = Some(yaw);

            let position = [tool.p.x(), tool.p.y(), tool.p.z()];
            for (series, value) in graphs.xyz.iter_mut().zip(position) {
                series.push([t, value]);
            }
            for (series, value) in graphs.rpy.iter_mut().zip([roll, pitch, yaw]) {
                series.push([t, value]);
            }
        }
    }

    graphs
}

/// Where the plan on display came from: a preview of the queue or a run the user started.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanSource {
    Preview,
    Run,
}

/// The Motion tab's state: the queue, the draft, the plan, and the playback clock.
#[derive(Resource)]
pub struct MotionRuntime {
    pub commands: Vec<MotionCommand>,
    pub editor: MotionEditor,
    pub plan: Option<PlaybackPlan>,
    pub plan_error: Option<String>,
    pub plan_source: Option<PlanSource>,
    pub plan_origin_deg: [f64; JOINT_COUNT],
    pub plan_parameters: DHParameters,
    pub plan_physical: MotionLimits,
    pub preview_dirty: bool,
    /// A run is in flight: playing or paused. Queue edits are disabled.
    pub active: bool,
    pub playing: bool,
    pub time: f64,
    pub status: String,
    pub status_is_error: bool,
    pub command_import: String,
    pub queue_import: String,
    pub reset_plots: bool,
}

impl Default for MotionRuntime {
    fn default() -> Self {
        Self {
            commands: Vec::new(),
            editor: MotionEditor::default(),
            plan: None,
            plan_error: None,
            plan_source: None,
            plan_origin_deg: [0.0; JOINT_COUNT],
            plan_parameters: DHParameters::shipped(),
            plan_physical: MotionLimits::default(),
            preview_dirty: true,
            active: false,
            playing: false,
            time: 0.0,
            status: String::from("Set a start and stop, then add the move to the queue."),
            status_is_error: false,
            command_import: String::new(),
            queue_import: String::new(),
            reset_plots: false,
        }
    }
}

impl MotionRuntime {
    /// Keep a preview of the queue on display while nothing is running.
    ///
    /// A run's plan is never replaced here: the user is looking at what actually happened,
    /// and `Play all` is what rebuilds from the current pose. A failed build is recorded
    /// once; the inputs have to change before another attempt is made.
    pub fn ensure_preview(
        &mut self,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) {
        if self.active || matches!(self.plan_source, Some(PlanSource::Run)) {
            return;
        }
        if self.commands.is_empty() {
            if self.plan.is_some() || self.plan_error.is_some() || self.plan_source.is_some() {
                self.plan = None;
                self.plan_error = None;
                self.plan_source = None;
                self.time = 0.0;
                self.reset_plots = true;
            }
            return;
        }

        let inputs_changed = self.plan_origin_deg != current_deg
            || self.plan_parameters != *parameters
            || self.plan_physical != *physical;
        if !self.preview_dirty && !inputs_changed && self.plan_source == Some(PlanSource::Preview) {
            return;
        }
        self.rebuild_preview(parameters, physical, current_deg);
    }

    fn rebuild_preview(
        &mut self,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) {
        self.preview_dirty = false;
        self.plan_origin_deg = current_deg;
        self.plan_parameters = *parameters;
        self.plan_physical = *physical;
        self.plan_source = Some(PlanSource::Preview);
        self.time = 0.0;
        self.reset_plots = true;
        match PlaybackPlan::build(&self.commands, current_deg, parameters, physical) {
            Ok(plan) => {
                self.plan = Some(plan);
                self.plan_error = None;
            }
            Err(error) => {
                self.plan = None;
                self.plan_error = Some(error);
            }
        }
    }

    /// Plan and append the editor's draft.
    pub fn add_command(
        &mut self,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) -> Result<(), String> {
        let command = self.editor.command();
        let duration = command.plan(physical)?.total_time();
        self.commands.push(command);
        self.editor.start_deg = self.editor.stop_deg;
        self.preview_dirty = true;
        self.plan_source = Some(PlanSource::Preview);
        self.ensure_preview(parameters, physical, current_deg);
        self.status = format!(
            "Added move {} ({}).",
            self.commands.len(),
            seconds(duration)
        );
        self.status_is_error = false;
        Ok(())
    }

    pub fn remove_command(
        &mut self,
        index: usize,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) {
        if index >= self.commands.len() {
            return;
        }
        self.commands.remove(index);
        self.sync_editor_start(current_deg);
        self.preview_dirty = true;
        self.plan_source = Some(PlanSource::Preview);
        self.ensure_preview(parameters, physical, current_deg);
        self.status = format!("Removed move {}.", index + 1);
        self.status_is_error = false;
    }

    pub fn clear_queue(
        &mut self,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) {
        self.commands.clear();
        self.editor.start_deg = current_deg;
        self.preview_dirty = true;
        self.plan_source = Some(PlanSource::Preview);
        self.ensure_preview(parameters, physical, current_deg);
        self.status = String::from("Queue cleared.");
        self.status_is_error = false;
    }

    /// Replace the queue from JSON, atomically.
    ///
    /// The candidate commands are planned before the queue is touched, so a queue that
    /// parses but cannot execute leaves the old one in place.
    pub fn import_queue(
        &mut self,
        text: &str,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) -> Result<(), String> {
        let commands = queue_from_json(text)?;
        if commands.is_empty() {
            self.commands.clear();
            self.plan = None;
            self.plan_error = None;
            self.plan_source = None;
            self.preview_dirty = true;
            self.time = 0.0;
            self.editor.start_deg = current_deg;
            self.plan_origin_deg = current_deg;
            self.reset_plots = true;
            return Ok(());
        }

        let plan = PlaybackPlan::build(&commands, current_deg, parameters, physical)?;
        self.commands = commands;
        self.plan = Some(plan);
        self.plan_error = None;
        self.plan_source = Some(PlanSource::Preview);
        self.plan_origin_deg = current_deg;
        self.plan_parameters = *parameters;
        self.plan_physical = *physical;
        self.preview_dirty = false;
        self.time = 0.0;
        self.reset_plots = true;
        self.sync_editor_start(current_deg);
        Ok(())
    }

    pub fn fill_start_from_current(&mut self, current_deg: [f64; JOINT_COUNT]) {
        self.editor.start_deg = current_deg;
        self.status = String::from("Start set to the current pose.");
        self.status_is_error = false;
    }

    pub fn fill_start_from_last(&mut self) -> Result<(), String> {
        let Some(last) = self.commands.last() else {
            return Err(String::from("the queue is empty"));
        };
        self.editor.start_deg = last.stop_deg();
        self.status = String::from("Start set to the last queued stop.");
        self.status_is_error = false;
        Ok(())
    }

    fn sync_editor_start(&mut self, current_deg: [f64; JOINT_COUNT]) {
        self.editor.start_deg = self
            .commands
            .last()
            .map_or(current_deg, |command| command.stop_deg());
    }

    /// Build from the current pose and start the run.
    pub fn play_all(
        &mut self,
        parameters: &DHParameters,
        physical: &MotionLimits,
        current_deg: [f64; JOINT_COUNT],
    ) -> Result<(), String> {
        if self.commands.is_empty() {
            return Err(String::from("the queue is empty"));
        }
        let plan = PlaybackPlan::build(&self.commands, current_deg, parameters, physical)?;
        if plan.total_time() <= 0.0 {
            return Err(String::from("the queue has no motion to play"));
        }
        let transitions = plan.transitions();
        self.plan = Some(plan);
        self.plan_error = None;
        self.plan_source = Some(PlanSource::Run);
        self.plan_origin_deg = current_deg;
        self.plan_parameters = *parameters;
        self.plan_physical = *physical;
        self.preview_dirty = false;
        self.time = 0.0;
        self.active = true;
        self.playing = true;
        self.reset_plots = true;
        self.status = format!(
            "Playing {} command(s), {} transition(s).",
            self.commands.len(),
            transitions
        );
        self.status_is_error = false;
        Ok(())
    }

    pub fn pause(&mut self) {
        if self.active {
            self.playing = false;
            self.status = String::from("Paused.");
            self.status_is_error = false;
        }
    }

    pub fn resume(&mut self) {
        if self.active {
            self.playing = true;
            self.status = String::from("Playing.");
            self.status_is_error = false;
        }
    }

    /// Halt the run. The pose and the run's plan stay on screen; `Play all` rebuilds from
    /// wherever the arm stopped.
    pub fn stop(&mut self) {
        if self.active {
            self.playing = false;
            self.active = false;
            self.status = String::from("Stopped.");
            self.status_is_error = false;
        }
    }

    /// Advance the clock and write the planned pose. Called from `Update`.
    pub fn advance(&mut self, dt_secs: f64, robot: &mut RobotState, session: &mut Session) {
        if !self.playing {
            return;
        }
        let Some(total) = self.plan.as_ref().map(PlaybackPlan::total_time) else {
            self.playing = false;
            self.active = false;
            return;
        };
        let dt = if dt_secs.is_finite() {
            dt_secs.clamp(0.0, MAX_FRAME_DELTA_SECS)
        } else {
            0.0
        };
        self.time = (self.time + dt).min(total);
        let angles = self
            .plan
            .as_ref()
            .map_or(robot.runtime_angles_deg, |plan| plan.eval_deg(self.time));
        robot.runtime_angles_deg = angles;
        // The Parameters tab's fields are the same angles in text; keeping them in step
        // means applying an edit after a run cannot snap the arm back to its old pose.
        session.sync_joint_angles(&angles);

        if self.time >= total {
            self.playing = false;
            self.active = false;
            self.status = format!("Finished in {}.", seconds(total));
            self.status_is_error = false;
        }
    }

    /// The label of the segment the cursor is in, for the plan readout.
    pub fn current_segment_label(&self) -> Option<&str> {
        self.plan
            .as_ref()
            .and_then(|plan| plan.segment_at(self.time))
            .map(|segment| segment.label.as_str())
    }
}

/// Bevy system: advance playback before the scene reads the joint angles.
pub fn advance_motion(
    time: Res<Time>,
    mut motion: ResMut<MotionRuntime>,
    mut robot: ResMut<RobotState>,
    mut session: ResMut<Session>,
) {
    motion.advance(time.delta_secs_f64(), &mut robot, &mut session);
}

fn seconds(value: f64) -> String {
    format!("{value:.2} s")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pyformat::format_g;

    fn limits() -> MotionLimits {
        MotionLimits::default()
    }

    fn shipped() -> DHParameters {
        DHParameters::shipped()
    }

    fn command(start: [f64; JOINT_COUNT], stop: [f64; JOINT_COUNT]) -> MotionCommand {
        MotionCommand::movej(start, stop, CommandLimits::default())
    }

    fn runtime_with(stop: [f64; JOINT_COUNT]) -> MotionRuntime {
        let mut runtime = MotionRuntime::default();
        runtime.editor.stop_deg = stop;
        runtime
            .add_command(&shipped(), &limits(), [0.0; JOINT_COUNT])
            .expect("the draft plans");
        runtime
    }

    #[test]
    fn movej_json_uses_the_movej_tag() {
        let text = r#"{
          "type": "movej",
          "start_deg": [0, 0, 0, 0, 0, 0],
          "stop_deg": [10, 20, 30, 40, 50, 60],
          "limits": {
            "velocity_deg_s": 90,
            "acceleration_deg_s2": 180,
            "jerk_deg_s3": 360
          }
        }"#;
        let command = command_from_json(text).expect("the documented shape parses");
        assert_eq!(command.start_deg(), [0.0; JOINT_COUNT]);
        assert_eq!(command.stop_deg(), [10.0, 20.0, 30.0, 40.0, 50.0, 60.0]);
        // `rename_all` alone would have spelled this `move_j`.
        assert!(command_from_json(&text.replace("\"movej\"", "\"move_j\"")).is_err());
    }

    #[test]
    fn command_json_round_trips() {
        let command = MotionCommand::movej(
            [-10.5, 0.25, 3.0, 4.0, 5.0, 6.0],
            [10.5, -20.25, 30.0, 40.0, 50.0, 60.0],
            CommandLimits {
                velocity_deg_s: 12.5,
                acceleration_deg_s2: 34.5,
                jerk_deg_s3: 56.5,
            },
        );
        let text = command_to_json(&command).expect("finite values serialize");
        assert_eq!(command_from_json(&text).expect("round trip"), command);
    }

    #[test]
    fn bad_command_json_is_rejected() {
        // Unknown type.
        assert!(
            command_from_json(
                r#"{"type": "movel", "start_deg": [], "stop_deg": [], "limits": {}}"#
            )
            .is_err()
        );
        // The wrong number of joints.
        let five = r#"{"type":"movej","start_deg":[0,0,0,0,0],"stop_deg":[0,0,0,0,0,0],"limits":{"velocity_deg_s":1,"acceleration_deg_s2":1,"jerk_deg_s3":1}}"#;
        assert!(command_from_json(five).is_err());
        // A non-positive limit is structurally valid JSON but not a command.
        let zero = r#"{"type":"movej","start_deg":[0,0,0,0,0,0],"stop_deg":[0,0,0,0,0,0],"limits":{"velocity_deg_s":0,"acceleration_deg_s2":1,"jerk_deg_s3":1}}"#;
        assert!(command_from_json(zero).is_err());
    }

    #[test]
    fn non_finite_values_are_rejected_before_serialization() {
        let mut command = command([0.0; JOINT_COUNT], [1.0; JOINT_COUNT]);
        let MotionCommand::MoveJ(movej) = &mut command;
        movej.stop_deg[2] = f64::NAN;
        assert!(command_to_json(&command).is_err());
        assert!(queue_to_json(std::slice::from_ref(&command)).is_err());
    }

    #[test]
    fn queue_json_round_trips_and_accepts_a_bare_array() {
        let commands = vec![
            command([0.0; JOINT_COUNT], [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            command(
                [10.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                [10.0, 20.0, 0.0, 0.0, 0.0, 0.0],
            ),
        ];
        let text = queue_to_json(&commands).expect("serialize");
        assert!(text.contains("\"schema\": \"robot-app.motion-queue\""));
        assert_eq!(queue_from_json(&text).expect("envelope"), commands);

        let bare = serde_json::to_string(&commands).expect("serialize the array");
        assert_eq!(queue_from_json(&bare).expect("bare array"), commands);
    }

    #[test]
    fn queue_json_rejects_a_wrong_schema_or_version() {
        let commands = vec![command([0.0; JOINT_COUNT], [1.0; JOINT_COUNT])];
        let text = queue_to_json(&commands).expect("serialize");
        assert!(queue_from_json(&text.replace(QUEUE_SCHEMA, "other")).is_err());
        assert!(queue_from_json(&text.replace("\"version\": 1", "\"version\": 2")).is_err());
    }

    #[test]
    fn effective_limits_are_the_tighter_of_command_and_joint() {
        let mut physical = limits();
        physical.joints[1] = JointMotionLimits::new(10.0, 20.0, 30.0);
        let command = CommandLimits {
            velocity_deg_s: 30.0,
            acceleration_deg_s2: 100.0,
            jerk_deg_s3: 200.0,
        };
        let effective = command.effective_per_joint(&physical);
        // Joint 2's physical limits are the tightest on every component.
        assert_eq!(effective[1], physical.joints[1]);
        // Joint 1's physical limits are looser than the command on every component.
        assert_eq!(effective[0], JointMotionLimits::new(30.0, 100.0, 200.0));
        assert!(command.exceeds_physical(&physical));

        let modest = CommandLimits {
            velocity_deg_s: 5.0,
            acceleration_deg_s2: 5.0,
            jerk_deg_s3: 5.0,
        };
        assert_eq!(
            modest.effective_per_joint(&physical)[1],
            JointMotionLimits::new(5.0, 5.0, 5.0)
        );
        assert!(!modest.exceeds_physical(&physical));
    }

    #[test]
    fn no_transition_when_the_first_command_starts_at_the_origin() {
        let origin = [0.0; JOINT_COUNT];
        let plan = PlaybackPlan::build(
            &[command(origin, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0])],
            origin,
            &shipped(),
            &limits(),
        )
        .expect("plans");
        assert_eq!(plan.transitions(), 0);
        assert_eq!(plan.segments().len(), 1);
        assert!(matches!(plan.segments()[0].kind, SegmentKind::Command(0)));
        assert_eq!(plan.eval_deg(0.0), origin);
        assert!((plan.eval_deg(plan.total_time())[0] - 10.0).abs() < 1e-9);
    }

    #[test]
    fn the_first_command_gets_a_transition_from_the_current_pose() {
        let origin = [0.0; JOINT_COUNT];
        let start = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let stop = [20.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let plan = PlaybackPlan::build(&[command(start, stop)], origin, &shipped(), &limits())
            .expect("plans");
        assert_eq!(plan.transitions(), 1);
        assert_eq!(plan.segments().len(), 2);
        assert!(matches!(plan.segments()[0].kind, SegmentKind::Transition));
        let boundary = plan.segments()[0].end_time();
        let at_boundary = plan.eval_deg(boundary);
        for (actual, wanted) in at_boundary.iter().zip(start) {
            assert!((actual - wanted).abs() < 1e-9, "{at_boundary:?}");
        }
        assert!(matches!(
            plan.segment_at(boundary).unwrap().kind,
            SegmentKind::Command(0)
        ));
    }

    #[test]
    fn gaps_between_commands_get_transitions() {
        let origin = [0.0; JOINT_COUNT];
        let first = command(origin, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        // Starts somewhere the first did not end.
        let second = command(
            [30.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [40.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        );
        let plan =
            PlaybackPlan::build(&[first, second], origin, &shipped(), &limits()).expect("plans");
        assert_eq!(plan.transitions(), 1);
        assert_eq!(plan.segments().len(), 3);
        assert!(matches!(plan.segments()[0].kind, SegmentKind::Command(0)));
        assert!(matches!(plan.segments()[1].kind, SegmentKind::Transition));
        assert!(matches!(plan.segments()[2].kind, SegmentKind::Command(1)));
    }

    #[test]
    fn auto_chained_commands_have_no_internal_transitions() {
        let origin = [0.0; JOINT_COUNT];
        let middle = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let plan = PlaybackPlan::build(
            &[
                command(origin, middle),
                command(middle, [20.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ],
            origin,
            &shipped(),
            &limits(),
        )
        .expect("plans");
        assert_eq!(plan.transitions(), 0);
        assert_eq!(plan.segments().len(), 2);
    }

    #[test]
    fn a_zero_motion_command_with_a_different_start_still_gets_a_transition() {
        let origin = [0.0; JOINT_COUNT];
        let start = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let plan = PlaybackPlan::build(&[command(start, start)], origin, &shipped(), &limits())
            .expect("plans");
        // The command itself has no duration, but reaching its start does.
        assert_eq!(plan.transitions(), 1);
        assert_eq!(plan.segments().len(), 1);
        assert!(matches!(plan.segments()[0].kind, SegmentKind::Transition));
        assert!((plan.eval_deg(plan.total_time())[0] - 10.0).abs() < 1e-9);
    }

    #[test]
    fn zero_motion_commands_are_skipped_without_stalls() {
        let origin = [0.0; JOINT_COUNT];
        let hold = command(origin, origin);
        let move_ = command(origin, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        let plan =
            PlaybackPlan::build(&[hold, move_], origin, &shipped(), &limits()).expect("plans");
        assert_eq!(plan.segments().len(), 1);
        assert!(plan.total_time() > 0.0);
        assert!((plan.eval_deg(plan.total_time())[0] - 10.0).abs() < 1e-9);
    }

    #[test]
    fn eval_is_clamped_and_finite() {
        let origin = [0.0; JOINT_COUNT];
        let plan = PlaybackPlan::build(
            &[command(origin, [10.0, -20.0, 30.0, -40.0, 50.0, -60.0])],
            origin,
            &shipped(),
            &limits(),
        )
        .expect("plans");
        for point in [-1.0, 0.0, plan.total_time() * 0.5, plan.total_time(), 1e9] {
            let angles = plan.eval_deg(point);
            assert!(angles.iter().all(|angle| angle.is_finite()));
        }
        assert_eq!(plan.eval_deg(-1.0), origin);
        let end = plan.eval_deg(1e9);
        for (actual, wanted) in end.iter().zip([10.0, -20.0, 30.0, -40.0, 50.0, -60.0]) {
            assert!((actual - wanted).abs() < 1e-9, "{end:?}");
        }
    }

    #[test]
    fn graph_series_cover_the_plan() {
        let origin = [0.0; JOINT_COUNT];
        let plan = PlaybackPlan::build(
            &[command(origin, [10.0, -20.0, 30.0, -40.0, 50.0, -60.0])],
            origin,
            &shipped(),
            &limits(),
        )
        .expect("plans");
        assert!(plan.cartesian_error().is_none());
        let joint_lengths: Vec<usize> = plan.joint_series().iter().map(Vec::len).collect();
        assert!(
            joint_lengths
                .iter()
                .all(|length| *length == joint_lengths[0])
        );
        assert!(joint_lengths[0] > 1);
        for series in plan.joint_series() {
            assert_eq!(series.first().unwrap()[0], 0.0);
            assert!((series.last().unwrap()[0] - plan.total_time()).abs() < 1e-12);
            assert!(series.iter().all(|point| point[1].is_finite()));
            assert!(series.windows(2).all(|pair| pair[0][0] <= pair[1][0]));
        }
        for series in plan.xyz_series() {
            assert_eq!(series.len(), joint_lengths[0]);
            assert!(series.iter().all(|point| point[1].is_finite()));
        }
        for series in plan.rpy_series() {
            assert_eq!(series.len(), joint_lengths[0]);
        }
    }

    #[test]
    fn bad_geometry_keeps_joint_graphs_and_reports_the_cartesian_error() {
        let mut parameters = shipped();
        // `carrier_pose` needs a positive first link; the structure check is not part of
        // it, so an unsupported alpha would still produce a pose.
        parameters.joints[1].a = 0.0;
        let origin = [0.0; JOINT_COUNT];
        let plan = PlaybackPlan::build(
            &[command(origin, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0])],
            origin,
            &parameters,
            &limits(),
        )
        .expect("the joint move does not need the geometry");
        assert!(plan.cartesian_error().is_some());
        assert!(!plan.joint_series()[0].is_empty());
        assert!(plan.xyz_series().iter().all(Vec::is_empty));
        assert!(plan.rpy_series().iter().all(Vec::is_empty));
    }

    #[test]
    fn rpy_series_are_unwrapped_across_the_branch_cut() {
        assert_eq!(unwrap_degrees(-179.0, Some(179.0)), 181.0);
        assert_eq!(unwrap_degrees(179.0, Some(-179.0)), -181.0);
        assert_eq!(unwrap_degrees(10.0, None), 10.0);
    }

    #[test]
    fn adding_chains_the_editor_start_to_the_new_stop() {
        let mut runtime = MotionRuntime::default();
        runtime.editor.stop_deg = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        runtime
            .add_command(&shipped(), &limits(), [0.0; JOINT_COUNT])
            .expect("plans");
        assert_eq!(runtime.commands.len(), 1);
        assert_eq!(runtime.editor.start_deg, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
    }

    #[test]
    fn removing_and_clearing_update_the_editor_start() {
        let origin = [0.0; JOINT_COUNT];
        let mut runtime = MotionRuntime::default();
        runtime.editor.stop_deg = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        runtime.add_command(&shipped(), &limits(), origin).unwrap();
        runtime.editor.stop_deg = [20.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        runtime.add_command(&shipped(), &limits(), origin).unwrap();
        runtime.remove_command(1, &shipped(), &limits(), origin);
        assert_eq!(runtime.editor.start_deg, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        runtime.clear_queue(&shipped(), &limits(), origin);
        assert_eq!(runtime.editor.start_deg, origin);
        assert!(runtime.plan.is_none());
    }

    #[test]
    fn queue_import_is_atomic_and_sets_the_start_from_the_last_stop() {
        let origin = [0.0; JOINT_COUNT];
        let mut runtime = runtime_with([10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        assert_eq!(runtime.commands.len(), 1);

        assert!(
            runtime
                .import_queue("not json", &shipped(), &limits(), origin)
                .is_err()
        );
        assert_eq!(
            runtime.commands.len(),
            1,
            "the failed import changed nothing"
        );

        let commands = vec![
            command(origin, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            command(
                [10.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                [20.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            ),
        ];
        let text = queue_to_json(&commands).expect("serialize");
        runtime
            .import_queue(&text, &shipped(), &limits(), origin)
            .expect("valid queue");
        assert_eq!(runtime.commands, commands);
        assert_eq!(runtime.editor.start_deg, [20.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
    }

    #[test]
    fn playback_advances_pauses_resumes_and_completes() {
        let origin = [0.0; JOINT_COUNT];
        let stop = [10.0, -20.0, 30.0, -40.0, 50.0, -60.0];
        let mut runtime = runtime_with(stop);
        let total = runtime.plan.as_ref().expect("preview").total_time();
        assert!(total > 0.0);

        runtime
            .play_all(&shipped(), &limits(), origin)
            .expect("starts");
        let mut robot = RobotState::default();
        let mut session = Session::new(std::path::PathBuf::from("robot_parameters.json"));

        runtime.advance(0.5, &mut robot, &mut session);
        assert!(runtime.playing);
        assert!(robot.runtime_angles_deg[0] > 0.0);
        let paused_at = runtime.time;
        assert!(paused_at > 0.0);

        runtime.pause();
        runtime.advance(0.5, &mut robot, &mut session);
        assert_eq!(runtime.time, paused_at, "paused time does not move");
        runtime.resume();

        // A delta far beyond the cap is clamped, so one stalled frame cannot jump to the
        // end; the run still has to spend its planned time.
        runtime.advance(1e9, &mut robot, &mut session);
        assert!(runtime.time <= paused_at + MAX_FRAME_DELTA_SECS + 1e-12);
        for _ in 0..10_000 {
            if !runtime.playing {
                break;
            }
            runtime.advance(total, &mut robot, &mut session);
        }
        assert!(runtime.time <= total + 1e-12);
        assert!(!runtime.playing);
        assert!(!runtime.active);
        for (actual, wanted) in robot.runtime_angles_deg.iter().zip(stop) {
            assert!(
                (actual - wanted).abs() < 1e-9,
                "{:?}",
                robot.runtime_angles_deg
            );
        }
        for (field, wanted) in session.joint_angles.iter().zip(stop) {
            assert_eq!(*field, format_g(wanted));
        }
    }

    #[test]
    fn stop_keeps_the_pose_and_the_run_plan() {
        let origin = [0.0; JOINT_COUNT];
        let mut runtime = runtime_with([10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        runtime.play_all(&shipped(), &limits(), origin).unwrap();
        let mut robot = RobotState::default();
        let mut session = Session::new(std::path::PathBuf::from("robot_parameters.json"));
        runtime.advance(0.05, &mut robot, &mut session);
        let held = robot.runtime_angles_deg;
        runtime.stop();
        assert!(!runtime.active);
        assert_eq!(runtime.plan_source, Some(PlanSource::Run));
        assert!(runtime.plan.is_some());
        runtime.advance(0.5, &mut robot, &mut session);
        assert_eq!(robot.runtime_angles_deg, held);
    }

    #[test]
    fn a_completed_run_is_not_replaced_by_a_preview() {
        let origin = [0.0; JOINT_COUNT];
        let mut runtime = runtime_with([10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        runtime.play_all(&shipped(), &limits(), origin).unwrap();
        let mut robot = RobotState::default();
        let mut session = Session::new(std::path::PathBuf::from("robot_parameters.json"));
        for _ in 0..10_000 {
            if !runtime.playing {
                break;
            }
            runtime.advance(10.0, &mut robot, &mut session);
        }
        assert!(!runtime.active);
        let origin_of_run = runtime.plan_origin_deg;
        runtime.ensure_preview(&shipped(), &limits(), [30.0; JOINT_COUNT]);
        assert_eq!(runtime.plan_origin_deg, origin_of_run);
        assert_eq!(runtime.plan_source, Some(PlanSource::Run));
    }

    #[test]
    fn a_pose_change_invalidates_a_preview() {
        let mut runtime = runtime_with([10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        runtime.ensure_preview(&shipped(), &limits(), [0.0; JOINT_COUNT]);
        assert_eq!(runtime.plan_origin_deg, [0.0; JOINT_COUNT]);
        runtime.ensure_preview(&shipped(), &limits(), [5.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
        assert_eq!(runtime.plan_origin_deg, [5.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
    }

    #[test]
    fn fill_start_helpers_use_current_and_last() {
        let origin = [0.0; JOINT_COUNT];
        let mut runtime = MotionRuntime::default();
        assert!(runtime.fill_start_from_last().is_err());
        runtime.fill_start_from_current([1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        assert_eq!(runtime.editor.start_deg, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        runtime.editor.stop_deg = [10.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        runtime.add_command(&shipped(), &limits(), origin).unwrap();
        runtime.editor.start_deg = origin;
        runtime.fill_start_from_last().expect("one command");
        assert_eq!(runtime.editor.start_deg, [10.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
    }
}
