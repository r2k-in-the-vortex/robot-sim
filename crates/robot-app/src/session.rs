//! The editable configuration and every operation the buttons behind it perform.
//!
//! # Why the fields are text
//!
//! `simulator.py` keeps two things apart and so does this: the **stored** state
//! ([`Document`] plus the runtime angles) is what the view draws, and the **fields** are
//! what the user has typed into, which may be ahead of or behind it. Every handler re-reads
//! the fields rather than trusting the stored state, because the reference does —
//! `_read_entry_values` (`simulator.py:601`) parses the widgets afresh on each jog, so an
//! edit that has not been applied still steers the next jog.
//!
//! Two consequences of that are worth stating outright because they look like bugs and are
//! not:
//!
//! * **A joint jog applies the DH fields too.** `_jog_joint` builds its table from
//!   `_read_entry_values()` (`simulator.py:328`), so an unapplied DH edit takes effect the
//!   moment a joint is jogged. A DH field that does not parse refuses the jog entirely and
//!   says so in the status line.
//! * **A joint jog ignores unapplied joint-field edits.** It moves from the *stored*
//!   angles and then rewrites all six fields from the result (`:329-337`), so a typed-in
//!   angle that was never applied is discarded.
//!
//! # The display-precision split
//!
//! Runtime angles are held at full precision and rendered back into the fields at six
//! significant digits, so a field is ambiguous: `0.333333` might mean the stored
//! `0.3333333333333333` or a typed-in `0.333333`. [`Session::read_joint_angles`] resolves it
//! the way the reference does (`:612-628`) — a field whose text still equals its own
//! rendering yields the *stored* value at full precision, and only a field that differs from
//! its rendering is taken at face value. Without that, applying an edit to one joint would
//! quietly round the other five down to six digits. `test_kinematics.py:361` covers it.
//!
//! # What is not here
//!
//! Runtime joint angles never reach the saved file: they have no JSON key, and
//! [`Session::save_json`] writes a [`Document`], which has no field for them. The file is
//! the schema's, not this module's.

use std::path::{Path, PathBuf};

use bevy::prelude::Resource;
use robot_kinematics::{Geometry, GeometryError, JOINT_COUNT, Pose, fk, units};
use robot_model::table::TableError;
use robot_model::{DHParameters, DhRow, Document, MESH_COUNT, MeshSettings};

use crate::jog::{self, Axis};
use crate::pyformat::{format_g, format_plus_g, format_precision_g};
use crate::solve;

/// `_read_step`'s message for the joint-step field (`simulator.py:331`).
pub const JOINT_STEP_ERROR: &str = "Joint step must be a finite positive angle.";
/// `_read_step`'s message for the base- and tool-frame translation fields (`:402`, `:411`).
pub const JOG_STEP_ERROR: &str = "Jog step must be a finite positive length.";
/// `_read_step`'s message for the two rotation-step call sites (`:420`, `:429`).
pub const ROTATION_STEP_ERROR: &str = "Rotation step must be a finite positive angle.";
/// `_pose_jog`'s report when the solve comes back empty (`simulator.py:385-387`). The move
/// is all-or-nothing: the robot is left exactly where it was.
pub const NO_SOLUTION: &str = "No exact-pose IK solution; robot was not moved.";
/// `_copy_t6_position`'s status line (`simulator.py:316`).
pub const COPIED: &str = "Copied T6 pose and joint angles";

/// A failure the UI puts in a messagebox, keeping the reference's own title.
///
/// The reference's titles are not decoration: the same sentence can arrive under two
/// different titles depending on which `try` raised it, and "Invalid parameters" is the
/// fields' complaint while "Could not load parameters" is the file's.
#[derive(Clone, PartialEq, Debug)]
pub struct Failure {
    /// The messagebox title, `messagebox.showerror(title, message)`.
    pub title: &'static str,
    /// The message, which is the reference's sentence.
    pub message: String,
}

impl Failure {
    fn new(title: &'static str, message: impl Into<String>) -> Self {
        Self {
            title,
            message: message.into(),
        }
    }
}

/// `_apply_from_entries`'s title (`simulator.py:673`).
pub const INVALID_PARAMETERS_TITLE: &str = "Invalid parameters";
/// `_save_json`'s write failure, which it reports separately from a read failure
/// (`simulator.py:702`).
pub const COULD_NOT_SAVE_TITLE: &str = "Could not save parameters";
/// `_load_json`'s title (`simulator.py:812`).
pub const COULD_NOT_LOAD_TITLE: &str = "Could not load parameters";
/// The startup load's title, `__init__` (`simulator.py:220`).
pub const PARAMETER_FILE_ERROR_TITLE: &str = "Parameter file error";

/// The precision `Copy XYZ` renders at: `f"{value:.15g}"` (`simulator.py:303-311`).
///
/// Fifteen significant digits is the most that survives a round trip through `f64`'s
/// decimal printing, which is the point of the button — the readout on screen is three
/// decimals, and this is for pasting into something that wants the real number.
const CLIPBOARD_PRECISION: usize = 15;

/// One mesh row's editable text.
#[derive(Clone, PartialEq, Debug)]
pub struct MeshForm {
    pub path: String,
    pub offset: [String; 3],
    pub rotation: [String; 3],
    pub opacity: String,
}

impl MeshForm {
    fn from_settings(settings: &MeshSettings) -> Self {
        Self {
            path: settings.path.clone(),
            offset: settings.offset.map(format_g),
            rotation: settings.rotation_deg.map(format_g),
            opacity: format_g(settings.opacity),
        }
    }
}

/// The Parameters tab's fields and the 3D view's jog controls, as text.
///
/// A Bevy [`Resource`] because the shell reads and writes it from separate systems — the
/// side panel and the tab pages each render with a `ResMut<Session>` of their own.
#[derive(Resource, Clone, PartialEq, Debug)]
pub struct Session {
    /// `theta_offset_deg`, `d`, `a`, `alpha_deg` per row — the column order of
    /// `self.parameter_entries` (`simulator.py:461-490`).
    pub dh: [[String; 4]; JOINT_COUNT],
    /// The six runtime-angle fields, which are *not* the stored angles.
    pub joint_angles: [String; JOINT_COUNT],
    pub meshes: [MeshForm; MESH_COUNT],
    pub jog_step: String,
    pub rotation_step: String,
    pub joint_step: String,
    /// The jog status line under the 3D view (`self.jog_status_label`).
    pub status: String,
    /// The pending messagebox, if any. The reference has no such state — it raises a modal
    /// inside the handler — but a modal is not something a Bevy system can do mid-frame, so
    /// the failure is stored and [`crate::ui`] draws it.
    pub notice: Option<Failure>,
    /// The file Save and Load default to, and the one the startup load reads.
    pub config_path: PathBuf,
}

impl Session {
    /// A session whose fields hold the shipped document and zero runtime angles.
    pub fn new(config_path: PathBuf) -> Self {
        let mut session = Self {
            dh: core::array::from_fn(|_| core::array::from_fn(|_| String::new())),
            joint_angles: core::array::from_fn(|_| format_g(0.0)),
            meshes: core::array::from_fn(|_| MeshForm::from_settings(&MeshSettings::default())),
            jog_step: String::from("1"),
            rotation_step: String::from("5"),
            joint_step: String::from("5"),
            status: String::new(),
            notice: None,
            config_path,
        };
        session.populate_from(&Document::shipped());
        session
    }

    /// The startup state: the fields, the document they were populated from, zero runtime
    /// angles, and whatever the configuration load had to complain about.
    ///
    /// `simulator.py:211-223`: the file is read if it exists, a failure is *reported* rather
    /// than fatal, and the applied state is then read back out of the fields — which is what
    /// makes a refused file fall back to the defaults instead of leaving the app with no
    /// table at all.
    pub fn start() -> (Self, Document, [f64; JOINT_COUNT]) {
        let path = default_config_path();
        let mut session = Self::new(path.clone());
        let mut document = Document::shipped();
        if path.exists() {
            match Document::load(&path) {
                Ok(loaded) => {
                    session.populate_from(&loaded);
                    document = loaded;
                }
                Err(error) => {
                    session.notice =
                        Some(Failure::new(PARAMETER_FILE_ERROR_TITLE, error.to_string()));
                }
            }
        }

        // The fields were just populated from a document, so these parses cannot fail; the
        // `if let` is here because a startup path that can panic is worse than one that
        // silently keeps the default table.
        if let Ok(rows) = session.read_dh_rows() {
            document.parameters = DHParameters::new(rows);
        }
        if let Ok(meshes) = session.read_meshes() {
            document.meshes = meshes;
        }

        let angles = [0.0; JOINT_COUNT];
        session.sync_joint_angles(&angles);
        (session, document, angles)
    }

    /// Fill the fields from a document, as `_populate_dh_entries` and
    /// `_populate_mesh_entries` do (`simulator.py:646-663`).
    pub fn populate_from(&mut self, document: &Document) {
        self.populate_dh(&document.parameters);
        for (form, settings) in self.meshes.iter_mut().zip(&document.meshes) {
            *form = MeshForm::from_settings(settings);
        }
    }

    /// Fill the DH fields, leaving the runtime-angle fields alone.
    pub fn populate_dh(&mut self, parameters: &DHParameters) {
        for (fields, row) in self.dh.iter_mut().zip(parameters.joints) {
            let values = [row.theta_offset_deg, row.d, row.a, row.alpha_deg];
            for (field, value) in fields.iter_mut().zip(values) {
                *field = format_g(value);
            }
        }
    }

    /// Render the runtime angles into their fields, `_sync_joint_angle_views`
    /// (`simulator.py:318-325`).
    ///
    /// The front readouts the reference also updates there — `f"{angle:.1f}°"` — are drawn
    /// from the stored angles by [`crate::ui`] rather than stored a second time.
    pub fn sync_joint_angles(&mut self, angles: &[f64; JOINT_COUNT]) {
        for (field, angle) in self.joint_angles.iter_mut().zip(angles) {
            *field = format_g(*angle);
        }
    }

    /// The DH table the fields ask for, `_read_entry_values` (`simulator.py:601-608`).
    ///
    /// The reference's first sentence — "Exactly six joints with four DH values each are
    /// required." — has no counterpart here: a `[[String; 4]; 6]` cannot be the wrong shape,
    /// so the check is structural and the message unreachable.
    pub fn read_dh_rows(&self) -> Result<[DhRow; JOINT_COUNT], String> {
        // Every field is parsed before anything is checked, matching the reference's order:
        // it builds the whole tuple first, so a mistyped field anywhere reports `float()`'s
        // complaint in preference to a finiteness failure in an earlier row.
        let mut values = [[0.0; 4]; JOINT_COUNT];
        for (fields, row) in self.dh.iter().zip(values.iter_mut()) {
            for (text, value) in fields.iter().zip(row.iter_mut()) {
                *value = parse_float(text)?;
            }
        }
        if !values.iter().flatten().all(|value| value.is_finite()) {
            return Err(String::from("All DH values must be finite numbers."));
        }
        Ok(core::array::from_fn(|joint| {
            DhRow::new(
                values[joint][0],
                values[joint][1],
                values[joint][2],
                values[joint][3],
            )
        }))
    }

    /// The runtime angles the fields ask for, `_read_joint_angle_values`
    /// (`simulator.py:612-628`) — see the module docs for the display-precision split.
    ///
    /// The reference's shape check ("Exactly six runtime joint angles are required.") is
    /// structural here for the same reason as the DH one.
    pub fn read_joint_angles(
        &self,
        stored: &[f64; JOINT_COUNT],
    ) -> Result<[f64; JOINT_COUNT], String> {
        let mut requested = [0.0; JOINT_COUNT];
        for (joint, (text, current)) in self.joint_angles.iter().zip(stored).enumerate() {
            requested[joint] = if *text == format_g(*current) {
                *current
            } else {
                parse_float(text)?
            };
        }
        if !requested.iter().all(|value| value.is_finite()) {
            return Err(String::from(
                "All runtime joint angles must be finite numbers.",
            ));
        }
        Ok(requested)
    }

    /// The mesh settings the fields ask for, `_read_mesh_entries` (`simulator.py:630-644`).
    pub fn read_meshes(&self) -> Result<[MeshSettings; MESH_COUNT], String> {
        let mut settings: [MeshSettings; MESH_COUNT] =
            core::array::from_fn(|_| MeshSettings::default());
        for (form, setting) in self.meshes.iter().zip(settings.iter_mut()) {
            let mut values = [0.0; 7];
            let fields = form
                .offset
                .iter()
                .chain(form.rotation.iter())
                .chain(core::iter::once(&form.opacity));
            for (text, value) in fields.zip(values.iter_mut()) {
                *value = parse_float(text)?;
            }
            if !values.iter().all(|value| value.is_finite()) {
                return Err(String::from(
                    "Mesh offsets, rotations, and opacity must be finite numbers.",
                ));
            }
            let opacity = values[6];
            if !(0.0..=1.0).contains(&opacity) {
                return Err(String::from("Mesh opacity must be from 0 to 1."));
            }
            // The reference trims before both the check and the store, so the setting
            // carries the trimmed path.
            let path = form.path.trim();
            if !path.is_empty() && path_suffix_lower(path) != ".stl" {
                return Err(format!("Mesh path must point to an STL file: {path}"));
            }
            setting.path = path.to_string();
            setting.offset = [values[0], values[1], values[2]];
            setting.rotation_deg = [values[3], values[4], values[5]];
            setting.opacity = opacity;
        }
        Ok(settings)
    }

    /// A step field's value, `_read_step` (`simulator.py:355-360`).
    pub fn read_step(text: &str, message: &str) -> Result<f64, String> {
        let step = parse_float(text)?;
        if !step.is_finite() || step <= 0.0 {
            return Err(String::from(message));
        }
        Ok(step)
    }

    /// "Apply to View" and "Apply Meshes" — `_apply_from_entries` (`simulator.py:665-678`).
    ///
    /// Both tabs share the one handler in the reference, so the button on the DH page
    /// applies the mesh rows as well and vice versa. The failure is a message [the caller
    /// shows](INVALID_PARAMETERS_TITLE) rather than a status line, which is the reference's
    /// split between `messagebox.showerror` here and the jog status label elsewhere.
    pub fn apply_from_entries(
        &mut self,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) -> Result<(), Failure> {
        // Order is the reference's, so the first complaint is the one Python would raise.
        let requested = self
            .read_joint_angles(angles)
            .map_err(|message| Failure::new(INVALID_PARAMETERS_TITLE, message))?;
        let parameters = DHParameters::new(
            self.read_dh_rows()
                .map_err(|message| Failure::new(INVALID_PARAMETERS_TITLE, message))?,
        );
        let meshes = self
            .read_meshes()
            .map_err(|message| Failure::new(INVALID_PARAMETERS_TITLE, message))?;

        *angles = requested;
        document.parameters = parameters;
        document.meshes = meshes;
        self.sync_joint_angles(angles);
        Ok(())
    }

    /// One joint jog, `_jog_joint` (`simulator.py:327-341`).
    ///
    /// The move is applied to the stored angles and then written back over all six fields,
    /// which is what discards an unapplied edit to a joint field.
    pub fn jog_joint(
        &mut self,
        joint: usize,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) {
        let step_text = self.joint_step.clone();
        let outcome = (|| -> Result<String, String> {
            let parameters = DHParameters::new(self.read_dh_rows()?);
            let step = Self::read_step(&step_text, JOINT_STEP_ERROR)?;
            let mut requested = *angles;
            requested[joint] += f64::from(direction) * step;
            self.apply_joint_solution(&parameters, &requested, document, angles);
            Ok(format!(
                "Jogged J{} {} deg",
                joint + 1,
                format_plus_g(f64::from(direction) * step)
            ))
        })();
        self.status = outcome.unwrap_or_else(|message| message);
    }

    /// One base-frame translation jog, `_jog_cartesian` (`simulator.py:399-406`).
    ///
    /// The direction is the button's whole meaning and it is applied twice: once to the
    /// target pose and once in the status line, exactly as the reference's two lambdas each
    /// spell out `direction * step` (`:403-404`). Dropping it from the first leaves a pair of
    /// buttons that jog the same way while one of them reports the other.
    pub fn jog_cartesian(
        &mut self,
        axis: Axis,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) {
        let step_text = self.jog_step.clone();
        let describe = |step: f64| {
            format!(
                "Moved base {} {}",
                axis.letter(),
                format_plus_g(f64::from(direction) * step)
            )
        };
        self.pose_jog(
            &step_text,
            JOG_STEP_ERROR,
            document,
            angles,
            |pose, step| jog::offset_pose_translation(pose, axis, f64::from(direction) * step),
            describe,
        );
    }

    /// One tool-frame translation jog, `_jog_tool_translation` (`simulator.py:408-415`).
    ///
    /// As above, the direction reaches the target pose (`:412`) and the report (`:413`).
    pub fn jog_tool_translation(
        &mut self,
        axis: Axis,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) {
        let step_text = self.jog_step.clone();
        let describe = |step: f64| {
            format!(
                "Moved tool {} {}",
                axis.letter(),
                format_plus_g(f64::from(direction) * step)
            )
        };
        self.pose_jog(
            &step_text,
            JOG_STEP_ERROR,
            document,
            angles,
            |pose, step| jog::offset_pose_tool_translation(pose, axis, f64::from(direction) * step),
            describe,
        );
    }

    /// One base-frame rotation jog, `_jog_rotation_world` (`simulator.py:417-424`).
    pub fn jog_rotation_world(
        &mut self,
        axis: Axis,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) {
        self.rotation_jog(
            axis,
            direction,
            document,
            angles,
            jog::rotate_pose_world_axis,
            "Rotated base",
        );
    }

    /// One tool-frame rotation jog, `_jog_rotation_tool` (`simulator.py:426-433`).
    pub fn jog_rotation_tool(
        &mut self,
        axis: Axis,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
    ) {
        self.rotation_jog(
            axis,
            direction,
            document,
            angles,
            jog::rotate_pose_tool_axis,
            "Rotated tool",
        );
    }

    /// The four rotation jogs differ only in which rotation and which verb, both of which
    /// arrive as arguments — the reference writes them out twice, once per frame.
    ///
    /// The signed angle is what the button means: `math.radians(direction * step)` in the
    /// reference's two rotation lambdas (`simulator.py:420`, `:429`), the sign applied
    /// before the conversion exactly as there, and the same signed value in the report.
    fn rotation_jog(
        &mut self,
        axis: Axis,
        direction: i32,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
        rotate: fn(&Pose<f64>, Axis, f64) -> Pose<f64>,
        verb: &'static str,
    ) {
        let step_text = self.rotation_step.clone();
        let describe = |step: f64| {
            format!(
                "{verb} R{} {} deg",
                axis.letter(),
                format_plus_g(f64::from(direction) * step)
            )
        };
        self.pose_jog(
            &step_text,
            ROTATION_STEP_ERROR,
            document,
            angles,
            move |pose, step| rotate(pose, axis, (f64::from(direction) * step).to_radians()),
            describe,
        );
    }

    /// The shared body of all four Cartesian jogs, `_pose_jog` (`simulator.py:362-397`).
    ///
    /// Everything that can fail is collected inside one closure so that a single status-line
    /// assignment covers all of it, exactly as the reference's `try` does. Nothing is written
    /// to the stored state before the solve succeeds, which is what makes the jog
    /// all-or-nothing: an unreachable target leaves the arm where it was and says
    /// [`NO_SOLUTION`].
    fn pose_jog(
        &mut self,
        step_text: &str,
        step_error: &str,
        document: &mut Document,
        angles: &mut [f64; JOINT_COUNT],
        target_of: impl Fn(&Pose<f64>, f64) -> Pose<f64>,
        describe: impl Fn(f64) -> String,
    ) {
        let outcome = (|| -> Result<String, String> {
            // The DH fields, not the applied document — see the module docs.
            let parameters = DHParameters::new(self.read_dh_rows()?);
            let current = *angles;
            let step = Self::read_step(step_text, step_error)?;
            let geometry = geometry_of(&parameters)?;
            let current_pose = fk(&geometry, &parameters.total_angles_rad(&current));
            let requested = target_of(&current_pose, step);
            let solutions =
                solve::solve(&parameters, &requested).map_err(|error| error.to_string())?;

            // `min(solutions, key=Σ wrap(angle - current)²)` (`simulator.py:392-395`): the
            // branch nearest the pose the arm is already in, so a jog continues in the
            // configuration it found rather than flipping the elbow or the shoulder.
            //
            // The reference compares *runtime* radians and this compares totals; the two
            // differ by the joint's static offset, which cancels in the subtraction
            // (`wrapped_distance_sq` wraps the difference, so a whole-turn discrepancy
            // cannot matter either). Using the totals keeps the reference's own
            // `total_angles_rad` as the single place the offset is applied.
            let reference = robot_kinematics::Solution {
                angles: parameters.total_angles_rad(&current),
                shoulder: 1,
                elbow: 1,
            };
            let Some(chosen) = solutions.nearest_to(&reference) else {
                return Err(String::from(NO_SOLUTION));
            };

            // Back to runtime degrees for the stored state, which is the change of variable
            // `_apply_joint_solution` performs with `math.degrees` (`simulator.py:343-353`).
            let solved = core::array::from_fn(|joint| {
                units::rad_to_deg(units::runtime_angle(
                    chosen.angles[joint],
                    parameters.joints[joint].theta_offset_deg,
                ))
            });
            self.apply_joint_solution(&parameters, &solved, document, angles);
            Ok(describe(step))
        })();
        self.status = outcome.unwrap_or_else(|message| message);
    }

    /// Store a solved or jogged configuration at full precision and refresh the fields from
    /// it, `_apply_joint_solution` (`simulator.py:343-353`).
    ///
    /// Note what it does *not* carry over: the mesh settings, which a jog leaves alone.
    fn apply_joint_solution(
        &mut self,
        parameters: &DHParameters,
        solved: &[f64; JOINT_COUNT],
        document: &mut Document,
        stored: &mut [f64; JOINT_COUNT],
    ) {
        *stored = *solved;
        self.sync_joint_angles(solved);
        document.parameters = *parameters;
    }

    /// The `Copy XYZ` clipboard text, `_copy_t6_position` (`simulator.py:297-316`).
    ///
    /// Fifteen lines, `%.15g` on every number, and no trailing newline — the reference joins
    /// with `"\n"`. The pose comes from the *applied* table and the *stored* angles, so the
    /// button copies what is on screen rather than what is typed.
    pub fn copy_xyz_text(
        parameters: &DHParameters,
        runtime_deg: &[f64; JOINT_COUNT],
    ) -> Result<String, String> {
        let geometry = geometry_of(parameters)?;
        let tool = fk(&geometry, &parameters.total_angles_rad(runtime_deg));
        let [roll, pitch, yaw] = rotation_to_rpy_degrees(&tool);
        let value = |number: f64| format_precision_g(number, CLIPBOARD_PRECISION);

        let mut lines = vec![
            String::from("T6 position (model units):"),
            format!("X: {}", value(tool.p.x())),
            format!("Y: {}", value(tool.p.y())),
            format!("Z: {}", value(tool.p.z())),
            String::from("T6 orientation (RPY, ZYX, degrees):"),
            format!("Roll: {}", value(roll)),
            format!("Pitch: {}", value(pitch)),
            format!("Yaw: {}", value(yaw)),
            String::from("Runtime joint angles (degrees):"),
        ];
        for (index, angle) in runtime_deg.iter().enumerate() {
            lines.push(format!("J{}: {}", index + 1, value(*angle)));
        }
        Ok(lines.join("\n"))
    }

    /// "Save JSON", `_save_json` (`simulator.py:680-711`).
    ///
    /// Reads the DH and mesh fields — not the joint fields, so an unapplied joint edit is
    /// discarded rather than saved — writes the file, and *then* adopts what it wrote as the
    /// applied state, which is why a save also applies unapplied DH and mesh edits.
    ///
    /// **Deviation.** The reference writes to the fixed path at
    /// `Path(__file__).with_name("robot_parameters.json")` and never asks. Here the caller
    /// passes the path a file dialog returned; the file's own bytes are unaffected, and
    /// `path.parent()` is what relative mesh paths are computed against either way.
    pub fn save_json(&mut self, document: &mut Document, path: &Path) -> Result<String, Failure> {
        // The fields are the user's complaint; the write is the file system's. The reference
        // keeps the two apart too, with its two `try` blocks and two titles.
        let parameters = DHParameters::new(
            self.read_dh_rows()
                .map_err(|message| Failure::new(INVALID_PARAMETERS_TITLE, message))?,
        );
        let meshes = self
            .read_meshes()
            .map_err(|message| Failure::new(INVALID_PARAMETERS_TITLE, message))?;

        // The flags come from the document, which is where the UI's checkboxes write them
        // live (`simulator.py:691-693` reads the widgets, which is the same thing).
        let mut written = document.clone();
        written.parameters = parameters;
        // Cloned because the same settings are adopted as the applied state below, and
        // `MeshSettings` is not `Copy`.
        written.meshes = meshes.clone();
        written
            .save(path)
            .map_err(|error| Failure::new(COULD_NOT_SAVE_TITLE, error.to_string()))?;

        document.parameters = parameters;
        document.meshes = meshes;
        self.config_path = path.to_path_buf();
        Ok(format!(
            "Saved to {}.",
            path.file_name().map_or_else(
                || path.display().to_string(),
                |name| name.to_string_lossy().into_owned()
            )
        ))
    }

    /// "Load JSON", `_load_json` (`simulator.py:809-825`).
    ///
    /// The runtime angles are left alone: the reference keeps `joint_angles_degrees` and
    /// folds it into the freshly loaded table, so loading a table is not a move, and the
    /// file has no key to load angles out of anyway.
    pub fn load_json(
        &mut self,
        document: &mut Document,
        angles: &[f64; JOINT_COUNT],
        path: &Path,
    ) -> Result<(), Failure> {
        let loaded = Document::load(path)
            .map_err(|error| Failure::new(COULD_NOT_LOAD_TITLE, error.to_string()))?;
        self.populate_from(&loaded);
        self.sync_joint_angles(angles);
        *document = loaded;
        self.config_path = path.to_path_buf();
        Ok(())
    }

    /// Queue a messagebox, `messagebox.showinfo`/`showerror`.
    pub fn show_notice(&mut self, title: &'static str, message: impl Into<String>) {
        self.notice = Some(Failure::new(title, message));
    }
}

/// Roll, pitch, yaw in degrees for `R = Rz(yaw) · Ry(pitch) · Rx(roll)`, the extraction
/// `_rotation_to_rpy_degrees` performs (`simulator.py:45-58`).
///
/// Both consumers of this are here — [`Session::copy_xyz_text`] and the pose readout in
/// [`crate::ui`] — so it lives beside the first and the second delegates.
///
/// The two-branch structure is the reference's own: at pitch ±90° the first column vanishes
/// and roll and yaw have become the same axis, so the yaw is recovered from the second row
/// instead and the roll is reported as zero. The `1e-9` threshold is what decides "vanished".
pub fn rotation_to_rpy_degrees(pose: &Pose<f64>) -> [f64; 3] {
    let pitch = (-pose.r.at(2, 0)).atan2(pose.r.at(0, 0).hypot(pose.r.at(1, 0)));
    let (roll, yaw) = if pose.r.at(0, 0).hypot(pose.r.at(1, 0)) > 1e-9 {
        (
            pose.r.at(2, 1).atan2(pose.r.at(2, 2)),
            pose.r.at(1, 0).atan2(pose.r.at(0, 0)),
        )
    } else {
        (0.0, (-pose.r.at(0, 1)).atan2(pose.r.at(1, 1)))
    };
    [roll.to_degrees(), pitch.to_degrees(), yaw.to_degrees()]
}

/// The geometry a table describes, or the reference's sentence for why it has none.
///
/// `forward_kinematics` in Python multiplies any table at all, so the only place a zero link
/// length is ever *reported* is `_validate_supported_geometry` (`kinematics.py:443-445`).
/// The sentences are [`TableError`]'s, so this defers to it rather than writing them twice.
fn geometry_of(parameters: &DHParameters) -> Result<Geometry<f64>, String> {
    parameters.geometry().map_err(|error| match error {
        GeometryError::LinkOneNotPositive => TableError::LinkOneNotPositive.to_string(),
        GeometryError::LinkTwoNotPositive => TableError::LinkTwoNotPositive.to_string(),
        GeometryError::NotFinite => TableError::NotFinite.to_string(),
    })
}

/// `float(text)`, including its complaint.
///
/// Python accepts surrounding whitespace and rejects everything else with
/// `could not convert string to float: '…'`, quoting the text as typed; this reproduces
/// both, so a mistyped field reads the same here as it does in the reference. Python also
/// accepts `"infinity"`, `"1_000"` and a leading `+` on every form, none of which Rust's
/// parser takes — a deviation in what is *accepted*, not in what is reported.
fn parse_float(text: &str) -> Result<f64, String> {
    text.trim()
        .parse::<f64>()
        .map_err(|_| format!("could not convert string to float: '{text}'"))
}

/// `pathlib.Path::suffix` lowercased: the extension of the final component, empty when there
/// is none.
///
/// The leading-dot case is why this is not `ends_with`: in `pathlib` a dot at the start of a
/// name is part of the name, not an extension, so `Path(".stl").suffix` is `""` and the
/// reference rejects a mesh path of exactly `.stl`.
fn path_suffix_lower(path: &str) -> String {
    let name = path.rsplit(['/', '\\']).next().unwrap_or("");
    match name.rfind('.') {
        Some(0) | None => String::new(),
        Some(dot) => name[dot..].to_ascii_lowercase(),
    }
}

/// Where `robot_parameters.json` is read from and written to by default.
///
/// **Deviation.** The reference pins this beside the script
/// (`Path(__file__).with_name("robot_parameters.json")`, `simulator.py:171`); a compiled
/// binary has no script directory, so this looks beside the executable first and then in the
/// working directory. The second is what makes `cargo run` from the repository root find the
/// file that ships there — without it the app would always open on the defaults, since
/// `cargo run` puts the binary in `target/`.
///
/// The build stages a copy of the shipped file, and the `mesh/` tree beside it, into the
/// directory the executable lands in (`build.rs`), so the first branch is what an executable
/// run from its own directory takes. That copy is authoritative while it is there: a save
/// through the dialog writes it, and the next build only overwrites it if the shipped file
/// itself has changed.
pub fn default_config_path() -> PathBuf {
    let beside_executable = std::env::current_exe()
        .ok()
        .and_then(|exe| exe.parent().map(Path::to_path_buf))
        .unwrap_or_else(|| PathBuf::from("."))
        .join("robot_parameters.json");
    if beside_executable.exists() {
        return beside_executable;
    }
    let working_directory = PathBuf::from("robot_parameters.json");
    if working_directory.exists() {
        return working_directory;
    }
    beside_executable
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::{FRAME_COUNT, Mat3, Vec3, carrier_pose};
    use robot_model::MESH_FRAME_NAMES;

    /// A session holding the shipped document, with the runtime angles at zero.
    fn session() -> (Session, Document, [f64; JOINT_COUNT]) {
        let mut document = Document::shipped();
        let mut session = Session::new(PathBuf::from("robot_parameters.json"));
        let angles = [0.0; JOINT_COUNT];
        session.sync_joint_angles(&angles);
        document.parameters = DHParameters::new(session.read_dh_rows().expect("shipped fields"));
        (session, document, angles)
    }

    // --- the display-precision split ------------------------------------------------

    #[test]
    fn an_untouched_field_yields_the_stored_angle_at_full_precision() {
        // `test_kinematics.py:361`. The field renders `0.333333`; the stored angle is the
        // full double, and reading it back must not round it to the field's six digits.
        let (mut session, _document, _angles) = session();
        let stored = [0.3333333333333333; JOINT_COUNT];
        session.sync_joint_angles(&stored);
        assert_eq!(session.joint_angles[0], "0.333333");

        let read = session.read_joint_angles(&stored).expect("valid fields");
        assert_eq!(read, stored, "rounding would give 0.333333");
    }

    #[test]
    fn a_retyped_field_is_taken_at_face_value() {
        let (mut session, _document, _angles) = session();
        let stored = [0.3333333333333333; JOINT_COUNT];
        session.sync_joint_angles(&stored);
        session.joint_angles[2] = String::from("12.5");
        let read = session.read_joint_angles(&stored).expect("valid fields");
        assert_eq!(read[2], 12.5);
        // ... and the five fields that were not retyped keep their full precision.
        for joint in [0, 1, 3, 4, 5] {
            assert_eq!(read[joint], 0.3333333333333333);
        }
    }

    #[test]
    fn a_retyped_field_that_happens_to_match_its_rendering_is_indistinguishable() {
        // The split is decided on the text, so typing the six-digit rendering *is* the
        // full-precision angle. That is the reference's behavior and worth pinning: the
        // ambiguity is resolved in favor of precision, not in favor of the keystrokes.
        let (mut session, _document, _angles) = session();
        let stored = [0.3333333333333333; JOINT_COUNT];
        session.sync_joint_angles(&stored);
        session.joint_angles[0] = String::from("0.333333");
        let read = session.read_joint_angles(&stored).expect("valid fields");
        assert_eq!(read[0], 0.3333333333333333);
    }

    #[test]
    fn a_long_angle_renders_in_the_reference_spelling() {
        let (mut session, _document, _angles) = session();
        session.sync_joint_angles(&[1234567.0, -0.0001234567, 1.0 / 3.0, 90.0, 1e-7, 0.0]);
        assert_eq!(session.joint_angles[0], "1.23457e+06");
        assert_eq!(session.joint_angles[1], "-0.000123457");
        assert_eq!(session.joint_angles[2], "0.333333");
        assert_eq!(session.joint_angles[3], "90");
        assert_eq!(session.joint_angles[4], "1e-07");
        assert_eq!(session.joint_angles[5], "0");
    }

    // --- field validation -----------------------------------------------------------

    #[test]
    fn the_shipped_fields_read_back_as_the_shipped_table() {
        let (session, _document, _angles) = session();
        assert_eq!(
            session.read_dh_rows().expect("shipped fields"),
            DHParameters::shipped().joints
        );
    }

    #[test]
    fn mistyped_text_reports_pythons_float_complaint() {
        let (mut session, _document, _angles) = session();
        session.dh[1][2] = String::from("forty");
        assert_eq!(
            session.read_dh_rows().expect_err("not a number"),
            "could not convert string to float: 'forty'"
        );
        // The message quotes the text as typed, whitespace and all.
        session.dh[1][2] = String::from(" 40 ");
        assert_eq!(
            session.read_dh_rows().expect("surrounding space is fine")[1].a,
            40.0
        );
    }

    #[test]
    fn a_non_finite_dh_value_is_reported_after_every_field_parses() {
        // The reference builds the whole tuple before it checks anything
        // (`simulator.py:602-605`), so a mistyped field in a later row wins over an `inf`
        // in an earlier one.
        let (mut session, _document, _angles) = session();
        session.dh[0][1] = String::from("inf");
        assert_eq!(
            session.read_dh_rows().expect_err("inf is not accepted"),
            "All DH values must be finite numbers."
        );
        session.dh[5][3] = String::from("nope");
        assert_eq!(
            session.read_dh_rows().expect_err("text wins"),
            "could not convert string to float: 'nope'"
        );
    }

    #[test]
    fn the_three_step_messages_are_the_references_own() {
        assert!(Session::read_step("5", JOINT_STEP_ERROR).is_ok());
        assert_eq!(
            Session::read_step("0", JOINT_STEP_ERROR).expect_err("zero is not a step"),
            "Joint step must be a finite positive angle."
        );
        assert_eq!(
            Session::read_step("-1", JOG_STEP_ERROR).expect_err("negative is not a step"),
            "Jog step must be a finite positive length."
        );
        assert_eq!(
            Session::read_step("abc", ROTATION_STEP_ERROR).expect_err("text is not a step"),
            "could not convert string to float: 'abc'"
        );
        assert_eq!(
            Session::read_step("nan", ROTATION_STEP_ERROR).expect_err("nan is not a step"),
            "Rotation step must be a finite positive angle."
        );
    }

    #[test]
    fn mesh_rows_are_checked_for_their_numbers_their_opacity_and_their_extension() {
        let (mut session, _document, _angles) = session();
        assert!(session.read_meshes().is_ok());

        session.meshes[3].offset[1] = String::from("x");
        assert_eq!(
            session.read_meshes().expect_err("not a number"),
            "could not convert string to float: 'x'"
        );
        session.meshes[3].offset[1] = String::from("0");

        session.meshes[3].opacity = String::from("inf");
        assert_eq!(
            session.read_meshes().expect_err("inf is not finite"),
            "Mesh offsets, rotations, and opacity must be finite numbers."
        );

        session.meshes[3].opacity = String::from("1.5");
        assert_eq!(
            session.read_meshes().expect_err("out of range"),
            "Mesh opacity must be from 0 to 1."
        );
        session.meshes[3].opacity = String::from("0");
        assert!(session.read_meshes().is_ok(), "zero opacity is legal");

        session.meshes[3].opacity = String::from("1");
        session.meshes[3].path = String::from("mesh/part.step");
        assert_eq!(
            session.read_meshes().expect_err("not an STL"),
            "Mesh path must point to an STL file: mesh/part.step"
        );

        session.meshes[3].path = String::from("  mesh/part.STL  ");
        let meshes = session.read_meshes().expect("upper case is fine");
        assert_eq!(meshes[3].path, "mesh/part.STL", "the reference trims");

        // `pathlib` reads a leading dot as part of a hidden file's name, not as an
        // extension, so a path of exactly `.stl` has no suffix.
        session.meshes[3].path = String::from(".stl");
        assert_eq!(
            session
                .read_meshes()
                .expect_err("a hidden file has no suffix"),
            "Mesh path must point to an STL file: .stl"
        );
    }

    #[test]
    fn the_extension_check_looks_at_the_final_component_only() {
        assert_eq!(path_suffix_lower("mesh/part.stl"), ".stl");
        assert_eq!(path_suffix_lower("mesh/stl.d/part"), "");
        assert_eq!(path_suffix_lower("Part.STL"), ".stl");
        assert_eq!(path_suffix_lower("mesh\\part.stl"), ".stl");
        assert_eq!(path_suffix_lower(".hidden"), "");
        assert_eq!(path_suffix_lower("part"), "");
    }

    // --- joint jogs -----------------------------------------------------------------

    #[test]
    fn a_joint_jog_moves_one_joint_and_reports_the_reference_string() {
        let (mut session, mut document, mut angles) = session();
        session.jog_joint(0, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Jogged J1 +5 deg");
        assert_eq!(angles[0], 5.0);
        assert_eq!(session.joint_angles[0], "5");

        session.jog_joint(3, -1, &mut document, &mut angles);
        assert_eq!(session.status, "Jogged J4 -5 deg");
        assert_eq!(angles[3], -5.0);

        session.joint_step = String::from("0.25");
        session.jog_joint(5, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Jogged J6 +0.25 deg");
        assert_eq!(angles[5], 0.25);
    }

    #[test]
    fn a_joint_jog_reads_the_dh_fields_not_the_applied_table() {
        // `_jog_joint` builds its table from `_read_entry_values` (`simulator.py:328`), so an
        // unapplied edit takes effect on the next jog. That is the reference's behavior.
        let (mut session, mut document, mut angles) = session();
        // Column 2 is `a`; the columns are theta, d, a, alpha (`simulator.py:461-490`).
        session.dh[1][2] = String::from("70");
        assert_eq!(document.parameters.joints[1].a, 25.0, "not applied yet");

        session.jog_joint(0, 1, &mut document, &mut angles);
        assert_eq!(document.parameters.joints[1].a, 70.0);
        assert_eq!(session.status, "Jogged J1 +5 deg");
    }

    #[test]
    fn a_joint_jog_discards_an_unapplied_joint_field_edit() {
        let (mut session, mut document, mut angles) = session();
        session.joint_angles[2] = String::from("90");
        session.jog_joint(0, 1, &mut document, &mut angles);
        assert_eq!(angles[2], 0.0);
        assert_eq!(
            session.joint_angles[2], "0",
            "rewritten from the stored state"
        );
    }

    #[test]
    fn a_joint_jog_with_a_bad_dh_field_is_refused_with_that_message() {
        let (mut session, mut document, mut angles) = session();
        session.dh[4][0] = String::from("oops");
        session.jog_joint(1, 1, &mut document, &mut angles);
        assert_eq!(session.status, "could not convert string to float: 'oops'");
        assert_eq!(angles, [0.0; JOINT_COUNT], "nothing moved");
    }

    #[test]
    fn a_joint_jog_with_a_bad_step_is_refused_with_that_message() {
        let (mut session, mut document, mut angles) = session();
        session.joint_step = String::from("-5");
        session.jog_joint(1, 1, &mut document, &mut angles);
        assert_eq!(session.status, JOINT_STEP_ERROR);
        assert_eq!(angles, [0.0; JOINT_COUNT]);
    }

    // --- pose jogs ------------------------------------------------------------------

    #[test]
    fn a_base_translation_jog_reports_the_reference_string() {
        let (mut session, mut document, mut angles) = session();
        session.jog_cartesian(Axis::Y, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Moved base Y +1");

        session.jog_cartesian(Axis::X, -1, &mut document, &mut angles);
        assert_eq!(session.status, "Moved base X -1");

        session.jog_step = String::from("2.5");
        session.jog_cartesian(Axis::Z, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Moved base Z +2.5");
    }

    #[test]
    fn a_tool_translation_jog_reports_the_reference_string() {
        let (mut session, mut document, mut angles) = session();
        session.jog_tool_translation(Axis::Z, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Moved tool Z +1");
    }

    #[test]
    fn the_rotation_jogs_report_the_reference_strings() {
        let (mut session, mut document, mut angles) = session();
        session.jog_rotation_world(Axis::X, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Rotated base RX +5 deg");

        session.jog_rotation_tool(Axis::X, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Rotated tool RX +5 deg");

        session.rotation_step = String::from("15");
        session.jog_rotation_tool(Axis::Z, -1, &mut document, &mut angles);
        assert_eq!(session.status, "Rotated tool RZ -15 deg");
    }

    #[test]
    fn a_translation_jog_actually_moves_the_tool_by_the_step() {
        // The status string is only worth reporting if the move happened, so this checks the
        // tool origin through forward kinematics rather than trusting the angles.
        let (mut session, mut document, mut angles) = session();
        let before = tool_position(&document, &angles);
        session.jog_cartesian(Axis::Y, 1, &mut document, &mut angles);
        let after = tool_position(&document, &angles);
        assert!(
            (after[1] - before[1] - 1.0).abs() < 1e-9,
            "{before:?} {after:?}"
        );
        assert!((after[0] - before[0]).abs() < 1e-9);
        assert!((after[2] - before[2]).abs() < 1e-9);
    }

    #[test]
    fn a_rotation_jog_keeps_the_tool_origin_and_turns_it_by_the_step() {
        let (mut session, mut document, mut angles) = session();
        let before = carrier_pose_of(&document, &angles)[FRAME_COUNT - 1];
        session.jog_rotation_world(Axis::Z, 1, &mut document, &mut angles);
        let after = carrier_pose_of(&document, &angles)[FRAME_COUNT - 1];
        assert!(
            before.p.distance(after.p) < 1e-9,
            "a rotation must not translate the tool"
        );
        // A +5 degree turn about the base z axis pre-multiplies the orientation by `Rz(5°)`.
        // The comparison is the whole matrix rather than, say, the heading `atan2(r10, r00)`:
        // at zero angles the tool's x axis points along the world z axis, where a heading is
        // the `atan2` of two near-zero entries and so means nothing.
        let expected = jog::axis_rotation(Axis::Z, 5.0_f64.to_radians()) * before.r;
        assert!(
            after.r.frobenius_distance(expected) < 1e-9,
            "status {:?}\nbefore {before:?}\nafter {after:?}",
            session.status
        );
    }

    #[test]
    fn an_unreachable_target_leaves_the_arm_alone() {
        // `_pose_jog` refuses the whole move when the solve comes back empty
        // (`simulator.py:385-387`). A step a million units long is well outside an arm whose
        // links are 25 units.
        let (mut session, mut document, mut angles) = session();
        let before = angles;
        let before_parameters = document.parameters;
        session.jog_step = String::from("1000000");
        session.jog_cartesian(Axis::X, 1, &mut document, &mut angles);
        assert_eq!(session.status, NO_SOLUTION);
        assert_eq!(angles, before, "the robot was not moved");
        assert_eq!(
            session.joint_angles,
            core::array::from_fn(|_| String::from("0"))
        );
        assert_eq!(document.parameters, before_parameters);
    }

    #[test]
    fn a_pose_jog_on_an_unsupported_table_names_the_parameter() {
        // `test_kinematics.py:677-691` types 45 into joint 3's alpha and expects the status
        // line to say which parameter is wrong.
        let (mut session, mut document, mut angles) = session();
        session.dh[2][3] = String::from("45");
        session.jog_cartesian(Axis::X, 1, &mut document, &mut angles);
        assert!(
            session.status.contains("joint 3 alpha"),
            "status was {:?}",
            session.status
        );
        assert_eq!(angles, [0.0; JOINT_COUNT], "nothing moved");
    }

    #[test]
    fn a_pose_jog_stays_on_the_branch_it_started_on() {
        // The reason for the nearest-branch rule: without it a jog can flip the elbow or
        // the shoulder, which is a different configuration of the same pose and a jump on
        // screen. Walking a few steps must not.
        let (mut session, mut document, mut angles) = session();
        session.jog_step = String::from("0.5");
        for _ in 0..10 {
            session.jog_cartesian(Axis::Z, -1, &mut document, &mut angles);
            assert_eq!(session.status, "Moved base Z -0.5");
        }
        // Ten half-unit steps down from zero: the arm has moved, and no joint has taken a
        // near-half-turn hop.
        assert!(angles.iter().any(|angle| angle.abs() > 0.5));
        for (joint, angle) in angles.iter().enumerate() {
            assert!(
                angle.abs() < 180.0,
                "joint {joint} hopped to {angle}, a branch flip"
            );
        }
    }

    #[test]
    fn a_pose_jog_applies_the_dh_fields_too() {
        let (mut session, mut document, mut angles) = session();
        session.dh[5][1] = String::from("30"); // joint 6's d, the tool offset
        session.jog_cartesian(Axis::Y, 1, &mut document, &mut angles);
        assert_eq!(session.status, "Moved base Y +1");
        assert_eq!(document.parameters.joints[5].d, 30.0);
    }

    #[test]
    fn a_pose_jog_leaves_the_mesh_settings_alone() {
        let (mut session, mut document, mut angles) = session();
        document.meshes[2].path = String::from("mesh/joint3.stl");
        session.jog_cartesian(Axis::Y, 1, &mut document, &mut angles);
        assert_eq!(document.meshes[2].path, "mesh/joint3.stl");
    }

    #[test]
    fn the_angles_a_pose_jog_stores_are_runtime_angles_at_full_precision() {
        // The stored state is runtime degrees, so joint 2's 90 degree static offset has to
        // come back off the totals the solver works in.
        let (mut session, mut document, mut angles) = session();
        session.jog_cartesian(Axis::Y, 1, &mut document, &mut angles);
        let totals = document.parameters.total_angles_rad(&angles);
        let geometry = document.parameters.geometry().expect("shipped");
        let tool = fk(&geometry, &totals);
        assert_eq!(tool.p.x(), fk(&geometry, &totals).p.x());
        assert!(
            angles.iter().all(|angle| angle.abs() < 180.0),
            "{angles:?} should be wrapped runtime angles"
        );
        // Every field renders its stored angle, so the split round-trips through the fields.
        assert_eq!(
            session.read_joint_angles(&angles).expect("valid fields"),
            angles
        );
    }

    // --- every button jogs the way its label says -----------------------------------

    /// A jog button's identity: which group's row it sits in and whether it moves the pose
    /// or turns it. With an axis and a direction this names one of the panel's twenty-four
    /// buttons, and the four groups are exactly the handler pairs
    /// `ui::frame_jog_buttons` is handed for the "Base frame" and "Tool frame" groups.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum JogButton {
        BaseTranslation,
        BaseRotation,
        ToolTranslation,
        ToolRotation,
    }

    impl JogButton {
        /// All four, in the order the two groups appear on screen.
        const ALL: [JogButton; 4] = [
            JogButton::BaseTranslation,
            JogButton::BaseRotation,
            JogButton::ToolTranslation,
            JogButton::ToolRotation,
        ];

        /// The two that move the tool, and the two that turn it.
        const TRANSLATIONS: [JogButton; 2] =
            [JogButton::BaseTranslation, JogButton::ToolTranslation];
        const ROTATIONS: [JogButton; 2] = [JogButton::BaseRotation, JogButton::ToolRotation];

        /// Whether the button turns the pose rather than moving it, which is what the `R`
        /// in its label says.
        fn rotates(self) -> bool {
            matches!(self, JogButton::BaseRotation | JogButton::ToolRotation)
        }

        /// Whether the button works in the axes the pose itself carries rather than the
        /// base frame's, which is what separates the two groups.
        fn tool_frame(self) -> bool {
            matches!(self, JogButton::ToolTranslation | JogButton::ToolRotation)
        }

        /// The label the panel puts on this button, from the panel's own spelling of it.
        fn label(self, axis: Axis, direction: i32) -> String {
            crate::ui::jog_button_label(axis, direction, self.rotates())
        }

        /// Click it: the handler `ui::frame_jog_buttons` is handed for this group.
        fn press(
            self,
            session: &mut Session,
            axis: Axis,
            direction: i32,
            document: &mut Document,
            angles: &mut [f64; JOINT_COUNT],
        ) {
            match self {
                JogButton::BaseTranslation => {
                    session.jog_cartesian(axis, direction, document, angles);
                }
                JogButton::BaseRotation => {
                    session.jog_rotation_world(axis, direction, document, angles);
                }
                JogButton::ToolTranslation => {
                    session.jog_tool_translation(axis, direction, document, angles);
                }
                JogButton::ToolRotation => {
                    session.jog_rotation_tool(axis, direction, document, angles);
                }
            }
        }
    }

    /// The crate's own rotation about one axis, taken in degrees. `jog::axis_rotation` is
    /// pinned against `rotX`/`rotY`/`rotZ` bit for bit, so an expectation built here shares
    /// no line with the code a jog runs.
    fn turn_about(axis: Axis, degrees: f64) -> Mat3<f64> {
        let radians = degrees.to_radians();
        match axis {
            Axis::X => Mat3::rot_x(radians),
            Axis::Y => Mat3::rot_y(radians),
            Axis::Z => Mat3::rot_z(radians),
        }
    }

    /// Every translation button moves the tool origin by the step its box holds, along the
    /// axis its label names *and in the direction the label's sign names*: a coordinate axis
    /// of the base frame for the base group, an axis the pose itself carries — a column of
    /// its rotation block — for the tool group. The orientation is left alone either way.
    ///
    /// The expectations are built from [`Vec3`] and the rotation block rather than from
    /// `jog`'s helpers, so this states what the label means on its own terms; the helpers
    /// are pinned against the reference in `jog`'s own tests. The step is read out of the
    /// session, so the shipped default is the one under test.
    #[test]
    fn every_translation_button_moves_the_tool_the_way_its_label_says() {
        for button in JogButton::TRANSLATIONS {
            for axis in Axis::ALL {
                for direction in [-1, 1] {
                    let label = button.label(axis, direction);
                    let (mut session, mut document, mut angles) = session();
                    let step = session.jog_step.parse::<f64>().expect("the shipped step");
                    let signed_step = f64::from(direction) * step;
                    let before = tool_pose_of(&document, &angles);

                    button.press(&mut session, axis, direction, &mut document, &mut angles);
                    let after = tool_pose_of(&document, &angles);

                    let expected = if button.tool_frame() {
                        before.r.col(axis.index()) * signed_step
                    } else {
                        match axis {
                            Axis::X => Vec3::new(signed_step, 0.0, 0.0),
                            Axis::Y => Vec3::new(0.0, signed_step, 0.0),
                            Axis::Z => Vec3::new(0.0, 0.0, signed_step),
                        }
                    };
                    assert!(
                        (after.p - before.p).distance(expected) < 1e-9,
                        "{label}: the tool origin moved by {:?}, not {expected:?}",
                        after.p - before.p
                    );
                    assert!(
                        after.r.frobenius_distance(before.r) < 1e-9,
                        "{label}: a translation must not turn the tool"
                    );
                }
            }
        }
    }

    /// Every rotation button turns the tool by the angle its box holds, about the axis its
    /// label names and towards the side its sign names — about a base axis for the base
    /// group, which pre-multiplies the rotation, and about one of the pose's own axes for the
    /// tool group, which post-multiplies it. The origin stays exactly where it was, which is
    /// what makes a rotation jog a reorientation in place rather than a move.
    #[test]
    fn every_rotation_button_turns_the_tool_the_way_its_label_says() {
        for button in JogButton::ROTATIONS {
            for axis in Axis::ALL {
                for direction in [-1, 1] {
                    let label = button.label(axis, direction);
                    let (mut session, mut document, mut angles) = session();
                    let step = session
                        .rotation_step
                        .parse::<f64>()
                        .expect("the shipped rotation step");
                    let signed_turn = turn_about(axis, f64::from(direction) * step);
                    let before = tool_pose_of(&document, &angles);

                    button.press(&mut session, axis, direction, &mut document, &mut angles);
                    let after = tool_pose_of(&document, &angles);

                    let expected = if button.tool_frame() {
                        before.r * signed_turn
                    } else {
                        signed_turn * before.r
                    };
                    assert!(
                        after.r.frobenius_distance(expected) < 1e-9,
                        "{label}: the orientation is not the {direction}-way turn about {axis:?}"
                    );
                    assert!(
                        before.p.distance(after.p) < 1e-9,
                        "{label}: a rotation must not translate the tool"
                    );
                }
            }
        }
    }

    /// The two buttons of a pair have to do opposite things: each moves the arm off the pose
    /// it started on, and the second puts it back exactly where the first found it.
    ///
    /// This is the shape of the bug the suite is here for — the direction reached the status
    /// line but not the target pose, so both buttons of a pair jogged the same way while one
    /// of them said it had gone the other way. The status line is checked too, against the
    /// signed step the button carries rather than against the direction alone: a report that
    /// disagrees with the move is the same lie in a different place.
    #[test]
    fn the_buttons_of_a_pair_jog_opposite_ways_and_undo_each_other() {
        for button in JogButton::ALL {
            for axis in Axis::ALL {
                let (mut session, mut document, mut angles) = session();
                let forward_label = button.label(axis, 1);
                let backward_label = button.label(axis, -1);
                let step = if button.rotates() {
                    session.rotation_step.parse::<f64>()
                } else {
                    session.jog_step.parse::<f64>()
                }
                .expect("the shipped step");
                let start = tool_pose_of(&document, &angles);

                button.press(&mut session, axis, 1, &mut document, &mut angles);
                let forward = tool_pose_of(&document, &angles);
                let reported = format_plus_g(step);
                assert!(
                    session.status.contains(&reported),
                    "{forward_label} reported {:?}, which is not {reported}",
                    session.status
                );
                assert!(
                    forward.p.distance(start.p) > 1e-6
                        || forward.r.frobenius_distance(start.r) > 1e-6,
                    "{forward_label}: the button did not move the arm at all"
                );

                button.press(&mut session, axis, -1, &mut document, &mut angles);
                let back = tool_pose_of(&document, &angles);
                let reported = format_plus_g(-step);
                assert!(
                    session.status.contains(&reported),
                    "{backward_label} reported {:?}, which is not {reported}",
                    session.status
                );
                assert!(
                    back.p.distance(start.p) < 1e-9 && back.r.frobenius_distance(start.r) < 1e-9,
                    "{backward_label} did not undo {forward_label}: the pose is {:?} / {:?}, \
                     not {:?} / {:?}",
                    back.p,
                    back.r,
                    start.p,
                    start.r
                );
            }
        }
    }

    // --- applying -------------------------------------------------------------------

    #[test]
    fn applying_reads_every_field_and_updates_the_view_state() {
        let (mut session, mut document, mut angles) = session();
        session.dh[0][1] = String::from("55");
        session.joint_angles[4] = String::from("12.5");
        session.meshes[1].path = String::from("mesh/j1.stl");
        session.meshes[1].offset[0] = String::from("3");

        session
            .apply_from_entries(&mut document, &mut angles)
            .expect("every field is valid");
        assert_eq!(document.parameters.joints[0].d, 55.0);
        assert_eq!(angles[4], 12.5);
        assert_eq!(document.meshes[1].path, "mesh/j1.stl");
        assert_eq!(document.meshes[1].offset[0], 3.0);
        assert_eq!(session.joint_angles[4], "12.5");
    }

    #[test]
    fn applying_reports_the_joint_error_first_exactly_as_the_reference_does() {
        let (mut session, mut document, mut angles) = session();
        session.joint_angles[5] = String::from("x");
        session.dh[0][0] = String::from("y");
        assert_eq!(
            session
                .apply_from_entries(&mut document, &mut angles)
                .expect_err("both are broken")
                .message,
            "could not convert string to float: 'x'"
        );
        assert_eq!(INVALID_PARAMETERS_TITLE, "Invalid parameters");
    }

    #[test]
    fn a_failed_apply_changes_nothing() {
        let (mut session, mut document, mut angles) = session();
        let before = document.clone();
        session.meshes[6].opacity = String::from("2");
        session.joint_angles[0] = String::from("30");
        assert!(
            session
                .apply_from_entries(&mut document, &mut angles)
                .is_err()
        );
        assert_eq!(document, before);
        assert_eq!(angles, [0.0; JOINT_COUNT]);
    }

    // --- the clipboard --------------------------------------------------------------

    #[test]
    fn the_clipboard_text_has_the_reference_layout() {
        // `simulator.py:297-316`, line for line. The numbers are `%.15g`, so a whole number
        // prints without a decimal point and the zero pose prints exactly like this.
        let document = Document::shipped();
        let angles = [0.0; JOINT_COUNT];
        let text = Session::copy_xyz_text(&document.parameters, &angles).expect("shipped");
        let lines: Vec<&str> = text.split('\n').collect();
        assert_eq!(lines.len(), 15);
        assert_eq!(lines[0], "T6 position (model units):");
        assert!(lines[1].starts_with("X: 41"), "{:?}", lines[1]);
        assert!(lines[2].starts_with("Y: "), "{:?}", lines[2]);
        assert!(lines[3].starts_with("Z: 57"), "{:?}", lines[3]);
        assert_eq!(lines[4], "T6 orientation (RPY, ZYX, degrees):");
        assert!(lines[5].starts_with("Roll: "), "{:?}", lines[5]);
        assert!(lines[6].starts_with("Pitch: "), "{:?}", lines[6]);
        assert!(lines[7].starts_with("Yaw: "), "{:?}", lines[7]);
        assert_eq!(lines[8], "Runtime joint angles (degrees):");
        for joint in 0..JOINT_COUNT {
            assert_eq!(lines[9 + joint], format!("J{}: 0", joint + 1));
        }
        assert!(
            !text.ends_with('\n'),
            "the reference joins without a trailer"
        );
    }

    #[test]
    fn the_clipboard_prints_at_fifteen_significant_digits() {
        let document = Document::shipped();
        let angles = [1.0 / 3.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let text = Session::copy_xyz_text(&document.parameters, &angles).expect("shipped");
        let joint_line = text.lines().nth(9).expect("nine lines before J1");
        assert_eq!(joint_line, "J1: 0.333333333333333");
    }

    #[test]
    fn the_zero_pose_copies_the_documented_tool_origin() {
        // `d1 + a2 + d4 + d6` along +x is 32 + 25 + 25 + 6 = 88 at zero angles... but the
        // arm's frames stack along z for the first three, so the shipped arm at rest reaches
        // (41, 0, 57), the pose `docs/main_window_image.png` shows.
        let document = Document::shipped();
        let text =
            Session::copy_xyz_text(&document.parameters, &[0.0; JOINT_COUNT]).expect("shipped");
        assert_eq!(text.lines().nth(1).expect("X line"), "X: 41");
        assert_eq!(text.lines().nth(3).expect("Z line"), "Z: 57");
    }

    // --- the shared helpers ---------------------------------------------------------

    #[test]
    fn the_axis_letters_are_the_references_own() {
        // `'XYZ'[axis]` in the status strings, now carried by the axis type itself so a
        // button row cannot be wired to the wrong letter.
        assert_eq!(Axis::ALL.map(Axis::letter), ['X', 'Y', 'Z']);
        assert_eq!(Axis::ALL.map(Axis::index), [0, 1, 2]);
        assert_eq!(CLIPBOARD_PRECISION, 15);
    }

    #[test]
    fn the_rpy_extraction_matches_the_reference_including_its_gimbal_lock_branch() {
        // `simulator.py:45-58`, the extraction both the clipboard and the pose readout use.
        // `axis_rotation` takes radians and the extraction returns degrees, which is why the
        // triples below are converted on the way in and compared as they come out.
        let axis = |index: usize| Axis::from_index(index).expect("axes are 0, 1, 2");
        let pose_of = |rx: f64, ry: f64, rz: f64| {
            Pose::new(
                jog::axis_rotation(axis(2), rz.to_radians())
                    * jog::axis_rotation(axis(1), ry.to_radians())
                    * jog::axis_rotation(axis(0), rx.to_radians()),
                robot_kinematics::Vec3::zero(),
            )
        };

        for (rx, ry, rz) in [
            (0.0, 0.0, 0.0),
            (10.0, 20.0, 30.0),
            (-45.0, 15.5, 170.0),
            (80.0, -30.0, -120.0),
        ] {
            let [roll, pitch, yaw] = rotation_to_rpy_degrees(&pose_of(rx, ry, rz));
            assert!((roll - rx).abs() < 1e-9, "roll {roll} for {rx}");
            assert!((pitch - ry).abs() < 1e-9, "pitch {pitch} for {ry}");
            assert!((yaw - rz).abs() < 1e-9, "yaw {yaw} for {rz}");
        }

        // At pitch 90 degrees the first column vanishes, so the yaw is taken from the second
        // row and the roll is reported as zero. The two axes have coincided by then and only
        // their difference is recoverable: `Rz(20)·Ry(90)·Rx(35)` is the same rotation as
        // `Rz(-15)·Ry(90)`, so -15 is the answer, not 20.
        let [roll, pitch, yaw] = rotation_to_rpy_degrees(&pose_of(35.0, 90.0, 20.0));
        assert!(roll.abs() < 1e-9, "roll {roll}");
        assert!((pitch - 90.0).abs() < 1e-9, "pitch {pitch}");
        assert!((yaw + 15.0).abs() < 1e-9, "yaw {yaw}");
    }

    #[test]
    fn a_session_starts_on_the_shipped_table_with_zero_angles() {
        let (session, document, angles) = session();
        assert_eq!(document.parameters, DHParameters::shipped());
        assert_eq!(angles, [0.0; JOINT_COUNT]);
        assert_eq!(session.jog_step, "1");
        assert_eq!(session.rotation_step, "5");
        assert_eq!(session.joint_step, "5");
        assert_eq!(session.meshes.len(), MESH_COUNT);
        assert_eq!(session.meshes[0].path, "");
        assert_eq!(session.meshes[0].opacity, "1");
        assert_eq!(MESH_FRAME_NAMES[0], "Base");
    }

    /// The applied table's tool pose, through the crate's own forward kinematics.
    fn tool_position(document: &Document, angles: &[f64; JOINT_COUNT]) -> [f64; 3] {
        let pose = tool_pose_of(document, angles);
        [pose.p.x(), pose.p.y(), pose.p.z()]
    }

    /// The tool frame's whole pose, `carrier_pose`'s last entry.
    fn tool_pose_of(
        document: &Document,
        angles: &[f64; JOINT_COUNT],
    ) -> robot_kinematics::Pose<f64> {
        carrier_pose_of(document, angles)[FRAME_COUNT - 1]
    }

    fn carrier_pose_of(
        document: &Document,
        angles: &[f64; JOINT_COUNT],
    ) -> [robot_kinematics::Pose<f64>; FRAME_COUNT] {
        let geometry = document.parameters.geometry().expect("shipped");
        carrier_pose(&geometry, &document.parameters.total_angles_rad(angles))
    }
}
