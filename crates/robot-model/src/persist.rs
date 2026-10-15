//! Reading and writing `robot_parameters.json`.
//!
//! `simulator.py` is the reference for both directions: `_save_json` (lines 680-710) and
//! `_serialize_mesh_setting` (712-725) write the file, `_read_json_configuration`
//! (727-804) reads it. Three things about that format are load-bearing:
//!
//! * **Indentation and key order.** The file is `json.dumps(data, indent=2) + "\n"`, with
//!   the keys inserted in `_save_json`'s order, so a file this module writes and a file
//!   the reference writes are the same bytes. [`to_json`] reproduces that with a struct
//!   whose fields are declared in that order — `serde_json` writes a struct's fields in
//!   declaration order, while a `Value` built by hand would come out alphabetized, since
//!   its object is a map with sorted keys.
//! * **Static offsets, never runtime angles.** A joint carries the angle it is zeroed at,
//!   in degrees; the angle the arm is standing at is not in the file at all, which is why
//!   [`Document`] has no field for it and the round-trip test asserts it stays that way
//!   (`test_kinematics.py:87-90`).
//! * **Mesh paths belong to the disk, not to the file.** They are written relative to the
//!   file where they can be (712-725) and resolved back against the file's own directory
//!   on read (797-802).
//!
//! **Why the file is read through [`RawValue`] rather than `serde_json::Value`.** `Value`
//! refuses a number that overflows `f64` — `1e400` is a "number out of range" parse error
//! — and has nowhere to keep an infinity even if it did not. The reference calls `float()`
//! on every DH value and *then* checks `math.isfinite` (747-757), so a file holding
//! `1e400` has to reach that check carrying `inf` for the two to agree; `RawValue` keeps
//! each value as the text it was written as, and `f64::from_str` on that text is `float()`
//! exactly, overflow to infinity included.

use std::collections::HashMap;
use std::fmt;
use std::path::{Component, Path, PathBuf};

use serde::Serialize;
use serde_json::value::RawValue;

use crate::dh::{DHParameters, DhRow};
use crate::document::{Document, SCHEMA_VERSION, units};
use crate::mesh::MeshSettings;
use crate::{FRAME_COUNT, JOINT_COUNT};

/// The file the reference reads and writes: `simulator.py:171` puts it next to the script.
pub const FILE_NAME: &str = "robot_parameters.json";

// The reference's own sentences, character for character (`simulator.py:738-797`). They
// are written out here rather than composed, because a user who has seen one of these in
// the Python application has to see the same words in this one.
const MUST_BE_OBJECT: &str = "Parameter file must contain a JSON object.";
const BAD_SCHEMA: &str = "Unsupported parameter file schema version.";
const BAD_ANGLE_UNITS: &str = "Parameter file angles must use degrees.";
const BAD_JOINT_COUNT: &str = "Parameter file must contain exactly six joints.";
const BAD_DH_VALUE: &str = "DH parameter values must all be finite numbers.";
const BAD_MESH_EDGES: &str = "show_mesh_edges must be true or false.";
const BAD_GIZMOS: &str = "show_coordinate_gizmos must contain seven true/false values.";
const BAD_JOINT_LABELS: &str = "show_joint_labels must be true or false.";
const BAD_MESH_COUNT: &str =
    "Parameter file must contain seven mesh settings: base and joints 1-6.";
const BAD_MESH_OBJECT: &str = "Each mesh setting must be a JSON object.";
const BAD_MESH_PATH: &str = "Mesh paths must be strings.";
const BAD_MESH_OFFSET: &str = "Each mesh offset must contain exactly three values.";
const BAD_MESH_ROTATION: &str = "Each mesh rotation must contain exactly three values.";
const BAD_MESH_VALUE: &str = "Mesh offsets, rotations, and opacity must be finite numbers.";
const BAD_MESH_OPACITY: &str = "Mesh opacity must be from 0 to 1.";

/// The `joints` key's own name in the two places a joint can go wrong.
const JOINT_SCOPE: &str = "joint";
/// The `meshes` key's own name, likewise.
const MESH_SCOPE: &str = "mesh";

/// Why a configuration file could not be read or written.
///
/// `Display` produces the reference's own message wherever the reference has a fixed one,
/// so the text can go straight into an error dialog. Where the reference instead shows the
/// text of the exception it raised — `_load_json` reports with `str(error)`
/// (`simulator.py:812`) — this carries the same information in a fixed shape; the exact
/// Python wording is not reproducible there because the wording is a Python builtin's.
#[derive(Debug)]
pub enum DocumentError {
    /// The file could not be read or written: an `OSError` in the reference.
    Io(std::io::Error),
    /// The text is not JSON: a `json.JSONDecodeError` in the reference.
    ///
    /// `serde_json`'s parser is stricter than `json.loads` in one visible way: it lexes
    /// `NaN` and `Infinity` as syntax errors, where `json.loads` accepts both by default
    /// and turns them into the matching float. (Numbers that merely *overflow* the range
    /// of `f64`, such as `1e400`, are a parse error to `serde_json` too, but this module
    /// never lets it see them: read through `RawValue`, their text survives to
    /// [`parse`]'s own `float()`-equivalent, exactly as in the reference.)
    Json(serde_json::Error),
    /// A check the reference reports with one of its own sentences, reproduced here
    /// character for character.
    Invalid(&'static str),
    /// A row field the reference fails on with a `KeyError`, `TypeError` or
    /// `AttributeError` and reports by showing that exception's text: a `joints` entry
    /// that is not an object, a DH value that is missing or is not a number, or a mesh
    /// `offset`, `rotation_deg` or `opacity` that is not a number.
    Field {
        /// `"joint"` or `"mesh"`, the word the row is named by in the reference's own
        /// messages.
        scope: &'static str,
        /// The row's number, counted from 1 the way the UI counts joints.
        index: usize,
        /// The key at fault, or `None` when the row itself is not a JSON object.
        name: Option<&'static str>,
    },
}

impl fmt::Display for DocumentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => error.fmt(formatter),
            Self::Json(error) => error.fmt(formatter),
            Self::Invalid(message) => formatter.write_str(message),
            Self::Field {
                scope,
                index,
                name: Some(name),
            } => write!(
                formatter,
                "{scope} {index}: '{name}' is missing or not a number."
            ),
            Self::Field {
                scope,
                index,
                name: None,
            } => write!(formatter, "{scope} {index} is not a JSON object."),
        }
    }
}

impl std::error::Error for DocumentError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Json(error) => Some(error),
            Self::Invalid(_) | Self::Field { .. } => None,
        }
    }
}

/// This error under the name the Parameters tab's own session code reads it by.
///
/// It is the same type; the two names are both in use because the file half of the
/// crate and the session half were written against different spellings of it.
pub type LoadError = DocumentError;

/// Read a configuration file. `config_dir` is the directory relative mesh paths resolve
/// against.
pub fn load(path: &Path) -> Result<Document, DocumentError> {
    // `Path::read_text(encoding="utf-8")` (`simulator.py:736`): the file is UTF-8, and one
    // that is not reports as an `Io` error, which is what a `UnicodeDecodeError` amounts
    // to at this boundary. The reference does not create the file's directory either.
    let text = std::fs::read_to_string(path).map_err(DocumentError::Io)?;
    parse(&text, &config_dir_of(path))
}

/// Write a configuration file, relativizing mesh paths against the file's own directory.
/// The bytes written are [`to_json`]'s exactly.
pub fn save(document: &Document, path: &Path) -> Result<(), DocumentError> {
    let text = to_json(document, &config_dir_of(path))?;
    // Deliberately `fs::write` rather than a text-mode write: `Path::write_text` opens in
    // text mode, so the reference's file comes out with CRLF line endings on Windows and
    // LF everywhere else, while this writes the same bytes on every platform. Readers of
    // the file accept both; `xtask`'s goldens and the round-trip test normalize them the
    // same way.
    std::fs::write(path, text).map_err(DocumentError::Io)
}

/// Parse `robot_parameters.json` text. `config_dir` is the directory of the file the text
/// came from, which is what relative mesh paths resolve against.
pub fn parse(text: &str, config_dir: &Path) -> Result<Document, DocumentError> {
    // The whole document first, as raw text per value. The order of the checks below is
    // the reference's (`simulator.py:736-804`), and it is observable: a file that gets
    // `units` and `joints` wrong reports the units.
    let root = serde_json::from_str::<&RawValue>(text).map_err(DocumentError::Json)?;
    let Some(file) = object(root) else {
        return Err(DocumentError::Invalid(MUST_BE_OBJECT));
    };

    // `data.get("schema_version") != 1`: Python compares numbers, so the JSON `1.0` is the
    // same version, and so is `1e0`. Python would also accept `true`, since `True == 1`;
    // a boolean is not a number in this JSON model, so it is rejected — the one place
    // where the check is stricter than the reference's.
    if number_field(&file, "schema_version") != Some(f64::from(SCHEMA_VERSION)) {
        return Err(DocumentError::Invalid(BAD_SCHEMA));
    }

    // `units` has to be an object whose `angles` is "degrees". `units.lengths` is not
    // read at all (`simulator.py:741-743`), and neither is any other key.
    let angles_are_degrees = file
        .get("units")
        .and_then(|raw| object(raw))
        .and_then(|block| block.get("angles").and_then(|raw| string(raw)))
        .is_some_and(|angles| angles == units::ANGLES);
    if !angles_are_degrees {
        return Err(DocumentError::Invalid(BAD_ANGLE_UNITS));
    }

    let Some(joints) = file.get("joints").and_then(|raw| array(raw)) else {
        return Err(DocumentError::Invalid(BAD_JOINT_COUNT));
    };
    if joints.len() != JOINT_COUNT {
        return Err(DocumentError::Invalid(BAD_JOINT_COUNT));
    }
    let mut rows = [DhRow::ZERO; JOINT_COUNT];
    for (index, joint) in joints.iter().enumerate() {
        rows[index] = joint_row(joint, index)?;
    }
    // The finiteness check comes after every joint has been read, as it does in the
    // reference: a file with both a missing `d` and a `1e400` reports the missing `d`
    // (`simulator.py:747-757`).
    let finite = rows.iter().all(|row| {
        [row.theta_offset_deg, row.d, row.a, row.alpha_deg]
            .iter()
            .all(|value| value.is_finite())
    });
    if !finite {
        return Err(DocumentError::Invalid(BAD_DH_VALUE));
    }

    // The three display flags are read before `meshes` is looked at. An explicit `null` is
    // a value, not a missing key, so it takes the error path rather than the default
    // (`dict.get` semantics, `simulator.py:760-773`).
    let show_mesh_edges = match file.get("show_mesh_edges") {
        None => false,
        Some(raw) => boolean(raw).ok_or(DocumentError::Invalid(BAD_MESH_EDGES))?,
    };
    let show_coordinate_gizmos = match file.get("show_coordinate_gizmos") {
        None => [true; FRAME_COUNT],
        Some(raw) => {
            let visible = array(raw).ok_or(DocumentError::Invalid(BAD_GIZMOS))?;
            if visible.len() != FRAME_COUNT {
                return Err(DocumentError::Invalid(BAD_GIZMOS));
            }
            let mut flags = [false; FRAME_COUNT];
            for (flag, value) in flags.iter_mut().zip(&visible) {
                *flag = boolean(value).ok_or(DocumentError::Invalid(BAD_GIZMOS))?;
            }
            flags
        }
    };
    let show_joint_labels = match file.get("show_joint_labels") {
        None => true,
        Some(raw) => boolean(raw).ok_or(DocumentError::Invalid(BAD_JOINT_LABELS))?,
    };

    let meshes = match file.get("meshes") {
        // A missing `meshes` key and an explicit `null` both mean "the defaults"
        // (`simulator.py:774-775`); a `meshes` that is present as a list has to have all
        // seven entries, so the defaults cannot be had by handing over a shorter list.
        None => core::array::from_fn(|_| MeshSettings::default()),
        Some(raw) if is_null(raw) => core::array::from_fn(|_| MeshSettings::default()),
        Some(raw) => {
            let entries = array(raw).ok_or(DocumentError::Invalid(BAD_MESH_COUNT))?;
            if entries.len() != FRAME_COUNT {
                return Err(DocumentError::Invalid(BAD_MESH_COUNT));
            }
            let mut settings = core::array::from_fn(|_| MeshSettings::default());
            for (index, entry) in entries.iter().enumerate() {
                settings[index] = mesh_setting(entry, index, config_dir)?;
            }
            settings
        }
    };

    Ok(Document {
        schema_version: SCHEMA_VERSION,
        show_mesh_edges,
        show_coordinate_gizmos,
        show_joint_labels,
        parameters: DHParameters::new(rows),
        meshes,
    })
}

/// Render a document as the file's bytes: `json.dumps(data, indent=2) + "\n"`.
pub fn to_json(document: &Document, config_dir: &Path) -> Result<String, DocumentError> {
    // `json.dumps` writes a non-finite float as `NaN` or `Infinity`, which is not JSON;
    // `serde_json` writes `null`, which is valid JSON and silently loses the value. This
    // refuses instead, with the sentence the reference uses for the same values on read,
    // so a document that cannot be written honestly is reported rather than quietly
    // damaged. Nothing in this crate produces such a value from a file.
    let finite = document.parameters.joints.iter().all(|row| {
        [row.theta_offset_deg, row.d, row.a, row.alpha_deg]
            .iter()
            .all(|value| value.is_finite())
    });
    if !finite {
        return Err(DocumentError::Invalid(BAD_DH_VALUE));
    }

    let mut meshes = Vec::with_capacity(crate::MESH_COUNT);
    for setting in &document.meshes {
        let finite = setting
            .offset
            .iter()
            .chain(&setting.rotation_deg)
            .chain(core::iter::once(&setting.opacity))
            .all(|value| value.is_finite());
        if !finite {
            return Err(DocumentError::Invalid(BAD_MESH_VALUE));
        }
        meshes.push(FileMesh {
            path: stored_mesh_path(&setting.path, config_dir)?,
            offset: setting.offset,
            rotation_deg: setting.rotation_deg,
            opacity: setting.opacity,
        });
    }

    let file = FileRoot {
        schema_version: document.schema_version,
        units: FileUnits {
            angles: units::ANGLES,
            lengths: units::LENGTHS,
        },
        show_mesh_edges: document.show_mesh_edges,
        show_coordinate_gizmos: document.show_coordinate_gizmos,
        show_joint_labels: document.show_joint_labels,
        joints: document.parameters.joints.map(|row| FileJoint {
            theta_offset_deg: row.theta_offset_deg,
            d: row.d,
            a: row.a,
            alpha_deg: row.alpha_deg,
        }),
        meshes,
    };
    let mut text = serde_json::to_string_pretty(&file).map_err(DocumentError::Json)?;
    text.push('\n');
    Ok(text)
}

impl Document {
    /// Parse `robot_parameters.json` text, with relative mesh paths taken as relative to
    /// the current directory.
    ///
    /// A file's own directory is not something its text knows, so this is as much of
    /// `_read_json_configuration` as can be had without one. [`Document::load`] has the
    /// path and uses the file's directory, which is what the reference does; reach for
    /// [`parse`] when the directory is known to be something else.
    pub fn from_json(text: &str) -> Result<Self, DocumentError> {
        crate::persist::parse(text, Path::new("."))
    }

    /// The bytes [`save`] would write, with mesh paths relative to `base_dir`.
    pub fn to_json(&self, base_dir: &Path) -> Result<String, DocumentError> {
        crate::persist::to_json(self, base_dir)
    }

    /// Read this document from `path`, resolving mesh paths against the file's directory.
    pub fn load(path: &Path) -> Result<Self, DocumentError> {
        crate::persist::load(path)
    }

    /// Write this document to `path`, relativizing mesh paths against the file's directory.
    pub fn save(&self, path: &Path) -> Result<(), DocumentError> {
        crate::persist::save(self, path)
    }
}

/// The file's shape, in `_save_json`'s key order (`simulator.py:688-699`).
///
/// Field order is the format: `json.dumps` writes a dict in insertion order and
/// `serde_json` writes a struct in declaration order, so this is what keeps a saved file
/// diff-free against one the reference wrote.
#[derive(Serialize)]
struct FileRoot {
    schema_version: u32,
    units: FileUnits,
    show_mesh_edges: bool,
    show_coordinate_gizmos: [bool; FRAME_COUNT],
    show_joint_labels: bool,
    joints: [FileJoint; JOINT_COUNT],
    meshes: Vec<FileMesh>,
}

/// The `units` block, which is documentation rather than data: the reader checks only
/// `angles` and the writer always writes both strings as they are.
#[derive(Serialize)]
struct FileUnits {
    angles: &'static str,
    lengths: &'static str,
}

/// One DH row as the file spells it. `theta_offset_deg` is the static zero angle; the
/// runtime angle is not written at all.
#[derive(Serialize)]
struct FileJoint {
    theta_offset_deg: f64,
    d: f64,
    a: f64,
    alpha_deg: f64,
}

/// One mesh setting as the file spells it.
#[derive(Serialize)]
struct FileMesh {
    path: String,
    offset: [f64; 3],
    rotation_deg: [f64; 3],
    opacity: f64,
}

/// One row of the `joints` array (`simulator.py:747-755`).
fn joint_row(raw: &RawValue, index: usize) -> Result<DhRow, DocumentError> {
    let Some(joint) = object(raw) else {
        // The reference reaches an `AttributeError` here — `joint.get(...)` on something
        // that is not a dict — and the handler at `simulator.py:812` does not catch that,
        // so it dies rather than reporting. There is no message to match, so this names
        // the row instead.
        return Err(DocumentError::Field {
            scope: JOINT_SCOPE,
            index: index + 1,
            name: None,
        });
    };
    // `joint.get("theta_offset_deg", joint.get("theta_deg"))`: `theta_deg` is the old
    // spelling of the same static offset and is still read, though never written. The
    // fallback is on the key being *absent*: an explicit `null` under either name is a
    // value, and is reported rather than skipped over.
    let theta = joint
        .get("theta_offset_deg")
        .or_else(|| joint.get("theta_deg"))
        .copied();
    Ok(DhRow::new(
        joint_value(theta, index, "theta_offset_deg")?,
        joint_value(joint.get("d").copied(), index, "d")?,
        joint_value(joint.get("a").copied(), index, "a")?,
        joint_value(joint.get("alpha_deg").copied(), index, "alpha_deg")?,
    ))
}

/// One DH value, or the row and key it is missing from.
fn joint_value(
    value: Option<&RawValue>,
    index: usize,
    key: &'static str,
) -> Result<f64, DocumentError> {
    value.and_then(number).ok_or(DocumentError::Field {
        scope: JOINT_SCOPE,
        index: index + 1,
        name: Some(key),
    })
}

/// One entry of the `meshes` array (`simulator.py:779-803`).
fn mesh_setting(
    raw: &RawValue,
    index: usize,
    config_dir: &Path,
) -> Result<MeshSettings, DocumentError> {
    let Some(mesh) = object(raw) else {
        return Err(DocumentError::Invalid(BAD_MESH_OBJECT));
    };
    let path = match mesh.get("path") {
        None => String::new(),
        Some(raw) => string(raw).ok_or(DocumentError::Invalid(BAD_MESH_PATH))?,
    };
    let offset = mesh_vector(
        mesh.get("offset").copied(),
        index,
        "offset",
        BAD_MESH_OFFSET,
    )?;
    let rotation_deg = mesh_vector(
        mesh.get("rotation_deg").copied(),
        index,
        "rotation_deg",
        BAD_MESH_ROTATION,
    )?;
    let opacity = match mesh.get("opacity") {
        None => 1.0,
        Some(raw) => number(raw).ok_or(DocumentError::Field {
            scope: MESH_SCOPE,
            index: index + 1,
            name: Some("opacity"),
        })?,
    };
    let finite = offset
        .iter()
        .chain(&rotation_deg)
        .chain(core::iter::once(&opacity))
        .all(|value| value.is_finite());
    if !finite {
        return Err(DocumentError::Invalid(BAD_MESH_VALUE));
    }
    // The range check comes after the finiteness one, so an opacity of `NaN` is reported
    // as non-finite rather than as out of range (`simulator.py:794-797`).
    if !(0.0..=1.0).contains(&opacity) {
        return Err(DocumentError::Invalid(BAD_MESH_OPACITY));
    }
    let path = if path.is_empty() {
        String::new()
    } else {
        resolved_mesh_path(&path, config_dir)?
    };
    Ok(MeshSettings {
        path,
        offset,
        rotation_deg,
        opacity,
    })
}

/// Three numbers out of a mesh's `offset` or `rotation_deg`.
fn mesh_vector(
    value: Option<&RawValue>,
    index: usize,
    key: &'static str,
    shape_message: &'static str,
) -> Result<[f64; 3], DocumentError> {
    let Some(raw) = value else {
        return Ok([0.0; 3]);
    };
    let Some(values) = array(raw) else {
        return Err(DocumentError::Invalid(shape_message));
    };
    if values.len() != 3 {
        return Err(DocumentError::Invalid(shape_message));
    }
    let mut vector = [0.0; 3];
    for (slot, raw) in vector.iter_mut().zip(&values) {
        *slot = number(raw).ok_or(DocumentError::Field {
            scope: MESH_SCOPE,
            index: index + 1,
            name: Some(key),
        })?;
    }
    Ok(vector)
}

/// Where a mesh path in the file points, as an absolute path.
///
/// `simulator.py:798-802` expands `~`, puts the configuration file's directory in front of
/// a relative path, and calls `Path.resolve()`. `resolve()` also follows symlinks and, on
/// Windows, lowercases the drive letter; neither is reproduced here, because both mean
/// touching the filesystem to answer what a path *means*, and a path in a configuration
/// file has to be readable without the file it names existing. The difference shows up
/// only for a path whose middle is a symlink.
fn resolved_mesh_path(stored: &str, config_dir: &Path) -> Result<String, DocumentError> {
    let expanded = expand_home(stored);
    let joined = if expanded.is_absolute() {
        expanded
    } else {
        config_dir.join(expanded)
    };
    Ok(path_text(&anchor(&joined)?))
}

/// A mesh path as the file stores it: relative to the file's own directory when it is
/// inside it, absolute otherwise, always with forward slashes.
///
/// `_serialize_mesh_setting` (712-725) resolves the path, takes it relative to the file's
/// directory — a purely lexical question, on paths that have both been resolved first —
/// and falls back to the absolute path when that fails. `.as_posix()` is why the relative
/// form uses forward slashes on Windows as well; the absolute fallback is
/// `str(mesh_path)`, which keeps whatever separators the platform uses.
///
/// Note the asymmetry with [`resolved_mesh_path`], which is the reference's own: a
/// *relative* path in the document resolves against the current directory when writing
/// (`Path(path).resolve()`, line 715) and against the file's directory when reading
/// (line 801, which joins first). A document read by either implementation holds absolute
/// paths, so the difference only shows for one built by hand.
fn stored_mesh_path(stored: &str, config_dir: &Path) -> Result<String, DocumentError> {
    if stored.is_empty() {
        return Ok(String::new());
    }
    let absolute = anchor(&expand_home(stored))?;
    let directory = anchor(config_dir)?;
    // `strip_prefix` compares whole components, so `..` cannot smuggle a path in from
    // above the directory and a sibling whose name merely starts the same does not
    // qualify. It is case-sensitive where Python's `relative_to` is too, and the drive
    // letter is left as written where `resolve()` would have lowercased both sides.
    match absolute.strip_prefix(&directory) {
        Ok(relative) => Ok(relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<String>>()
            .join("/")),
        Err(_) => Ok(path_text(&absolute)),
    }
}

/// An absolute, `.`- and `..`-free path, without looking at the filesystem.
///
/// `Path::absolute` is the honest counterpart of the filesystem-free half of
/// `Path.resolve()`: it anchors a relative path at the current directory and drops `.`
/// components (unlike `canonicalize`, which would need the path to exist).
fn anchor(path: &Path) -> Result<PathBuf, DocumentError> {
    let absolute = std::path::absolute(path).map_err(DocumentError::Io)?;
    Ok(normalize(&absolute))
}

/// The same path with every `.` removed and every `..` applied to the name before it.
fn normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                // `PathBuf::pop` refuses to climb past a root or a prefix, and there is
                // always one of those in front by the time anything gets here, so a `..`
                // that cannot be applied survives as `..` rather than being dropped.
                if !normalized.pop() {
                    normalized.push(component.as_os_str());
                }
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                normalized.push(component.as_os_str());
            }
        }
    }
    normalized
}

/// A path as text.
///
/// Paths in the document are strings, so anything that got here is UTF-8 unless the
/// configuration directory it was joined to was not; a Windows path that is not valid
/// UTF-8 loses its odd characters rather than failing the save.
fn path_text(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

/// `Path.expanduser()`, for the one form that does not need a user database.
///
/// `~` on its own and `~/...` become the home directory; `~someone/...` is left alone,
/// because expanding it means looking the user up and a wrong home directory is worse
/// than a path that visibly does not exist. `expanduser()` reads `HOME` on POSIX and
/// `USERPROFILE` on Windows; with neither set it returns the path unchanged, and so does
/// this.
fn expand_home(path: &str) -> PathBuf {
    let Some(rest) = path.strip_prefix('~') else {
        return PathBuf::from(path);
    };
    if !(rest.is_empty() || rest.starts_with('/') || rest.starts_with('\\')) {
        return PathBuf::from(path);
    }
    let home = std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"));
    let Some(home) = home else {
        return PathBuf::from(path);
    };
    let rest = rest.trim_start_matches(['/', '\\']);
    if rest.is_empty() {
        return PathBuf::from(home);
    }
    Path::new(&home).join(rest)
}

/// The directory a configuration file lives in, which is what stored paths are relative
/// to.
///
/// `Path::parent()` of a bare file name is empty where `Path("name.json").parent` is `.`,
/// so that case is spelled out: an empty parent means the current directory.
fn config_dir_of(path: &Path) -> PathBuf {
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
        _ => PathBuf::from("."),
    }
}

/// The fields of one JSON object.
type RawObject<'a> = HashMap<String, &'a RawValue>;

// The accessors below each re-read their own subtree's text with `serde_json`. The
// document is a few hundred bytes and it is read once per load or save, so the extra
// passes are not worth a hand-written visitor; what they buy is that every question about
// a value is answered with the *text* the file held, which is the only place a number
// like `1e400` still exists.

/// The fields of a JSON object, or `None` for any other kind of value.
fn object(raw: &RawValue) -> Option<RawObject<'_>> {
    serde_json::from_str(raw.get()).ok()
}

/// The elements of a JSON array, or `None` for any other kind of value.
fn array(raw: &RawValue) -> Option<Vec<&RawValue>> {
    serde_json::from_str(raw.get()).ok()
}

/// A JSON string, unescaped, or `None` for any other kind of value.
fn string(raw: &RawValue) -> Option<String> {
    serde_json::from_str(raw.get()).ok()
}

/// A JSON boolean, or `None` for any other kind of value — including `1`, which Python's
/// `isinstance(visible, bool)` also rejects.
fn boolean(raw: &RawValue) -> Option<bool> {
    serde_json::from_str(raw.get()).ok()
}

/// Whether the value is the JSON literal `null`.
///
/// `()` deserializes from `null` and from nothing else, which is how serde spells "this
/// value is null"; a `Value` would say so directly, but a `Value` cannot hold the numbers
/// this module has to keep.
fn is_null(raw: &RawValue) -> bool {
    serde_json::from_str::<()>(raw.get()).is_ok()
}

/// A JSON number, read the way the reference reads it.
///
/// `f64::from_str` on the number's own text is `float()`'s result, overflow included: a
/// file holding `1e400` yields `inf` here, which is what makes the two finiteness checks
/// reachable.
///
/// Deviation: the reference wraps these in `float()`, which also accepts the *strings*
/// `"40"` and the booleans (`float(True)` is `1.0`). A file the reference's own save wrote
/// never contains either, and accepting them here would let a typo such as `"d": "40 mm"`
/// travel further than it should, so this takes JSON numbers only.
fn number(raw: &RawValue) -> Option<f64> {
    raw.get().trim().parse().ok()
}

/// One named number out of an object.
fn number_field(file: &RawObject<'_>, key: &str) -> Option<f64> {
    file.get(key).and_then(|raw| number(raw))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;

    /// The repository root, which is where `robot_parameters.json` ships.
    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    /// The shipped file's text, with the working copy's line endings normalized.
    fn shipped_text() -> String {
        // The file on Windows has CRLF endings because the reference writes it with
        // `Path.write_text`, which is text mode; the bytes the reference *builds* are
        // `json.dumps(data, indent=2) + "\n"`, and that is what this module has to
        // reproduce, so the comparison is made against the LF form.
        include_str!("../../../robot_parameters.json").replace("\r\n", "\n")
    }

    /// One DH row as [`text`] writes it: all zeroes, so a test can swap one value out.
    const JOINT: &str = r#"{"theta_offset_deg": 0, "d": 0, "a": 0, "alpha_deg": 0}"#;

    /// A minimal valid file as text: `count` zero joints and no `meshes` key, so every
    /// optional field lands on the reference's default.
    fn text(joints: usize) -> String {
        format!(
            r#"{{"schema_version": 1, "units": {{"angles": "degrees"}}, "joints": [{}]}}"#,
            vec![JOINT; joints].join(", ")
        )
    }

    /// [`text`] with one more top-level field, added at the front. The reference looks
    /// every field up by name, so where a field sits in the object does not matter.
    fn with_field(field: &str) -> String {
        text(6).replacen('{', &format!("{{{field},"), 1)
    }

    /// [`text`] with a `meshes` array of `count` entries: the first is `base`, the rest are
    /// empty. A count that is not seven is what `BAD_MESH_COUNT` is about — leaving the
    /// key out entirely is the way to ask for the defaults.
    fn text_with_meshes(joints: usize, count: usize, base: &str) -> String {
        let empty = r#"{"path": ""}"#;
        let mut entries = String::from(base);
        for _ in 1..count {
            entries.push_str(", ");
            entries.push_str(empty);
        }
        text(joints).replacen('{', &format!(r#"{{"meshes": [{entries}],"#), 1)
    }

    /// Parse `text` and expect one of the reference's sentences back, word for word.
    fn expect_message(text: &str, message: &str) {
        match parse(text, &repo_root()) {
            Ok(document) => panic!("expected {message:?}, parsed {document:?}"),
            Err(error) => assert_eq!(error.to_string(), message),
        }
    }

    /// A directory under the system temp directory that no other test is using.
    fn unique_temp_dir(label: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("the system clock is after 1970")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "robot-model-{label}-{}-{nanos}",
            std::process::id()
        ))
    }

    #[test]
    fn the_shipped_file_round_trips_byte_for_byte() {
        let shipped = shipped_text();
        let root = repo_root();
        let document = parse(&shipped, &root).expect("the shipped file parses");
        assert_eq!(document, Document::shipped(), "the shipped document");
        let written = to_json(&document, &root).expect("the shipped document serializes");
        assert_eq!(written, shipped, "byte for byte");
    }

    #[test]
    fn the_file_never_carries_a_runtime_joint_angle() {
        // `test_kinematics.py:89-90` asserts all of this about the file the reference
        // writes, and it has to stay true of this one: `document` has no field for a
        // runtime angle, and neither does the file.
        let written = to_json(&Document::shipped(), &repo_root()).expect("serialize");
        assert!(!written.contains("joint_angle_deg"));
        assert!(!written.contains("\"theta_deg\""));
        assert!(written.contains("\"theta_offset_deg\""));
        assert!(written.ends_with("}\n"), "one trailing newline");
        assert!(!written.contains('\r'), "LF endings");
    }

    #[test]
    fn a_legacy_theta_deg_key_is_read_as_the_static_offset() {
        let legacy = shipped_text().replace("\"theta_offset_deg\"", "\"theta_deg\"");
        let document = parse(&legacy, &repo_root()).expect("the legacy spelling parses");
        assert_eq!(document, Document::shipped(), "the same document");
        let written = to_json(&document, &repo_root()).expect("serialize");
        assert!(written.contains("\"theta_offset_deg\": 90.0"));
        assert!(
            !written.contains("\"theta_deg\""),
            "written under the new key only"
        );
    }

    #[test]
    fn a_relative_mesh_path_is_resolved_on_read_and_written_back_relative() {
        let root = repo_root();
        let text = text_with_meshes(6, 7, r#"{"path": "mesh/arm.stl"}"#);
        let document = parse(&text, &root).expect("parse");
        let expected = anchor(&root.join("mesh/arm.stl")).expect("anchor");
        assert_eq!(Path::new(&document.meshes[0].path), expected);
        assert!(document.meshes[0].path.ends_with("arm.stl"));
        let written = to_json(&document, &root).expect("serialize");
        assert!(
            written.contains(r#""path": "mesh/arm.stl""#),
            "relative with forward slashes: {written}"
        );
        // The other six frames keep the empty path they were given.
        assert_eq!(written.matches(r#""path": """#).count(), 6);
    }

    #[test]
    fn a_mesh_path_outside_the_configuration_directory_is_written_absolute() {
        // The temp directory is not under the crate directory, and on any platform they
        // are different branches of the tree.
        let config_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let outside = std::env::temp_dir().join("robot-model-outside.stl");
        let mut document = Document::shipped();
        document.meshes[0].path = path_text(&outside);
        let written = to_json(&document, config_dir).expect("serialize");
        let literal = serde_json::to_string(&document.meshes[0].path).expect("escape");
        assert!(written.contains(&literal), "absolute: {written}");
        let reloaded = parse(&written, config_dir).expect("parse");
        assert_eq!(reloaded.meshes[0].path, document.meshes[0].path);
    }

    #[test]
    fn a_relative_path_in_a_document_is_anchored_at_the_current_directory_on_write() {
        // The other half of the reference's asymmetry: writing resolves a relative path
        // against the current directory (line 715) and only then asks whether it is inside
        // the file's directory, while reading joins it to the file's directory first
        // (line 801, covered above). Since the file's directory here is the current
        // directory's parent, the two rules disagree about the target: the current
        // directory rule gives <cwd>/mesh/arm.stl — inside the parent, so stored relative
        // to it, which is `<cwd's name>/mesh/arm.stl` with forward slashes — where joining
        // first would give "mesh/arm.stl" and a different file. The expectation is built
        // from the current directory's name rather than from its path, so it does not
        // depend on where the crate happens to be checked out.
        let current = std::env::current_dir().expect("a current directory");
        let config_dir = current.parent().expect("the crate directory has a parent");
        let name = current
            .file_name()
            .expect("the crate directory has a name")
            .to_string_lossy();
        let mut document = Document::shipped();
        document.meshes[0].path = "mesh/arm.stl".to_string();
        let written = to_json(&document, config_dir).expect("serialize");
        let literal = serde_json::to_string(&format!("{name}/mesh/arm.stl")).expect("escape");
        assert!(written.contains(&literal), "current directory: {written}");
    }

    #[test]
    fn a_tilde_is_expanded_on_read_and_the_home_itself_stays_absolute() {
        let Some(home) = std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"))
        else {
            // Without a home directory the reference leaves the tilde alone, which the
            // other half of this test covers.
            let config_dir = repo_root();
            let text = text_with_meshes(6, 7, r#"{"path": "~/arm.stl"}"#);
            let document = parse(&text, &config_dir).expect("parse");
            assert_eq!(document.meshes[0].path, "~/arm.stl");
            return;
        };
        let config_dir = repo_root();
        let text = text_with_meshes(6, 7, r#"{"path": "~/arm.stl"}"#);
        let document = parse(&text, &config_dir).expect("parse");
        let expected = anchor(&Path::new(&home).join("arm.stl")).expect("anchor");
        assert_eq!(Path::new(&document.meshes[0].path), expected);
        // A path that is not this user's home is not touched: `expanduser()` looks the
        // user up, and this does not guess.
        let other = text_with_meshes(6, 7, r#"{"path": "~someone/arm.stl"}"#);
        let document = parse(&other, &config_dir).expect("parse");
        assert_eq!(
            Path::new(&document.meshes[0].path),
            anchor(&config_dir.join("~someone/arm.stl")).expect("anchor")
        );
    }

    #[test]
    fn a_missing_meshes_key_means_seven_default_settings() {
        let document = parse(&text(6), &repo_root()).expect("parse");
        assert_eq!(document.meshes.len(), 7);
        assert!(
            document
                .meshes
                .iter()
                .all(|mesh| *mesh == MeshSettings::default())
        );
        // An explicit null is the same as leaving the key out (`simulator.py:774`).
        let document = parse(&with_field(r#""meshes": null"#), &repo_root()).expect("parse");
        assert!(
            document
                .meshes
                .iter()
                .all(|mesh| *mesh == MeshSettings::default())
        );
    }

    #[test]
    fn the_optional_flags_default_the_way_the_reference_defaults_them() {
        let document = parse(&text(6), &repo_root()).expect("parse");
        assert!(!document.show_mesh_edges);
        assert!(document.show_joint_labels);
        assert_eq!(document.show_coordinate_gizmos, [true; FRAME_COUNT]);
        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert_eq!(
            document.parameters,
            crate::DHParameters::new([DhRow::ZERO; 6])
        );
    }

    #[test]
    fn the_flags_that_are_present_are_read() {
        let text = with_field(r#""show_mesh_edges": true, "show_joint_labels": false"#);
        let text = text.replacen(
            '{',
            r#"{"show_coordinate_gizmos": [false, true, true, true, true, true, false],"#,
            1,
        );
        let document = parse(&text, &repo_root()).expect("parse");
        assert!(document.show_mesh_edges);
        assert!(!document.show_joint_labels);
        assert!(!document.show_coordinate_gizmos[0]);
        assert!(document.show_coordinate_gizmos[3]);
        assert!(!document.show_coordinate_gizmos[6]);
    }

    #[test]
    fn the_top_level_must_be_an_object() {
        expect_message("[]", MUST_BE_OBJECT);
        expect_message("\"joints\"", MUST_BE_OBJECT);
        expect_message("5", MUST_BE_OBJECT);
        // `serde_json`'s own failures keep `serde_json`'s own text, which is as close as
        // an `OSError`-style message can come to `json.JSONDecodeError`'s.
        assert!(matches!(
            parse("{", &repo_root()),
            Err(DocumentError::Json(_))
        ));
        assert!(matches!(
            parse("", &repo_root()),
            Err(DocumentError::Json(_))
        ));
    }

    #[test]
    fn the_schema_version_must_be_one() {
        expect_message(
            &text(6).replace("\"schema_version\": 1", "\"schema_version\": 2"),
            BAD_SCHEMA,
        );
        expect_message(
            &text(6).replace("\"schema_version\": 1", "\"schema_version\": \"1\""),
            BAD_SCHEMA,
        );
        // `data.get("schema_version") != 1` is a numeric comparison, so the JSON `1.0` is
        // the same version.
        let decimal = text(6).replace("\"schema_version\": 1", "\"schema_version\": 1.0");
        assert!(parse(&decimal, &repo_root()).is_ok());
    }

    #[test]
    fn the_angles_must_be_in_degrees() {
        expect_message(
            &text(6).replace("\"angles\": \"degrees\"", "\"angles\": \"radians\""),
            BAD_ANGLE_UNITS,
        );
        // A missing or non-object `units` is the same sentence, and `lengths` is not read.
        expect_message(
            &text(6).replace(r#""units": {"angles": "degrees"}, "#, ""),
            BAD_ANGLE_UNITS,
        );
        expect_message(
            &text(6).replace(r#"{"angles": "degrees"}"#, "\"degrees\""),
            BAD_ANGLE_UNITS,
        );
        let other_lengths = text(6).replace("\"degrees\"", "\"degrees\", \"lengths\": \"m\"");
        assert!(parse(&other_lengths, &repo_root()).is_ok());
    }

    #[test]
    fn there_must_be_exactly_six_joints() {
        for count in [0, 5, 7] {
            expect_message(&text(count), BAD_JOINT_COUNT);
        }
        // Not a list at all is the same sentence.
        expect_message(
            &text(6).replace(
                "\"joints\": [",
                "\"joints\": \"six of them\", \"ignored\": [",
            ),
            BAD_JOINT_COUNT,
        );
    }

    #[test]
    fn every_dh_value_must_be_a_finite_number() {
        // `1e400` is `inf` to `float()` and stays `inf` here, so the check is the one that
        // reports it rather than the parser.
        for key in ["theta_offset_deg", "d", "a", "alpha_deg"] {
            let broken =
                text(6).replacen(&format!("\"{key}\": 0"), &format!("\"{key}\": 1e400"), 1);
            expect_message(&broken, BAD_DH_VALUE);
            // The row loses the key entirely, which is a different failure from a value
            // that is not a number and is reported by name.
            let removal = if key == "theta_offset_deg" {
                format!("\"{key}\": 0, ")
            } else {
                format!(", \"{key}\": 0")
            };
            let missing = text(6).replacen(&removal, "", 1);
            match parse(&missing, &repo_root()) {
                Err(error) => assert!(
                    matches!(error, DocumentError::Field { name: Some(name), .. } if name == key),
                    "{key}: {error}"
                ),
                Ok(_) => panic!("{key} is required"),
            }
        }
        // A joint that is not an object is reported by row: the reference dies on an
        // `AttributeError` here, so there is no sentence of its own to match.
        let not_an_object = text(6).replacen(JOINT, "5", 1);
        match parse(&not_an_object, &repo_root()) {
            Err(error) => assert_eq!(error.to_string(), "joint 1 is not a JSON object."),
            Ok(_) => panic!("a joint has to be an object"),
        }
        // Deviation: `float()` also takes strings and booleans, so the reference reads
        // `"40"` as 40 degrees; this takes JSON numbers only.
        let quoted = text(6).replacen(r#""d": 0"#, r#""d": "40""#, 1);
        match parse(&quoted, &repo_root()) {
            Err(error) => assert_eq!(
                error.to_string(),
                "joint 1: 'd' is missing or not a number."
            ),
            Ok(_) => panic!("a quoted number is not a number"),
        }
    }

    #[test]
    fn a_missing_dh_value_names_the_row_and_the_key() {
        // The reference raises `KeyError('d')` here and shows the key's name; this names
        // the row as well, which it has and the reference's message does not.
        let missing = text(6).replacen(", \"d\": 0", "", 1);
        match parse(&missing, &repo_root()) {
            Err(error) => assert_eq!(
                error.to_string(),
                "joint 1: 'd' is missing or not a number."
            ),
            Ok(_) => panic!("d is required"),
        }
        let null = text(6).replacen(r#""d": 0"#, r#""d": null"#, 1);
        match parse(&null, &repo_root()) {
            Err(error) => assert_eq!(
                error.to_string(),
                "joint 1: 'd' is missing or not a number."
            ),
            Ok(_) => panic!("null is not a number"),
        }
        // The legacy key is only consulted when the new one is absent, so an explicit
        // null is a value rather than a reason to fall back.
        let both = text(6).replacen(
            "\"theta_offset_deg\": 0",
            "\"theta_offset_deg\": null, \"theta_deg\": 5",
            1,
        );
        match parse(&both, &repo_root()) {
            Err(error) => assert_eq!(
                error.to_string(),
                "joint 1: 'theta_offset_deg' is missing or not a number."
            ),
            Ok(_) => panic!("null is not a number"),
        }
    }

    #[test]
    fn the_display_flags_must_be_booleans() {
        expect_message(&with_field(r#""show_mesh_edges": 1"#), BAD_MESH_EDGES);
        expect_message(&with_field(r#""show_mesh_edges": null"#), BAD_MESH_EDGES);
        expect_message(
            &with_field(r#""show_joint_labels": "yes""#),
            BAD_JOINT_LABELS,
        );
        expect_message(&with_field(r#""show_joint_labels": 0"#), BAD_JOINT_LABELS);
    }

    #[test]
    fn the_gizmo_flags_must_be_seven_booleans() {
        expect_message(
            &with_field(r#""show_coordinate_gizmos": [true, true, true, true, true, true]"#),
            BAD_GIZMOS,
        );
        expect_message(
            &with_field(
                r#""show_coordinate_gizmos": [true, true, true, true, true, true, true, true]"#,
            ),
            BAD_GIZMOS,
        );
        expect_message(&with_field(r#""show_coordinate_gizmos": 1"#), BAD_GIZMOS);
        // `isinstance(visible, bool)` is false for `1`, and so is this.
        expect_message(
            &with_field(r#""show_coordinate_gizmos": [1, 1, 1, 1, 1, 1, 1]"#),
            BAD_GIZMOS,
        );
    }

    #[test]
    fn the_meshes_array_must_have_seven_entries() {
        expect_message(&text_with_meshes(6, 6, r#"{"path": ""}"#), BAD_MESH_COUNT);
        expect_message(&with_field(r#""meshes": []"#), BAD_MESH_COUNT);
        expect_message(&with_field(r#""meshes": {"base": {}}"#), BAD_MESH_COUNT);
    }

    #[test]
    fn every_mesh_entry_must_be_an_object() {
        expect_message(
            &text_with_meshes(6, 7, r#""not an object""#),
            BAD_MESH_OBJECT,
        );
        expect_message(&text_with_meshes(6, 7, "5"), BAD_MESH_OBJECT);
        expect_message(&text_with_meshes(6, 7, "[]"), BAD_MESH_OBJECT);
    }

    #[test]
    fn a_mesh_path_must_be_a_string() {
        expect_message(&text_with_meshes(6, 7, r#"{"path": 5}"#), BAD_MESH_PATH);
        expect_message(&text_with_meshes(6, 7, r#"{"path": null}"#), BAD_MESH_PATH);
        // An empty path means "no mesh" and is never resolved, so it stays empty.
        let document = parse(&text_with_meshes(6, 7, r#"{"path": ""}"#), &repo_root())
            .expect("an empty path is fine");
        assert!(document.meshes[0].path.is_empty());
    }

    #[test]
    fn mesh_offsets_and_rotations_must_be_three_numbers() {
        expect_message(
            &text_with_meshes(6, 7, r#"{"offset": [0, 0]}"#),
            BAD_MESH_OFFSET,
        );
        expect_message(&text_with_meshes(6, 7, r#"{"offset": 0}"#), BAD_MESH_OFFSET);
        expect_message(
            &text_with_meshes(6, 7, r#"{"rotation_deg": [0, 0, 0, 0]}"#),
            BAD_MESH_ROTATION,
        );
        expect_message(
            &text_with_meshes(6, 7, r#"{"offset": [0, "1", 2]}"#),
            "mesh 1: 'offset' is missing or not a number.",
        );
        // A missing offset or rotation is the zero vector, and a missing opacity is 1.
        let document = parse(
            &text_with_meshes(6, 7, r#"{"path": "a.stl"}"#),
            &repo_root(),
        )
        .expect("defaults");
        assert_eq!(document.meshes[0].offset, [0.0; 3]);
        assert_eq!(document.meshes[0].rotation_deg, [0.0; 3]);
        assert_eq!(document.meshes[0].opacity, 1.0);
    }

    #[test]
    fn a_mesh_opacity_must_be_a_finite_number_from_zero_to_one() {
        // `NaN` and `Infinity` are not JSON — `json.loads` accepts them as an extension,
        // `serde_json` does not — so a value that is not finite is written the way JSON
        // can write one: out of range.
        expect_message(
            &text_with_meshes(6, 7, r#"{"opacity": 1e400}"#),
            BAD_MESH_VALUE,
        );
        expect_message(
            &text_with_meshes(6, 7, r#"{"offset": [0, 1e400, 2]}"#),
            BAD_MESH_VALUE,
        );
        expect_message(
            &text_with_meshes(6, 7, r#"{"opacity": 1.5}"#),
            BAD_MESH_OPACITY,
        );
        expect_message(
            &text_with_meshes(6, 7, r#"{"opacity": -0.5}"#),
            BAD_MESH_OPACITY,
        );
        for opacity in ["0", "0.5", "1"] {
            let text = text_with_meshes(6, 7, &format!(r#"{{"opacity": {opacity}}}"#));
            assert!(
                parse(&text, &repo_root()).is_ok(),
                "opacity {opacity} is in range"
            );
        }
    }

    #[test]
    fn a_non_finite_value_cannot_be_written() {
        // `json.dumps` writes `NaN` and `serde_json` writes `null`; neither is a value
        // this format can read back, so the write is refused with the sentence the
        // reference uses for the same problem on read.
        let mut document = Document::shipped();
        document.parameters.joints[2].alpha_deg = f64::NAN;
        match to_json(&document, &repo_root()) {
            Err(error) => assert_eq!(error.to_string(), BAD_DH_VALUE),
            Ok(text) => panic!("a NaN was written: {text}"),
        }
        let mut document = Document::shipped();
        document.meshes[0].opacity = f64::INFINITY;
        match to_json(&document, &repo_root()) {
            Err(error) => assert_eq!(error.to_string(), BAD_MESH_VALUE),
            Ok(text) => panic!("an infinity was written: {text}"),
        }
    }

    #[test]
    fn save_and_load_round_trip_through_a_file() {
        let directory = unique_temp_dir("round-trip");
        std::fs::create_dir_all(&directory).expect("the temp directory is creatable");
        let path = directory.join(FILE_NAME);

        let mut document = Document::shipped();
        document.show_mesh_edges = true;
        document.show_joint_labels = false;
        document.show_coordinate_gizmos[2] = false;
        document.parameters.joints[1].a = 41.5;
        document.meshes[0] = MeshSettings {
            path: path_text(&directory.join("base.stl")),
            offset: [1.0, -2.0, 3.5],
            rotation_deg: [4.0, 5.0, -6.0],
            opacity: 0.25,
        };

        save(&document, &path).expect("the document saves");
        let written = std::fs::read_to_string(&path).expect("the file is there");
        assert!(written.ends_with("}\n"));
        assert!(!written.contains('\r'), "LF endings, whatever the platform");
        // The mesh is inside the file's own directory, so it is stored relative to it.
        assert!(
            written.contains(r#""path": "base.stl""#),
            "relative mesh path: {written}"
        );

        let loaded = load(&path).expect("the document loads");
        assert_eq!(loaded, document, "everything survives the trip");

        // `save` writes through `fs::write`, so the file is exactly `to_json`'s bytes.
        assert_eq!(
            written,
            to_json(&document, &directory).expect("serialize"),
            "the same bytes"
        );

        std::fs::remove_dir_all(&directory).expect("the temp directory is removable");
    }

    #[test]
    fn load_reports_a_file_that_is_not_there() {
        let missing = unique_temp_dir("missing").join(FILE_NAME);
        match load(&missing) {
            Err(error) => {
                assert!(matches!(error, DocumentError::Io(_)));
                // `str(OSError)` on the reference's side, `io::Error`'s on this one: the
                // kind of message is the same even though the words cannot be.
                assert!(error.source().is_some());
            }
            Ok(document) => panic!("loaded {document:?} from nowhere"),
        }
    }

    #[test]
    fn the_document_methods_agree_with_the_free_functions() {
        let root = repo_root();
        let text = text_with_meshes(6, 7, r#"{"path": "mesh/arm.stl"}"#);
        let document = Document::from_json(&text).expect("parse");
        // `from_json` has no directory to work with, so it resolves against the current
        // directory, where `parse` with the repository root resolves against that.
        assert_eq!(
            document,
            parse(&text, Path::new(".")).expect("the same document")
        );
        assert_eq!(
            document.to_json(&root).expect("serialize"),
            to_json(&document, &root).expect("serialize")
        );

        let directory = unique_temp_dir("methods");
        std::fs::create_dir_all(&directory).expect("the temp directory is creatable");
        let path = directory.join(FILE_NAME);
        document.save(&path).expect("save");
        assert_eq!(Document::load(&path).expect("load"), document);
        std::fs::remove_dir_all(&directory).expect("the temp directory is removable");
    }
}
