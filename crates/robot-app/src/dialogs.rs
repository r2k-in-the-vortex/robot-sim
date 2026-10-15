//! The file choosers the Parameters tab opens.
//!
//! # Deviation
//!
//! `simulator.py` opens a chooser for exactly one of the three: `_browse_stl`
//! (`simulator.py:580-588`). Save and Load never ask — they read and write
//! `Path(__file__).with_name("robot_parameters.json")` and report through a messagebox. This
//! module asks for all three, defaulting to the same file the reference would have used, for
//! the reason [`crate::session::default_config_path`] records: a compiled binary has no
//! script directory to anchor the path to, so the user needs a way to point at one. The
//! *bytes* written are unaffected — see [`crate::session::Session::save_json`].
//!
//! # Blocking
//!
//! These are the blocking `rfd` calls, so the window is unresponsive while a dialog is up.
//! That is what a native modal does, and it is only ever entered from a button press inside
//! the egui pass, which runs on the main thread — `rfd` requires that on Windows.

use std::path::{Path, PathBuf};

/// The STL chooser's filter list, `_browse_stl` (`simulator.py:583`):
/// `(("STL mesh", "*.stl"), ("All files", "*.*"))`.
const STL_FILTER: &str = "STL mesh";
/// The second filter, so a mesh with an unexpected extension is still reachable.
const ALL_FILES_FILTER: &str = "All files";

/// The parameter file's extension, for the Save and Load choosers.
const JSON_EXTENSION: &str = "json";

/// Ask for an STL file, opening where the row's current path points.
///
/// An empty current path opens the dialog wherever the platform last was, which is the best
/// available stand-in for the reference's always-blank entry.
pub fn pick_stl(current: &str) -> Option<PathBuf> {
    let mut dialog = rfd::FileDialog::new()
        .set_title("Select STL mesh")
        .add_filter(STL_FILTER, &["stl"])
        .add_filter(ALL_FILES_FILTER, &["*"]);

    if !current.trim().is_empty() {
        let path = Path::new(current.trim());
        if let Some(directory) = path.parent().filter(|parent| parent.is_dir()) {
            dialog = dialog.set_directory(directory);
        }
        if let Some(name) = path.file_name() {
            dialog = dialog.set_file_name(name.to_string_lossy().into_owned());
        }
    }
    dialog.pick_file()
}

/// Ask where to write the parameter file, starting at the current one.
pub fn save_config(config_path: &Path) -> Option<PathBuf> {
    rfd::FileDialog::new()
        .set_title("Save parameters")
        .add_filter("JSON parameter file", &[JSON_EXTENSION])
        .set_directory(directory_of(config_path))
        .set_file_name(file_name_of(config_path))
        .save_file()
}

/// Ask which parameter file to open, starting at the current one.
pub fn load_config(config_path: &Path) -> Option<PathBuf> {
    rfd::FileDialog::new()
        .set_title("Load parameters")
        .add_filter("JSON parameter file", &[JSON_EXTENSION])
        .set_directory(directory_of(config_path))
        .set_file_name(file_name_of(config_path))
        .pick_file()
}

/// The directory part of a path, `.` when it has none.
///
/// A bare `"robot_parameters.json"` has an empty parent rather than no parent, and `rfd`
/// treats an empty directory as "wherever the platform last was" rather than as the current
/// directory, so it is spelled out.
fn directory_of(path: &Path) -> PathBuf {
    path.parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
}

/// The name part of a path, the shipped file's name when it has none.
fn file_name_of(path: &Path) -> String {
    path.file_name().map_or_else(
        || String::from("robot_parameters.json"),
        |name| name.to_string_lossy().into_owned(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    // The dialogs themselves cannot be driven headless — `rfd` opens a real window and there
    // is no display in CI. What is testable is the path arithmetic that decides where each
    // dialog opens, so that is what is covered; the rest is exercised by hand.

    #[test]
    fn a_bare_file_name_opens_in_the_current_directory() {
        assert_eq!(
            directory_of(Path::new("robot_parameters.json")),
            PathBuf::from(".")
        );
        assert_eq!(
            file_name_of(Path::new("robot_parameters.json")),
            "robot_parameters.json"
        );
    }

    #[test]
    fn a_full_path_opens_beside_the_file_it_names() {
        let path = Path::new("/data/robot/robot_parameters.json");
        assert_eq!(directory_of(path), PathBuf::from("/data/robot"));
        assert_eq!(file_name_of(path), "robot_parameters.json");
    }

    #[test]
    fn a_directory_with_no_name_still_has_a_file_name() {
        // `Path::new("/").file_name()` is `None`, which must not become an empty file name:
        // rfd would then open with no name filled in.
        assert_eq!(file_name_of(Path::new("/")), "robot_parameters.json");
    }
}
