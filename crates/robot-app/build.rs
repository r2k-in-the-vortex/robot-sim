//! Stages the shipped configuration and its meshes beside the executable.
//!
//! `session::default_config_path` looks for `robot_parameters.json` beside the executable
//! first, the way the reference pins it beside the script (`Path(__file__).with_name(...)`,
//! `simulator.py:171`) and a compiled binary has no script directory. Nothing used to put a
//! file there, so an executable run from its own directory — a double-click, or
//! `cargo run --release` after an earlier session had saved one — opened on the empty
//! default document, or on a stale copy of somebody's saved state.
//!
//! Cargo gives a build script no supported way to place a file next to the executable:
//! `OUT_DIR` is `<profile>/build/<package>-<hash>/out`, a directory of its own inside the
//! build tree. This walks up from there to the profile directory beside the binary
//! (`target/debug`, `target/release`, or `target/<triple>/<profile>`) and writes the two
//! things the app reads on startup. The alternative is an `xtask` step somebody has to
//! remember before every run, which is the state this replaces.
//!
//! The meshes come along because the shipped configuration names them by a path relative to
//! itself (`"mesh/Robot c 4 a 601 s - c4-a601s_01-1.STL"`), and `persist::config_dir_of`
//! resolves those against the directory the configuration file is in. A copy of the file
//! without the meshes beside it would load with seven missing-link notices.
//!
//! Every copy is conditional on the bytes differing, so a rebuild that changes nothing does
//! not touch a timestamp, and a configuration the app itself saved beside the binary — which
//! is what the file there is for — survives until the shipped file really changes.

use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    let root = repository_root();
    let configuration = root.join("robot_parameters.json");
    let meshes = root.join("mesh");
    println!("cargo:rerun-if-changed={}", configuration.display());
    println!("cargo:rerun-if-changed={}", meshes.display());

    let profile = profile_directory();
    copy_if_different(&configuration, &profile.join("robot_parameters.json"));

    let staged_meshes = profile.join("mesh");
    fs::create_dir_all(&staged_meshes)
        .unwrap_or_else(|error| panic!("could not create {}: {error}", staged_meshes.display()));
    for entry in fs::read_dir(&meshes)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", meshes.display()))
    {
        let path = entry.expect("a readable mesh directory entry").path();
        // The same rule `mesh.rs` loads by: the extension names an STL whatever its case,
        // and the files in `mesh/` are the ones the shipped configuration lists.
        if !path
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("STL"))
        {
            continue;
        }
        let name = path.file_name().expect("a mesh file has a name");
        copy_if_different(&path, &staged_meshes.join(name));
    }
}

/// The repository root, which is where `robot_parameters.json` and `mesh/` ship.
fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The directory the executable is linked into.
///
/// `OUT_DIR` is `<profile>/build/<package>-<hash>/out`, and the walk takes the first
/// ancestor named `build` and steps to its parent, which is the profile directory for a
/// plain `cargo build` and for `--target <triple>` alike.
fn profile_directory() -> PathBuf {
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    out.ancestors()
        .find(|directory| directory.file_name().is_some_and(|name| name == "build"))
        .and_then(Path::parent)
        .unwrap_or_else(|| panic!("no `build` directory above {}", out.display()))
        .to_path_buf()
}

/// Copy `source` to `destination` unless the destination already holds those bytes.
fn copy_if_different(source: &Path, destination: &Path) {
    let contents = fs::read(source)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", source.display()));
    if fs::read(destination).is_ok_and(|existing| existing == contents) {
        return;
    }
    fs::write(destination, &contents)
        .unwrap_or_else(|error| panic!("could not write {}: {error}", destination.display()));
}
