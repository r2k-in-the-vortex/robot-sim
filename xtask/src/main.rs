//! Repository tasks, run as `cargo xtask <task>` through the alias in `.cargo/config.toml`.
//!
//! `test_data/` is generated output: the exact-rational vectors are produced by the Lean
//! generators in `lean/`, and nothing else may write them. Both tasks here drive those
//! generators, so regenerating is the only supported way to change the corpus, and
//! `check-golden` is what lets CI say the committed vectors are exactly what the Lean
//! produces rather than merely consistent with it.

use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus};

/// `xtask` sits directly under the repository root, so the manifest directory's parent is
/// the root whatever directory cargo was invoked from.
const MANIFEST_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Each Lean generator with the output path it is given, relative to `lean/` — spelled the
/// way the generators themselves document it. `lake exe` compiles a generator on demand;
/// none of them is in the lakefile's `defaultTargets`, so `lake build` stays a proof-only
/// build.
const GENERATORS: [(&str, &str); 4] = [
    (
        "kinematics_test_data",
        "../test_data/kinematics_frames.json",
    ),
    (
        "force_torque_test_data",
        "../test_data/force_torque_frames.json",
    ),
    ("branch_decision_q", "../test_data/branch_plans.json"),
    ("motion_test_data", "../test_data/motion_profiles.json"),
];

fn main() -> ExitCode {
    match std::env::args().nth(1).as_deref() {
        Some("gen-golden") => match run_generators() {
            Ok(()) => ExitCode::SUCCESS,
            Err(code) => code,
        },
        Some("check-golden") => match run_generators().and_then(|()| diff_test_data()) {
            Ok(()) => ExitCode::SUCCESS,
            Err(code) => code,
        },
        Some("-h" | "--help") => {
            println!("{USAGE}");
            println!(
                "\n  gen-golden    run the Lean generators in lean/, writing test_data/\n  \
                 check-golden  run them, then fail if the working tree's test_data/ changed"
            );
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("{USAGE}");
            ExitCode::FAILURE
        }
    }
}

/// Short enough to be the only thing an unknown task says to stderr.
const USAGE: &str = "usage: cargo xtask <gen-golden|check-golden>";

/// The generator run stops at the first failure: a later generator cannot repair a partial
/// corpus, and the caller wants the first diagnosis.
fn run_generators() -> Result<(), ExitCode> {
    let lean_dir = repo_root().join("lean");
    for (exe, output) in GENERATORS {
        let status = Command::new("lake")
            .args(["exe", exe, output])
            .current_dir(&lean_dir)
            .status()
            .map_err(|err| {
                if err.kind() == ErrorKind::NotFound {
                    // The version the Lean is known to build under lives in the toolchain
                    // file; elan and lakeup both read it from the working directory.
                    eprintln!(
                        "lake is not on PATH; install the toolchain pinned by {}",
                        lean_dir.join("lean-toolchain").display()
                    );
                } else {
                    eprintln!("could not run `lake exe {exe}`: {err}");
                }
                ExitCode::FAILURE
            })?;
        if !status.success() {
            eprintln!("`lake exe {exe}` failed");
            return Err(exit_code(status));
        }
    }
    Ok(())
}

/// The corpus is committed generated output, so being in sync with the Lean is exactly
/// "regenerating leaves no diff". `git diff` sees tracked files only, which is the intent:
/// the guard is over the committed vectors, and a new one has to be committed before it can
/// go stale.
fn diff_test_data() -> Result<(), ExitCode> {
    let root = repo_root();
    let status = Command::new("git")
        .args(["diff", "--exit-code", "--", "test_data"])
        .current_dir(&root)
        .status()
        .map_err(|err| {
            eprintln!("could not run `git diff` in {}: {err}", root.display());
            ExitCode::FAILURE
        })?;
    match status.code() {
        // `--exit-code`'s differences, not an error: git reserves codes above 1 for those.
        Some(1) => {
            eprintln!(
                "test_data/ is not what the Lean generators produce; run `cargo xtask gen-golden` \
                 and commit the result"
            );
            Err(ExitCode::FAILURE)
        }
        Some(0) => Ok(()),
        _ => {
            eprintln!("`git diff` did not run to completion: {status}");
            Err(exit_code(status))
        }
    }
}

/// A child's own code becomes the task's code, so a script reading it sees the generator's
/// verdict rather than a generic failure.
fn exit_code(status: ExitStatus) -> ExitCode {
    match status.code() {
        // `ExitCode` carries a `u8`; a wider code (Windows allows 32-bit ones) has no byte
        // to forward and becomes a plain failure.
        Some(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
        // No code means the child died from a signal.
        None => ExitCode::FAILURE,
    }
}

/// The repository root: this crate's manifest directory is `<root>/xtask`.
fn repo_root() -> PathBuf {
    Path::new(MANIFEST_DIR)
        .parent()
        .expect("the manifest directory of xtask is <root>/xtask")
        .to_owned()
}
