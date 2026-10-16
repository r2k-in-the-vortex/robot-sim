# Robot arm validations

A local workspace extension that puts this repository's validations in VS Code's Test view.
It exists because VS Code has no way to be told about a test declaratively, and nothing
installed provides a provider for Rust or Lean: the Python suites show up because the Python
extension contributes them, and nothing contributes `cargo test`, `lake build` or
`cargo xtask check-golden`.

## Installing it

VS Code scans each workspace folder's `.vscode/extensions` directory and offers what it
finds under *Workspace Recommendations* in the Extensions view -- install it there. It
needs the workspace to be trusted, and it is installed for this workspace only.

Editing the code afterwards needs a reload to take effect: *Developer: Restart Extension
Host*, or any window reload.

If it does not appear in the recommendations (an older VS Code, or the folder opened in an
unusual way), either run *Developer: Install Extension from Location...* and pick this
directory -- which installs it for the whole profile rather than the workspace -- or open
the repository root as the folder.

## What it adds

```
Robot arm
├── Rust tests              cargo test --workspace, then per package, target and test
├── Lean proofs             lake build, or one item per library in the lakefile
├── Ground truth            cargo xtask check-golden
└── Repository checks       cargo fmt --all --check
                            cargo clippy --workspace --all-targets -- -D warnings
                            cargo build -p robot-kinematics --no-default-features --features libm
```

Every command is one `ci.yml` runs, from the same directory, with one addition: the Rust
commands pass `--no-fail-fast`, so one failing test does not hide the rest of the package
the way CI's first-failure-wins does.

The Python suites are deliberately absent -- the Python extension already lists them, and
*Run All Tests* spans controllers, so it covers both without anything appearing twice.

## Things worth knowing

- **Discovery compiles.** Listing a package's tests runs `cargo test -p <pkg> -- --list`,
  which builds the package's test binaries without running them. That is why packages are
  only listed when something asks for them: expanding one, or starting a run that covers
  them. Expanding `robot-app` builds Bevy.
- **Failures are clickable.** A failing test's message is the block libtest printed for it,
  with the `panicked at file:line:col` attached, and a build failure attaches the first
  compiler diagnostic that points at a file that exists.
- **The gutter run buttons** come from a scan of the target's sources for `fn <name>`, so
  the item has a file and a range to hang an icon on. It is a heuristic and only a
  location: which test runs is always decided by the name cargo printed. Doctests have no
  `fn` to find and so have no gutter icon.
- **Doctests run whole.** libtest prints a doctest's whole source path with a `(line N)`
  suffix, which no filter matches reliably, so selecting one runs that package's doc tests
  and attributes the results by name.
- **`gen-golden` is not here.** It rewrites committed ground truth rather than checking
  anything, so it stays a terminal command.
- **If `rust-analyzer` is installed later**, it contributes its own Rust test items and the
  Rust tree appears twice, once per controller. Nothing merges them; drop the `Rust tests`
  root in `extension.js` if its version is the one you want.

## Trimming it

`extension.js` holds the lists: `CHECKS` for the three checks, `GOLDEN` for the ground
truth item, and the Lean items are read out of `lean/lakefile.toml`'s `defaultTargets`, so
adding a library there adds it to the tree. `SINGLE_TEST_LIMIT` is the point past which
selecting many tests in one target runs the target instead of one command per test.

## Testing it

The parsing and the command lines live in `plan.js`, which imports nothing from VS Code.
`extension.js` needs VS Code, so `test/extension.test.js` stubs the API -- strictly: a
`TestItem`'s `id`, `uri`, `children` and `parent` are non-writable there, as they are in the
host, because assigning one is a mistake this extension has made once already (it threw
inside discovery and was reported as "cargo metadata failed").

```powershell
node --test ".vscode/extensions/robot-arm-validations/test/*.test.js"
```

`test/fixtures/` holds real output from the commands concerned: a `--list` and a passing
run from `robot-golden`, a `--list` with doctests, a failing run and a build failure from a
throwaway crate, and `cargo metadata` for this workspace.
