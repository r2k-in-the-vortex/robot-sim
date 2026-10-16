# Six-axis robot arm simulator

A desktop application that simulates a 6-axis articulated robot arm. It draws the
arm as a chain of Denavit–Hartenberg frames in an interactive 3D view, can overlay
an STL mesh on the base and on each joint, and moves the arm either joint by joint
or by jogging the end effector in Cartesian space. Cartesian and rotation jogs are
solved with a closed-form inverse kinematics derived for this arm's structure.

The mathematics behind it is written out in [`mathematics.md`](mathematics.md) and
proved in Lean under [`lean/`](lean) — see [Mathematics](#mathematics) below.

There are two implementations. The **Rust** one under [`crates/`](crates) is the
one being developed: it has a GPU renderer, a kinematics core built for a real-time
control loop, and a force/torque sensor model that the Python never had. The
**Python** one (`simulator.py`, `kinematics.py`) is the original, kept as a
reference and as a frozen regression oracle — its behaviour is the contract the Rust
matches, and it still passes its own suite unchanged.

![main window](doc/main_window_image.png)

## Run

### Rust

```powershell
cargo run -p robot-app --release
```

### Python

Install the Python dependencies and launch the viewport:

```powershell
python -m pip install -r requirements.txt
python simulator.py
```

## Using the simulator

### 3D View tab

The view draws the base and all six joint frames as xyz axis markers at their
frame origins, plus a scale-adaptive XY reference grid on the Z=0 plane. Drag
with the left mouse button to orbit, drag with the right mouse button to pan,
and use the scroll wheel to zoom. The view starts in an isometric orthographic
angle.

The front readout shows the current T6 pose — the end effector's position and
orientation. **Copy XYZ** puts the T6 position, its orientation as ZYX
roll/pitch/yaw, and all six runtime joint angles on the clipboard at full
precision.

### Parameters tab

Two sub-tabs, **DH Parameters** and **Meshes**.

**DH Parameters.** DH values are editable per joint. Angles are entered in
degrees, while `d`, `a`, and mesh offsets use consistent model units. The DH
table separates each joint's static theta offset from its runtime joint angle.
Runtime angles start at zero each time the application launches; **Apply to
View** uses offset plus runtime angle for forward kinematics. Saving stores only
the static theta offset and link dimensions, never the runtime joint position.
Solves run on the runtime angles at full precision; the joint angle fields and
the front readouts render them rounded, and a field left untouched keeps its
exact value when an edit elsewhere is applied. Older configuration files using
`theta_deg` are read as static offsets.

Independent coordinate-gizmo visibility checkboxes cover the base and J1–J6. All
are visible by default, and their states are stored in `show_coordinate_gizmos`
in `robot_parameters.json`. Joint labels have a separate show/hide checkbox,
defaulting to visible.

**Meshes.** Each of the base and the six joints can load an STL mesh. A mesh has
a local XYZ offset from its zero marker and local X/Y/Z Euler rotations applied
in that order, in degrees. Opacity ranges from 0 (transparent) to 1 (opaque).
Use **Show triangle edges** to toggle mesh outlines; it is off by default. Apply
changes to update the view.

**Save JSON** and **Load JSON** persist all DH and mesh settings in
`robot_parameters.json`; mesh paths are stored relative to the configuration
file when possible. The included DH values are illustrative starter dimensions
that match the shipped `robot_parameters.json`, not measurements for a specific
robot.

### Jogging

The 3D View groups its jog controls into a **Base frame** group, a **Tool
frame** group, and a **Joint jogs** group, with one shared jog step in model
units and one shared rotation step in degrees.

**Base frame** and **Tool frame** each carry X/Y/Z buttons that offset the
current T6 position along that frame's axes and RX/RY/RZ buttons that turn T6
about them. Base-frame moves run along the base axes, while tool-frame moves run
along the axes frame 6 carries, which is what you want when advancing along the
tool's own approach direction. Rotation jogs keep the T6 origin fixed and apply
the requested rotation about the axes of whichever group the button belongs to,
base or tool.

Every pose jog, base frame or tool frame, solves the new pose with its full
orientation fixed. If inverse kinematics cannot satisfy both the requested
position and orientation, the jog is rejected and the robot remains at its
current pose; it does not silently rotate the end effector.

**Joint jogs.** Individual joints can also be jogged directly, with `J1`–`J6`
minus/plus buttons and a configurable joint-angle step. The displayed runtime
angles stay synchronized with the Joint Angle fields in the Parameters tab;
applying angle edits there also refreshes the front-screen readouts.

## Inverse kinematics

Cartesian and rotation jogs solve the full pose with closed-form inverse
kinematics, which is derived for this robot's structure: `alpha` of 90, 0, 90,
90, -90, 0 degrees, `a3 = a4 = a5 = a6 = 0`, `d2 = d3 = d5 = 0`, and positive
`a2` and `d4`. A DH table that departs from that structure is still drawn and
can still be jogged joint by joint, but a pose jog reports which parameter is
unsupported in the status line instead of moving the robot.

The derivation is in the *Inverse kinematics* section of
[`mathematics.md`](mathematics.md).

## Repository layout

| Path | Contents |
| --- | --- |
| `crates/robot-kinematics` | DH transforms, forward kinematics, closed-form inverse kinematics |
| `crates/robot-dynamics` | Wrench frame algebra, gravity and inertia compensation |
| `crates/robot-model` | Parameter types and `robot_parameters.json` persistence |
| `crates/robot-app` | Bevy + egui desktop application |
| `crates/robot-golden` | Exact rational arithmetic and the Lean numeral format, for tests |
| `xtask` | `cargo xtask gen-golden` / `check-golden` |
| `docs/verification.md` | What is proved, what is tested, and what is neither |
| `simulator.py` | The original Tkinter application, kept as a reference |
| `kinematics.py` | The original DH transforms and closed-form inverse kinematics |
| `mathematics.md` | Derivations: forward and inverse kinematics, force/torque sensor dynamics |
| `lean/` | Lean formalisation and proofs of the same mathematics |
| `robot_parameters.json` | Default DH and mesh configuration |
| `mesh/` | Example STL meshes to load into the view |
| `test_data/` | Generated ground truth, produced by the Lean generators |
| `test_kinematics.py`, `test_force_torque.py` | Python test suites |
| `.vscode/extensions/robot-arm-validations` | The Rust, Lean and ground-truth items in VS Code's Test view |

## Mathematics

[`mathematics.md`](mathematics.md) derives everything the simulator computes;
[`lean/`](lean) proves the same results formally, as pure proof libraries with no
robot code of their own.

| Topic | Derivation in `mathematics.md` | Proof in `lean/` |
| --- | --- | --- |
| DH transform, frame chain, joint and tool positions | *Forward Kinematics with Denavit–Hartenberg Parameters* | `Kinematics.lean` |
| Closed-form inverse solver | *Inverse kinematics* | `InverseKinematics.lean`, on `Zyz.lean` and `Atan2.lean` |
| Wrench transport between frames | *Force/torque sensor dynamics* → *Frame changes* | `TorqueWrench.lean` |
| Sensor measurement model and compensation | *Force/torque sensor dynamics* | `Dynamics.lean` |

### Kinematics

`lean/Kinematics.lean` covers the Denavit–Hartenberg transform, the cumulative
frames the simulator draws, and the planar reduction.
`lean/InverseKinematics.lean` covers the closed-form solver and proves it sound —
every candidate it returns reproduces the target pose exactly
(`fk_of_mem_solutions`) — and complete: for a commanded configuration outside
three degenerate cases the solver returns that configuration, every angle equal
modulo a full turn (`exists_solution_angles_eq`).
The three exceptions are named exactly rather than approximated: a wrist center
on the base axis, the arm folded back with equal links, and the wrist singularity
`sin θ5 = 0`, where joints 4 and 6 share an axis and only `θ4 ± θ6` is
observable. The numeric position solvers, floating-point tolerances and joint
limits are deliberately out of scope — the specification covers the closed form,
and over the reals the thresholds the code uses become exact predicates.

`lake build` in `lean/` builds all of it, and the derivation it follows is in
[`mathematics.md`](mathematics.md).

### Force/torque control

For force torque control to be possible, 6DOF force sensor readings must be
recalculated from one frame of reference to another — for example from the
sensor frame to the tooltip frame where the contact point actually is. That
static frame algebra is proved in `lean/TorqueWrench.lean`.

The frame transforms alone are not enough for a real robot: the sensor measures
the wrench *transmitted through it*, which also contains the gravitational and
inertial wrench of the tool and payload. Those are modelled in
`lean/Dynamics.lean`, which proves that gravity/inertia compensation recovers the
contact wrench exactly (`recoveredContactWrench_measuredWrench`), that the model
does not depend on which frame it is evaluated in (`inertialWrench_transport`,
`gravityWrench_transport`), and that rigidly attached bodies combine into one
(`inertialWrench_add`). The derivation, with the sign conventions, is in the
*Force/torque sensor dynamics* section of [`mathematics.md`](mathematics.md).

## Tests

Much of `test_kinematics.py` drives real Tk widgets, so those tests skip
themselves when there is no display. `test_force_torque.py` re-derives every
number in `test_data/force_torque_frames.json` (schema 3, including the
`dynamics_cases` section) from the case inputs in exact rational arithmetic.

The Rust suites go further, because they can: the forward chain, the wrench
algebra and the dynamics are polynomials in their inputs, so they evaluate exactly
over the rationals and are checked against the generated vectors with `==` and no
tolerance at all. The forward chain manages this because every `alpha` in the arm's
fixed twist pattern is a quarter turn — cosine `0`, sine `1`, both exact — and
because the chain reads each joint angle only through its cosine and sine, so
supplying those as data makes the whole thing polynomial. The angle-valued parts
cannot be treated this way, since `atan2` and `arccos` are irrational outside a
handful of cases; those are covered by restating the Lean theorems as executable
properties instead. [`docs/verification.md`](docs/verification.md) sets out the
whole boundary, including what is deliberately not attempted.

```powershell
cargo test --workspace          # everything, including the exact comparisons
cargo xtask gen-golden          # regenerate test_data/ from the Lean generators
cargo xtask check-golden        # regenerate and fail if the committed data has drifted
```

`check-golden` takes minutes rather than seconds: the Lean generators re-derive
each case by evaluation before writing anything, and that check sweep dominates.

CI runs three independent jobs: the Python suite under `xvfb-run`, the Rust
workspace, and `lake build` over the Lean libraries in `defaultTargets`. The Lean
job also regenerates the ground truth and fails if it differs from what is
committed — the Rust and Python suites both read the committed files and never
regenerate them, so without that step the data could drift from the Lean that
produced it while every suite kept passing on stale numbers.

All of it is also in VS Code's Test view. The workspace extension in
[`.vscode/extensions/robot-arm-validations`](.vscode/extensions/robot-arm-validations)
contributes the Rust tests per package, target and test function, one item per Lean
library in the lakefile, `check-golden`, and the fmt / clippy / `no_std` checks; the
Python suites are there too, from the Python extension. Nothing provides a Test view for
Rust or Lean, which is what the extension is for — install it once from *Workspace
Recommendations* in the Extensions view. Its output parsing runs under plain Node, which
is also how it is tested:

```powershell
node --test .vscode/extensions/robot-arm-validations/test/plan.test.js
```

## Where the Rust deliberately differs from the Python

Three changes are intentional rather than oversights, and all are visible.

**Mesh scale.** `simulator.py` applies no scale factor to the STL meshes at all,
so the meshes and the DH table never actually lined up: the shipped meshes are in
millimetres and span hundreds, while the DH dimensions are tens. The Rust applies a
factor of `0.1`, which is what makes a loaded mesh sit on the arm. The shipped
`robot_parameters.json` has every mesh path empty, so nothing loads at startup in
either implementation until a mesh is chosen.

**Gizmo checkboxes.** In `simulator.py` the labels and the things they toggle are
off by one: the checkbox labelled *J1* toggles the **base** gizmo, *J2* toggles J1,
and so on to *Tool/Flange*, which toggles J6. The render side is right and the
labels are wrong. The Rust labels them to match what they toggle.

**Save and Load ask for a file.** `simulator.py` has no chooser for either: both
read and write `Path(__file__).with_name("robot_parameters.json")`, the file beside
the script, and report through a message box. A compiled binary has no script
directory to anchor that to, so the Rust starts at the same name — beside the
executable, then in the working directory, then beside the executable — and opens
whatever the user picks. The bytes written are unaffected, apart from line endings:
Python's `write_text` is text mode, so it turns the newlines into CRLF on Windows,
while the Rust writes `json.dumps(data, indent=2) + "\n"` as-is. Both read either
form back.
