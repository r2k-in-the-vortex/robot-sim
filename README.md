# Six-axis robot arm simulator

A Python desktop application that simulates a 6-axis articulated robot arm. It
draws the arm as a chain of Denavit–Hartenberg frames in an interactive 3D view,
can overlay an STL mesh on the base and on each joint, and moves the arm either
joint by joint or by jogging the end effector in Cartesian space. Cartesian and
rotation jogs are solved with a closed-form inverse kinematics derived for this
arm's structure.

The mathematics behind the simulator is written out in
[`mathematics.md`](mathematics.md) and proved in Lean under [`lean/`](lean) — see
[Mathematics](#mathematics) below.

![main window](doc/main_window_image.png)

## Run

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
| `simulator.py` | Tkinter application: 3D view, jog controls, parameter tabs, JSON configuration |
| `kinematics.py` | DH transforms, forward kinematics, closed-form inverse kinematics |
| `mathematics.md` | Derivations: forward and inverse kinematics, force/torque sensor dynamics |
| `lean/` | Lean formalisation and proofs of the same mathematics |
| `robot_parameters.json` | Default DH and mesh configuration |
| `mesh/` | Example STL meshes to load into the view |
| `test_data/` | Generated ground truth for the force/torque tests |
| `test_kinematics.py`, `test_force_torque.py` | Python test suites |

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
Regenerate that file with, from `lean/`:

```powershell
lake exe force_torque_test_data
```

CI runs both toolchains in independent jobs: the Python suite under `xvfb-run`,
and `lake build` over the Lean libraries in `defaultTargets`.
