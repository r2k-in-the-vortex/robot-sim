# Aim of this repo is to write 6 axis robot simulation

0) everything written in python first

1) visual 3D view that can draw xyz axis markers, and later optionally load meshes to visualize robot. the view should be rotatable/scaleable/panable by mouse. my drawing one set of xyz markers at coordinate zero

## Run

Install the Python dependencies and launch the viewport:

```powershell
python -m pip install -r requirements.txt
python simulator.py
```

The **3D View** tab displays the base and all six joint frames. Drag with the
left mouse button to orbit, drag with the right mouse button to pan, and use the
scroll wheel to zoom. The view starts in an isometric orthographic angle. The
**Parameters** tab contains separate **DH Parameters**
and **Meshes** tabs. DH values are editable per joint; angles are entered in
degrees, while `d`, `a`, and mesh offsets use consistent model units. The DH
table separates each joint's static theta offset from its runtime joint angle.
Runtime angles start at zero each time the application launches; **Apply to
View** uses offset plus runtime angle for forward kinematics. Saving stores only
the static theta offset and link dimensions, never the runtime joint position.
Solves run on the runtime angles at full precision; the joint angle fields and
the front readouts render them rounded, and a field left untouched keeps its
exact value when an edit elsewhere is applied. **Copy XYZ** likewise copies the
runtime angles unrounded.
Older configuration files using `theta_deg` are read as static offsets. Each mesh
can have a local XYZ offset and local X/Y/Z Euler rotations applied in that
order, in degrees. Opacity ranges from 0 (transparent) to 1 (opaque). Use
**Show triangle edges** in the Meshes tab to toggle mesh outlines; it is off by
default. Apply changes to update the view. Save JSON and Load JSON persist all
DH and mesh settings in `robot_parameters.json`; mesh paths are stored relative
to the configuration file when possible. The included DH values are illustrative
starter dimensions that match the shipped `robot_parameters.json`, not
measurements for a specific robot.

Cartesian and rotation jogs solve the full pose with closed-form inverse
kinematics, which is derived for this robot's structure: `alpha` of 90, 0, 90,
90, -90, 0 degrees, `a3 = a4 = a5 = a6 = 0`, `d2 = d3 = d5 = 0`, and positive
`a2` and `d4`. A DH table that departs from that structure is still drawn and
can still be jogged joint by joint, but a pose jog reports which parameter is
unsupported in the status line instead of moving the robot.

The DH Parameters tab also has independent coordinate-gizmo visibility
checkboxes for the base and J1-J6. All are visible by default, and their states
are stored in `show_coordinate_gizmos` in `robot_parameters.json`.
Joint labels have a separate show/hide checkbox, defaulting to visible, and the
3D View includes a scale-adaptive XY reference grid on the Z=0 plane.

1) next we need mathematical model of forward transformation, to go from joint angles to joint positions and final end of arm positions. That is a series of matrix multiplications, for each of 6 axes, according to Denavit–Hartenberg Convention. We need function to create per joint martixes using parameters:
    • \(\theta _{i}\): Joint angle (rotation about the previous \(Z\) axis)
    • \(d_{i}\): Link offset (translation along the previous \(Z\) axis)
    • \(a_{i}\): Link length (translation along the current \(X\) axis)
    • \(\alpha _{i}\): Link twist (rotation about the current \(X\) axis)
multiplying these joint by joint, yields each joint location

2) add math functions to calculate joint transformations according to mathematics.md, for each joint draw a xyz marker. make the joint parameter settings changeable in different tab of UI, save the parameters as json

3) under parameters, add option to load STL file mesh for base and each of 6 joints. The meshes need location offset from the zero marker, and there needs to be opacity option for meshes. Save all the mesh parameters in json.

4) on the front tab, there should be current T6 display, to show the end effector position and orientation.

5) The DH theta parameter is split into a static offset and a runtime joint angle. Only the static offset is stored in JSON; the runtime angle starts at zero whenever the application launches.

6) The 3D View groups its jog controls into a **Base frame** group, a **Tool
frame** group, and a **Joint jogs** group, with one shared jog step in model
units and one shared rotation step in degrees. Each frame group carries X/Y/Z
buttons that offset the current T6 position along that frame's axes and RX/RY/RZ
buttons that turn T6 about them: base-frame moves run along the base axes, while
tool-frame moves run along the axes frame 6 carries, which is what you want when
advancing along the tool's own approach direction. Every jog solves the new pose
with its full orientation fixed. If inverse kinematics cannot satisfy both the
requested position and orientation, the jog is rejected and the robot remains at
its current pose; it does not silently rotate the end effector.

6) The front display has controls to jog the robot in X, Y, Z directions by a given step length.
The mechanism of that is that the step offset from current T6 is used to calculate new T6', which is fed into inverse kinematics to calculate new joint angles, which are used to update the robot position

7) add buttons to jog rotations of end effector, Rx+, Rx+ Ry+ etc for rotations around respective world axes

Every rotation jog keeps the T6 origin fixed and applies the requested rotation
about the axes of whichever group the button belongs to, base or tool. If the
full target pose has no IK solution, the request is rejected and the robot
remains unchanged.

Individual joints can also be jogged directly from the **Joint jogs** group with
its `J1`–`J6` minus/plus buttons and a configurable joint-angle step. The
displayed runtime angles stay synchronized with the Joint Angle fields in the
Parameters tab; applying angle edits there also refreshes the front-screen
readouts.

## Force torque control

1) for Force torque control to be possible, 6DOF force sensor readings must be recalculated from one frame of reference to another. For example from sensor frame to tooltip frame where the contact point actually is.

2) to validate the mathematics of the force/torque control, before implementing it in code, the mathematics should be proved in lean/TorqueWrench.lean
