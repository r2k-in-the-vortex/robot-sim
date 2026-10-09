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
scroll wheel to zoom. The **Parameters** tab contains separate **DH Parameters**
and **Meshes** tabs. DH values are editable per joint; angles are entered in
degrees, while `d`, `a`, and mesh offsets use consistent model units. The DH
table separates each joint's static theta offset from its runtime joint angle.
Runtime angles start at zero each time the application launches; **Apply to
View** uses offset plus runtime angle for forward kinematics. Saving stores only
the static theta offset and link dimensions, never the runtime joint position.
Older configuration files using `theta_deg` are read as static offsets. Each mesh
can have a local XYZ offset and local X/Y/Z Euler rotations applied in that
order, in degrees. Opacity ranges from 0 (transparent) to 1 (opaque). Use
**Show triangle edges** in the Meshes tab to toggle mesh outlines; it is off by
default. Apply changes to update the view. Save JSON and Load JSON persist all
DH and mesh settings in `robot_parameters.json`; mesh paths are stored relative
to the configuration file when possible. The included DH values are illustrative
starter dimensions, not measurements for a specific robot.

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

6) The 3D View includes Cartesian jog controls for base-frame X, Y, and Z. Set
the step length in model units and choose a positive or negative axis button.
Each jog offsets the current T6 position, keeps its orientation fixed, solves
the new pose with inverse kinematics, and applies the closest valid joint
solution. An unreachable step leaves the robot at its current pose.

6) The front display has controls to jog the robot in X, Y, Z directions by a given step length.
The mechanism of that is that the step offset from current T6 is used to calculate new T6', which is fed into inverse kinematics to calculate new joint angles, which are used to update the robot position