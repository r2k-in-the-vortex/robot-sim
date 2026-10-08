# Aim of this repo is to write 6 axis robot simulation

0) everything written in python first

1) visual 3D view that can draw xyz axis markers, and later optionally load meshes to visualize robot. the view should be rotatable/scaleable/panable by mouse. my drawing one set of xyz markers at coordinate zero

## Run

Install the Python dependency and launch the viewport:

```powershell
python -m pip install -r requirements.txt
python simulator.py
```

The **3D View** tab displays the base and all six joint frames from the DH
parameters. Drag with the left mouse button to orbit, drag with the right mouse
button to pan, and use the scroll wheel to zoom. The **Parameters** tab contains
separate **DH Parameters** and **Meshes** tabs. DH values are editable per joint;
angles are entered in degrees, while `d`, `a`, and mesh offsets use consistent
model units. The Meshes tab selects an STL for the base or any joint, sets a
local XYZ offset from that frame's origin, and sets opacity from 0 (transparent)
to 1 (opaque). Apply changes to update the view. Save JSON and Load JSON
persist all DH and mesh settings in `robot_parameters.json`; mesh paths are
stored relative to the configuration file when possible. The included DH values
are illustrative starter dimensions, not measurements for a specific robot.

1) next we need mathematical model of forward transformation, to go from joint angles to joint positions and final end of arm positions. That is a series of matrix multiplications, for each of 6 axes, according to Denavit–Hartenberg Convention. We need function to create per joint martixes using parameters:
    • \(\theta _{i}\): Joint angle (rotation about the previous \(Z\) axis)
    • \(d_{i}\): Link offset (translation along the previous \(Z\) axis)
    • \(a_{i}\): Link length (translation along the current \(X\) axis)
    • \(\alpha _{i}\): Link twist (rotation about the current \(X\) axis)
multiplying these joint by joint, yields each joint location

2) add math functions to calculate joint transformations according to mathematics.md, for each joint draw a xyz marker. make the joint parameter settings changeable in different tab of UI, save the parameters as json

3) under parameters, add option to load STL file mesh for base and each of 6 joints. The meshes need location offset from the zero marker, and there needs to be opacity option for meshes. Save all the mesh parameters in json.