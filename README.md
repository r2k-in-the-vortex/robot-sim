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
button to pan, and use the scroll wheel to zoom. The **DH Parameters** tab lets
you edit each joint's theta, d, a, and alpha values. Angles are entered in
degrees; d and a use consistent model units. Apply changes to update the view,
and use Save JSON or Load JSON to persist the values in `robot_parameters.json`.
The included DH values are illustrative starter dimensions, not measurements
for a specific robot.

1) next we need mathematical model of forward transformation, to go from joint angles to joint positions and final end of arm positions. That is a series of matrix multiplications, for each of 6 axes, according to Denavit–Hartenberg Convention. We need function to create per joint martixes using parameters:
    • \(\theta _{i}\): Joint angle (rotation about the previous \(Z\) axis)
    • \(d_{i}\): Link offset (translation along the previous \(Z\) axis)
    • \(a_{i}\): Link length (translation along the current \(X\) axis)
    • \(\alpha _{i}\): Link twist (rotation about the current \(X\) axis)
multiplying these joint by joint, yields each joint location

2) add math functions to calculate joint transformations according to mathematics.md, for each joint draw a xyz marker. make the joint parameter settings changeable in different tab of UI, save the parameters as json