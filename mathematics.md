# Forward Kinematics with Denavit–Hartenberg Parameters

Forward kinematics maps the six joint variables to the position and orientation
of every link frame and the end effector. Assign a coordinate frame to each
joint, with frame 0 fixed to the robot base. For joint/link `i`, define the
Denavit–Hartenberg (DH) parameters:

| Parameter | Meaning |
| --- | --- |
| $\theta_i$ | Rotation about the previous frame's $Z$ axis |
| $d_i$ | Translation along the previous frame's $Z$ axis |
| $a_i$ | Translation along the current frame's $X$ axis |
| $\alpha_i$ | Rotation about the current frame's $X$ axis |

With column vectors and the standard DH convention, the transform from frame
`i` to frame `i - 1` is the ordered product

$$
{}^{i-1}T_i
= R_z(\theta_i)\,T_z(d_i)\,T_x(a_i)\,R_x(\alpha_i)
=
\begin{bmatrix}
\cos\theta_i & -\sin\theta_i\cos\alpha_i & \sin\theta_i\sin\alpha_i & a_i\cos\theta_i \\
\sin\theta_i & \cos\theta_i\cos\alpha_i & -\cos\theta_i\sin\alpha_i & a_i\sin\theta_i \\
0 & \sin\alpha_i & \cos\alpha_i & d_i \\
0 & 0 & 0 & 1
\end{bmatrix}.
$$

Here $R_x$ and $R_z$ are rotations, and $T_x$ and $T_z$ are translations. The
order matters: each operation is expressed in the convention's moving frames.
Angles are in radians when evaluated by the simulator.

## Chain the Six Joint Transforms

Let $A_i = {}^{i-1}T_i$ denote the DH matrix for joint/link `i`. For six joints,
multiply each adjacent-frame transform in order to express each frame in the
base frame:

$$
{}^0T_1 = A_1,
\\qquad
{}^0T_2 = A_1 A_2,
\\qquad
{}^0T_3 = A_1 A_2 A_3,
$$

$$
{}^0T_i = \\prod_{k=1}^{i} A_k,
\qquad i=1,\ldots,6.
$$

The product is written left to right in increasing joint order. $^0T_i$
contains both the orientation and position of frame `i`, relative to the base.

## Extract Joint and Tool Positions

The origin of frame `i`, expressed in base coordinates, is found by transforming
the homogeneous origin:

$$
{}^0\mathbf{p}_i
= {}^0T_i
\begin{bmatrix}0\\0\\0\\1\end{bmatrix}
=
\begin{bmatrix}x_i\\y_i\\z_i\\1\end{bmatrix}.
$$

Record $^0\mathbf{p}_i$ for $i=1,\ldots,6$ to obtain the six joint-frame
positions used to draw the robot. The final transform $^0T_6$ gives the pose
of the sixth frame. If the tool tip is offset from frame 6, define a fixed tool
transform $^6T_{tool}$ and calculate

$$
{}^0T_{tool} = {}^0T_6\,{}^6T_{tool}.
$$

The tool-tip position is the translation column of $^0T_{tool}$, equivalently
${}^0T_{tool}[0,0,0,1]^T$.

## Joint Variables

For a revolute joint, the measured joint angle changes $\theta_i$ while $d_i$ is
constant. For a prismatic joint, the joint displacement changes $d_i$ while
$\theta_i$ is constant. A robot-specific DH table supplies the constant link
dimensions and offsets; this document defines the calculation but does not
assume dimensions for a particular arm.

The actual robot has no prismatic joints, only revolute joints, prismatic parameters are configuration constants.

# Inverse kinematics

The robot has only revolute joints, so the joint angles are the variables; all DH distances and link dimensions are fixed. For the configured arm, joint 5 has $d_5 = a_5 = 0$, and joint 6 has $d_6 = 0.12$, $a_6 = 0$, and $\alpha_6 = 0$. There is no additional tool transform, so frame 6 is the end-effector frame.

### 1. Back out the J6 and J5 frame origins

Write the desired end-effector pose as

$$
{}^0T_6 =
\begin{bmatrix}
R_0^6 & {}^0\mathbf{p}_6 \\
\mathbf{0}^T & 1
\end{bmatrix},
\qquad
{}^0\mathbf{p}_6 =
\begin{bmatrix}x_6\\y_6\\z_6\end{bmatrix}.
$$

Because frame 6 is the end-effector frame, its origin is the target position:

$$
{}^0\mathbf{p}_{J6} = {}^0\mathbf{p}_6 = {}^0\mathbf{p}_{EE}.
$$

The J6 DH translation is $d_6$ along the preceding frame's $Z$ axis. Since $a_6 = 0$ and $\alpha_6 = 0$, the $Z$ axes of frames 5 and 6 are aligned, so the frame 5 (J5) origin is

$$
{}^0\mathbf{p}_{J5}
= {}^0\mathbf{p}_5
= {}^0\mathbf{p}_6 - d_6 R_0^6
\begin{bmatrix}0\\0\\1\end{bmatrix}
= {}^0\mathbf{p}_{EE} - 0.12
\begin{bmatrix}r_{13}\\r_{23}\\r_{33}\end{bmatrix}.
$$

Here $[r_{13},r_{23},r_{33}]^T$ is the end-effector's local $Z$ axis expressed in base coordinates (the third column of $R_0^6$). Thus the end-effector position alone determines J6, but finding J5 also requires the desired end-effector orientation, or at least its $Z$-axis direction.

### 2. Find the J1 angle and reduce to a plane

The J1 axis lies on base $Z$, so its origin $P_1$ has $x_1=y_1=0$. The
points $P_1$ through $P_5$ lie in the vertical plane selected by $\theta_1$.
The azimuth of $P_5$ around base $Z$ gives the angle of that plane:

$$
	heta_1 = \operatorname{atan2}(y_5-y_1,\ x_5-x_1)
= \operatorname{atan2}(y_5,\ x_5).
$$

Here $\operatorname{atan2}(y,x)$ returns the quadrant-correct angle, typically
in $(-\pi,\pi]$. This expression uses a nonnegative planar radius
$\rho=\sqrt{x_5^2+y_5^2}$. If the planar solution instead uses a signed radius,
the equivalent representation $\theta_1+\pi$ with radius $-\rho$ must also be
considered. Once the branch is chosen, rotate the target and arm geometry by
$-\theta_1$ about base $Z$; the remaining positions then lie in a 2D plane for
solving the other joint angles.

Thus the first joint angle is

$$
	heta_1 = \operatorname{atan2}(y_5,\ x_5).
$$

Rotate $P_5$ by $-\theta_1$ about base $Z$ to align the arm's plane with the
base $XZ$ plane. Since $P_1=(0,0,d_1)$ and this robot has $d_1=0.3$, the
resulting coordinates relative to J1 are

$$
{}^1\mathbf{p}_{5,\mathrm{plane}}
= R_z(-\theta_1)\left({}^0\mathbf{p}_5-{}^0\mathbf{p}_1\right)
= \begin{bmatrix}
\cos\theta_1 & \sin\theta_1 & 0 \\
-\sin\theta_1 & \cos\theta_1 & 0 \\
0 & 0 & 1
\end{bmatrix}
\begin{bmatrix}x_5\\y_5\\z_5-0.3\end{bmatrix}
= \begin{bmatrix}\rho\\0\\z_5-0.3\end{bmatrix},
\qquad
\rho=\sqrt{x_5^2+y_5^2}.
$$

So the 2D target for the remaining planar solve is $(\rho,\ z_5-0.3)$ in
radial-height coordinates measured from J1. The rotated point in base
coordinates, before subtracting J1, is $(\rho,0,z_5)$.