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

Here $[r_{13},r_{23},r_{33}]^T$ is the end-effector's local $Z$ axis expressed in base coordinates (the third column of $R_0^6$). Thus the end-effector position alone gives $P_6$, but finding $P_5$ also requires the desired end-effector orientation, or at least its $Z$-axis direction.

### 2. Robot handedness and branch choices

Inverse kinematics can have multiple branches. For this DH table, test both J1
plane orientations and both planar elbow configurations. Joint limits,
reachability, and collision checks can reject candidates. Also, $a_3=d_3=0$
and $\alpha_3=0$, so joints 3 and 4 are coaxial in this ideal DH model: the
pose depends on their sum $\psi=\theta_3+\theta_4$, not on each angle
individually. Position and orientation therefore cannot distinguish their
individual values; choose a split that satisfies the joint limits.

### 3. Find the J1 angle and reduce to a plane

The J1 rotation axis lies on base $Z$. In the current DH table, however,
$a_1=0.1$, so the frame origin $P_1$ is offset from that axis. The plane
containing $P_1$ through $P_5$ can have either of two azimuths, separated by
$\pi$. Let $r=\sqrt{x_5^2+y_5^2}$ and define $\sigma\in\{+1,-1\}$ to select
the plane orientation:

$$
\phi=\operatorname{atan2}(y_5,x_5),
\qquad
θ_1^{(\sigma)}=\operatorname{atan2}(\sigma y_5,\sigma x_5).
$$

Equivalently, $\theta_1^{(+)}=\phi$ and
$\theta_1^{(-)}=\operatorname{wrap}(\phi+\pi)$. Rotating $P_5$ into each
candidate plane and measuring from the actual frame origin $P_1$ gives the
signed planar radial target

$$
q_\sigma=\sigma r-a_1=\sigma r-0.1,
\qquad
h=z_5-d_1=z_5-0.3.
$$

Thus each J1 branch gives a different 2D target relative to J1:

$$
{}^1\mathbf{p}_{5,\mathrm{plane}}^{(\sigma)}
=\begin{bmatrix}q_\sigma\\h\end{bmatrix}
=\begin{bmatrix}\sigma\sqrt{x_5^2+y_5^2}-0.1\\z_5-0.3\end{bmatrix}.
$$

If $r=0$, the azimuth $\phi$ is undefined; position alone cannot determine
$\theta_1$, so handle that as a singular case rather than evaluating
$\operatorname{atan2}(0,0)$.

### 4. Calculate the planar elbow angle

The planar triangle has link lengths $L_2=a_2=0.4$ and $L_4=a_4=0.3$. For
each J1 branch $\sigma$, use its 2D target $(q_\sigma,h)$ and define

$$
D_\sigma=\sqrt{q_\sigma^2+h^2}.
$$

This is the distance from $P_1$ to $P_5$. The law of cosines gives two
candidate values for the relative direction of the second link, which for
this robot is the combined angle $\psi=\theta_3+\theta_4$:

$$
\cos\psi_\sigma=
\frac{D_\sigma^2-L_2^2-L_4^2}{2L_2L_4},
\qquad
\psi_{\sigma,\pm}=\pm\cos^{-1}\left(
\frac{D_\sigma^2-L_2^2-L_4^2}{2L_2L_4}
\right).
$$

For each J1 branch, a solution exists only if
$|L_2-L_4|\le D_\sigma\le L_2+L_4$. Clamp the cosine argument to $[-1,1]$
only to absorb small floating-point errors; otherwise reject an unreachable
target. Both signs are the elbow branches. The target determines $\psi$, not
$\theta_3$ by itself.

### 5. Calculate J2 from P5 and the selected branches

For each selected J1 and elbow branch, let $\psi=\psi_{\sigma,\pm}$ from the
previous section. The planar position equations are

$$
q_\sigma=L_2\cos\theta_2+L_4\cos(\theta_2+\psi),
\qquad
h=L_2\sin\theta_2+L_4\sin(\theta_2+\psi).
$$

Solving for $\theta_2$ gives

$$
θ_2=
\operatorname{atan2}(h,q_\sigma)
-\operatorname{atan2}\left(
L_4\sin\psi,\ L_2+L_4\cos\psi
\right).
$$

Only the sum $\psi=\theta_3+\theta_4$ is determined by this position solve.
Because joints 3 and 4 are coaxial with no intervening translation or twist,
the full DH pose also depends on them only through this sum. Choose any
$\theta_3$ within its limits and set

$$
θ_4=\operatorname{wrap}(\psi-\theta_3).
$$

Use radians in these equations and check all joint limits for the selected
branch and split.

### 6. Calculate J4

With $\theta_1$, $\theta_2$, and $\theta_3$ selected, the orientation $R_0^3$
is known. Since this robot has $a_5=d_5=0$, frames 4 and 5 have the same
origin, so $P_5-P_3$ is the fixed $a_4$ link vector. Express that vector in
frame 3:

$$
\mathbf{v}_4=(R_0^3)^T
\left({}^0\mathbf{p}_5-{}^0\mathbf{p}_3\right).
$$

Standard DH gives $\mathbf{v}_4=a_4[\cos\theta_4,\sin\theta_4,0]^T$.
Therefore

$$
θ_4=\operatorname{atan2}(v_{4y},v_{4x}),
\qquad a_4=0.3.
$$

The target must satisfy $\|\mathbf{v}_4\|=a_4$ and $v_{4z}=0$ within
numerical tolerance. Once $\theta_4$ is found, the frame-4 orientation is

$$
R_0^4=R_0^3R_z(\theta_4)R_x(\alpha_4),
\qquad \alpha_4=\frac{\pi}{2}.
$$

This recovers $\theta_4$ once a value of $\theta_3$ has been chosen. It should
agree with $\operatorname{wrap}(\psi-\theta_3)$ from the planar solve. The two
are not independently determined by the target pose; only their sum is.

### 7. Calculate J5

Since $a_5=d_5=0$, frames 4 and 5 have the same origin, so
${}^0\mathbf{p}_5$ is already known. The J6 offset is $d_6=0.12$ along the
local $Z$ axis of frame 5. Express the directed vector from P5 to P6 in frame
4 and normalize it:

$$
\mathbf{u}_5=(R_0^4)^T
\frac{{}^0\mathbf{p}_6-{}^0\mathbf{p}_5}{d_6}.
$$

For $\alpha_5=-\pi/2$, standard DH gives
$\mathbf{u}_5=[-\sin\theta_5,\ \cos\theta_5,\ 0]^T$, hence

$$
θ_5=\operatorname{atan2}(-u_{5x},u_{5y})
\pmod{2\pi}.
$$

Check that $\|{}^0\mathbf{p}_6-{}^0\mathbf{p}_5\|=d_6$ and $u_{5z}=0$
within numerical tolerance.

### 8. Calculate J6

The angle $\theta_6$ does not affect the position of P6 because this joint has
$a_6=0$ and its fixed offset $d_6$ lies along frame 5's $Z$ axis. Therefore,
P6 and the upstream joint angles alone cannot determine $\theta_6$; the desired
end-effector orientation $R_0^6$ is also required.

Once $\theta_1$ through $\theta_5$ are known, calculate the orientation of
frame 5:

$$
R_0^5=R_0^4R_z(\theta_5)R_x(\alpha_5),
\qquad \alpha_5=-\frac{\pi}{2}.
$$

The relative orientation from frame 5 to frame 6 is

$$
R_5^6=(R_0^5)^T R_0^6.
$$

Since $\alpha_6=0$, its DH rotation is simply $R_5^6=R_z(\theta_6)$, giving

$$
θ_6=\operatorname{atan2}\left((R_5^6)_{21},(R_5^6)_{11}\right)
\pmod{2\pi}.
$$

Here matrix indices are 1-based. For a valid target, $R_5^6$ should have the
form $R_z(\theta_6)$ (up to numerical tolerance); deviations indicate an
inconsistent target orientation or an incorrect upstream branch.