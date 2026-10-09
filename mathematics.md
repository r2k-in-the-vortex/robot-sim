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

### 2. Robot handedness and branch choices

Inverse kinematics can have multiple branches. For position, test both J1
plane orientations and both elbow configurations; for a full-pose target, also
test the wrist configurations allowed by the orientation constraints. These
choices form a branch tree, but joint limits, collisions, and reachability can
reject any candidate. The branches are not independent: for this DH table,
position determines $\theta_3+\theta_4$, so a J3 value requires a chosen or
otherwise solved $\theta_4$.

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

### 4. Calculate J3 angle

For this robot, $a_3=0$, so the planar triangle has link lengths
$L_2=a_2=0.4$ and $L_4=a_4=0.3$. For each J1 branch $\sigma$, use its 2D
target $(q_\sigma,h)$ from the previous section and define

$$
D_\sigma=\sqrt{q_\sigma^2+h^2}.
$$

This is the distance from J1 frame origin $P_1$ to $P_5$. The two elbow
branches are the two signs of the relative link angle $\beta$. By the law of
cosines,

$$
\cos\beta_\sigma=
\frac{D_\sigma^2-L_2^2-L_4^2}{2L_2L_4},
\qquad
\beta_{\sigma,\pm}=\pm\cos^{-1}\left(
\frac{D_\sigma^2-L_2^2-L_4^2}{2L_2L_4}
\right).
$$

For either elbow branch, the corresponding J2 angle is

$$
θ_{2,\sigma,\pm}
=\operatorname{atan2}(h,q_\sigma)
-\operatorname{atan2}\left(
L_4\sin\beta_{\sigma,\pm},\ L_2+L_4\cos\beta_{\sigma,\pm}
\right).
$$

With these standard DH parameters, the direction of the $a_4$ link is set by
$\theta_2+\theta_3+\theta_4$. Therefore the position solve gives
$\beta=\theta_3+\theta_4$, not $\theta_3$ alone. Once $\theta_4$ has been
selected or determined from the desired orientation, each branch gives

$$
θ_{3,\sigma,\pm}
=\beta_{\sigma,\pm}-\theta_4
\pmod{2\pi}.
$$

Evaluate these two elbow branches for both $\sigma=+1$ and $\sigma=-1$; reject
any branch for which $|L_2-L_4|\le D_\sigma\le L_2+L_4$ is not satisfied. Then
apply joint limits, orientation constraints, and collision checks to the
remaining candidates. If $\theta_4=0$, the J3 candidates are simply
$\theta_{3,\sigma,\pm}=\beta_{\sigma,\pm}$

### 5. Calculate J2 from P5 and the selected branches

For a selected J1 branch, express $P_5$ relative to $P_1$ in the 2D plane as
$(q_\sigma,h)$. Let $\delta=\theta_3+\theta_4$ be the relative direction of
the $a_4$ link with respect to the $a_2$ link. The planar position equations
are

$$
q_\sigma=L_2\cos\theta_2+L_4\cos(\theta_2+\delta),
\qquad
h=L_2\sin\theta_2+L_4\sin(\theta_2+\delta).
$$

Solving for $\theta_2$ gives

$$
	heta_2=
\operatorname{atan2}(h,q_\sigma)
-\operatorname{atan2}\left(
L_4\sin\delta,\ L_2+L_4\cos\delta
\right).
$$

If $\theta_3$ is known and $\theta_4$ is fixed, substitute
$\delta=\theta_3+\theta_4$. In particular, if $\theta_4=0$, then
$\delta=\theta_3$. If only $\theta_3$ is known but $\theta_4$ is free,
$P_5$, J1, and J3 do not determine a unique J2; the position constrains the
sum $\theta_3+\theta_4$ instead. Use radians in these equations, and wrap the
result to the robot's joint-angle convention before checking joint limits.

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

This determines $\theta_4$ modulo $2\pi$ for the selected upstream branch.
Calculating $\theta_5$ is a later step: it requires the desired orientation,
or the target position $P_6$ as well as $P_5$.

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
within numerical tolerance. If the target pose also supplies $R_0^6$, the
remaining wrist angle can be recovered from

$$
R_4^6=(R_0^4)^T R_0^6,
\qquad
R_z(\theta_6)=R_x(\pi/2)R_z(-\theta_5)R_4^6,
$$

so $\theta_6=\operatorname{atan2}([R_z(\theta_6)]_{21},
[R_z(\theta_6)]_{11})$. This also provides an orientation consistency check
for the selected upstream and wrist branches.