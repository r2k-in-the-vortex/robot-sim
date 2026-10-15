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

The robot has only revolute joints, so the joint angles are the variables; all DH distances and link dimensions are fixed. For the current configuration, $a_3 = d_3 = 0$ puts frame 3 on frame 2, $a_4 = 0$ keeps the joint 4 axis on the frame-3 $Z$ axis, $a_5 = d_5 = 0$ puts frame 5 on frame 4, joint 6 has $a_6 = 0$ and $\alpha_6 = 0$, and $\alpha_4 = \pi/2$ with $\alpha_5 = -\pi/2$. Joints 4, 5, and 6 therefore meet in a spherical wrist at the frame-4 origin. There is no additional tool transform, so frame 6 is the end-effector frame.

### 1. Back out the wrist center

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

The wrist center is the shared origin of frames 4 and 5. Since $\alpha_6=0$, frame 6's $Z$ axis is frame 5's $Z$ axis, and the frame-6 origin sits $a_6$ along frame 6's $X$ axis and $d_6$ along its $Z$ axis from the wrist center:

$$
{}^0\mathbf{p}_4
= {}^0\mathbf{p}_6 - R_0^6
\begin{bmatrix}a_6\\0\\d_6\end{bmatrix}
= {}^0\mathbf{p}_{EE} - a_6\,\mathbf{r}_1 - d_6\,\mathbf{r}_3,
$$

where $\mathbf{r}_1$ and $\mathbf{r}_3$ are the first and third columns of $R_0^6$, that is, frame 6's $X$ and $Z$ axes in base coordinates. The current robot has $a_6=0$ and $d_6=10$, so the wrist center is $P_{EE} - d_6\mathbf{r}_3$: finding it requires the desired orientation, not just the end-effector position.

### 2. Robot handedness and branch choices

Inverse kinematics can have multiple branches. For this DH table, test both J1
plane orientations, both planar elbow configurations, and both wrist flips, so
a reachable pose has up to eight solutions. Joint limits, reachability, and
collision checks can reject candidates. Because joints 3 and 4 are
perpendicular here rather than coaxial, the target determines each of them
separately. Every candidate is checked against the target pose with forward
kinematics before it is accepted, so a branch that does not reproduce the pose
is discarded instead of returned.

### 3. Find the J1 angle and reduce to a plane

The J1 rotation axis lies on base $Z$. In the current DH table, however,
$a_1=10$, so the frame origin $P_1$ is offset from that axis, and the frame-1
$X$ axis is the radial direction of the arm plane at azimuth $\theta_1$.
Everything past frame 1 lies in that plane: the plane containing $P_1$ and the
wrist center $P_4$ can have either of two azimuths, separated by
$\pi$. Let $r=\sqrt{x_4^2+y_4^2}$ and define $\sigma\in\{+1,-1\}$ to select
the plane orientation:

$$
\phi=\operatorname{atan2}(y_4,x_4),
\qquad
\theta_1^{(\sigma)}=\operatorname{atan2}(\sigma y_4,\sigma x_4).
$$

Equivalently, $\theta_1^{(+)}=\phi$ and
$\theta_1^{(-)}=\operatorname{wrap}(\phi+\pi)$. Rotating the wrist center into
each candidate plane and measuring from the actual frame origin $P_1$ gives the
signed planar radial target

$$
q_\sigma=\sigma r-a_1=\sigma r-10,
\qquad
h=z_4-d_1=z_4-40.
$$

Thus each J1 branch gives a different 2D target relative to J1:

$$
{}^1\mathbf{p}_{4,\mathrm{plane}}^{(\sigma)}
=\begin{bmatrix}q_\sigma\\h\end{bmatrix}
=\begin{bmatrix}\sigma\sqrt{x_4^2+y_4^2}-10\\z_4-40\end{bmatrix}.
$$

If $r=0$, the azimuth $\phi$ is undefined; position alone cannot determine
$\theta_1$. The pose is still reachable, so anchor the plane at $\theta_1=0$
and let the pose check decide, rather than evaluating
$\operatorname{atan2}(0,0)$.

### 4. Calculate the planar elbow angle

The planar chain has link lengths $L_2=a_2=40$ and $L_4=d_4=40$. The second
link is the $d_4$ offset along the joint 4 axis, which $\alpha_3=\pi/2$ turns
into a link perpendicular to that axis. For each J1 branch $\sigma$, use its 2D
target $(q_\sigma,h)$ and define

$$
D_\sigma=\sqrt{q_\sigma^2+h^2}.
$$

This is the distance from $P_1$ to the wrist center. The law of cosines gives
two candidate values for the relative direction of the second link, $\psi$:

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
target. Both signs are the elbow branches.

### 5. Calculate J2 from the wrist center and the selected branches

For each selected J1 and elbow branch, let $\psi=\psi_{\sigma,\pm}$ from the
previous section. The planar position equations are

$$
q_\sigma=L_2\cos\theta_2+L_4\cos(\theta_2+\psi),
\qquad
h=L_2\sin\theta_2+L_4\sin(\theta_2+\psi).
$$

Solving for $\theta_2$ gives

$$
\theta_2=
\operatorname{atan2}(h,q_\sigma)
-\operatorname{atan2}\left(
L_4\sin\psi,\ L_2+L_4\cos\psi
\right).
$$

### 6. Calculate J3

The second link points along $\theta_2+\psi$ in the plane, and because
$\alpha_3=\pi/2$ that direction is $\theta_2+\theta_3-\pi/2$. Hence

$$
\psi=\theta_3-\pi/2,
\qquad
\theta_3=\psi+\pi/2,
$$

so the position solve fixes $\theta_3$ as well: joints 3 and 4 are
perpendicular here, not coaxial, and the target separates them. One case is
still free: when $L_2=L_4$ and $D_\sigma=0$ the arm folds back with the wrist
center on $P_1$, which leaves $\theta_2$ undetermined. That pose is reachable,
so a split that reproduces it is returned rather than rejected.

Use radians in these equations and check all joint limits for the selected
branch.

### 7. Calculate the wrist angles

With $\theta_1$ through $\theta_3$ known, the orientation $R_0^3$ is known, and
the wrist rotation relative to frame 3 is

$$
R_3^6=(R_0^3)^T R_0^6
=R_z(\theta_4)R_x(\pi/2)R_z(\theta_5)R_x(-\pi/2)R_z(\theta_6)
=R_z(\theta_4)R_y(-\theta_5)R_z(\theta_6),
$$

a ZYZ decomposition. Its entries give the sine and cosine of $\theta_5$
directly:

$$
\sin\theta_5=\sqrt{(R_3^6)_{13}^2+(R_3^6)_{23}^2},
\qquad
\cos\theta_5=(R_3^6)_{33},
\qquad
\theta_5^{(\pm)}=\pm\operatorname{atan2}(\sin\theta_5,\cos\theta_5).
$$

Reading them from the matrix instead of through $\cos^{-1}$ matters near
$\theta_5=0$: there $\cos^{-1}$ stalls at the square root of the rounding
error in $(R_3^6)_{33}$, and the $d_6$ offset to the end effector magnifies
that stall into a position error.

For $\sin\theta_5\ne0$ the pair

$$
\theta_4=\operatorname{atan2}\left((R_3^6)_{23},(R_3^6)_{13}\right),
\qquad
\theta_6=\operatorname{atan2}\left((R_3^6)_{32},-(R_3^6)_{31}\right)
$$

solves the decomposition on the negative $\theta_5$ branch; adding $\pi$ to
both angles gives the positive branch. Those two are the wrist branches.

### 8. The wrist singularity

When $\sin\theta_5=0$, joints 4 and 6 share an axis, so only their combination
is observable: $\theta_4+\theta_6$ when $\theta_5=0$, and $\theta_4-\theta_6$
when $\theta_5=\pi$. Hold $\theta_4=0$ and read the combination off what
remains after removing joint 5:

$$
R_y(\theta_5)\,(R_0^3)^T R_0^6=R_z(\theta_6)
\qquad\text{when }\theta_4=0,
$$

so $\theta_6$ is the $\operatorname{atan2}$ pair of that product's first
column, and the position then follows from $P_4$ and the frame-4 orientation.
The pose is still reachable; only the split between joints 4 and 6 is not
unique, and any valid split may be chosen.

Here matrix indices are 1-based. Every candidate branch is verified with
forward kinematics before it is returned, so a target that no branch
reproduces, such as an unreachable position or an orientation inconsistent
with the position, yields no solution rather than an approximate one.
# Force/torque sensor dynamics

The static frame algebra of a wrench is proved in `lean/TorqueWrench.lean`; the model below adds
the two terms a real sensor actually measures — the inertia of the tool and payload, and gravity.
It is formalised in `lean/Dynamics.lean`, and the exact numbers it predicts are generated into
`test_data/force_torque_frames.json` (schema 3) and re-derived in `test_force_torque.py`.

## The measurement model

A sensor mounted between the wrist and the tool measures the wrench *transmitted through it*:
the wrench the proximal side applies to everything distal to it. That equals the contact wrench
carried up to the sensor frame, plus the inertial wrench of the distal body, minus the wrench
gravity exerts on it:

$$
W_{\text{measured}} = \operatorname{Ad}^{*}\!(p,R)\, W_{\text{contact}} + W_{\text{inertial}} - W_{\text{gravity}} .
$$

All three terms are expressed in the sensor frame. $g$ is the gravitational **acceleration**
(pointing down, $g \approx (0,0,-9.81)$ in the base frame); gravity exerts the force $m g$ on the
body, so a sensor holding it still feels $+m g$ from the arm and reads $-W_{\text{gravity}}$.

## Newton–Euler about the sensor origin

With $m$ the distal mass, $c$ its centre of mass in sensor coordinates, $I_c$ its inertia tensor
about the centre of mass, and $(v,\omega)$ and $(a,\alpha)$ the body's twist and acceleration,

$$
a_c = a + \alpha \times c + \omega \times (\omega \times c), \qquad
F = m\,a_c, \qquad
\tau = I_c\,\alpha + \omega \times (I_c\,\omega) + c \times F .
$$

$a_c$ is the acceleration of the material point at the centre of mass; the centripetal term
$\omega \times (\omega \times c)$ is the difference between that point and the sensor origin and
is the term most often dropped. The torque has three parts: the inertia couple $I_c \alpha$, the
gyroscopic term $\omega \times (I_c \omega)$, and the moment of the force through the lever arm
$c$.

## Gravity

$$
W_{\text{gravity}} = \bigl(m\,g,\; c \times (m\,g)\bigr) .
$$

A body at rest ($a = \alpha = 0$, $v = \omega = 0$) has $W_{\text{inertial}} = 0$, so the sensor
reads exactly $-W_{\text{gravity}}$. That single equation pins down the sign convention of the
whole model and is the first case in the generated data (`rest_gravity_only`).

## Frame changes

Writing $p$ for the tip origin in sensor coordinates and $R$ for the rotation from tip
coordinates to sensor coordinates, and assuming both frames are bolted to the same rigid body:

- a wrench is a covector and transports by the dual map, $\tau \mapsto R\tau + p \times (RF)$;
- a twist transports linearly, $v \mapsto R^T(v + \omega \times p)$, $\omega \mapsto R^T\omega$;
- an **acceleration does not transport like a twist**: the material point at the tip is not the
  one at the sensor origin, so
  $$
  a \mapsto R^T\bigl(a + \alpha \times p + \omega \times (\omega \times p)\bigr), \qquad
  \alpha \mapsto R^T \alpha ,
  $$
  which is why the acceleration transport has to be told the twist;
- the body's own description changes by $c \mapsto p + Rc$ and $I_c \mapsto R I_c R^T$.

With those rules the model is frame-independent: computing $W_{\text{inertial}}$ in the tip frame
and carrying it up gives the same wrench as computing it directly in the sensor frame, and the
same holds for gravity (with $g \mapsto Rg$). That is `Dynamics.inertialWrench_transport` and
`Dynamics.gravityWrench_transport`, and it is what lets mass properties be identified in one
frame and used in another.

## Compensation

The controller wants $W_{\text{contact}}$, so it runs the model backwards:

$$
W_{\text{contact}} = \operatorname{Ad}^{*}\!(p,R)^{-1}\Bigl(W_{\text{measured}} - W_{\text{inertial}} + W_{\text{gravity}}\Bigr) .
$$

Substituting the measurement model into the right-hand side returns the contact wrench exactly —
`Dynamics.recoveredContactWrench_measuredWrench`, with no approximation anywhere. What is left in
a real system is the accuracy of $m$, $c$, $I_c$ and of the acceleration estimate, not the algebra.

## Two forms of the same equations, and composition

Moving the inertia to the frame origin by the parallel-axis theorem, $I_O = I_c + m(\langle c,c\rangle \mathbf 1 - cc^T)$,
the torque becomes

$$
\tau = I_O\,\alpha + \omega \times (I_O\,\omega) + h \times a , \qquad h = m c ,
$$

and the force becomes $F = m a + \alpha \times h + \omega \times (\omega \times h)$: the same
motion, but the body now enters only through the triple $(m, h, I_O)$. That triple is what makes
bodies add — for two rigidly attached bodies with the same reference origin, masses, first
moments $h$ and origin inertias all sum, and so do their inertial and gravity wrenches. This is
`Dynamics.inertialWrench_add` / `Dynamics.gravityWrench_add`, i.e. how a tool and its payload
combine into one body. Note that the centre of mass itself,
$c = h/m$, is the one quantity that does *not* add without division, which is why the formalisation
is written in terms of $h$.

## Power

The inertial wrench's power on the body's own twist is

$$
F \cdot v + \tau \cdot \omega = m\, a_c \cdot (v + \omega \times c) + \alpha \cdot (I_c\,\omega),
$$

in which both the gyroscopic term and the lever arm cancel: the first because
$\omega \cdot (\omega \times I_c\omega) = 0$, the second by the cyclic invariance of the scalar
triple product. Gravity's power is $m\,g \cdot (v + \omega \times c)$, the rate at which
gravitational potential energy is lost. These are proved algebraically
(`Dynamics.virtualWork_inertialWrench`, `Dynamics.virtualWork_gravityWrench`), so they hold over
the rationals and are checkable by evaluation — no derivatives are needed anywhere in this file.
