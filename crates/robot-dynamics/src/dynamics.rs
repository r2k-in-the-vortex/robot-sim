//! Inertia, gravity, and the force/torque sensor measurement model: `lean/Dynamics.lean`.
//!
//! [`wrench`](crate::wrench) is the *static* frame algebra — a wrench carried from the tool tip
//! to the sensor frame, with virtual power preserved. A real sensor, though, measures the wrench
//! *transmitted through it*, which is the contact wrench plus the gravitational and inertial
//! wrench of everything mounted distal to it. This module adds those two terms
//! ([`inertial_wrench`], [`gravity_wrench`]), puts them together into the measurement model
//! ([`measured_wrench`]), and runs it backwards ([`recovered_contact_wrench`]).
//!
//! No calculus appears anywhere. Acceleration is an independent datum rather than a derivative,
//! so the "power" identities that would elsewhere be statements about `d/dt` of kinetic energy
//! are polynomial equations here and hold over any field — which is what makes the whole module
//! checkable by evaluation over the rationals.
//!
//! Conventions, all inherited from [`wrench`](crate::wrench) unless stated:
//!
//! * `p` is the tip origin in **sensor** coordinates and a [`Rotation`] maps tip coordinates to
//!   sensor coordinates. Both frames are rigidly attached to the same body, which is what makes
//!   the acceleration transport an identity of rigid-body kinematics rather than an assumption.
//! * The sensor measures the wrench the proximal side applies to the distal body. With `g` the
//!   gravitational *acceleration* (pointing down, not the reaction to it), a sensor at rest reads
//!   `-gravityWrench`.
//! * [`MassProperties`] carries the centre of mass and the inertia **about the centre of mass**.
//!   The inertia about the frame origin is derived ([`origin_inertia`]), and it is that derived
//!   quantity, with the mass and the first moment, that makes bodies add.

use crate::wrench::{Rotation, Twist, Wrench, sensor_to_tip, tip_to_sensor};
use core::ops::{Add, Neg, Sub};
use robot_kinematics::{Field, Mat3, Vec3};

/// The mass distribution of a rigid body in one frame: its mass, the centre of mass relative to
/// the frame origin, and the inertia tensor about that centre of mass.
///
/// `Dynamics.MassProperties`. The inertia is required to be symmetric, which the Lean structure
/// bundles as the field `inertia_symm` and this type checks in [`MassProperties::new`]. Symmetry
/// is not cosmetic: it is what lets the angular power be written as `α ⋅ (I ω)` rather than
/// `(I α) ⋅ ω` (`dot_mulVec_self`).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MassProperties<S> {
    mass: S,
    com: Vec3<S>,
    inertia: Mat3<S>,
}

impl<S: Field> MassProperties<S> {
    /// The checked constructor: `None` unless the inertia tensor is symmetric.
    #[inline]
    pub fn new(mass: S, com: Vec3<S>, inertia: Mat3<S>) -> Option<Self> {
        if inertia.transpose() == inertia {
            Some(Self { mass, com, inertia })
        } else {
            None
        }
    }

    /// The constructor for the sites where symmetry is *proved* rather than checked.
    ///
    /// Lean's `tipMassToSensor` and `sensorMassToTip` each discharge the structure's `inertia_symm`
    /// obligation with a `calc` over transposes — conjugating a symmetric tensor by `R` and by `Rᵀ`
    /// is symmetric again, with no orthogonality needed. This constructor is that proof carried by
    /// the type: it is private, so no caller can reach it, and the two functions above are the only
    /// users.
    #[inline]
    fn symmetric(mass: S, com: Vec3<S>, inertia: Mat3<S>) -> Self {
        Self { mass, com, inertia }
    }

    /// The mass, Lean's `MassProperties.mass`.
    #[inline]
    pub fn mass(self) -> S {
        self.mass
    }

    /// The centre of mass relative to the frame origin, Lean's `MassProperties.com`.
    #[inline]
    pub fn com(self) -> Vec3<S> {
        self.com
    }

    /// The inertia tensor about the centre of mass, Lean's `MassProperties.inertia`.
    #[inline]
    pub fn inertia(self) -> Mat3<S> {
        self.inertia
    }
}

/// The acceleration of a frame: `a` is the acceleration of the frame origin's material point and
/// `alpha` the angular acceleration, both in that frame's coordinates.
///
/// `Dynamics.Accel`. Unlike a velocity, an acceleration is **not** frame-independent: it belongs
/// to a particular material point, which is why the transports below have to name both points.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Accel<S> {
    /// Lean's `Accel.a`.
    pub a: Vec3<S>,
    /// Lean's `Accel.alpha`.
    pub alpha: Vec3<S>,
}

impl<S: Field> Accel<S> {
    #[inline]
    pub const fn new(a: Vec3<S>, alpha: Vec3<S>) -> Self {
        Self { a, alpha }
    }

    /// The zero acceleration, Lean's `0`.
    #[inline]
    pub fn zero() -> Self {
        Self::new(Vec3::zero(), Vec3::zero())
    }

    /// Scale both parts, Lean's `c • x`.
    #[inline]
    pub fn scale(self, factor: S) -> Self {
        Self::new(self.a.scale(factor), self.alpha.scale(factor))
    }
}

impl<S: Field> Add for Accel<S> {
    type Output = Self;
    #[inline]
    fn add(self, other: Self) -> Self {
        Self::new(self.a + other.a, self.alpha + other.alpha)
    }
}

impl<S: Field> Sub for Accel<S> {
    type Output = Self;
    #[inline]
    fn sub(self, other: Self) -> Self {
        Self::new(self.a - other.a, self.alpha - other.alpha)
    }
}

impl<S: Field> Neg for Accel<S> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::new(-self.a, -self.alpha)
    }
}

/// The acceleration of the body's centre of mass, Lean's `comAccel`:
/// `a + α × c + ω × (ω × c)`.
///
/// The centripetal term `ω × (ω × c)` is the difference between the acceleration of the material
/// point at the frame origin and the one at the centre of mass. It is the term most often
/// dropped, and dropping it silently breaks every covariance statement downstream — which is why
/// the Lean proof isolates it in `comAccel_transport`.
#[inline]
pub fn com_accel<S: Field>(mp: MassProperties<S>, t: Twist<S>, acc: Accel<S>) -> Vec3<S> {
    let c = mp.com();
    acc.a + acc.alpha.cross(c) + t.omega.cross(t.omega.cross(c))
}

/// The inertial wrench of a rigid body: the wrench that has to be applied to produce the motion
/// `(t, acc)`, i.e. minus the wrench the body's inertia exerts on its surroundings.
///
/// `Dynamics.inertialWrench`, the Newton–Euler equations about the frame origin: the force is
/// `m a_c`, and the torque is the inertia couple `I α`, the gyroscopic term `ω × (I ω)` and the
/// moment of the force through the lever arm `c × F`.
#[inline]
pub fn inertial_wrench<S: Field>(mp: MassProperties<S>, t: Twist<S>, acc: Accel<S>) -> Wrench<S> {
    let inertia = mp.inertia();
    let force = com_accel(mp, t, acc).scale(mp.mass());
    let torque = inertia.mul_vec(acc.alpha)
        + t.omega.cross(inertia.mul_vec(t.omega))
        + mp.com().cross(force);
    Wrench::new(force, torque)
}

/// The wrench a uniform gravitational field `g` exerts on the body, Lean's `gravityWrench`: the
/// force `m g` applied at the centre of mass, so its moment about the frame origin is `c × (m g)`.
///
/// `g` is the gravitational *acceleration*, pointing down — not the reaction to it. Gravity exerts
/// `m g` on the body, so a sensor holding it still feels `+m g` from the arm and reads
/// `-gravityWrench`; that single equation pins the sign convention of the whole model
/// (`measuredWrench_at_rest`).
#[inline]
pub fn gravity_wrench<S: Field>(mp: MassProperties<S>, g: Vec3<S>) -> Wrench<S> {
    let force = g.scale(mp.mass());
    Wrench::new(force, mp.com().cross(force))
}

/// The first moment of mass `m c`, Lean's `firstMoment`.
///
/// It is the quantity that adds when bodies are combined, where the centre of mass itself would
/// need division — which is why the whole additive form below is written in terms of it.
#[inline]
pub fn first_moment<S: Field>(mp: MassProperties<S>) -> Vec3<S> {
    mp.com().scale(mp.mass())
}

/// The parallel-axis term `m (⟨c, c⟩ 1 - c cᵀ)` of Lean's `originInertia`, on its own.
///
/// Exposed because the *inverse* direction needs exactly this correction — recovering `I_c` from
/// an inertia identified about the frame origin — and Lean, which never has to invert the shift,
/// only ever writes the two terms together.
#[inline]
pub fn parallel_axis_inertia<S: Field>(mass: S, com: Vec3<S>) -> Mat3<S> {
    let square = com.dot(com);
    matrix_scale(
        matrix_sub(matrix_scale(Mat3::identity(), square), outer(com, com)),
        mass,
    )
}

/// The inertia tensor about the *frame origin* rather than about the centre of mass, Lean's
/// `originInertia`: the parallel-axis shift `I_c + m (⟨c, c⟩ 1 - c cᵀ)`.
///
/// This is the form in which inertias add, and it is one of the three quantities — with the mass
/// and the first moment — through which a body enters the spatial inertial wrench. The centre of
/// mass is the one thing that does *not* add, because it needs a division to combine.
#[inline]
pub fn origin_inertia<S: Field>(mp: MassProperties<S>) -> Mat3<S> {
    matrix_add(
        mp.inertia(),
        parallel_axis_inertia(mp.mass(), mp.com()),
    )
}

/// The tip's acceleration in tip coordinates, from the sensor's twist and acceleration: Lean's
/// `sensorAccelToTip`.
///
/// Both frames are rigidly attached to the same body, so the material point at the tip has
/// acceleration `a + α × p + ω × (ω × p)` in sensor coordinates. The `ω × (ω × p)` term is the
/// centripetal difference between the two points — the classic acceleration frame-change error is
/// to drop it — and the result rotates back by `Rᵀ`, as the twist transport does. Note the
/// signature: the transport has to be told the *twist*, because the acceleration of a point is not
/// a function of the frame alone.
#[inline]
pub fn sensor_accel_to_tip<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    t: Twist<S>,
    acc: Accel<S>,
) -> Accel<S> {
    let a = acc.a + acc.alpha.cross(p) + t.omega.cross(t.omega.cross(p));
    Accel::new(r.transpose_mul_vec(a), r.transpose_mul_vec(acc.alpha))
}

/// The inverse of [`sensor_accel_to_tip`], Lean's `tipAccelToSensor`: the sensor's acceleration in
/// sensor coordinates, from the tip's twist and acceleration in tip coordinates.
///
/// The lever arm is `p` in sensor coordinates — the same arm [`crate::tip_twist_to_sensor`]
/// subtracts — combined with the angular parts rotated forward; the centripetal term is subtracted
/// along with the `α × p` one.
#[inline]
pub fn tip_accel_to_sensor<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    t: Twist<S>,
    acc: Accel<S>,
) -> Accel<S> {
    let alpha = r.mul_vec(acc.alpha);
    let omega = r.mul_vec(t.omega);
    Accel::new(
        r.mul_vec(acc.a) - alpha.cross(p) - omega.cross(omega.cross(p)),
        alpha,
    )
}

/// The same body described in sensor coordinates, Lean's `tipMassToSensor`: the mass is unchanged,
/// the centre of mass moves to `p + R c`, and the inertia tensor conjugates to `R I Rᵀ`.
///
/// Mass properties are intrinsic to the body, so this is a change of description rather than a
/// change of physics — which is what `inertialWrench_transport` and `gravityWrench_transport`
/// make good on, and what lets a body be identified in one frame and used in another.
#[inline]
pub fn tip_mass_to_sensor<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    mp: MassProperties<S>,
) -> MassProperties<S> {
    let mat = r.mat();
    MassProperties::symmetric(
        mp.mass(),
        p + r.mul_vec(mp.com()),
        mat * mp.inertia() * mat.transpose(),
    )
}

/// The inverse of [`tip_mass_to_sensor`], Lean's `sensorMassToTip`: the same body described in tip
/// coordinates, with the centre of mass back at `Rᵀ (c - p)` and the inertia tensor conjugated by
/// `Rᵀ`.
#[inline]
pub fn sensor_mass_to_tip<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    mp: MassProperties<S>,
) -> MassProperties<S> {
    let mat = r.mat();
    MassProperties::symmetric(
        mp.mass(),
        r.transpose_mul_vec(mp.com() - p),
        mat.transpose() * mp.inertia() * mat,
    )
}

/// The inertial wrench in terms of the additive triple — mass, first moment, and inertia about the
/// frame *origin* — instead of the centre of mass and the inertia about it. Lean's
/// `spatialInertialWrench`.
///
/// The two are the same Newton–Euler equations (`inertialWrench_origin_form`), but this is the
/// form that can be *summed*: the torque about the frame origin is
/// `I_O α + ω × (I_O ω) + h × a`, and none of `(m, h, I_O)` needs division to combine.
#[inline]
pub fn spatial_inertial_wrench<S: Field>(
    mass: S,
    first_moment: Vec3<S>,
    origin_inertia: Mat3<S>,
    t: Twist<S>,
    acc: Accel<S>,
) -> Wrench<S> {
    let force = acc.a.scale(mass)
        + acc.alpha.cross(first_moment)
        + t.omega.cross(t.omega.cross(first_moment));
    let torque = origin_inertia.mul_vec(acc.alpha)
        + t.omega.cross(origin_inertia.mul_vec(t.omega))
        + first_moment.cross(acc.a);
    Wrench::new(force, torque)
}

/// The gravity wrench in the additive form, Lean's `spatialGravityWrench`: the force is `m g` and
/// the moment is `h × g`, the centre of mass appearing only through the first moment.
#[inline]
pub fn spatial_gravity_wrench<S: Field>(
    mass: S,
    first_moment: Vec3<S>,
    g: Vec3<S>,
) -> Wrench<S> {
    Wrench::new(g.scale(mass), first_moment.cross(g))
}

/// The wrench a force/torque sensor reads, Lean's `measuredWrench`: the contact wrench carried up
/// to the sensor frame, plus the inertial wrench of everything distal to it, minus the
/// gravitational wrench of that same body.
///
/// `mp` is the mass distribution of everything distal to the sensor, in **tip** coordinates; `t`,
/// `acc` and `g` are the body's twist, its acceleration and the gravitational acceleration in
/// **sensor** coordinates; `contact` is the external wrench at the tip, in tip coordinates. This is
/// a model of an ideal sensor: no bias, no noise, no compliance.
#[inline]
pub fn measured_wrench<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    mp: MassProperties<S>,
    t: Twist<S>,
    acc: Accel<S>,
    g: Vec3<S>,
    contact: Wrench<S>,
) -> Wrench<S> {
    let distal = tip_mass_to_sensor(p, r, mp);
    tip_to_sensor(p, r, contact) + inertial_wrench(distal, t, acc) - gravity_wrench(distal, g)
}

/// Gravity and inertia compensation, Lean's `recoveredContactWrench`: subtract the model's
/// inertial wrench from the measurement, add gravity back, and carry the result down to the tip,
/// where the contact actually is.
///
/// `recoveredContactWrench_measuredWrench` proves this is an exact inverse of
/// [`measured_wrench`] — no approximation, no tuning — so what is left in a real system is the
/// accuracy of `m`, `c`, `I_c` and of the acceleration estimate, not the algebra.
#[inline]
pub fn recovered_contact_wrench<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    mp: MassProperties<S>,
    t: Twist<S>,
    acc: Accel<S>,
    g: Vec3<S>,
    measured: Wrench<S>,
) -> Wrench<S> {
    let distal = tip_mass_to_sensor(p, r, mp);
    sensor_to_tip(
        p,
        r,
        measured - inertial_wrench(distal, t, acc) + gravity_wrench(distal, g),
    )
}

// The kinematics crate's `Mat3` carries the product and the transpose, which is all the chain
// machinery needs. The Newton-Euler equations need entry-wise arithmetic as well; these three
// helpers supply it here rather than widening the frozen kinematics API.

/// `left + right`, entry-wise.
fn matrix_add<S: Field>(left: Mat3<S>, right: Mat3<S>) -> Mat3<S> {
    let mut sum = left;
    for i in 0..3 {
        for j in 0..3 {
            sum.set(i, j, left.at(i, j) + right.at(i, j));
        }
    }
    sum
}

/// `left - right`, entry-wise.
fn matrix_sub<S: Field>(left: Mat3<S>, right: Mat3<S>) -> Mat3<S> {
    let mut difference = left;
    for i in 0..3 {
        for j in 0..3 {
            difference.set(i, j, left.at(i, j) - right.at(i, j));
        }
    }
    difference
}

/// `matrix * factor`, entry-wise.
fn matrix_scale<S: Field>(matrix: Mat3<S>, factor: S) -> Mat3<S> {
    let mut scaled = matrix;
    for i in 0..3 {
        for j in 0..3 {
            scaled.set(i, j, matrix.at(i, j) * factor);
        }
    }
    scaled
}

/// The outer product `u vᵀ`, Lean's `Matrix.vecMulVec`.
fn outer<S: Field>(u: Vec3<S>, v: Vec3<S>) -> Mat3<S> {
    let mut product = Mat3::zero();
    for i in 0..3 {
        for j in 0..3 {
            product.set(i, j, u[i] * v[j]);
        }
    }
    product
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_golden::Ratio as R;
    use robot_kinematics::Field;

    fn vec3(x: i128, y: i128, z: i128) -> Vec3<R> {
        Vec3::new(R::integer(x), R::integer(y), R::integer(z))
    }

    fn diagonal(a: i128, b: i128, c: i128) -> Mat3<R> {
        Mat3::from_rows([
            [R::integer(a), R::zero(), R::zero()],
            [R::zero(), R::integer(b), R::zero()],
            [R::zero(), R::zero(), R::integer(c)],
        ])
    }

    /// A body of mass 2 with its centre of mass on the x axis and unit inertia.
    fn body() -> MassProperties<R> {
        MassProperties::new(R::integer(2), vec3(1, 0, 0), diagonal(1, 1, 1))
            .expect("a diagonal inertia is symmetric")
    }

    #[test]
    fn an_asymmetric_inertia_is_rejected() {
        let crooked = Mat3::from_rows([
            [R::one(), R::one(), R::zero()],
            [R::zero(), R::one(), R::zero()],
            [R::zero(), R::zero(), R::one()],
        ]);
        assert!(MassProperties::new(R::one(), Vec3::zero(), crooked).is_none());

        // conjugating a symmetric tensor by a rotation is symmetric, which is the obligation
        // `tip_mass_to_sensor` discharges privately rather than by checking
        let r = Rotation::rot_z_cs(R::pair((3, 5), (4, 5))).expect("(3/5, 4/5) is a unit pair");
        let moved = tip_mass_to_sensor(vec3(0, 0, 3), r, body());
        assert_eq!(moved.inertia().transpose(), moved.inertia());
        assert_eq!(sensor_mass_to_tip(vec3(0, 0, 3), r, moved), body());
    }

    #[test]
    fn a_body_with_no_motion_has_no_inertial_wrench() {
        assert_eq!(
            inertial_wrench(body(), Twist::zero(), Accel::zero()),
            Wrench::zero(),
            "inertialWrench_zero"
        );
        assert_eq!(gravity_wrench(body(), Vec3::zero()), Wrench::zero());
        assert_eq!(com_accel(body(), Twist::zero(), Accel::zero()), Vec3::zero());
    }

    #[test]
    fn a_spinning_body_feels_only_the_centripetal_term() {
        // a = α = 0 at the origin, but the centre of mass is off the axis: the force is exactly
        // `m ω × (ω × c)`, which is what a model missing the centripetal term reports as zero.
        let t = Twist::new(Vec3::zero(), vec3(0, 0, 3));
        let force = inertial_wrench(body(), t, Accel::zero()).force;
        // ω × (ω × c) with ω = 3ẑ and c = x̂ is -9 x̂
        assert_eq!(force, vec3(-18, 0, 0));
    }

    #[test]
    fn the_parallel_axis_shift_is_the_textbook_one() {
        // a point mass a unit off the z axis: `I_O = m (⟨c,c⟩ 1 - c cᵀ)` is `diag(0, 1, 1)`
        let point = MassProperties::new(R::one(), vec3(1, 0, 0), Mat3::zero())
            .expect("the zero matrix is symmetric");
        assert_eq!(origin_inertia(point), diagonal(0, 1, 1));
        assert_eq!(first_moment(point), vec3(1, 0, 0));
    }

    #[test]
    fn gravity_on_a_body_at_rest_is_a_force_through_the_centre_of_mass() {
        // `g` points down, so the force is `m g` and the moment is `c × (m g)` = -m g c_y ... and
        // with c on the x axis and g down z, the moment is about the y axis.
        let w = gravity_wrench(body(), vec3(0, 0, -1));
        assert_eq!(w.force, vec3(0, 0, -2));
        assert_eq!(w.torque, vec3(0, 2, 0));
    }

    #[test]
    fn the_two_newton_euler_forms_agree_on_a_worked_case() {
        // `inertialWrench_origin_form`, at a single concrete motion rather than by property.
        let mp = body();
        let t = Twist::new(vec3(1, -1, 2), vec3(0, 1, 0));
        let acc = Accel::new(vec3(0, 2, 1), vec3(1, 0, -1));
        assert_eq!(
            inertial_wrench(mp, t, acc),
            spatial_inertial_wrench(
                mp.mass(),
                first_moment(mp),
                origin_inertia(mp),
                t,
                acc
            )
        );
        assert_eq!(
            gravity_wrench(mp, vec3(0, 0, -1)),
            spatial_gravity_wrench(mp.mass(), first_moment(mp), vec3(0, 0, -1))
        );
    }

    #[test]
    fn compensation_undoes_the_measurement() {
        let mp = body();
        let contact = Wrench::new(vec3(1, 2, 3), vec3(-1, 0, 1));
        let t = Twist::new(vec3(1, 0, 0), vec3(0, 2, 0));
        let acc = Accel::new(vec3(0, 0, -1), vec3(0, 1, 0));
        let g = vec3(0, 0, -9);
        let p = vec3(0, 1, 2);
        let r = Rotation::rot_y_cs(R::pair((4, 5), (3, 5))).expect("(4/5, 3/5) is a unit pair");

        let measured = measured_wrench(p, r, mp, t, acc, g, contact);
        assert_eq!(
            recovered_contact_wrench(p, r, mp, t, acc, g, measured),
            contact
        );
        // and at rest with no contact the sensor reads minus its gravity wrench
        assert_eq!(
            measured_wrench(p, r, mp, Twist::zero(), Accel::zero(), g, Wrench::zero()),
            -gravity_wrench(tip_mass_to_sensor(p, r, mp), g)
        );
    }
}
