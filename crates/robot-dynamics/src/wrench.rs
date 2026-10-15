//! Wrench and twist frame transformations: `lean/TorqueWrench.lean`.
//!
//! A wrench ([`Wrench`]) is a force and a moment; a twist ([`Twist`]) is a linear and an
//! angular velocity. The transformation that matters is the one that preserves virtual power,
//! so this module defines both transforms and states the power identity in
//! [`virtual_work`]'s presence — `virtualWork_invariant`, re-derived as an executable property
//! in `tests/theorems.rs`.
//!
//! Throughout, `p` is the tip origin expressed in sensor coordinates and a [`Rotation`] maps
//! tip coordinates to sensor coordinates. Both frames are rigidly attached to the same body.
//!
//! Everything is a polynomial in the inputs, so every function here is generic over
//! [`Field`] and evaluates exactly over the rationals.

use core::ops::{Add, Mul, Neg, Sub};
use robot_kinematics::{CosSin, Field, Mat3, Vec3};

/// A wrench: a force and a torque (a moment) about the frame origin.
///
/// `TorqueWrench.Wrench`. The name of the Lean module is the only place "torque wrench"
/// appears — the structure is the subject, and every transform below is one of its changes of
/// frame.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Wrench<S> {
    /// The linear part, Lean's `Wrench.force`.
    pub force: Vec3<S>,
    /// The moment part, Lean's `Wrench.torque`.
    pub torque: Vec3<S>,
}

/// A twist: the velocity of a rigid body at a point, as a linear and an angular part.
///
/// `TorqueWrench.Twist`. `v` is the velocity of the reference point, `omega` the angular
/// velocity; both are measured along the frame's axes, which is what makes the frame change
/// more than a shift of reference point.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Twist<S> {
    /// The velocity of the reference point, Lean's `Twist.v`.
    pub v: Vec3<S>,
    /// The angular velocity, Lean's `Twist.ω` — spelled out here.
    pub omega: Vec3<S>,
}

impl<S: Field> Wrench<S> {
    #[inline]
    pub const fn new(force: Vec3<S>, torque: Vec3<S>) -> Self {
        Self { force, torque }
    }

    /// The zero wrench, Lean's `0`. A free-held body at rest reads exactly this.
    #[inline]
    pub fn zero() -> Self {
        Self::new(Vec3::zero(), Vec3::zero())
    }

    /// Scale both parts, Lean's `c • a`. The mass factors out of the inertial wrench this way.
    #[inline]
    pub fn scale(self, factor: S) -> Self {
        Self::new(self.force.scale(factor), self.torque.scale(factor))
    }
}

impl<S: Field> Twist<S> {
    #[inline]
    pub const fn new(v: Vec3<S>, omega: Vec3<S>) -> Self {
        Self { v, omega }
    }

    /// The zero twist, Lean's `0`. A body with zero twist and zero acceleration has no
    /// inertial wrench (`inertialWrench_zero`).
    #[inline]
    pub fn zero() -> Self {
        Self::new(Vec3::zero(), Vec3::zero())
    }

    /// Scale both parts, Lean's `c • a`.
    #[inline]
    pub fn scale(self, factor: S) -> Self {
        Self::new(self.v.scale(factor), self.omega.scale(factor))
    }
}

// The pointwise group and module operations `Dynamics.lean` adds: a measured wrench is a sum
// of terms, and compensation subtracts them again, so both structures need them.

impl<S: Field> Add for Wrench<S> {
    type Output = Self;
    #[inline]
    fn add(self, other: Self) -> Self {
        Self::new(self.force + other.force, self.torque + other.torque)
    }
}

impl<S: Field> Sub for Wrench<S> {
    type Output = Self;
    #[inline]
    fn sub(self, other: Self) -> Self {
        Self::new(self.force - other.force, self.torque - other.torque)
    }
}

impl<S: Field> Neg for Wrench<S> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::new(-self.force, -self.torque)
    }
}

impl<S: Field> Add for Twist<S> {
    type Output = Self;
    #[inline]
    fn add(self, other: Self) -> Self {
        Self::new(self.v + other.v, self.omega + other.omega)
    }
}

impl<S: Field> Sub for Twist<S> {
    type Output = Self;
    #[inline]
    fn sub(self, other: Self) -> Self {
        Self::new(self.v - other.v, self.omega - other.omega)
    }
}

impl<S: Field> Neg for Twist<S> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::new(-self.v, -self.omega)
    }
}

/// The virtual power (work rate) of a wrench on a twist: `F ⋅ v + τ ⋅ ω`, Lean's `virtualWork`.
///
/// This is the quantity the frame change has to preserve, and that requirement is what pins
/// the transformations down: a wrench is a covector and transports by the dual map, a twist
/// transports linearly, and only that pair leaves this dot product alone.
#[inline]
pub fn virtual_work<S: Field>(wrench: Wrench<S>, twist: Twist<S>) -> S {
    wrench.force.dot(twist.v) + wrench.torque.dot(twist.omega)
}

/// A rotation: an orthogonal matrix with determinant one, Lean's `Rotation`.
///
/// Both properties are load-bearing and neither implies the other:
///
/// * orthogonality makes the transforms invertible — the round trips `sensorToTip_tipToSensor`
///   and `tipToSensor_sensorToTip` need `Rᵀ R = 1` and `R Rᵀ = 1` respectively;
/// * determinant one makes a rotation commute with the cross product (`mulVec_cross`), which
///   is what lets a frame change be composed — a rotation from `diag(1, 1, -1)` satisfies the
///   first and *anti*-commutes with the cross product instead, so composing through it would
///   report the wrong torque (`Rotation`'s section of `TorqueWrench.lean` says exactly this).
///
/// The matrix is private: the only ways in are [`Rotation::new`], [`Rotation::checked`], the
/// axis rotations built from a unit cosine/sine pair, [`Rotation::identity`], composition and
/// inversion — every one of which either checks the invariant or preserves it.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Rotation<S> {
    mat: Mat3<S>,
}

impl<S: Field> Rotation<S> {
    /// The checked constructor: `None` unless `matᵀ mat` is the identity and `det mat` is one.
    ///
    /// The comparison is `==` on the entries — the exact test, which is the right one over the
    /// rationals the ground truth is written in. Over a floating-point [`Field`] use
    /// [`Rotation::checked`], which takes a band instead.
    #[inline]
    pub fn new(mat: Mat3<S>) -> Option<Self> {
        Self::checked(mat, S::zero())
    }

    /// The checked constructor with a tolerance, for a floating-point [`Field`] where exact
    /// orthogonality is not achievable. `tolerance` of zero is [`Rotation::new`].
    ///
    /// The band is a practical compromise, not a weakening of the algebra: a matrix that is
    /// only *approximately* orthogonal satisfies the round trips only approximately, so the
    /// caller is trading exactness for representability, exactly as every floating-point use
    /// of the specification does.
    #[inline]
    pub fn checked(mat: Mat3<S>, tolerance: S) -> Option<Self> {
        let orthogonality = mat.transpose() * mat;
        if within(orthogonality, Mat3::identity(), tolerance)
            && (mat.det() - S::one()).abs() <= tolerance
        {
            Some(Self { mat })
        } else {
            None
        }
    }

    /// The identity rotation, `Rotation.id`.
    #[inline]
    pub fn identity() -> Self {
        Self {
            mat: Mat3::identity(),
        }
    }

    /// A rotation about the x axis from an explicit cosine and sine, Lean's `rotX`.
    ///
    /// The pair is *data*, not an angle: a Pythagorean pair such as `(4/5, 3/5)` is exactly on
    /// the unit circle, so a rotation built from one is an exact rational rotation. That is how
    /// the exact tests generate rotations at all — there is no angle in this crate.
    ///
    /// `None` when the pair is not on the unit circle, so what the constructor checks is the
    /// invariant and not merely the arithmetic.
    #[inline]
    pub fn rot_x_cs(angle: CosSin<S>) -> Option<Self> {
        Self::new(Mat3::rot_x_cs(angle))
    }

    /// A rotation about the y axis from an explicit cosine and sine, Lean's `rotY`.
    #[inline]
    pub fn rot_y_cs(angle: CosSin<S>) -> Option<Self> {
        Self::new(Mat3::rot_y_cs(angle))
    }

    /// A rotation about the z axis from an explicit cosine and sine, Lean's `rotZ`.
    #[inline]
    pub fn rot_z_cs(angle: CosSin<S>) -> Option<Self> {
        Self::new(Mat3::rot_z_cs(angle))
    }

    /// The matrix behind the rotation, Lean's `Rotation.mat`.
    #[inline]
    pub fn mat(self) -> Mat3<S> {
        self.mat
    }

    /// Rotate a vector: `ρ.mat *ᵥ u`. The operation every tip-to-sensor transform is built on.
    #[inline]
    pub fn mul_vec(self, v: Vec3<S>) -> Vec3<S> {
        self.mat.mul_vec(v)
    }

    /// Rotate a vector by the inverse — `ρ.matᵀ *ᵥ u`, which for a rotation *is* the inverse
    /// (`Rotation.inv`). The operation every sensor-to-tip transform is built on.
    #[inline]
    pub fn transpose_mul_vec(self, v: Vec3<S>) -> Vec3<S> {
        self.mat.transpose().mul_vec(v)
    }

    /// The inverse rotation, which for a rotation is the transpose (`Rotation.inv`).
    #[inline]
    pub fn inverse(self) -> Self {
        Self {
            mat: self.mat.transpose(),
        }
    }

    /// Whether this is the identity rotation. Used by callers that can take a shortcut when no
    /// frame change is needed at all; not a Lean declaration.
    #[inline]
    pub fn is_identity(self) -> bool {
        self.mat == Mat3::identity()
    }
}

impl<S: Field> Mul for Rotation<S> {
    type Output = Self;

    /// Composition: `ρ * σ` is `ρ` after `σ`, Lean's `Rotation.mul`.
    ///
    /// The product is unchecked because it needs no check: the product of two orthogonal
    /// determinant-one matrices is one, which is the `orth` and `det_eq_one` proof inside
    /// Lean's `Rotation.mul` and is the reason composition can be stated in the first place.
    #[inline]
    fn mul(self, other: Self) -> Self {
        Self {
            mat: self.mat * other.mat,
        }
    }
}

/// Entry-wise `|left - right| ≤ tolerance` over a 3x3. With a zero tolerance this is `==`,
/// which is the comparison [`Rotation::new`] makes.
fn within<S: Field>(left: Mat3<S>, right: Mat3<S>, tolerance: S) -> bool {
    (0..3).all(|i| (0..3).all(|j| (left.at(i, j) - right.at(i, j)).abs() <= tolerance))
}

/// The transformation from a tip wrench up to the sensor frame, Lean's `tipToSensor`.
///
/// `p` is the vector from the sensor origin to the tip origin in sensor coordinates, and `r`
/// maps tip coordinates to sensor coordinates. A wrench is a covector: the force rotates, and
/// the torque picks up the moment `p × F` the lever arm contributes. That second term is why
/// the wrench transform is the dual of the twist transform and not the same map.
#[inline]
pub fn tip_to_sensor<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    tip_wrench: Wrench<S>,
) -> Wrench<S> {
    let force = r.mul_vec(tip_wrench.force);
    let torque = r.mul_vec(tip_wrench.torque) + p.cross(force);
    Wrench::new(force, torque)
}

/// The transformation from a sensor wrench down to the tip, Lean's `sensorToTip` — the
/// direction force/torque control actually needs, since the sensor measures at its own origin
/// while the contact happens at the tip.
///
/// `Rᵀ` undoes the rotation and `- p × F` removes the moment the lever arm contributed, which
/// is exactly the term `tipToSensor` added: the two are mutual inverses given orthogonality.
#[inline]
pub fn sensor_to_tip<S: Field>(
    p: Vec3<S>,
    r: Rotation<S>,
    sensor_wrench: Wrench<S>,
) -> Wrench<S> {
    let force = r.transpose_mul_vec(sensor_wrench.force);
    let torque = r.transpose_mul_vec(sensor_wrench.torque - p.cross(sensor_wrench.force));
    Wrench::new(force, torque)
}

/// The velocity of the tip's material point, still in sensor coordinates, from the sensor's
/// twist: `v + ω × p`, Lean's `sensorTwistToTipVelocity`.
///
/// Only a shift of reference point — no rotation yet, because the components are still resolved
/// along the sensor's axes.
#[inline]
pub fn sensor_twist_to_tip_velocity<S: Field>(p: Vec3<S>, t: Twist<S>) -> Vec3<S> {
    t.v + t.omega.cross(p)
}

/// The tip twist, in tip coordinates, from the sensor's twist, Lean's `sensorTwistToTip`.
///
/// Shifting the reference point is not enough on its own: the components are still measured
/// along the sensor's axes, so both parts rotate back by `Rᵀ`. The `Rᵀ` is also what makes
/// `virtualWork_invariant` hold — with the unrotated velocity in the tip frame the two sides
/// differ in general, because the sensor-frame wrench would then act on a twist whose angular
/// part is still resolved in sensor axes.
#[inline]
pub fn sensor_twist_to_tip<S: Field>(p: Vec3<S>, r: Rotation<S>, t: Twist<S>) -> Twist<S> {
    Twist::new(
        r.transpose_mul_vec(sensor_twist_to_tip_velocity(p, t)),
        r.transpose_mul_vec(t.omega),
    )
}

/// The inverse of [`sensor_twist_to_tip`], Lean's `tipTwistToSensor`: a twist at the tip,
/// expressed at the sensor origin in sensor coordinates.
///
/// The angular part rotates forward and the lever arm is subtracted, mirroring the
/// `+ ω × p` that [`sensor_twist_to_tip_velocity`] adds. The arm is `p` *after* the rotation,
/// which is what makes the composed form `p + ρ *ᵥ q` close.
#[inline]
pub fn tip_twist_to_sensor<S: Field>(p: Vec3<S>, r: Rotation<S>, t: Twist<S>) -> Twist<S> {
    let omega = r.mul_vec(t.omega);
    Twist::new(r.mul_vec(t.v) - omega.cross(p), omega)
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_golden::Ratio as R;
    use robot_kinematics::Field;

    fn vec3(x: i128, y: i128, z: i128) -> Vec3<R> {
        Vec3::new(R::integer(x), R::integer(y), R::integer(z))
    }

    fn wrench(force: [i128; 3], torque: [i128; 3]) -> Wrench<R> {
        Wrench::new(
            vec3(force[0], force[1], force[2]),
            vec3(torque[0], torque[1], torque[2]),
        )
    }

    /// A rotation from a Pythagorean pair: exact over the rationals with no trigonometry.
    fn quarter_turn_z() -> Rotation<R> {
        Rotation::rot_z_cs(R::pair((0, 1), (1, 1))).expect("(0, 1) is on the unit circle")
    }

    #[test]
    fn the_identity_rotation_leaves_a_wrench_alone() {
        let w = wrench([1, -2, 3], [4, 5, -6]);
        assert_eq!(
            tip_to_sensor(Vec3::zero(), Rotation::identity(), w),
            w,
            "tipToSensor with p = 0 and R = 1 is the identity transform"
        );
        assert!(Rotation::<R>::identity().is_identity());
    }

    #[test]
    fn a_pure_translation_only_shifts_the_torque() {
        // The lever-arm term and nothing else: `p × F`, with the force untouched.
        let p = vec3(0, 0, 10);
        let w = wrench([1, 0, 0], [0, 0, 0]);
        let moved = tip_to_sensor(p, Rotation::identity(), w);
        assert_eq!(moved.force, w.force);
        assert_eq!(moved.torque, vec3(0, 10, 0));
    }

    #[test]
    fn a_reflection_is_not_a_rotation() {
        // `diag(1, 1, -1)` is orthogonal — so the round trips would work — but its determinant
        // is -1, and it anti-commutes with the cross product. This is the check that keeps
        // `mulVec_cross` true of every value of the type.
        let reflection = Mat3::from_rows([
            [R::one(), R::zero(), R::zero()],
            [R::zero(), R::one(), R::zero()],
            [R::zero(), R::zero(), -R::one()],
        ]);
        assert_eq!(reflection.transpose() * reflection, Mat3::identity());
        assert_eq!(reflection.det(), -R::one());
        assert!(Rotation::new(reflection).is_none());

        // and the reflection really does flip a cross product, which is what the rejection
        // above is protecting the rest of the crate from
        let (u, v) = (vec3(1, 0, 0), vec3(0, 1, 0));
        let crossed = reflection.mul_vec(u.cross(v));
        assert_ne!(crossed, reflection.mul_vec(u).cross(reflection.mul_vec(v)));
    }

    #[test]
    fn a_matrix_that_is_not_orthogonal_is_rejected() {
        // A hair off the unit circle: exact orthogonality fails, a band admits it. This is the
        // difference between the rational path (`Rotation::new`) and the floating-point one.
        let near = Mat3::from_rows([
            [R::new(1001, 1000), R::zero(), R::zero()],
            [R::zero(), R::one(), R::zero()],
            [R::zero(), R::zero(), R::one()],
        ]);
        assert!(Rotation::new(near).is_none());
        assert!(Rotation::checked(near, R::new(1, 100)).is_some());
    }

    #[test]
    fn a_quarter_turn_about_z_sends_x_to_y() {
        let rotated = quarter_turn_z().mul_vec(vec3(1, 0, 0));
        assert_eq!(rotated, vec3(0, 1, 0));
        // and the inverse brings it back: `transpose_mul_vec` is `mul_vec` of `ρ⁻¹`
        assert_eq!(
            quarter_turn_z().transpose_mul_vec(rotated),
            vec3(1, 0, 0)
        );
    }

    #[test]
    fn virtual_work_is_the_force_dot_velocity_plus_the_torque_dot_omega() {
        assert_eq!(
            virtual_work(wrench([1, 0, 0], [0, 0, 0]), Twist::new(vec3(3, 0, 0), Vec3::zero())),
            R::integer(3)
        );
        assert_eq!(
            virtual_work(wrench([0, 0, 0], [0, 0, 2]), Twist::new(Vec3::zero(), vec3(0, 5, 0))),
            R::zero()
        );
    }

    #[test]
    fn a_twist_at_the_origin_of_a_rotated_frame_keeps_its_angular_part() {
        // R = 1, p = 0: neither transform does anything at all.
        let t = Twist::new(vec3(1, 2, 3), vec3(-1, 0, 1));
        assert_eq!(sensor_twist_to_tip(Vec3::zero(), Rotation::identity(), t), t);
        assert_eq!(tip_twist_to_sensor(Vec3::zero(), Rotation::identity(), t), t);
    }
}
