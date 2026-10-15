//! Rigid poses and the Denavit-Hartenberg transform.
//!
//! The counterpart of `lean/Kinematics.lean`'s `Pose`, `dh` and `dhP`. A pose is kept as
//! a rotation and a translation rather than a 4x4 homogeneous matrix, exactly as Lean
//! keeps it: `Pose::to_matrix4` is `Kinematics.Pose.toMatrix4`, and `to_matrix4_mul`
//! there proves the two views agree, so the matrices `mathematics.md` writes out are
//! still readable from here.

use crate::angle::CosSin;
use crate::mat3::Mat3;
use core::ops::Mul;
use crate::scalar::{Field, Scalar};
use crate::vec3::Vec3;

/// A rigid pose: the rotation carrying a frame's coordinates to the base frame, and its
/// origin expressed in the base frame.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Pose<S> {
    /// Lean's `Pose.R`.
    pub r: Mat3<S>,
    /// Lean's `Pose.p`.
    pub p: Vec3<S>,
}

impl<S: Field> Pose<S> {
    #[inline]
    pub const fn new(r: Mat3<S>, p: Vec3<S>) -> Self {
        Self { r, p }
    }

    /// The frame coinciding with the base frame, `Pose.id`.
    #[inline]
    pub fn identity() -> Self {
        Self::new(Mat3::identity(), Vec3::zero())
    }

    /// The 4x4 homogeneous matrix of the pose, row-major, in the layout `mathematics.md`
    /// and `kinematics.py`'s `Matrix4` use.
    ///
    /// `Kinematics.Pose.toMatrix4_mul` proves this is multiplicative, so a caller that
    /// wants the homogeneous view can build it at the end rather than carrying it.
    #[inline]
    pub fn to_matrix4(self) -> [[S; 4]; 4] {
        [
            [self.r.at(0, 0), self.r.at(0, 1), self.r.at(0, 2), self.p.x()],
            [self.r.at(1, 0), self.r.at(1, 1), self.r.at(1, 2), self.p.y()],
            [self.r.at(2, 0), self.r.at(2, 1), self.r.at(2, 2), self.p.z()],
            [S::zero(), S::zero(), S::zero(), S::one()],
        ]
    }

    #[inline]
    pub fn is_finite(self) -> bool {
        self.r.is_finite() && self.p.is_finite()
    }

    /// The third column of the rotation — frame `self`'s z axis expressed in the base
    /// frame. This is what `wristCenter` reads, and what `kinematics.py` reads as
    /// `target_pose[axis][2]`.
    #[inline]
    pub fn z_axis(self) -> Vec3<S> {
        self.r.col(2)
    }

    /// The first column of the rotation — frame `self`'s x axis. `kinematics.py`'s
    /// wrist centre reads this as `target_pose[axis][0]`, the `a6` lever arm.
    #[inline]
    pub fn x_axis(self) -> Vec3<S> {
        self.r.col(0)
    }

    /// The translation part of a DH transform: `a` along the frame's x axis after the
    /// `θ` turn, and `d` along the previous z axis. Lean's `dhP`.
    #[inline]
    pub fn dh_translation_cs(theta: CosSin<S>, d: S, a: S) -> Vec3<S> {
        Vec3::new(a * theta.cos, a * theta.sin, d)
    }

    /// One standard-DH transform, `Rz θ · Tz d · Tx a · Rx α`. Lean's `dh`.
    ///
    /// `to_matrix4` of this is the matrix `mathematics.md` writes out entry for entry —
    /// `dh_toMatrix4` in Lean, `dh_transform_standard` in Python.
    ///
    /// The primitive: [`Pose::dh`] forwards to it, so the exact-rational path in the
    /// golden tests exercises this body rather than a transcription of it.
    #[inline]
    pub fn dh_cs(theta: CosSin<S>, d: S, a: S, alpha: CosSin<S>) -> Self {
        Self::new(
            Mat3::rot_z_cs(theta) * Mat3::rot_x_cs(alpha),
            Self::dh_translation_cs(theta, d, a),
        )
    }

}

impl<S: Field> Mul for Pose<S> {
    type Output = Self;

    /// Composition: `x * y` is `x` after `y`, so `(x * y).p` places `y`'s origin by `x`.
    /// Lean's `Pose.mul`, and the operation `toMatrix4_mul` proves corresponds to
    /// multiplying the homogeneous matrices.
    #[inline]
    fn mul(self, other: Self) -> Self {
        Self::new(self.r * other.r, self.r.mul_vec(other.p) + self.p)
    }
}

/// The operations that need a square root, and therefore cannot be evaluated over an
/// arbitrary field.
impl<S: Scalar> Pose<S> {
    /// Whether the rotation block is orthogonal with determinant one — the hypothesis
    /// `fk_of_mem_solutions` and `solutions_eq_nil_of_not_reachable` both carry, and the
    /// precondition a caller must meet before a pose names a rotation at all.
    ///
    /// `fk`'s own rotation always satisfies this (`fk_R_orth`, `fk_R_det`).
    #[inline]
    pub fn rotation_is_a_rotation(self, tolerance: S) -> bool {
        let identity = Mat3::identity();
        (self.r.transpose() * self.r).frobenius_distance(identity) <= tolerance
            && (self.r.det() - S::one()).abs() <= tolerance
    }

    /// One standard-DH transform from angles in radians.
    #[inline]
    pub fn dh(theta: S, d: S, a: S, alpha: S) -> Self {
        Self::dh_cs(CosSin::from_angle(theta), d, a, CosSin::from_angle(alpha))
    }
}

impl<S: Field> Default for Pose<S> {
    #[inline]
    fn default() -> Self {
        Self::identity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `dh_toMatrix4` in Lean writes the transform as an explicit 4x4; this is that
    /// matrix read off the `(R, p)` representation, and the two must agree entry by
    /// entry.
    #[test]
    fn dh_matrix_matches_the_written_out_form() {
        let (theta, d, a, alpha) = (0.3, 40.0, 10.0, 1.2);
        let m = Pose::dh(theta, d, a, alpha).to_matrix4();
        let (st, ct) = (theta.sin(), theta.cos());
        let (sa, ca) = (alpha.sin(), alpha.cos());

        assert!((m[0][0] - ct).abs() < 1e-12);
        assert!((m[0][1] + st * ca).abs() < 1e-12);
        assert!((m[0][2] - st * sa).abs() < 1e-12);
        assert!((m[0][3] - a * ct).abs() < 1e-12);
        assert!((m[1][0] - st).abs() < 1e-12);
        assert!((m[1][1] - ct * ca).abs() < 1e-12);
        assert!((m[1][2] + ct * sa).abs() < 1e-12);
        assert!((m[1][3] - a * st).abs() < 1e-12);
        assert!(m[2][0].abs() < 1e-12);
        assert!((m[2][1] - sa).abs() < 1e-12);
        assert!((m[2][2] - ca).abs() < 1e-12);
        assert!((m[2][3] - d).abs() < 1e-12);
        assert_eq!(m[3], [0.0, 0.0, 0.0, 1.0]);
    }

    #[test]
    fn composition_matches_the_homogeneous_product() {
        let x = Pose::dh(0.4, 12.0, 3.0, 0.9);
        let y = Pose::dh(-1.1, 0.0, 7.0, 0.0);
        let composed = (x * y).to_matrix4();
        let product = mul4(x.to_matrix4(), y.to_matrix4());
        for i in 0..4 {
            for j in 0..4 {
                assert!((composed[i][j] - product[i][j]).abs() < 1e-12);
            }
        }
    }

    #[test]
    fn identity_is_a_two_sided_unit() {
        let x = Pose::dh(0.4, 12.0, 3.0, 0.9);
        assert_eq!(Pose::<f64>::identity() * x, x);
        assert_eq!(x * Pose::identity(), x);
    }

    fn mul4(a: [[f64; 4]; 4], b: [[f64; 4]; 4]) -> [[f64; 4]; 4] {
        let mut out = [[0.0; 4]; 4];
        for i in 0..4 {
            for j in 0..4 {
                out[i][j] = (0..4).map(|k| a[i][k] * b[k][j]).sum();
            }
        }
        out
    }
}
