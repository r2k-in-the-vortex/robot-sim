//! A 3x3 matrix, the Rust counterpart of Lean's `Matrix (Fin 3) (Fin 3) ℝ`.
//!
//! Stored row-major, so `at(i, j)` is Lean's `M i j` and `as_rows()` is the nested-tuple
//! layout `kinematics.py` uses for its `Matrix4`. That agreement is what lets
//! `dh_to_matrix4` below be read against `mathematics.md` entry for entry.

use crate::angle::CosSin;
use crate::scalar::{Field, Scalar};
use crate::vec3::Vec3;
use core::ops::Mul;

/// A 3x3 matrix in row-major order.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Mat3<S> {
    entries: [S; 9],
}

/// The polynomial operations, available over any field — including the exact rationals
/// the golden vectors use.
impl<S: Field> Mat3<S> {
    /// Build from rows, `[[m00, m01, m02], [m10, m11, m12], [m20, m21, m22]]`.
    #[inline]
    pub const fn from_rows(rows: [[S; 3]; 3]) -> Self {
        Self {
            entries: [
                rows[0][0], rows[0][1], rows[0][2], rows[1][0], rows[1][1], rows[1][2],
                rows[2][0], rows[2][1], rows[2][2],
            ],
        }
    }

    /// Build from columns. Used where the Lean code reads a rotation by column, as
    /// `wristCenter` reads the third column for frame 6's z axis.
    #[inline]
    pub const fn from_cols(cols: [[S; 3]; 3]) -> Self {
        Self::from_rows([
            [cols[0][0], cols[1][0], cols[2][0]],
            [cols[0][1], cols[1][1], cols[2][1]],
            [cols[0][2], cols[1][2], cols[2][2]],
        ])
    }

    #[inline]
    pub fn identity() -> Self {
        Self::from_rows([
            [S::one(), S::zero(), S::zero()],
            [S::zero(), S::one(), S::zero()],
            [S::zero(), S::zero(), S::one()],
        ])
    }

    #[inline]
    pub fn zero() -> Self {
        Self::from_rows([[S::zero(); 3]; 3])
    }

    /// `M i j`, the entry in row `i` and column `j`.
    #[inline]
    pub fn at(self, i: usize, j: usize) -> S {
        self.entries[i * 3 + j]
    }

    #[inline]
    pub fn set(&mut self, i: usize, j: usize, value: S) {
        self.entries[i * 3 + j] = value;
    }

    /// The `j`-th column as a vector.
    #[inline]
    pub fn col(self, j: usize) -> Vec3<S> {
        Vec3::new(self.at(0, j), self.at(1, j), self.at(2, j))
    }

    /// The `i`-th row as a vector.
    #[inline]
    pub fn row(self, i: usize) -> Vec3<S> {
        Vec3::new(self.at(i, 0), self.at(i, 1), self.at(i, 2))
    }

    #[inline]
    pub fn transpose(self) -> Self {
        Self::from_rows([
            [self.at(0, 0), self.at(1, 0), self.at(2, 0)],
            [self.at(0, 1), self.at(1, 1), self.at(2, 1)],
            [self.at(0, 2), self.at(1, 2), self.at(2, 2)],
        ])
    }

    #[inline]
    pub fn mul(self, other: Self) -> Self {
        let mut out = Self::zero();
        for i in 0..3 {
            for j in 0..3 {
                out.set(
                    i,
                    j,
                    self.at(i, 0) * other.at(0, j)
                        + self.at(i, 1) * other.at(1, j)
                        + self.at(i, 2) * other.at(2, j),
                );
            }
        }
        out
    }

    /// The matrix-vector product, Lean's `M *ᵥ v`.
    #[inline]
    pub fn mul_vec(self, v: Vec3<S>) -> Vec3<S> {
        Vec3::new(
            self.row(0).dot(v),
            self.row(1).dot(v),
            self.row(2).dot(v),
        )
    }

    /// The determinant, by the rule of Sarrus. `fk_R_det` says the chain's rotation has
    /// determinant one; this is the function that checks it.
    #[inline]
    pub fn det(self) -> S {
        self.at(0, 0) * (self.at(1, 1) * self.at(2, 2) - self.at(1, 2) * self.at(2, 1))
            - self.at(0, 1) * (self.at(1, 0) * self.at(2, 2) - self.at(1, 2) * self.at(2, 0))
            + self.at(0, 2) * (self.at(1, 0) * self.at(2, 1) - self.at(1, 1) * self.at(2, 0))
    }

    /// The trace, the sum of the diagonal.
    #[inline]
    pub fn trace(self) -> S {
        self.at(0, 0) + self.at(1, 1) + self.at(2, 2)
    }

    #[inline]
    pub fn is_finite(self) -> bool {
        self.entries.iter().all(|entry| entry.is_finite())
    }

    /// Rotation about the x axis, Lean's `rotX`, from an explicitly supplied cosine and
    /// sine. The primitive: the angle-taking [`Mat3::rot_x`] forwards to it, so the
    /// exact-rational path and the floating-point path run the same code.
    #[inline]
    pub fn rot_x_cs(angle: CosSin<S>) -> Self {
        let (c, s) = (angle.cos, angle.sin);
        Self::from_rows([
            [S::one(), S::zero(), S::zero()],
            [S::zero(), c, -s],
            [S::zero(), s, c],
        ])
    }

    /// Rotation about the y axis, Lean's `rotY`, from a cosine and sine.
    #[inline]
    pub fn rot_y_cs(angle: CosSin<S>) -> Self {
        let (c, s) = (angle.cos, angle.sin);
        Self::from_rows([
            [c, S::zero(), s],
            [S::zero(), S::one(), S::zero()],
            [-s, S::zero(), c],
        ])
    }

    /// Rotation about the z axis, Lean's `rotZ`, from a cosine and sine.
    #[inline]
    pub fn rot_z_cs(angle: CosSin<S>) -> Self {
        let (c, s) = (angle.cos, angle.sin);
        Self::from_rows([
            [c, -s, S::zero()],
            [s, c, S::zero()],
            [S::zero(), S::zero(), S::one()],
        ])
    }

}

/// The operations that need a square root or a transcendental, and therefore cannot be
/// evaluated over an arbitrary field.
impl<S: Scalar> Mat3<S> {
    /// The Frobenius norm of the difference `self - other`.
    ///
    /// `kinematics.py`'s orientation error is exactly this on the two rotation blocks,
    /// which is why the compat layer in `solve` reports it in the same units.
    #[inline]
    pub fn frobenius_distance(self, other: Self) -> S {
        let mut sum = S::zero();
        for i in 0..3 {
            for j in 0..3 {
                let d = self.at(i, j) - other.at(i, j);
                sum = sum + d * d;
            }
        }
        sum.sqrt()
    }

    /// Rotation about the x axis by `α`, Lean's `rotX`.
    #[inline]
    pub fn rot_x(alpha: S) -> Self {
        Self::rot_x_cs(CosSin::from_angle(alpha))
    }

    /// Rotation about the y axis by `θ`, Lean's `rotY`.
    #[inline]
    pub fn rot_y(theta: S) -> Self {
        Self::rot_y_cs(CosSin::from_angle(theta))
    }

    /// Rotation about the z axis by `θ`, Lean's `rotZ`.
    #[inline]
    pub fn rot_z(theta: S) -> Self {
        Self::rot_z_cs(CosSin::from_angle(theta))
    }

    /// A quarter turn, `Kinematics.quarter`. The twist shared by `alpha1`, `alpha3`
    /// and `alpha4`.
    #[inline]
    pub fn quarter_turn() -> S {
        S::pi() / S::from_f64(2.0)
    }
}

impl<S: Field> Mul for Mat3<S> {
    type Output = Self;
    #[inline]
    fn mul(self, other: Self) -> Self {
        Mat3::mul(self, other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rot_z_is_orthogonal_with_unit_determinant() {
        let r = Mat3::rot_z(0.7);
        let identity = r.transpose().mul(r);
        assert!(identity.frobenius_distance(Mat3::<f64>::identity()) < 1e-15);
        assert!((r.det() - 1.0).abs() < 1e-15);
    }

    #[test]
    fn rot_x_quarter_turns_z_to_y() {
        // `rotX quarter` maps the z axis to the negative y axis; this is the
        // conjugation `rotX_conj` that makes the wrist a ZYZ ball joint.
        let quarter = Mat3::<f64>::quarter_turn();
        let mapped = Mat3::rot_x(quarter).mul_vec(Vec3::z_axis());
        assert!((mapped.z() - 0.0).abs() < 1e-15);
        assert!((mapped.y() + 1.0).abs() < 1e-15);
    }
}
