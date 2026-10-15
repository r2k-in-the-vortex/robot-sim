//! A three-vector, the Rust counterpart of Lean's `Fin 3 → ℝ`.

use crate::scalar::{Field, Scalar};
use core::ops::{Add, Index, Mul, Neg, Sub};

/// Three components indexed `0`, `1`, `2`, matching `Fin 3`.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Vec3<S> {
    components: [S; 3],
}

/// The polynomial operations, available over any field — including the exact rationals
/// the golden vectors use.
impl<S: Field> Vec3<S> {
    #[inline]
    pub const fn new(x: S, y: S, z: S) -> Self {
        Self {
            components: [x, y, z],
        }
    }

    #[inline]
    pub const fn splat(value: S) -> Self {
        Self {
            components: [value; 3],
        }
    }

    #[inline]
    pub fn zero() -> Self {
        Self::splat(S::zero())
    }

    #[inline]
    pub fn x(self) -> S {
        self.components[0]
    }

    #[inline]
    pub fn y(self) -> S {
        self.components[1]
    }

    #[inline]
    pub fn z(self) -> S {
        self.components[2]
    }

    /// The unit vector along the z axis. Lean writes this `![0, 0, 1]`, the axis
    /// `wristCenter` and the DH transform read.
    #[inline]
    pub fn z_axis() -> Self {
        Self::new(S::zero(), S::zero(), S::one())
    }

    #[inline]
    pub fn add(self, other: Self) -> Self {
        Self::new(
            self.x() + other.x(),
            self.y() + other.y(),
            self.z() + other.z(),
        )
    }

    #[inline]
    pub fn sub(self, other: Self) -> Self {
        Self::new(
            self.x() - other.x(),
            self.y() - other.y(),
            self.z() - other.z(),
        )
    }

    #[inline]
    pub fn scale(self, factor: S) -> Self {
        Self::new(self.x() * factor, self.y() * factor, self.z() * factor)
    }

    #[inline]
    pub fn neg(self) -> Self {
        Self::new(-self.x(), -self.y(), -self.z())
    }

    /// The dot product, Lean's `dotProduct`.
    #[inline]
    pub fn dot(self, other: Self) -> S {
        self.x() * other.x() + self.y() * other.y() + self.z() * other.z()
    }

    /// The cross product, Lean's `cross`.
    #[inline]
    pub fn cross(self, other: Self) -> Self {
        Self::new(
            self.y() * other.z() - self.z() * other.y(),
            self.z() * other.x() - self.x() * other.z(),
            self.x() * other.y() - self.y() * other.x(),
        )
    }

    #[inline]
    pub fn norm_sq(self) -> S {
        self.dot(self)
    }

    #[inline]
    pub fn is_finite(self) -> bool {
        self.x().is_finite() && self.y().is_finite() && self.z().is_finite()
    }

    /// The largest absolute component, used by the pose comparison to report how far
    /// apart two vectors are.
    #[inline]
    pub fn max_abs(self) -> S {
        let x = self.x().abs();
        let y = self.y().abs();
        let z = self.z().abs();
        let xy = if x > y { x } else { y };
        if xy > z { xy } else { z }
    }

    #[inline]
    pub fn as_array(&self) -> &[S; 3] {
        &self.components
    }
}

/// The operations that need a square root, and therefore cannot be evaluated over an
/// arbitrary field.
impl<S: Scalar> Vec3<S> {
    /// The Euclidean norm, `Real.sqrt` of the squared norm.
    #[inline]
    pub fn norm(self) -> S {
        self.norm_sq().sqrt()
    }

    /// `RealAtan2.hypot` of the first two components — the shoulder radius `r` the
    /// inverse solver reduces the base to.
    #[inline]
    pub fn hypot_xy(self) -> S {
        self.x().hypot(self.y())
    }

    /// The Euclidean distance to another point.
    #[inline]
    pub fn distance(self, other: Self) -> S {
        self.sub(other).norm()
    }
}

impl<S: Field> Index<usize> for Vec3<S> {
    type Output = S;

    /// Panics only on an out-of-range index, which is a programming error rather than
    /// a runtime condition; the solver itself uses [`Vec3::x`] and friends, which
    /// cannot fail.
    #[inline]
    fn index(&self, index: usize) -> &S {
        &self.components[index]
    }
}

impl<S: Field> Add for Vec3<S> {
    type Output = Self;
    #[inline]
    fn add(self, other: Self) -> Self {
        Vec3::add(self, other)
    }
}

impl<S: Field> Sub for Vec3<S> {
    type Output = Self;
    #[inline]
    fn sub(self, other: Self) -> Self {
        Vec3::sub(self, other)
    }
}

impl<S: Field> Neg for Vec3<S> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Vec3::neg(self)
    }
}

impl<S: Field> Mul<S> for Vec3<S> {
    type Output = Self;
    #[inline]
    fn mul(self, factor: S) -> Self {
        self.scale(factor)
    }
}

impl<S: Field> From<[S; 3]> for Vec3<S> {
    #[inline]
    fn from(components: [S; 3]) -> Self {
        Self { components }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(x: f64, y: f64, z: f64) -> Vec3<f64> {
        Vec3::new(x, y, z)
    }

    #[test]
    fn cross_is_antisymmetric() {
        let a = v(1.0, 2.0, 3.0);
        let b = v(-4.0, 5.0, 0.5);
        assert_eq!(a.cross(b), b.cross(a).neg());
    }

    #[test]
    fn cross_of_parallel_vectors_vanishes() {
        let a = v(1.0, -2.0, 3.0);
        assert_eq!(a.cross(a.scale(2.5)), Vec3::zero());
    }

    #[test]
    fn hypot_xy_of_the_origin_is_zero() {
        // `branch.rs` relies on this: `hypot(x, y) = 0` exactly when both are zero.
        assert_eq!(v(0.0, 0.0, 7.0).hypot_xy(), 0.0);
        assert_ne!(v(0.0, 1e-300, 7.0).hypot_xy(), 0.0);
    }
}
