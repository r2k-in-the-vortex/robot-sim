//! An angle carried as its cosine and sine rather than as a number of radians.
//!
//! This exists so the exact-rational golden vectors can exercise the *same* code the
//! floating-point path runs. `cos` and `sin` of a rational number of degrees are
//! irrational outside a handful of values (Niven), so a rational scalar has no `sin` to
//! call and `fk` cannot be evaluated over `ℚ` by angle. But every use the chain makes of
//! an angle is through its cosine and sine — which is exactly what `dh_congr` in Lean
//! says — so supplying the pair directly makes the forward chain a polynomial in those
//! entries, and a polynomial evaluates over any commutative ring.
//!
//! That is how `lean/ForceTorqueTestData.lean` already builds its rotations, and it is
//! what lets `lean/KinematicsTestData.lean` emit vectors Rust can compare with `==`
//! instead of a tolerance.
//!
//! The pair is not required to be normalised: a caller supplying `(0, 1)` for a quarter
//! turn gets exactly that, and the chain never re-derives one entry from the other.

use crate::scalar::{Field, Scalar};

/// The cosine and sine of an angle.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct CosSin<S> {
    /// `cos θ`.
    pub cos: S,
    /// `sin θ`.
    pub sin: S,
}

/// The polynomial operations, available over any field — including the exact rationals
/// the golden vectors use. Everything here is exact when the pair is.
impl<S: Field> CosSin<S> {
    /// Build from an explicitly supplied pair.
    #[inline]
    pub const fn new(cos: S, sin: S) -> Self {
        Self { cos, sin }
    }

    /// An exact quarter turn, `(0, 1)`: `Kinematics.quarter`, and the only non-trivial
    /// twist the supported arm's fixed `alpha` pattern uses.
    #[inline]
    pub fn quarter_turn() -> Self {
        Self {
            cos: S::zero(),
            sin: S::one(),
        }
    }

    /// The identity rotation, `(1, 0)`.
    #[inline]
    pub fn identity() -> Self {
        Self {
            cos: S::one(),
            sin: S::zero(),
        }
    }

    /// The same angle a quarter turn round, `(cos, sin) ↦ (-sin, cos)`.
    #[inline]
    pub fn plus_quarter_turn(self) -> Self {
        Self {
            cos: -self.sin,
            sin: self.cos,
        }
    }

    /// Negated, `(cos, sin) ↦ (cos, -sin)`.
    #[inline]
    pub fn negated(self) -> Self {
        Self {
            cos: self.cos,
            sin: -self.sin,
        }
    }

    /// The pair for `self + other`, by the angle addition formulas. Purely polynomial,
    /// so it works over any ring — this is what `cos_add`/`sin_add` reduce to.
    #[inline]
    pub fn then(self, other: Self) -> Self {
        Self {
            cos: self.cos * other.cos - self.sin * other.sin,
            sin: self.sin * other.cos + self.cos * other.sin,
        }
    }

    /// Whether the pair is finite.
    #[inline]
    pub fn is_finite(self) -> bool {
        self.cos.is_finite() && self.sin.is_finite()
    }
}

/// The operations that need a transcendental, and therefore cannot be evaluated over an
/// arbitrary field. These are the two points where a rotation angle meets the
/// floating-point world at all.
impl<S: Scalar> CosSin<S> {
    /// Read the pair off an angle.
    ///
    /// Infallible and total: `cos` and `sin` are defined everywhere.
    #[inline]
    pub fn from_angle(angle: S) -> Self {
        Self {
            cos: angle.cos(),
            sin: angle.sin(),
        }
    }

    /// The angle the pair names, reduced to `(-π, π]` by `Atan2.wrap`.
    ///
    /// Loses the full turns the pair cannot carry — which is the whole content of
    /// `fk_congr`.
    #[inline]
    pub fn angle(self) -> S {
        self.sin.atan2(self.cos)
    }
}

/// The six joint angles as cosine/sine pairs, the form the exact-rational path uses.
pub type AnglesCosSin<S> = [CosSin<S>; crate::units::JOINT_COUNT];

#[cfg(test)]
mod tests {
    use super::*;
    use core::f64::consts::{FRAC_PI_2, PI};

    #[test]
    fn from_angle_round_trips_inside_the_principal_range() {
        for angle in [-3.0, -1.0, 0.0, 1.0, 3.0] {
            assert!((CosSin::from_angle(angle).angle() - angle).abs() < 1e-15);
        }
    }

    #[test]
    fn a_full_turn_is_invisible_to_the_pair() {
        let a = CosSin::from_angle(0.3);
        let b = CosSin::from_angle(0.3 + 2.0 * PI);
        assert!((a.cos - b.cos).abs() < 1e-15);
        assert!((a.sin - b.sin).abs() < 1e-15);
    }

    #[test]
    fn then_composes_angles() {
        let sum = CosSin::from_angle(0.7).then(CosSin::from_angle(1.1));
        let direct = CosSin::from_angle(1.8);
        assert!((sum.cos - direct.cos).abs() < 1e-15);
        assert!((sum.sin - direct.sin).abs() < 1e-15);
    }

    #[test]
    fn plus_quarter_turn_agrees_with_adding_a_quarter_turn() {
        let turned = CosSin::from_angle(0.4).plus_quarter_turn();
        let direct = CosSin::from_angle(0.4 + FRAC_PI_2);
        assert!((turned.cos - direct.cos).abs() < 1e-15);
        assert!((turned.sin - direct.sin).abs() < 1e-15);
    }

    #[test]
    fn the_quarter_turn_is_exactly_representable() {
        // No rounding at all: this is what lets the fixed alpha pattern stay rational.
        let quarter = CosSin::<f64>::quarter_turn();
        assert_eq!(quarter.cos, 0.0);
        assert_eq!(quarter.sin, 1.0);
    }
}
