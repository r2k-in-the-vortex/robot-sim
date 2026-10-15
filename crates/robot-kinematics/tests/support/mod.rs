//! Shared test support.
//!
//! The one thing here is [`Ratio`]: an exact rational that implements the crate's
//! [`Field`] trait, so the polynomial half of the kinematics can be evaluated over `ℚ`
//! and compared against the Lean generator's vectors with `==` instead of a tolerance.
//!
//! It lives in the test tree rather than in the crate so that `robot-kinematics` keeps
//! the zero-dependency property `kinematics.py` has. `Field` is deliberately unsealed
//! for exactly this reason.
//!
//! It is a fixed-width rational over `i128`, not a big-integer one, because `Field`
//! requires `Copy` and a heap-allocated rational is not. That is enough for the golden
//! vectors: their denominators are products of the small Pythagorean ones (`5`, `13`,
//! `17`) over a six-joint chain, which stays far inside `i128`'s range. An overflow
//! panics, and would mean the generated vectors are larger than the design anticipated.

#![allow(dead_code)]

use robot_kinematics::Field;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// An exact rational, normalised to lowest terms with a positive denominator.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Ratio {
    numerator: i128,
    denominator: i128,
}

impl Ratio {
    pub const ZERO: Self = Self {
        numerator: 0,
        denominator: 1,
    };
    pub const ONE: Self = Self {
        numerator: 1,
        denominator: 1,
    };

    /// Build from a numerator and denominator, reducing and normalising the sign.
    ///
    /// # Panics
    /// If the denominator is zero, or if reducing overflows `i128`.
    pub fn new(numerator: i128, denominator: i128) -> Self {
        assert!(denominator != 0, "rational with zero denominator");
        let sign = if denominator < 0 { -1 } else { 1 };
        let numerator = numerator * sign;
        let denominator = denominator * sign;
        let divisor = gcd(numerator, denominator);
        Self {
            numerator: numerator / divisor,
            denominator: denominator / divisor,
        }
    }

    /// An integer as a rational.
    pub const fn integer(value: i128) -> Self {
        Self {
            numerator: value,
            denominator: 1,
        }
    }

    /// A rational from a small integer pair without reduction, for the generated
    /// vectors, whose values are already in lowest terms.
    pub fn from_parts(numerator: i128, denominator: i128) -> Self {
        Self::new(numerator, denominator)
    }

    pub fn numerator(self) -> i128 {
        self.numerator
    }

    pub fn denominator(self) -> i128 {
        self.denominator
    }

    /// Whether the value is zero.
    pub fn is_zero(self) -> bool {
        self.numerator == 0
    }

    /// The value as an `f64`, for reporting a disagreement in a test failure.
    pub fn to_f64(self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }
}

impl Field for Ratio {
    #[inline]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline]
    fn one() -> Self {
        Self::ONE
    }

    /// Exact conversion: the binary expansion of an `f64` is a rational with a power of
    /// two for a denominator, so this introduces no rounding at all.
    fn from_f64(value: f64) -> Self {
        assert!(value.is_finite(), "cannot convert a non-finite value exactly");
        if value == 0.0 {
            return Self::ZERO;
        }
        let bits = value.to_bits();
        let negative = bits >> 63 == 1;
        let raw_exponent = ((bits >> 52) & 0x7ff) as i64;
        let mantissa = (bits & 0x000f_ffff_ffff_ffff) as i128;
        // Subnormal values have no implicit leading one; the vectors never contain any,
        // but the branch keeps the conversion honest.
        let (mantissa, exponent) = if raw_exponent == 0 {
            (mantissa, -1074i64)
        } else {
            (mantissa | 0x0010_0000_0000_0000, raw_exponent - 1075)
        };
        let signed = if negative { -mantissa } else { mantissa };
        if exponent >= 0 {
            Self::integer(signed << exponent)
        } else {
            Self::new(signed, 1i128 << (-exponent))
        }
    }

    #[inline]
    fn abs(self) -> Self {
        if self.numerator < 0 {
            Self {
                numerator: -self.numerator,
                denominator: self.denominator,
            }
        } else {
            self
        }
    }

    #[inline]
    fn is_finite(self) -> bool {
        true
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(
            (self.numerator * other.denominator).cmp(&(other.numerator * self.denominator)),
        )
    }
}

impl Add for Ratio {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.denominator + other.numerator * self.denominator,
            self.denominator * other.denominator,
        )
    }
}

impl Sub for Ratio {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.denominator - other.numerator * self.denominator,
            self.denominator * other.denominator,
        )
    }
}

impl Mul for Ratio {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.numerator,
            self.denominator * other.denominator,
        )
    }
}

impl Div for Ratio {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        assert!(!other.is_zero(), "rational division by zero");
        Self::new(
            self.numerator * other.denominator,
            self.denominator * other.numerator,
        )
    }
}

impl Neg for Ratio {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl From<i128> for Ratio {
    fn from(value: i128) -> Self {
        Self::integer(value)
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 { 1 } else { a }
}

/// The cosine and sine of a quarter turn, exactly.
pub fn quarter_turn() -> robot_kinematics::CosSin<Ratio> {
    robot_kinematics::CosSin::new(Ratio::ZERO, Ratio::ONE)
}

/// An exact cosine/sine pair from small integers. The pairs are Pythagorean — `(3, 4)`
/// for a `3-4-5` triangle — so the pair is exact without any trigonometry.
pub fn pair(cos: (i128, i128), sin: (i128, i128)) -> robot_kinematics::CosSin<Ratio> {
    robot_kinematics::CosSin::new(
        Ratio::from_parts(cos.0, cos.1),
        Ratio::from_parts(sin.0, sin.1),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_reduce_and_normalise_sign() {
        assert_eq!(Ratio::new(2, 4), Ratio::new(1, 2));
        assert_eq!(Ratio::new(1, -2), Ratio::new(-1, 2));
        assert_eq!(Ratio::new(1, -2).denominator(), 2);
    }

    #[test]
    fn from_f64_is_exact_for_halves_and_integers() {
        assert_eq!(Ratio::from_f64(2.0), Ratio::integer(2));
        assert_eq!(Ratio::from_f64(0.5), Ratio::new(1, 2));
        assert_eq!(Ratio::from_f64(-0.25), Ratio::new(-1, 4));
        assert_eq!(Ratio::from_f64(180.0), Ratio::integer(180));
    }
}
