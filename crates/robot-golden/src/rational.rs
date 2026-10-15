//! An exact rational implementing the kinematics' [`Field`] trait.
//!
//! This is what lets the golden vectors be checked with `==` rather than a tolerance:
//! the polynomial half of the mathematics — the forward chain, the wrench algebra, the
//! dynamics — is exact over `ℚ`, so a disagreement is a real disagreement and not
//! floating-point drift.
//!
//! It is fixed-width over `i128` rather than a big-integer rational because [`Field`]
//! requires `Copy`, and a heap-allocated rational is not. That is ample for these
//! vectors: their denominators are products of the small Pythagorean ones (`5`, `13`,
//! `17`) over a six-joint chain, which stays far inside `i128`. An overflow panics, and
//! would mean a generated vector is larger than the design anticipated.

use core::cmp::Ordering;
use core::fmt::{self, Debug};
use core::ops::{Add, Div, Mul, Neg, Sub};
use robot_kinematics::{CosSin, Field};

/// An exact rational, normalised to lowest terms with a positive denominator.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
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
    /// If the denominator is zero.
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

    pub fn numerator(self) -> i128 {
        self.numerator
    }

    pub fn denominator(self) -> i128 {
        self.denominator
    }

    pub fn is_zero(self) -> bool {
        self.numerator == 0
    }

    /// The value as an `f64`, for reporting a disagreement in a failure message.
    pub fn to_f64(self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }
}

impl Debug for Ratio {
    /// Prints as `n/d`, or as a bare integer when the denominator is one, so a failing
    /// assertion reads the way the JSON does.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
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

    /// Exact conversion. The binary expansion of an `f64` is a rational whose
    /// denominator is a power of two, so this introduces no rounding at all — which
    /// matters because the structural constants (`2` in the law of cosines, `180` in
    /// the degree conversion) must not perturb an otherwise exact computation.
    fn from_f64(value: f64) -> Self {
        assert!(
            value.is_finite(),
            "cannot convert {value} to an exact rational"
        );
        if value == 0.0 {
            return Self::ZERO;
        }
        let bits = value.to_bits();
        let negative = bits >> 63 == 1;
        let raw_exponent = ((bits >> 52) & 0x7ff) as i64;
        let mantissa = (bits & 0x000f_ffff_ffff_ffff) as i128;
        // Subnormals carry no implicit leading one. The generated vectors never contain
        // any, but the branch keeps the conversion total.
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
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some((self.numerator * other.denominator).cmp(&(other.numerator * self.denominator)))
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

impl Ratio {
    /// An exact cosine/sine pair from a small integer pair.
    ///
    /// The vectors use Pythagorean pairs — `(4/5, 3/5)`, `(5/13, 12/13)`, `(15/17, 8/17)`
    /// — so the pair is exact without any trigonometry being involved.
    pub fn pair(cos: (i128, i128), sin: (i128, i128)) -> CosSin<Self> {
        CosSin::new(Self::new(cos.0, cos.1), Self::new(sin.0, sin.1))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_reduce_and_normalise_sign() {
        assert_eq!(Ratio::new(2, 4), Ratio::new(1, 2));
        assert_eq!(Ratio::new(1, -2), Ratio::new(-1, 2));
        assert_eq!(Ratio::new(1, -2).denominator(), 2);
        assert_eq!(Ratio::new(0, -7), Ratio::ZERO);
    }

    #[test]
    fn from_f64_is_exact() {
        assert_eq!(Ratio::from_f64(2.0), Ratio::integer(2));
        assert_eq!(Ratio::from_f64(0.5), Ratio::new(1, 2));
        assert_eq!(Ratio::from_f64(-0.25), Ratio::new(-1, 4));
        assert_eq!(Ratio::from_f64(180.0), Ratio::integer(180));
        // 0.1 has no finite decimal expansion in binary; the conversion is still exact
        // with respect to the f64, which is the point.
        assert_eq!(
            Ratio::from_f64(0.1),
            Ratio::new(3602879701896397, 36028797018963968)
        );
    }

    #[test]
    fn ordering_compares_across_denominators() {
        assert!(Ratio::new(1, 3) < Ratio::new(1, 2));
        assert!(Ratio::new(-1, 2) < Ratio::new(-1, 3));
        assert!(Ratio::new(2, 4) == Ratio::new(1, 2));
    }

    #[test]
    fn debug_prints_the_json_spelling() {
        assert_eq!(std::format!("{:?}", Ratio::integer(3)), "3");
        assert_eq!(std::format!("{:?}", Ratio::new(-3, 5)), "-3/5");
    }
}
