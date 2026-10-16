//! The arithmetic the kinematics is written against.
//!
//! Lean states the specification over `ℝ`. This crate states it over two traits, and the
//! division between them is the division the verification rests on:
//!
//! * [`Field`] is the **polynomial** layer — the four operations, nothing else. Every
//!   use the chain makes of an angle is through its cosine and sine, so once those are
//!   supplied as data (`CosSin`) the whole forward chain, the wrench algebra and the
//!   dynamics are polynomials in them. Polynomials evaluate over any commutative ring,
//!   so this layer runs unchanged over the exact rationals the Lean generator emits,
//!   which is what lets those vectors be compared with `==` rather than a tolerance.
//!
//! * [`Scalar`] adds the **transcendental** layer — `sqrt`, `sin`, `cos`, `atan2`,
//!   `acos`. This is where the Rust and the real-number specification genuinely part
//!   company, and it is deliberately a small, nameable set of functions. `Atan2.lean`
//!   exists because Mathlib has no `atan2`; this trait is its Rust counterpart.
//!
//! Production instantiates [`f64`] and nothing else, so every call monomorphises to a
//! plain floating-point instruction with no indirection. [`Scalar`] is sealed; [`Field`]
//! is not, so a test crate can supply an exact type of its own without this crate taking
//! a dependency on one.

use core::fmt::Debug;
use core::ops::{Add, Div, Mul, Neg, Sub};

mod sealed {
    /// Prevents downstream implementations of [`super::Scalar`].
    pub trait Sealed {}
    impl Sealed for f64 {}
    impl Sealed for f32 {}
}

/// A commutative field: the arithmetic Lean's `CommRing`-generic developments use.
///
/// Deliberately open, unlike [`Scalar`]. The exact-rational type the golden vectors are
/// checked against lives in the test crates rather than here, so that the kinematics
/// core keeps its zero-dependency property — the same property `kinematics.py` has,
/// which imports nothing but the standard library.
pub trait Field:
    Copy
    + Debug
    + PartialEq
    + PartialOrd
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;

    /// The value of a literal written as an `f64`.
    ///
    /// Used only for structural constants — the `2` in the law of cosines, the `180` in
    /// the degree conversion — never for transporting a computed value between types.
    /// An exact implementation converts exactly, so the constant introduces no
    /// rounding even over the rationals.
    fn from_f64(value: f64) -> Self;

    fn abs(self) -> Self;

    /// Whether the value is finite. Always true for an exact type.
    fn is_finite(self) -> bool;
}

/// A [`Field`] carrying the transcendental functions the solver needs.
///
/// Sealed: the set of scalars is `f64`, `f32` and the test-only high-precision type, and
/// a downstream crate introducing a fourth would invalidate the reasoning about which
/// instantiations the test suite exercises.
pub trait Scalar: Field + sealed::Sealed {
    fn sqrt(self) -> Self;
    fn sin(self) -> Self;
    fn cos(self) -> Self;
    /// `atan2(self, x)`, i.e. `RealAtan2.atan2 self x`, with the y argument first.
    fn atan2(self, x: Self) -> Self;
    fn acos(self) -> Self;

    fn is_nan(self) -> bool;

    /// Widen to `f64`. Exact for `f64` and `f32`; for the high-precision type this is
    /// lossy and is used only to report a value back to the test harness.
    fn to_f64(self) -> f64;

    /// `RealAtan2.hypot`: `sqrt (x² + y²)`, without the intermediate overflow a naive
    /// `sqrt (x*x + y*y)` would suffer.
    ///
    /// `hypot(x, y) = 0` holds exactly when `x = 0` and `y = 0`, which is what lets the
    /// wrist-singularity predicate be decided without a square root at all.
    fn hypot(self, other: Self) -> Self;

    /// `π`, the mathematical constant, at this scalar's precision.
    fn pi() -> Self;
}

/// The platform's maths library, used when the `std` feature is on.
///
/// Inherent methods win name resolution over the trait's, so `f64::sin` here is the
/// standard library's and not a recursive call back into this impl.
#[cfg(feature = "std")]
mod platform {
    use super::{Field, Scalar};

    // `$pi` is passed as an expression rather than reached through `$t`, because a `ty`
    // fragment cannot stand as a path segment inside the macro body.
    macro_rules! impl_float {
        ($t:ty, $pi:expr) => {
            impl Field for $t {
                #[inline]
                fn zero() -> Self {
                    0.0
                }
                #[inline]
                fn one() -> Self {
                    1.0
                }
                #[inline]
                fn from_f64(value: f64) -> Self {
                    value as $t
                }
                #[inline]
                fn abs(self) -> Self {
                    <$t>::abs(self)
                }
                #[inline]
                fn is_finite(self) -> bool {
                    <$t>::is_finite(self)
                }
            }

            impl Scalar for $t {
                #[inline]
                fn sqrt(self) -> Self {
                    <$t>::sqrt(self)
                }
                #[inline]
                fn sin(self) -> Self {
                    <$t>::sin(self)
                }
                #[inline]
                fn cos(self) -> Self {
                    <$t>::cos(self)
                }
                #[inline]
                fn atan2(self, x: Self) -> Self {
                    <$t>::atan2(self, x)
                }
                #[inline]
                fn acos(self) -> Self {
                    <$t>::acos(self)
                }
                #[inline]
                fn is_nan(self) -> bool {
                    <$t>::is_nan(self)
                }
                #[inline]
                fn to_f64(self) -> f64 {
                    self as f64
                }
                #[inline]
                fn hypot(self, other: Self) -> Self {
                    <$t>::hypot(self, other)
                }
                #[inline]
                fn pi() -> Self {
                    $pi
                }
            }
        };
    }

    impl_float!(f64, core::f64::consts::PI);
    impl_float!(f32, core::f32::consts::PI);
}

/// `libm`'s pure-Rust transcendentals, for `no_std` builds and for runs that have to
/// reproduce bit-for-bit on a different platform.
#[cfg(all(not(feature = "std"), feature = "libm"))]
mod pure_rust {
    use super::{Field, Scalar};

    impl Field for f64 {
        #[inline]
        fn zero() -> Self {
            0.0
        }
        #[inline]
        fn one() -> Self {
            1.0
        }
        #[inline]
        fn from_f64(value: f64) -> Self {
            value
        }
        #[inline]
        fn abs(self) -> Self {
            // `abs` is a `core` intrinsic, not a maths-library call.
            f64::abs(self)
        }
        #[inline]
        fn is_finite(self) -> bool {
            f64::is_finite(self)
        }
    }

    impl Scalar for f64 {
        #[inline]
        fn sqrt(self) -> Self {
            libm::sqrt(self)
        }
        #[inline]
        fn sin(self) -> Self {
            libm::sin(self)
        }
        #[inline]
        fn cos(self) -> Self {
            libm::cos(self)
        }
        #[inline]
        fn atan2(self, x: Self) -> Self {
            libm::atan2(self, x)
        }
        #[inline]
        fn acos(self) -> Self {
            libm::acos(self)
        }
        #[inline]
        fn is_nan(self) -> bool {
            f64::is_nan(self)
        }
        #[inline]
        fn to_f64(self) -> f64 {
            self
        }
        #[inline]
        fn hypot(self, other: Self) -> Self {
            libm::hypot(self, other)
        }
        #[inline]
        fn pi() -> Self {
            core::f64::consts::PI
        }
    }
}
