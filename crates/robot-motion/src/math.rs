//! The two roots the optimal planner needs, feature-gated.
//!
//! `std` uses the platform methods; `no_std` uses `libm`. The conservative planner and
//! the whole polynomial layer use neither, so an exact `Ratio` instantiation is possible.

#[cfg(feature = "std")]
#[inline]
pub(crate) fn sqrt(x: f64) -> f64 {
    x.sqrt()
}

#[cfg(feature = "std")]
#[inline]
pub(crate) fn cbrt(x: f64) -> f64 {
    x.cbrt()
}

#[cfg(all(not(feature = "std"), feature = "libm"))]
#[inline]
pub(crate) fn sqrt(x: f64) -> f64 {
    libm::sqrt(x)
}

#[cfg(all(not(feature = "std"), feature = "libm"))]
#[inline]
pub(crate) fn cbrt(x: f64) -> f64 {
    libm::cbrt(x)
}

#[cfg(all(not(feature = "std"), not(feature = "libm")))]
compile_error!("robot-motion needs either the `std` or the `libm` feature");
