//! The free dimensions of the supported arm.
//!
//! Lean's `Kinematics.Geometry`, whose positivity fields `linkOne_pos` and `linkTwo_pos`
//! become the check in [`Geometry::new`]. The arm's structure is fixed — `alpha` of
//! `90, 0, 90, 90, -90, 0` degrees with `a3 = a4 = a5 = a6 = 0` and `d2 = d3 = d5 = 0`
//! — and these five values are what `kinematics.py`'s `_validate_supported_geometry`
//! leaves open. The structure replaces that guard here, so a `Geometry` is proof that
//! the arm is one the closed form applies to.

use crate::scalar::Field;

/// The dimensions of the supported six-axis arm, in model units.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Geometry<S> {
    /// Base offset `a1`: the frame-1 origin sits this far off the base rotation axis.
    pub a1: S,
    /// Base height `d1`.
    pub d1: S,
    /// First link length, `a2`. Positive: the planar solve divides by it.
    pub link_one: S,
    /// Second link length, `d4`. Positive.
    pub link_two: S,
    /// Tool offset `d6` along frame 6's z axis.
    pub tool_offset: S,
}

/// Why a set of dimensions does not describe the supported arm.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum GeometryError {
    /// `linkOne` must be positive; the planar solve divides by it.
    LinkOneNotPositive,
    /// `linkTwo` must be positive.
    LinkTwoNotPositive,
    /// A dimension was infinite or `NaN`.
    NotFinite,
}

impl core::fmt::Display for GeometryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            Self::LinkOneNotPositive => "link one (a2) must be positive",
            Self::LinkTwoNotPositive => "link two (d4) must be positive",
            Self::NotFinite => "a dimension is not finite",
        };
        f.write_str(text)
    }
}

impl<S: Field> Geometry<S> {
    /// Build a geometry, rejecting the dimensions the specification excludes.
    ///
    /// This is the Rust form of Lean's positivity fields: a value of `Geometry` is
    /// evidence that the arm is one the closed form is stated for.
    pub fn new(
        a1: S,
        d1: S,
        link_one: S,
        link_two: S,
        tool_offset: S,
    ) -> Result<Self, GeometryError> {
        let values = [a1, d1, link_one, link_two, tool_offset];
        if !values.iter().all(|value| value.is_finite()) {
            return Err(GeometryError::NotFinite);
        }
        if link_one <= S::zero() {
            return Err(GeometryError::LinkOneNotPositive);
        }
        if link_two <= S::zero() {
            return Err(GeometryError::LinkTwoNotPositive);
        }
        Ok(Self {
            a1,
            d1,
            link_one,
            link_two,
            tool_offset,
        })
    }

    /// The geometry `robot_parameters.json` ships: `a1 = 10`, `d1 = 40`, `a2 = 40`,
    /// `d4 = 40`, `d6 = 10`.
    ///
    /// `exists_nonDegenerate` in Lean witnesses non-vacuity at exactly these values, so
    /// they are the arm the proofs are known to have something to say about.
    pub fn shipped() -> Self {
        Self {
            a1: S::from_f64(10.0),
            d1: S::from_f64(40.0),
            link_one: S::from_f64(40.0),
            link_two: S::from_f64(40.0),
            tool_offset: S::from_f64(10.0),
        }
    }

    /// The sum of the two link lengths: the outer radius of the reachable band.
    #[inline]
    pub fn reach(&self) -> S {
        self.link_one + self.link_two
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shipped_geometry_is_accepted() {
        assert!(Geometry::<f64>::new(10.0, 40.0, 40.0, 40.0, 10.0).is_ok());
        assert_eq!(Geometry::<f64>::shipped().reach(), 80.0);
    }

    #[test]
    fn non_positive_links_are_rejected_by_name() {
        assert_eq!(
            Geometry::new(10.0, 40.0, 0.0, 40.0, 10.0),
            Err(GeometryError::LinkOneNotPositive)
        );
        assert_eq!(
            Geometry::new(10.0, 40.0, 40.0, -1.0, 10.0),
            Err(GeometryError::LinkTwoNotPositive)
        );
        assert_eq!(
            Geometry::new(f64::NAN, 40.0, 40.0, 40.0, 10.0),
            Err(GeometryError::NotFinite)
        );
    }
}
