//! Whether a DH table is the arm the closed-form solver was derived for.
//!
//! This is deliberately *not* part of [`DHParameters::geometry`](crate::DHParameters::geometry).
//! In the reference the two questions are asked in different places:
//!
//! * `forward_kinematics` multiplies the DH transforms and works for **any** table, which
//!   is why the view still draws and still jogs joint by joint when the table departs from
//!   the structure (README, "Inverse kinematics").
//! * `inverse_kinematics` calls `_validate_supported_geometry` first (`kinematics.py:409`)
//!   and raises by name, which is why a *pose* jog on such a table reports the offending
//!   parameter instead of moving (`simulator.py:385-387`).
//!
//! So [`DHParameters::structure_error`] is the solver's precondition, kept beside the table
//! it guards, and [`TableError`]'s `Display` is the reference's own sentence — minus its
//! units, see [`TableError::Structure`].

use crate::dh::DHParameters;
use robot_kinematics::{JOINT_COUNT, deg_to_rad};

/// The tolerance `_validate_supported_geometry` is called with from `inverse_kinematics`
/// (`kinematics.py:453-468`), applied to the *radian* values the reference compares.
///
/// `robot_model` keeps the boundary values in degrees, so the comparison is made on the
/// converted radians and this constant is the reference's `1e-7` unchanged.
pub const STRUCTURE_TOLERANCE_RAD: f64 = 1e-7;

/// Why a DH table is not the supported arm.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum TableError {
    /// A DH value was infinite or `NaN`. `kinematics.py:423`, "All DH parameters must be
    /// finite numbers".
    NotFinite,
    /// One of the thirteen structural constants is wrong: `kinematics.py:425-442`.
    ///
    /// **Deviation from the reference.** Python formats both values as `{value:g}` of the
    /// raw conversion, so a mis-set twist reads `joint 3 alpha=1.5708, got 0.785398`. Those
    /// are radians, and this value lands in the status line of a tab whose every other
    /// number is degrees, so the message here reports the same quantity in the unit the
    /// table is stored in: `joint 3 alpha=90, got 45`. The parameter *name* — the part
    /// `test_kinematics.py:425` asserts on — is identical.
    Structure {
        /// The reference's parameter name, e.g. `"joint 3 alpha"`.
        name: &'static str,
        /// What the structure requires, in the table's own unit.
        expected: f64,
        /// What the table says, in the table's own unit.
        got: f64,
    },
    /// The first link length must be positive: the planar solve divides by it.
    /// `kinematics.py:443`, "Inverse kinematics requires a positive a2 link length".
    LinkOneNotPositive,
    /// The second link length must be positive. `kinematics.py:445`.
    LinkTwoNotPositive,
}

impl core::fmt::Display for TableError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::NotFinite => formatter.write_str("All DH parameters must be finite numbers"),
            Self::Structure {
                name,
                expected,
                got,
            } => write!(
                formatter,
                "Inverse kinematics requires {name}={expected}, got {got}"
            ),
            Self::LinkOneNotPositive => {
                formatter.write_str("Inverse kinematics requires a positive a2 link length")
            }
            Self::LinkTwoNotPositive => {
                formatter.write_str("Inverse kinematics requires a positive d4 link offset")
            }
        }
    }
}

impl std::error::Error for TableError {}

/// Which field of a [`DhRow`](crate::DhRow) a structural constant names.
///
/// An enum rather than a match on the reference's name string: `"joint 3 alpha"` ends in
/// the same letter as `"joint 3 a"`, and telling those apart by suffix is exactly the kind
/// of slip this list exists to prevent.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Field {
    /// A link offset `d`, a length in model units.
    D,
    /// A link length `a`, in model units.
    A,
    /// A twist `alpha`, an angle in degrees.
    Alpha,
}

/// One structural constant: the row it lives on, the field's name in the reference's
/// message, and what the structure requires.
///
/// The angles are held in degrees because that is what the table stores, and converted to
/// radians for the comparison so the tolerance is the reference's own.
struct Constant {
    joint: usize,
    field: Field,
    name: &'static str,
    expected: f64,
}

/// The thirteen checks of `kinematics.py:425-439`, in the reference's order so the first
/// failure reported is the first one Python would raise.
const CONSTANTS: [Constant; 13] = [
    // alpha1 = 90 puts the shoulder on a base offset rather than a vertical column.
    Constant::angle(0, "joint 1 alpha", 90.0),
    Constant::length(1, Field::D, "joint 2 d", 0.0),
    Constant::angle(1, "joint 2 alpha", 0.0),
    Constant::length(2, Field::A, "joint 3 a", 0.0),
    Constant::length(2, Field::D, "joint 3 d", 0.0),
    Constant::angle(2, "joint 3 alpha", 90.0),
    Constant::length(3, Field::A, "joint 4 a", 0.0),
    Constant::angle(3, "joint 4 alpha", 90.0),
    Constant::length(4, Field::A, "joint 5 a", 0.0),
    Constant::length(4, Field::D, "joint 5 d", 0.0),
    Constant::angle(4, "joint 5 alpha", -90.0),
    Constant::length(5, Field::A, "joint 6 a", 0.0),
    Constant::angle(5, "joint 6 alpha", 0.0),
];

impl Constant {
    const fn angle(joint: usize, name: &'static str, expected_deg: f64) -> Self {
        Self {
            joint,
            field: Field::Alpha,
            name,
            expected: expected_deg,
        }
    }

    const fn length(joint: usize, field: Field, name: &'static str, expected: f64) -> Self {
        Self {
            joint,
            field,
            name,
            expected,
        }
    }

    fn field_value(&self, row: crate::DhRow) -> f64 {
        match self.field {
            Field::D => row.d,
            Field::A => row.a,
            Field::Alpha => row.alpha_deg,
        }
    }

    /// The value this constant names, in the table's own unit.
    fn value(&self, parameters: &DHParameters) -> f64 {
        self.field_value(parameters.joints[self.joint])
    }

    /// The same value in the unit the reference compares: radians for a twist, model
    /// units for a length.
    fn comparison_value(&self, value: f64) -> f64 {
        if self.field == Field::Alpha {
            deg_to_rad(value)
        } else {
            value
        }
    }

    fn expected_rad(&self) -> f64 {
        self.comparison_value(self.expected)
    }
}

impl DHParameters {
    /// The arm's free dimensions, if this table is the supported arm; otherwise what
    /// departs from it.
    ///
    /// The solver's precondition, `_validate_supported_geometry` (`kinematics.py:409-444`).
    /// Order matters twice over: Python checks every value for finiteness first, then the
    /// structural constants in table order, then the two link signs, and a caller that
    /// reports the *first* problem to the user reports what Python would have raised.
    pub fn structure_error(&self) -> Option<TableError> {
        for row in &self.joints {
            let values = [row.theta_offset_deg, row.d, row.a, row.alpha_deg];
            if !values.iter().all(|value| value.is_finite()) {
                return Some(TableError::NotFinite);
            }
        }

        for constant in &CONSTANTS {
            let actual = constant.comparison_value(constant.value(self));
            if (actual - constant.expected_rad()).abs() > STRUCTURE_TOLERANCE_RAD {
                return Some(TableError::Structure {
                    name: constant.name,
                    expected: constant.expected,
                    got: constant.value(self),
                });
            }
        }

        // `a2` is the first link's *length* and `d4` the second's, which is why they are
        // read out of those rows rather than out of a `link` field.
        if self.joints[1].a <= 0.0 {
            return Some(TableError::LinkOneNotPositive);
        }
        if self.joints[3].d <= 0.0 {
            return Some(TableError::LinkTwoNotPositive);
        }

        // A sixth joint is structural rather than configuration, so this can only trip if
        // `JOINT_COUNT` and the table ever disagree.
        debug_assert_eq!(self.joints.len(), JOINT_COUNT);
        None
    }

    /// Whether [`DHParameters::structure_error`] is `None`.
    pub fn is_supported_arm(&self) -> bool {
        self.structure_error().is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_shipped_table_is_the_supported_arm() {
        assert_eq!(DHParameters::shipped().structure_error(), None);
        assert!(DHParameters::shipped().is_supported_arm());
    }

    #[test]
    fn a_bad_twist_names_its_joint_and_its_degrees() {
        // `test_kinematics.py:677-691` perturbs the third joint's alpha to 45 degrees and
        // expects the message to name it.
        let mut parameters = DHParameters::shipped();
        parameters.joints[2].alpha_deg = 45.0;
        let error = parameters
            .structure_error()
            .expect("alpha3 = 45 is not supported");
        assert_eq!(
            error,
            TableError::Structure {
                name: "joint 3 alpha",
                expected: 90.0,
                got: 45.0,
            }
        );
        assert!(error.to_string().contains("joint 3 alpha"), "{error}");
    }

    #[test]
    fn every_parameter_the_reference_checks_is_checked_here() {
        // One perturbation per constant, each landing on its own name. The names are the
        // reference's own (`kinematics.py:425-439`), so this is also the list's guard
        // against a transcription slip.
        type Perturbation = (usize, fn(&mut crate::DhRow), &'static str);
        let perturbations: [Perturbation; 13] = [
            (0, |row| row.alpha_deg = 0.0, "joint 1 alpha"),
            (1, |row| row.d = 5.0, "joint 2 d"),
            (1, |row| row.alpha_deg = 30.0, "joint 2 alpha"),
            (2, |row| row.a = 5.0, "joint 3 a"),
            (2, |row| row.d = 5.0, "joint 3 d"),
            (2, |row| row.alpha_deg = 45.0, "joint 3 alpha"),
            (3, |row| row.a = 5.0, "joint 4 a"),
            (3, |row| row.alpha_deg = 45.0, "joint 4 alpha"),
            (4, |row| row.a = 5.0, "joint 5 a"),
            (4, |row| row.d = 5.0, "joint 5 d"),
            (4, |row| row.alpha_deg = 45.0, "joint 5 alpha"),
            (5, |row| row.a = 5.0, "joint 6 a"),
            (5, |row| row.alpha_deg = 45.0, "joint 6 alpha"),
        ];
        for (joint, perturb, name) in perturbations {
            let mut parameters = DHParameters::shipped();
            perturb(&mut parameters.joints[joint]);
            match parameters.structure_error() {
                Some(TableError::Structure { name: actual, .. }) => {
                    assert_eq!(actual, name, "joint {joint} perturbation")
                }
                other => panic!("expected a structure error for {name}, got {other:?}"),
            }
        }
    }

    #[test]
    fn a_zero_link_length_is_reported_by_its_own_name() {
        // `test_kinematics.py:675-691` also covers a zeroed `d4`; zeroing `a2` is the same
        // check on the other link.
        let mut shipped = DHParameters::shipped();
        shipped.joints[1].a = 0.0;
        assert_eq!(
            shipped.structure_error(),
            Some(TableError::LinkOneNotPositive)
        );

        let mut shipped = DHParameters::shipped();
        shipped.joints[3].d = 0.0;
        assert_eq!(
            shipped.structure_error(),
            Some(TableError::LinkTwoNotPositive)
        );
    }

    #[test]
    fn the_free_parameters_may_be_anything() {
        // `d1`, `a1`, `theta`, and `d6` are the four the reference leaves open, so a table
        // that only departs in those is still the supported arm and must still solve.
        let mut parameters = DHParameters::shipped();
        parameters.joints[0].d = 123.5;
        parameters.joints[0].a = -7.0;
        parameters.joints[0].theta_offset_deg = 31.0;
        parameters.joints[4].theta_offset_deg = -180.0;
        parameters.joints[5].d = 42.25;
        assert_eq!(parameters.structure_error(), None);
    }

    #[test]
    fn the_finiteness_check_runs_before_the_structural_ones() {
        // Python scans every value for finiteness first (`kinematics.py:421-423`), so a
        // table that is both non-finite and misstructured reports the former.
        let mut parameters = DHParameters::shipped();
        parameters.joints[2].alpha_deg = 45.0;
        parameters.joints[3].d = f64::NAN;
        assert_eq!(parameters.structure_error(), Some(TableError::NotFinite));
    }

    #[test]
    fn a_twist_within_the_reference_tolerance_is_accepted() {
        // The comparison is the reference's own `abs_tol=1e-7` on radians, so 89.9999999
        // degrees is inside it and 89.999 degrees is not.
        let mut inside = DHParameters::shipped();
        inside.joints[2].alpha_deg = 90.0 - 1e-8;
        assert_eq!(inside.structure_error(), None);

        let mut outside = DHParameters::shipped();
        outside.joints[2].alpha_deg = 90.0 - 1e-3;
        assert!(outside.structure_error().is_some());
    }
}
