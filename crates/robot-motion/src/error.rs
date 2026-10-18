//! Closed error enums, with no allocation.

use core::fmt;

/// Why a planner call failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanError {
    /// A limit was zero, negative, or not finite.
    NonPositiveLimit,
    /// A state or position input was NaN or infinite.
    NonFiniteInput,
    /// The requested state fails the stop–move–start viability predicate.
    ///
    /// This is exact for that decomposition; it is not a global infeasibility
    /// certificate (a direct profile that never passes through rest can exist).
    Infeasible,
    /// A finite input produced a non-finite intermediate (overflow).
    NumericalFailure,
    /// The profile would exceed [`crate::MAX_PHASES`].
    ProfileOverflow,
}

impl fmt::Display for PlanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::NonPositiveLimit => "a limit is zero, negative, or not finite",
            Self::NonFiniteInput => "a state input is not finite",
            Self::Infeasible => "the state fails the stop-move-start viability predicate",
            Self::NumericalFailure => "a derived quantity overflowed to a non-finite value",
            Self::ProfileOverflow => "the profile would exceed MAX_PHASES",
        };
        f.write_str(text)
    }
}

impl core::error::Error for PlanError {}

/// Why a profile could not be constructed or transformed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProfileError {
    /// More segments than [`crate::MAX_PHASES`].
    TooManySegments,
    /// A segment duration was negative or not finite.
    NegativeDuration,
    /// A value was NaN or infinite.
    NonFinite,
    /// A stretch factor below one (the verified domain is `k >= 1`).
    InvalidStretch,
    /// `append` was called with a mismatched junction state.
    JunctionMismatch,
}

impl fmt::Display for ProfileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::TooManySegments => "too many segments for MAX_PHASES",
            Self::NegativeDuration => "a segment duration is negative or not finite",
            Self::NonFinite => "a value is not finite",
            Self::InvalidStretch => "a stretch factor must be at least one",
            Self::JunctionMismatch => "the appended profile does not start at the junction state",
        };
        f.write_str(text)
    }
}

impl core::error::Error for ProfileError {}
