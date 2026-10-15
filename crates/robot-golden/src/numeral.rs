//! Reading the numerals the Lean generators emit.
//!
//! `lean/ForceTorqueTestData.lean` established the format and it is worth restating,
//! because it is what makes exact comparison possible across the language boundary:
//! every numeral in the generated JSON is a **string**, either `"3"` or `"-3/5"`, and
//! never a JSON number. A JSON number would round-trip through a float and quietly
//! destroy the exactness the whole arrangement exists to provide.
//!
//! `test_force_torque.py` enforces the same rule from the Python side, and fails loudly
//! on finding a float — this module is its Rust counterpart.

use crate::rational::Ratio;
use serde_json::Value;

/// Why a generated value could not be read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NumeralError {
    /// The value was a JSON number rather than a string. The generator must never emit
    /// one; seeing this means the exactness guarantee has been broken upstream.
    NotAString(&'static str),
    /// A string that is not `"n"` or `"n/d"`.
    Malformed(String),
    /// The string parsed but the denominator was zero.
    ZeroDenominator(String),
}

impl core::fmt::Display for NumeralError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotAString(what) => write!(
                f,
                "{what} is a JSON number, not a string: the ground truth must stay exact"
            ),
            Self::Malformed(text) => write!(f, "not a numeral: {text:?}"),
            Self::ZeroDenominator(text) => write!(f, "numeral with a zero denominator: {text:?}"),
        }
    }
}

/// Read one numeral.
pub fn numeral(value: &Value) -> Result<Ratio, NumeralError> {
    let text = value
        .as_str()
        .ok_or(NumeralError::NotAString("value"))?;
    parse(text)
}

/// Read one numeral from a named field of an object.
pub fn numeral_at(object: &Value, key: &str) -> Result<Ratio, NumeralError> {
    let value = object
        .get(key)
        .ok_or_else(|| NumeralError::Malformed(format!("missing field {key:?}")))?;
    numeral(value)
}

/// Parse `"3"` or `"-3/5"`.
pub fn parse(text: &str) -> Result<Ratio, NumeralError> {
    match text.split_once('/') {
        None => text
            .parse::<i128>()
            .map(Ratio::integer)
            .map_err(|_| NumeralError::Malformed(text.to_owned())),
        Some((numerator, denominator)) => {
            let numerator = numerator
                .parse::<i128>()
                .map_err(|_| NumeralError::Malformed(text.to_owned()))?;
            let denominator = denominator
                .parse::<i128>()
                .map_err(|_| NumeralError::Malformed(text.to_owned()))?;
            if denominator == 0 {
                return Err(NumeralError::ZeroDenominator(text.to_owned()));
            }
            Ok(Ratio::new(numerator, denominator))
        }
    }
}

/// Read a three-vector, `["1", "0", "-3/5"]`.
pub fn vec3(value: &Value) -> Result<[Ratio; 3], NumeralError> {
    let array = value
        .as_array()
        .ok_or_else(|| NumeralError::Malformed("expected a three-element array".to_owned()))?;
    if array.len() != 3 {
        return Err(NumeralError::Malformed(format!(
            "expected three components, found {}",
            array.len()
        )));
    }
    Ok([
        numeral(&array[0])?,
        numeral(&array[1])?,
        numeral(&array[2])?,
    ])
}

/// Read a 3x3 matrix in the row-major layout every part of this project uses, so
/// `matrix(value)[i][j]` is the same entry as Lean's `M i j` and Python's `R[i][j]`.
pub fn matrix3(value: &Value) -> Result<[[Ratio; 3]; 3], NumeralError> {
    let rows = value
        .as_array()
        .ok_or_else(|| NumeralError::Malformed("expected three rows".to_owned()))?;
    if rows.len() != 3 {
        return Err(NumeralError::Malformed(format!(
            "expected three rows, found {}",
            rows.len()
        )));
    }
    Ok([vec3(&rows[0])?, vec3(&rows[1])?, vec3(&rows[2])?])
}

/// Read a named array of records, the shape every generated document uses at the top
/// level: `{ "cases": [ { "name": ..., ... }, ... ] }`.
pub fn entries<'a>(document: &'a Value, key: &str) -> Result<&'a Vec<Value>, NumeralError> {
    document
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| NumeralError::Malformed(format!("missing array {key:?}")))
}

/// The `name` field of a record, used to report which case failed.
pub fn name(record: &Value) -> &str {
    record.get("name").and_then(Value::as_str).unwrap_or("<unnamed>")
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn integers_and_fractions_round_trip() {
        assert_eq!(parse("3").unwrap(), Ratio::integer(3));
        assert_eq!(parse("-3/5").unwrap(), Ratio::new(-3, 5));
        assert_eq!(parse("6/4").unwrap(), Ratio::new(3, 2));
    }

    #[test]
    fn a_json_number_is_rejected_rather_than_rounded() {
        // The whole point of the string format: a bare number would have gone through a
        // float already. This must be an error, not a silent conversion.
        assert_eq!(
            numeral(&json!(0.5)),
            Err(NumeralError::NotAString("value"))
        );
    }

    #[test]
    fn a_zero_denominator_is_rejected() {
        assert!(matches!(parse("1/0"), Err(NumeralError::ZeroDenominator(_))));
    }

    #[test]
    fn vectors_and_matrices_read_in_row_major_order() {
        let v = vec3(&json!(["1", "0", "-3/5"])).unwrap();
        assert_eq!(v, [Ratio::integer(1), Ratio::ZERO, Ratio::new(-3, 5)]);

        let m = matrix3(&json!([["0", "1", "0"], ["-1", "0", "0"], ["0", "0", "1"]])).unwrap();
        assert_eq!(m[1][0], Ratio::integer(-1));
        assert_eq!(m[2][2], Ratio::integer(1));
    }

    #[test]
    fn a_wrong_length_is_rejected() {
        assert!(vec3(&json!(["1", "0"])).is_err());
        assert!(matrix3(&json!([["1", "0", "0"]])).is_err());
    }
}
