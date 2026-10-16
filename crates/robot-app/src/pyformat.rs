//! Python's `%g` number formatting, for the values the reference puts on screen.
//!
//! `simulator.py` shows every number through the `g` family, and it uses three shapes:
//! `_format_value` (`simulator.py:591-592`) fills the DH entries, the jog steps and the
//! runtime joint angles with `f"{value:g}"`; the Copy XYZ clipboard text spells the same
//! fields `.15g` (`simulator.py:304-312`); and the jog status strings use `+g`
//! (`simulator.py:341`, `:405`, `:414`, `:423`, `:432`). A window that printed `1.0`
//! where the reference printed `1` would be a cosmetic difference, but these strings also
//! go back into the entry fields as text, so the digits are part of the behavior and not
//! just of the look.
//!
//! # What `%g` does
//!
//! The value is rounded to `precision` significant digits, and the exponent of the
//! *rounded* value then picks the layout: scientific notation when that exponent is below
//! -4 or at or above `precision`, fixed notation otherwise. Trailing zeros come off the
//! fractional part, and a trailing decimal point with them. So `100000.0` prints as
//! `100000` while `1000000.0` prints as `1e+06`, and because the cutover follows the
//! rounded exponent rather than the value, `999999.5` — below a million — prints as
//! `1e+06` as well.
//!
//! The rounding is Rust's own: `{:.*e}` converts the exact binary value to `precision`
//! significant decimal digits, correctly rounded with ties to even, which is the rule
//! CPython's `dtoa` uses. The test tables below are the evidence, since "both round
//! half to even" is exactly the sort of claim that is worth checking rather than
//! asserting: they include the ties (`123456.5` and `123455.5` both print `123456`,
//! `125.0` at `%.2g` prints `1.2e+02`), where a round-half-away-from-zero rule would
//! print something else.
//!
//! # The two places this is more than layout
//!
//! A NaN carries no sign into the output, whatever its sign bit says. CPython prints
//! `nan` for `-float("nan")`, and `%+g` turns that into `+nan` — the flag adds a `+`
//! because the text does not already start with one. Rust's own spelling would be
//! `-NaN`, so the special values are handled before the sign is written.
//!
//! Nothing here is locale-dependent in either language, and nothing here rounds through
//! the decimal module, so the digit strings are the same on every platform as long as the
//! double is (`%g` is specified in terms of the value, not of the C library's printf).

/// Python's `format(value, "g")` / `"%g"` — six significant digits, trailing zeros
/// and a trailing decimal point removed.
///
/// Every widget text in the reference goes through this (`simulator.py:591-592`).
pub fn format_g(value: f64) -> String {
    format_signed_g(value, DEFAULT_PRECISION, false)
}

/// Python's `"%.<precision>g"`. `format_precision_g(value, 15)` is `"%.15g"`.
///
/// The Copy XYZ clipboard text is the reference's only `.15g` user
/// (`simulator.py:304-312`): a pose copied out of the window keeps fifteen digits rather
/// than the six the widget text it was read from had.
///
/// A precision of zero is treated as one, matching `%.0g`.
pub fn format_precision_g(value: f64, precision: usize) -> String {
    format_signed_g(value, precision, false)
}

/// Python's `"%+g"` — [`format_g`] with an explicit sign.
///
/// The jog status strings (`simulator.py:341`, `:405`, `:414`, `:423`, `:432`) show the
/// signed step so that the direction is readable without reading the axis.
pub fn format_plus_g(value: f64) -> String {
    format_signed_g(value, DEFAULT_PRECISION, true)
}

/// `%g`'s default precision: six significant digits.
const DEFAULT_PRECISION: usize = 6;

/// The one implementation: `precision` significant digits, `plus` for the `+` flag.
fn format_signed_g(value: f64, precision: usize, plus: bool) -> String {
    // Before any sign handling, because the sign of a NaN is not printed at all. The
    // `+` flag still applies, since CPython checks for a leading `-` and finds none.
    if value.is_nan() {
        return if plus { "+nan" } else { "nan" }.to_string();
    }

    let mut out = String::new();
    if value.is_sign_negative() {
        out.push('-');
    } else if plus {
        out.push('+');
    }

    // An infinity is the sign written above plus the word, which is how CPython prints
    // one; there is no mantissa to round.
    if value.is_infinite() {
        out.push_str("inf");
        return out;
    }

    // Python reads a precision of zero as one; there are no zero-significant-digit
    // numbers to print.
    let precision = precision.max(1);

    // Round to `precision` significant digits and read the exponent back off the result.
    // `{:.*e}` is the shortest path to a correctly rounded digit string: the exponent it
    // reports is the one belonging to the rounded value, so `9.999999e-5` comes back as
    // `1.00000e-4` and this side never has to carry a rounding overflow itself.
    //
    // The magnitude is formatted, not the value: `-0.0` has to keep its sign in the
    // output, and the sign is written above rather than left to the mantissa.
    let scientific = format!("{:.*e}", precision - 1, value.abs());
    let (mantissa, exponent) = scientific
        .split_once('e')
        .expect("`e` formatting always writes an exponent");
    let exponent: i32 = exponent
        .parse()
        .expect("`e` formatting writes a plain integer exponent");
    // `precision` digits with the point taken out, which is the digit string both layouts
    // are carved from.
    let digits = mantissa.replace('.', "");

    if exponent < -4 || exponent >= precision as i32 {
        // Scientific: one digit, then as many of the rest as survive the stripping of
        // trailing zeros. The exponent is signed and zero-padded to two digits, so the
        // reference's `1e-05` and `1e+06` come out with the padding and `1e+100` without.
        out.push_str(&digits[..1]);
        let fraction = digits[1..].trim_end_matches('0');
        if !fraction.is_empty() {
            out.push('.');
            out.push_str(fraction);
        }
        out.push('e');
        out.push(if exponent < 0 { '-' } else { '+' });
        out.push_str(&format!("{:02}", exponent.unsigned_abs()));
        return out;
    }

    // Fixed: `precision - 1 - exponent` digits after the point, which is the point's
    // position in the digit string. Everything the value does not reach is a zero —
    // leading zeros when the point falls left of the first digit, trailing ones when it
    // falls right of the last.
    let point = exponent + 1;
    let (integer, fraction) = if point <= 0 {
        (
            "0".to_string(),
            format!("{}{}", "0".repeat(-point as usize), digits),
        )
    } else if (point as usize) < digits.len() {
        (
            digits[..point as usize].to_string(),
            digits[point as usize..].to_string(),
        )
    } else {
        (
            format!("{}{}", digits, "0".repeat(point as usize - digits.len())),
            String::new(),
        )
    };
    out.push_str(&integer);
    let fraction = fraction.trim_end_matches('0');
    if !fraction.is_empty() {
        out.push('.');
        out.push_str(fraction);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(value, "%g", "%+g", "%.15g")`, copied from `repr()` of CPython's own output.
    ///
    /// Checked in rather than generated at test time, so the expectations are readable
    /// here and a change to either side has to be looked at: a script run with
    /// `python -I` reading `format(value, "g")`, `format(value, "+g")` and
    /// `format(value, ".15g")` for this value column prints these strings. CPython
    /// 3.11.9 produced the ones below.
    const PYTHON_TABLE: &[(f64, &str, &str, &str)] = &[
        // Integers, the sign of a zero, and the `+` flag.
        (0.0, "0", "+0", "0"),
        (-0.0, "-0", "-0", "-0"),
        (1.0, "1", "+1", "1"),
        (-1.0, "-1", "-1", "-1"),
        (5.0, "5", "+5", "5"),
        (-5.0, "-5", "-5", "-5"),
        (0.5, "0.5", "+0.5", "0.5"),
        (10.0, "10", "+10", "10"),
        (90.0, "90", "+90", "90"),
        (100.0, "100", "+100", "100"),
        // The fixed/scientific cutover at an exponent of -4.
        (0.0001, "0.0001", "+0.0001", "0.0001"),
        (1e-5, "1e-05", "+1e-05", "1e-05"),
        (0.001, "0.001", "+0.001", "0.001"),
        (0.000123456, "0.000123456", "+0.000123456", "0.000123456"),
        (
            -0.0001234567,
            "-0.000123457",
            "-0.000123457",
            "-0.0001234567",
        ),
        (0.0000123456, "1.23456e-05", "+1.23456e-05", "1.23456e-05"),
        // Exponents at and past the padding boundary, where the zero has to be added
        // rather than left off: the reference's own step sizes and distances land here.
        (1e-6, "1e-06", "+1e-06", "1e-06"),
        (1e-7, "1e-07", "+1e-07", "1e-07"),
        (2.5e-7, "2.5e-07", "+2.5e-07", "2.5e-07"),
        (-1e-7, "-1e-07", "-1e-07", "-1e-07"),
        (1e-8, "1e-08", "+1e-08", "1e-08"),
        // Rounded up across the cutover: six digits of `9.999999e-5` is `1.00000e-4`,
        // whose exponent puts it back on the fixed side.
        (9.999999e-5, "0.0001", "+0.0001", "9.999999e-05"),
        // The cutover at an exponent of `precision`, including the value that reaches it
        // only by rounding.
        (999999.0, "999999", "+999999", "999999"),
        (999999.5, "1e+06", "+1e+06", "999999.5"),
        (100000.0, "100000", "+100000", "100000"),
        (1000000.0, "1e+06", "+1e+06", "1000000"),
        (123456.0, "123456", "+123456", "123456"),
        (1234567.0, "1.23457e+06", "+1.23457e+06", "1234567"),
        // Exponents past two digits, which the padding must not truncate or re-pad.
        (1e15, "1e+15", "+1e+15", "1e+15"),
        (1e16, "1e+16", "+1e+16", "1e+16"),
        (1e21, "1e+21", "+1e+21", "1e+21"),
        (1e100, "1e+100", "+1e+100", "1e+100"),
        (1e-100, "1e-100", "+1e-100", "1e-100"),
        // Repeating decimals, where the last digit is a genuine rounding.
        (1.0 / 3.0, "0.333333", "+0.333333", "0.333333333333333"),
        (2.0 / 3.0, "0.666667", "+0.666667", "0.666666666666667"),
        (1.0 / 7.0, "0.142857", "+0.142857", "0.142857142857143"),
        (
            std::f64::consts::PI,
            "3.14159",
            "+3.14159",
            "3.14159265358979",
        ),
        // The double that is not 0.3, printed as if it were.
        (0.1 + 0.2, "0.3", "+0.3", "0.3"),
        (
            -std::f64::consts::PI,
            "-3.14159",
            "-3.14159",
            "-3.14159265358979",
        ),
        // The ends of the range: the smallest subnormal, a subnormal with a full
        // significand, the smallest normal and the largest finite value.
        (
            5e-324,
            "4.94066e-324",
            "+4.94066e-324",
            "4.94065645841247e-324",
        ),
        (
            1e-320,
            "9.99989e-321",
            "+9.99989e-321",
            "9.99988867182683e-321",
        ),
        (
            2.2250738585072014e-308,
            "2.22507e-308",
            "+2.22507e-308",
            "2.2250738585072e-308",
        ),
        (
            f64::MAX,
            "1.79769e+308",
            "+1.79769e+308",
            "1.79769313486232e+308",
        ),
        // The special values, where `+g` adds a sign to a NaN but the sign bit does not.
        (f64::NAN, "nan", "+nan", "nan"),
        (-f64::NAN, "nan", "+nan", "nan"),
        (f64::INFINITY, "inf", "+inf", "inf"),
        (f64::NEG_INFINITY, "-inf", "-inf", "-inf"),
    ];

    /// `(value, precision, "%.<precision>g")`, the narrower precisions, which are where
    /// a rounding tie shows at all. Same provenance as [`PYTHON_TABLE`].
    const PYTHON_PRECISION_TABLE: &[(f64, usize, &str)] = &[
        // A precision of zero is one significant digit, as `%.0g` is in CPython.
        (123.456, 0, "1e+02"),
        (0.0, 0, "0"),
        (0.0001, 0, "0.0001"),
        (999.9, 0, "1e+03"),
        (f64::NAN, 0, "nan"),
        // Ties to even, which is the rule that distinguishes this from `%.1g` of a
        // printf that rounds halves away from zero.
        (1.5, 1, "2"),
        (2.5, 1, "2"),
        (3.5, 1, "4"),
        (125.0, 2, "1.2e+02"),
        (135.0, 2, "1.4e+02"),
        (0.000123456, 3, "0.000123"),
        (1.23456e-5, 3, "1.23e-05"),
        (123456.5, 6, "123456"),
        (123455.5, 6, "123456"),
        (9.999999e-5, 6, "0.0001"),
        (999999.5, 6, "1e+06"),
        (1500000.0, 6, "1.5e+06"),
        (1.0 / 3.0, 15, "0.333333333333333"),
        (2.0 / 3.0, 15, "0.666666666666667"),
        (1.0 / 7.0, 15, "0.142857142857143"),
        (std::f64::consts::PI, 15, "3.14159265358979"),
        (999999.5, 15, "999999.5"),
        (1000000.0, 15, "1000000"),
        (1e-15, 15, "1e-15"),
        (5e-324, 15, "4.94065645841247e-324"),
    ];

    #[test]
    fn the_three_shapes_match_cpython() {
        for (value, g, plus_g, precision_g) in PYTHON_TABLE {
            assert_eq!(format_g(*value), *g, "format_g({value:?})");
            assert_eq!(format_plus_g(*value), *plus_g, "format_plus_g({value:?})");
            assert_eq!(
                format_precision_g(*value, 15),
                *precision_g,
                "format_precision_g({value:?}, 15)"
            );
        }
    }

    #[test]
    fn other_precisions_match_cpython() {
        for (value, precision, expected) in PYTHON_PRECISION_TABLE {
            assert_eq!(
                format_precision_g(*value, *precision),
                *expected,
                "format_precision_g({value:?}, {precision})"
            );
        }
    }

    /// The examples the task was specified against, spelled out as the single expressions
    /// a reader can check against the language they know.
    #[test]
    fn the_worked_examples_hold() {
        assert_eq!(format_g(5.0), "5");
        assert_eq!(format_g(0.001), "0.001");
        assert_eq!(format_g(1e-5), "1e-05");
        assert_eq!(format_g(1234567.0), "1.23457e+06");
        assert_eq!(format_g(100000.0), "100000");
        assert_eq!(format_g(1000000.0), "1e+06");
        assert_eq!(format_g(-0.0), "-0");
        assert_eq!(format_plus_g(5.0), "+5");
        assert_eq!(format_plus_g(0.5), "+0.5");
        assert_eq!(format_plus_g(-1.0), "-1");
        assert_eq!(format_precision_g(1.0 / 3.0, 15), "0.333333333333333");
    }
}
