// ECMA-262 numeric conversions: Number::toString(10) (the canonical shortest
// decimal repr every trace head must agree on byte-for-byte) and the
// StringNumericLiteral grammar behind ToNumber. Written from the spec
// (6.1.6.1.20, 7.1.4.1); the shortest round-trip mantissa comes from Rust's
// `{:e}` formatting, and the spec's positional rules are applied on top.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// ECMA-262 Number::toString(x, 10). This is the STRING-COERCION repr:
/// `-0` renders as `"0"`. The trace projection distinguishes `-0` separately.
#[must_use]
pub fn js_number_to_string(x: f64) -> String {
    if x.is_nan() {
        return "NaN".to_string();
    }
    if x == f64::INFINITY {
        return "Infinity".to_string();
    }
    if x == f64::NEG_INFINITY {
        return "-Infinity".to_string();
    }
    if x == 0.0 {
        return "0".to_string(); // both zeros
    }
    if x < 0.0 {
        return format!("-{}", js_number_to_string(-x));
    }
    // Shortest round-trip decimal: Rust's LowerExp gives `d[.ddd]e<exp>` with
    // the minimal digit count that round-trips (Grisu/Ryū since 1.32).
    let sci = format!("{x:e}");
    let (mant, exp_s) = sci
        .split_once('e')
        .expect("LowerExp always contains an exponent");
    let exp: i32 = exp_s.parse().expect("LowerExp exponent is an integer");
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let digits = digits.trim_end_matches('0');
    let digits = if digits.is_empty() { "0" } else { digits };
    // Spec 6.1.6.1.20: x = s × 10^(n-k) with k digits; here n = exp + 1.
    let k = i64::try_from(digits.len()).expect("digit count fits i64");
    let n = i64::from(exp) + 1;
    if k <= n && n <= 21 {
        // Integer with trailing zeros.
        let zeros = usize::try_from(n - k).expect("non-negative");
        format!("{digits}{}", "0".repeat(zeros))
    } else if 0 < n && n <= 21 {
        let split = usize::try_from(n).expect("positive");
        format!("{}.{}", &digits[..split], &digits[split..])
    } else if -6 < n && n <= 0 {
        let zeros = usize::try_from(-n).expect("non-negative");
        format!("0.{}{digits}", "0".repeat(zeros))
    } else {
        // Exponential form with explicit sign.
        let e = n - 1;
        let sign = if e >= 0 { "+" } else { "-" };
        let mag = e.abs();
        if k == 1 {
            format!("{digits}e{sign}{mag}")
        } else {
            format!("{}.{}e{sign}{mag}", &digits[..1], &digits[1..])
        }
    }
}

/// The projection repr of a number VALUE: identical to `js_number_to_string`
/// except `-0` renders `"-0"` (mirrors the driver's `numberRepr`).
#[must_use]
pub fn projection_number_repr(x: f64) -> String {
    if x == 0.0 && x.is_sign_negative() {
        return "-0".to_string();
    }
    js_number_to_string(x)
}

/// ECMA-262 WhiteSpace + LineTerminator, as trimmed by ToNumber(string).
fn is_js_ws(c: char) -> bool {
    matches!(
        c,
        '\t' | '\u{b}'
            | '\u{c}'
            | ' '
            | '\u{a0}'
            | '\u{feff}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200a}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\n'
            | '\r'
            | '\u{2028}'
            | '\u{2029}'
    )
}

/// ToNumber on a string (StringNumericLiteral). `Err(reason)` means the input
/// is outside the modeled slice (radix literal too long for exact f64
/// accumulation) and the case must refuse rather than guess.
pub fn to_number_str(s: &str) -> Result<f64, String> {
    let t: String = s
        .trim_matches(is_js_ws)
        .to_string();
    if t.is_empty() {
        return Ok(0.0);
    }
    // Radix prefixes admit no sign.
    if let Some(rest) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return radix_literal(rest, 16, 13);
    }
    if let Some(rest) = t.strip_prefix("0o").or_else(|| t.strip_prefix("0O")) {
        return radix_literal(rest, 8, 17);
    }
    if let Some(rest) = t.strip_prefix("0b").or_else(|| t.strip_prefix("0B")) {
        return radix_literal(rest, 2, 53);
    }
    let (neg, body) = match t.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, t.strip_prefix('+').unwrap_or(&t)),
    };
    if body == "Infinity" {
        return Ok(if neg { f64::NEG_INFINITY } else { f64::INFINITY });
    }
    if !is_str_decimal_literal(body) {
        return Ok(f64::NAN);
    }
    // Rust's parse is correctly rounded and accepts exactly the validated
    // shapes ("1.", ".5", "1e5", ...).
    let mag: f64 = body.parse().map_err(|e| format!("f64 parse: {e}"))?;
    Ok(if neg { -mag } else { mag })
}

fn radix_literal(digits: &str, radix: u32, max_len: usize) -> Result<f64, String> {
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return Ok(f64::NAN);
    }
    if digits.len() > max_len {
        // Beyond exact-in-f64 territory: progressive rounding could diverge
        // from the spec's round-once semantics. Refuse.
        return Err(format!("radix-{radix} literal longer than {max_len} digits"));
    }
    let v = u64::from_str_radix(digits, radix).map_err(|e| format!("radix parse: {e}"))?;
    #[allow(clippy::cast_precision_loss)] // exact by the length cap above
    Ok(v as f64)
}

/// StrDecimalLiteral (unsigned): digits [. digits?] [exp] | . digits [exp]
fn is_str_decimal_literal(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    let start_digits = eat_digits(b, &mut i);
    let mut any = start_digits;
    if i < b.len() && b[i] == b'.' {
        i += 1;
        let frac = eat_digits(b, &mut i);
        any = any || frac;
    }
    if !any {
        return false;
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        i += 1;
        if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
            i += 1;
        }
        if !eat_digits(b, &mut i) {
            return false;
        }
    }
    i == b.len()
}

fn eat_digits(b: &[u8], i: &mut usize) -> bool {
    let start = *i;
    while *i < b.len() && b[*i].is_ascii_digit() {
        *i += 1;
    }
    *i > start
}

/// ToUint32-exactness check for Array length writes: `Some(u)` iff the number
/// is a non-negative integer below 2^32 (so ToUint32 is the identity and no
/// RangeError modeling ambiguity arises); -0 maps to 0.
#[must_use]
pub fn exact_uint32(n: f64) -> Option<u32> {
    if n.is_finite() && n.trunc() == n && n >= -0.0 && n < 4_294_967_296.0 {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Some(n as u32)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_to_string_vectors() {
        let cases: &[(f64, &str)] = &[
            (1.0, "1"),
            (f64::NAN, "NaN"),
            (f64::INFINITY, "Infinity"),
            (f64::NEG_INFINITY, "-Infinity"),
            (0.1, "0.1"),
            (0.1 + 0.2, "0.30000000000000004"),
            (1e21, "1e+21"),
            (1e-7, "1e-7"),
            (123_456_789.0, "123456789"),
            (5e-324, "5e-324"),
            (1.7976931348623157e308, "1.7976931348623157e+308"),
            (100.0, "100"),
            (0.000_001, "0.000001"),
            (-1.5, "-1.5"),
            (2e21, "2e+21"),
            (1.5e22, "1.5e+22"),
            (123_456_789_012_345_680_000.0, "123456789012345680000"),
        ];
        for (x, want) in cases {
            assert_eq!(js_number_to_string(*x), *want, "input {x:?}");
        }
        // String coercion of -0 is "0"; the projection alone says "-0".
        assert_eq!(js_number_to_string(-0.0), "0");
        assert_eq!(projection_number_repr(-0.0), "-0");
        assert_eq!(projection_number_repr(0.0), "0");
        assert_eq!(projection_number_repr(f64::NAN), "NaN");
    }

    #[test]
    fn to_number_vectors() {
        assert_eq!(to_number_str("").unwrap(), 0.0);
        assert_eq!(to_number_str("  42  ").unwrap(), 42.0);
        assert_eq!(to_number_str("0x10").unwrap(), 16.0);
        assert_eq!(to_number_str("-Infinity").unwrap(), f64::NEG_INFINITY);
        assert_eq!(to_number_str("+1.5e2").unwrap(), 150.0);
        assert_eq!(to_number_str(".5").unwrap(), 0.5);
        assert_eq!(to_number_str("5.").unwrap(), 5.0);
        assert!(to_number_str("12abc").unwrap().is_nan());
        assert!(to_number_str("-0x10").unwrap().is_nan());
        assert!(to_number_str("1e").unwrap().is_nan());
        assert!(to_number_str("0xffffffffffffffff").is_err()); // 16 hex digits: refuse
        assert_eq!(
            to_number_str("-0").unwrap().to_bits(),
            (-0.0f64).to_bits()
        );
    }

    #[test]
    fn exact_uint32_vectors() {
        assert_eq!(exact_uint32(0.0), Some(0));
        assert_eq!(exact_uint32(-0.0), Some(0));
        assert_eq!(exact_uint32(4_294_967_295.0), Some(4_294_967_295));
        assert_eq!(exact_uint32(4_294_967_296.0), None);
        assert_eq!(exact_uint32(1.5), None);
        assert_eq!(exact_uint32(-1.0), None);
        assert_eq!(exact_uint32(f64::NAN), None);
    }
}
