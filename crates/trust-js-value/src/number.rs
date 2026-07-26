// ECMA-262 numeric conversions, written from the spec (6.1.6.1, 7.1):
// Number::toString(10) — the canonical shortest decimal repr every trace head
// must agree on byte-for-byte — plus StringNumericLiteral (ToNumber on
// strings), NumericLiteral MV (source literals with separators and all
// bases), and the integer conversions (ToIntegerOrInfinity, ToInt32,
// ToUint32, ToLength). The shortest round-trip mantissa comes from Rust's
// `{:e}` formatting (Grisu/Ryū, shortest round-trip since 1.32); the spec's
// positional rules are applied on top.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// ECMA-262 Number::toString(x, 10) — the STRING-COERCION repr: `-0` renders
/// as `"0"`. The trace projection distinguishes `-0` separately.
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
    // Shortest round-trip decimal digits and exponent.
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
        let zeros = usize::try_from(n - k).expect("non-negative");
        format!("{digits}{}", "0".repeat(zeros))
    } else if 0 < n && n <= 21 {
        let split = usize::try_from(n).expect("positive");
        format!("{}.{}", &digits[..split], &digits[split..])
    } else if -6 < n && n <= 0 {
        let zeros = usize::try_from(-n).expect("non-negative");
        format!("0.{}{digits}", "0".repeat(zeros))
    } else {
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
/// except `-0` renders `"-0"` (mirrors the trace driver's `numberRepr`).
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

/// ToNumber on a string value (StringNumericLiteral, 7.1.4.1). `Err(reason)`
/// means the input is outside the modeled slice (a radix literal too long for
/// exact accumulation) and the case must refuse rather than guess.
pub fn to_number_str(s: &str) -> Result<f64, String> {
    let t = s.trim_matches(is_js_ws);
    if t.is_empty() {
        return Ok(0.0);
    }
    // Radix prefixes admit no sign.
    if let Some(rest) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return radix_int(rest, 16);
    }
    if let Some(rest) = t.strip_prefix("0o").or_else(|| t.strip_prefix("0O")) {
        return radix_int(rest, 8);
    }
    if let Some(rest) = t.strip_prefix("0b").or_else(|| t.strip_prefix("0B")) {
        return radix_int(rest, 2);
    }
    let (neg, body) = match t.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, t.strip_prefix('+').unwrap_or(t)),
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

/// Exact non-decimal integer: u128 accumulation, correctly rounded once at
/// the final int→float conversion. NaN for non-digits; refusal past 128 bits
/// (progressive rounding could diverge from the spec's round-once semantics).
fn radix_int(digits: &str, radix: u32) -> Result<f64, String> {
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return Ok(f64::NAN);
    }
    match u128::from_str_radix(digits, radix) {
        // u128→f64 casts are correctly rounded (round-to-nearest-even).
        #[allow(clippy::cast_precision_loss)]
        Ok(v) => Ok(v as f64),
        Err(_) => Err(format!(
            "radix-{radix} literal beyond exact 128-bit accumulation"
        )),
    }
}

/// StrDecimalLiteral (unsigned): digits [. digits?] [exp] | . digits [exp]
fn is_str_decimal_literal(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    let int_digits = eat_digits(b, &mut i);
    let mut any = int_digits;
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

/// The mathematical value of a source NumericLiteral, as lexed by
/// trust-js-parse (raw text, possibly with `_` separators; 0x/0o/0b
/// prefixes; legacy octal `0777`; non-octal decimal `08`). BigInt suffixes
/// never reach here (the AST carries them as `Expr::BigInt`).
pub fn numeric_literal_mv(raw: &str) -> Result<f64, String> {
    let t: String = raw.chars().filter(|c| *c != '_').collect();
    if let Some(rest) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return exact_radix_literal(rest, 16);
    }
    if let Some(rest) = t.strip_prefix("0o").or_else(|| t.strip_prefix("0O")) {
        return exact_radix_literal(rest, 8);
    }
    if let Some(rest) = t.strip_prefix("0b").or_else(|| t.strip_prefix("0B")) {
        return exact_radix_literal(rest, 2);
    }
    // Legacy octal: `0` followed by octal digits only (the lexer classifies;
    // re-derive structurally: leading 0, ≥2 chars, all digits, none of 8/9,
    // no '.'/exponent).
    if t.len() >= 2
        && t.starts_with('0')
        && t.bytes().all(|b| b.is_ascii_digit())
        && !t.bytes().any(|b| b == b'8' || b == b'9')
    {
        return exact_radix_literal(&t[1..], 8);
    }
    // DecimalLiteral (including non-octal `08`-style with leading zeros):
    // Rust's decimal parse is correctly rounded over the full grammar.
    t.parse::<f64>().map_err(|e| format!("decimal literal parse: {e}"))
}

fn exact_radix_literal(digits: &str, radix: u32) -> Result<f64, String> {
    if digits.is_empty() {
        return Err("empty radix literal (parser bug?)".to_string());
    }
    match u128::from_str_radix(digits, radix) {
        #[allow(clippy::cast_precision_loss)]
        Ok(v) => Ok(v as f64),
        Err(_) => Err(format!(
            "radix-{radix} literal beyond exact 128-bit accumulation"
        )),
    }
}

/// ToIntegerOrInfinity (7.1.5), saturating far outside the safe range.
#[must_use]
pub fn to_integer_or_infinity(n: f64) -> f64 {
    if n.is_nan() || n == 0.0 {
        return 0.0;
    }
    n.trunc()
}

/// ToInt32 (7.1.6).
#[must_use]
pub fn to_int32(n: f64) -> i32 {
    let u = to_uint32(n);
    if u >= 0x8000_0000 {
        // Wrap into the signed range.
        i32::from_ne_bytes(u.to_ne_bytes())
    } else {
        i32::try_from(u).expect("below 2^31")
    }
}

/// ToUint32 (7.1.7).
#[must_use]
pub fn to_uint32(n: f64) -> u32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let t = n.trunc();
    let m = t.abs() % 4_294_967_296.0;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let mut u = m as u32; // m ∈ [0, 2^32); exact integer
    if t < 0.0 && u != 0 {
        u = u32::MAX - u + 1; // 2^32 - u
    }
    u
}

/// `Some(u)` iff the number is a non-negative integer below 2^32 (ToUint32 is
/// the identity); -0 maps to 0. The Array-length exactness check.
#[must_use]
pub fn exact_uint32(n: f64) -> Option<u32> {
    if n.is_finite() && n.trunc() == n && n >= -0.0 && n < 4_294_967_296.0 {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        Some(n as u32)
    } else {
        None
    }
}

/// ToLength (7.1.20) clamped to u64.
#[must_use]
pub fn to_length_u64(n: f64) -> u64 {
    if n.is_nan() || n <= 0.0 {
        return 0;
    }
    let t = n.trunc();
    if t >= 9_007_199_254_740_991.0 {
        9_007_199_254_740_991
    } else {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            t as u64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_to_string_vectors() {
        // The shared head vector list: every head must agree byte-for-byte.
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
        assert_eq!(to_number_str("0b101").unwrap(), 5.0);
        assert_eq!(to_number_str("0o17").unwrap(), 15.0);
        assert_eq!(to_number_str("-Infinity").unwrap(), f64::NEG_INFINITY);
        assert_eq!(to_number_str("+1.5e2").unwrap(), 150.0);
        assert_eq!(to_number_str(".5").unwrap(), 0.5);
        assert_eq!(to_number_str("5.").unwrap(), 5.0);
        assert!(to_number_str("12abc").unwrap().is_nan());
        assert!(to_number_str("-0x10").unwrap().is_nan());
        assert!(to_number_str("1e").unwrap().is_nan());
        // 16 hex digits fit exactly in u128 accumulation now.
        assert_eq!(
            to_number_str("0xffffffffffffffff").unwrap(),
            18_446_744_073_709_551_615_u128 as f64
        );
        // ...but 33 hex digits (>128 bits) refuse.
        assert!(to_number_str(&format!("0x1{}", "0".repeat(32))).is_err());
        assert_eq!(to_number_str("-0").unwrap().to_bits(), (-0.0f64).to_bits());
        assert_eq!(to_number_str("\u{a0}7\u{2028}").unwrap(), 7.0);
    }

    #[test]
    fn literal_mv_vectors() {
        assert_eq!(numeric_literal_mv("42").unwrap(), 42.0);
        assert_eq!(numeric_literal_mv("1_000_000").unwrap(), 1_000_000.0);
        assert_eq!(numeric_literal_mv("0xFF").unwrap(), 255.0);
        assert_eq!(numeric_literal_mv("0b1010").unwrap(), 10.0);
        assert_eq!(numeric_literal_mv("0o755").unwrap(), 493.0);
        assert_eq!(numeric_literal_mv("0755").unwrap(), 493.0); // legacy octal
        assert_eq!(numeric_literal_mv("08").unwrap(), 8.0); // non-octal decimal
        assert_eq!(numeric_literal_mv("089").unwrap(), 89.0);
        assert_eq!(numeric_literal_mv(".5").unwrap(), 0.5);
        assert_eq!(numeric_literal_mv("1.").unwrap(), 1.0);
        assert_eq!(numeric_literal_mv("1e3").unwrap(), 1000.0);
        assert_eq!(numeric_literal_mv("0").unwrap(), 0.0);
    }

    #[test]
    fn integer_conversions() {
        assert_eq!(to_uint32(4_294_967_296.0), 0);
        assert_eq!(to_uint32(-1.0), 4_294_967_295);
        assert_eq!(to_uint32(f64::NAN), 0);
        assert_eq!(to_uint32(1.9), 1);
        assert_eq!(to_uint32(-1.9), 4_294_967_295);
        assert_eq!(to_int32(2_147_483_648.0), -2_147_483_648);
        assert_eq!(to_int32(-2_147_483_649.0), 2_147_483_647);
        assert_eq!(to_int32(3_000_000_000.0), -1_294_967_296);
        assert_eq!(exact_uint32(0.0), Some(0));
        assert_eq!(exact_uint32(-0.0), Some(0));
        assert_eq!(exact_uint32(4_294_967_295.0), Some(4_294_967_295));
        assert_eq!(exact_uint32(4_294_967_296.0), None);
        assert_eq!(exact_uint32(1.5), None);
        assert_eq!(exact_uint32(-1.0), None);
        assert_eq!(to_length_u64(f64::INFINITY), 9_007_199_254_740_991);
        assert_eq!(to_length_u64(-5.0), 0);
        assert_eq!(to_length_u64(3.7), 3);
    }
}
