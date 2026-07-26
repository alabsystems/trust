// The BigInt numeric type (§6.1.6.2), written from ECMA-262 over an
// arbitrary-precision signed integer (`num_bigint::BigInt`, an existing
// workspace dependency — not new supply-chain surface). This module carries
// the pure value-level operations: NumericLiteral / StringToBigInt parsing,
// the BigInt::* abstract operations (add/sub/mul/div/rem/exponentiate,
// bitwise & | ^, shifts, unaryMinus, bitwiseNOT), Number/BigInt mixed
// comparison (exact real ordering), BigInt::toString(radix), and
// BigInt.asIntN / asUintN. Every partial (division by zero, negative
// exponent, an astronomically large intermediate) is surfaced as a typed
// error so the interpreter can throw the exact JS exception or refuse — never
// panic (the TOTALITY bar).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

pub use num_bigint::BigInt as JsBigInt;
use num_bigint::Sign;
use std::cmp::Ordering;

/// A BigInt binary operator (the arithmetic/bitwise/shift dispatch key).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BigOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

/// A BigInt operation that cannot produce a value: the interpreter maps
/// `DivZero`/`NegExponent` to the exact `RangeError` and `TooLarge` to a
/// sound refusal (an intermediate beyond the model's materialization cap).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BigErr {
    DivZero,
    NegExponent,
    TooLarge,
}

/// Cap on shift distances / exponent-driven bit growth (~16M bits ≈ 2 MiB per
/// value): well above every test262 fixture, well below an OOM.
const BIT_CAP: u64 = 1 << 24;

/// Cap on `bits` for asIntN/asUintN modulus materialization (~1M bits).
const AS_N_CAP: u64 = 1 << 20;

#[must_use]
pub fn bigint_is_zero(b: &JsBigInt) -> bool {
    b.sign() == Sign::NoSign
}

#[must_use]
pub fn bigint_from_bool(v: bool) -> JsBigInt {
    JsBigInt::from(u8::from(v))
}

#[must_use]
pub fn bigint_from_i64(v: i64) -> JsBigInt {
    JsBigInt::from(v)
}

#[must_use]
pub fn bigint_from_u64(v: u64) -> JsBigInt {
    JsBigInt::from(v)
}

/// BigInt::unaryMinus.
#[must_use]
pub fn bigint_neg(b: &JsBigInt) -> JsBigInt {
    -b
}

/// BigInt::bitwiseNOT — `-(x) - 1`.
#[must_use]
pub fn bigint_not(b: &JsBigInt) -> JsBigInt {
    -b - 1
}

/// The decimal (radix-10) string — the projection repr and default toString.
#[must_use]
pub fn bigint_to_decimal(b: &JsBigInt) -> String {
    b.to_string()
}

/// BigInt::toString(radix) — lowercase digits, `-` sign prefix; matches
/// `BigInt.prototype.toString`.
#[must_use]
pub fn bigint_to_radix(b: &JsBigInt, radix: u32) -> String {
    b.to_str_radix(radix)
}

/// JS whitespace + line terminators trimmed by StringToBigInt (identical to
/// the ToNumber(string) set).
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

/// The mathematical value of a NumericLiteral with the BigInt suffix, as lexed
/// by trust-js-parse (raw text incl. the trailing `n`, any `0x`/`0o`/`0b`
/// prefix, and `_` separators). Always non-negative (a source negative is the
/// unary-minus operator). `None` iff the raw text is not a well-formed literal
/// (a parser invariant violation — the interpreter refuses rather than guess).
#[must_use]
pub fn parse_bigint_literal(raw: &str) -> Option<JsBigInt> {
    let body = raw.strip_suffix('n').unwrap_or(raw);
    let cleaned: String = body.chars().filter(|c| *c != '_').collect();
    if let Some(rest) = cleaned.strip_prefix("0x").or_else(|| cleaned.strip_prefix("0X")) {
        return JsBigInt::parse_bytes(rest.as_bytes(), 16);
    }
    if let Some(rest) = cleaned.strip_prefix("0o").or_else(|| cleaned.strip_prefix("0O")) {
        return JsBigInt::parse_bytes(rest.as_bytes(), 8);
    }
    if let Some(rest) = cleaned.strip_prefix("0b").or_else(|| cleaned.strip_prefix("0B")) {
        return JsBigInt::parse_bytes(rest.as_bytes(), 2);
    }
    JsBigInt::parse_bytes(cleaned.as_bytes(), 10)
}

/// StringToBigInt (7.1.14) over WTF-16 code units. Empty / whitespace-only →
/// `0n`. `None` marks an invalid string (the caller throws `SyntaxError`).
/// Numeric separators are NOT permitted here (unlike source literals).
#[must_use]
pub fn string_to_bigint(units: &[u16]) -> Option<JsBigInt> {
    let s = String::from_utf16_lossy(units);
    let t = s.trim_matches(is_js_ws);
    if t.is_empty() {
        return Some(JsBigInt::from(0));
    }
    // Non-decimal prefixes admit no sign.
    if let Some(rest) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return parse_radix_no_sign(rest, 16);
    }
    if let Some(rest) = t.strip_prefix("0o").or_else(|| t.strip_prefix("0O")) {
        return parse_radix_no_sign(rest, 8);
    }
    if let Some(rest) = t.strip_prefix("0b").or_else(|| t.strip_prefix("0B")) {
        return parse_radix_no_sign(rest, 2);
    }
    let (neg, body) = match t.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, t.strip_prefix('+').unwrap_or(t)),
    };
    if body.is_empty() || !body.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let v = JsBigInt::parse_bytes(body.as_bytes(), 10)?;
    Some(if neg { -v } else { v })
}

fn parse_radix_no_sign(digits: &str, radix: u32) -> Option<JsBigInt> {
    if digits.is_empty() || !digits.bytes().all(|b| (b as char).is_digit(radix)) {
        return None;
    }
    JsBigInt::parse_bytes(digits.as_bytes(), radix)
}

/// A BigInt::* binary operation. `TooLarge` guards shift/exponent blowups.
pub fn bigint_binary(op: BigOp, x: &JsBigInt, y: &JsBigInt) -> Result<JsBigInt, BigErr> {
    match op {
        BigOp::Add => Ok(x + y),
        BigOp::Sub => Ok(x - y),
        BigOp::Mul => Ok(x * y),
        BigOp::Div => {
            if bigint_is_zero(y) {
                Err(BigErr::DivZero)
            } else {
                Ok(x / y)
            }
        }
        BigOp::Rem => {
            if bigint_is_zero(y) {
                Err(BigErr::DivZero)
            } else {
                Ok(x % y)
            }
        }
        BigOp::Pow => bigint_pow(x, y),
        BigOp::And => Ok(x & y),
        BigOp::Or => Ok(x | y),
        BigOp::Xor => Ok(x ^ y),
        BigOp::Shl => bigint_shift(x, y, true),
        BigOp::Shr => bigint_shift(x, y, false),
    }
}

/// BigInt::exponentiate — `y` must be non-negative (the caller rejects a
/// negative exponent with `RangeError`). Exponentiation by squaring, bounded
/// by an estimated result-size cap.
fn bigint_pow(base: &JsBigInt, exp: &JsBigInt) -> Result<JsBigInt, BigErr> {
    if exp.sign() == Sign::Minus {
        return Err(BigErr::NegExponent);
    }
    let e = u64::try_from(exp).map_err(|_| BigErr::TooLarge)?;
    let base_bits = base.bits();
    if base_bits > 0 && base_bits.saturating_mul(e) > BIT_CAP {
        return Err(BigErr::TooLarge);
    }
    let mut result = JsBigInt::from(1);
    let mut b = base.clone();
    let mut n = e;
    while n > 0 {
        if n & 1 == 1 {
            result = &result * &b;
        }
        n >>= 1;
        if n > 0 {
            b = &b * &b;
        }
    }
    Ok(result)
}

/// BigInt::leftShift / signedRightShift. A negative distance flips direction;
/// the right shift is arithmetic (floor division by 2^n).
fn bigint_shift(x: &JsBigInt, y: &JsBigInt, left: bool) -> Result<JsBigInt, BigErr> {
    // Determine the effective direction and non-negative magnitude.
    let (grow, mag) = if y.sign() == Sign::Minus {
        (!left, -y)
    } else {
        (left, y.clone())
    };
    if grow {
        // A growing shift beyond the size cap is refused (never a wrong value).
        if mag.bits() > 40 {
            return Err(BigErr::TooLarge);
        }
        let n = usize::try_from(&mag).map_err(|_| BigErr::TooLarge)?;
        if (x.bits().saturating_add(n as u64)) > BIT_CAP {
            return Err(BigErr::TooLarge);
        }
        Ok(x.clone() << n)
    } else {
        // Shrinking shift: a distance beyond the operand's bit width collapses
        // to 0 (x ≥ 0) or -1 (x < 0); clamp so a huge distance never overflows.
        let n = match usize::try_from(&mag) {
            Ok(n) => n,
            Err(_) => usize::try_from(x.bits().saturating_add(2)).unwrap_or(usize::MAX),
        };
        Ok(x.clone() >> n)
    }
}

/// SameValue for BigInt (`===` / SameValueZero over BigInt).
#[must_use]
pub fn bigint_cmp(x: &JsBigInt, y: &JsBigInt) -> Ordering {
    x.cmp(y)
}

/// Decompose a finite f64 into `(m, e)` with `value == m * 2^e` exactly.
fn f64_to_int_scale(y: f64) -> (JsBigInt, i32) {
    let bits = y.to_bits();
    let sign = if bits >> 63 == 1 { -1i8 } else { 1i8 };
    let exp = ((bits >> 52) & 0x7ff) as i64;
    let mant = bits & 0x000f_ffff_ffff_ffff;
    let (mantissa, e) = if exp == 0 {
        (mant, -1074_i64)
    } else {
        (mant | (1u64 << 52), exp - 1075)
    };
    let m = JsBigInt::from(mantissa) * sign;
    #[allow(clippy::cast_possible_truncation)]
    (m, e as i32)
}

/// NumberToBigInt's core (7.1.13): the exact BigInt of an integral Number.
/// `None` iff `y` is not an integer (non-finite or has a fractional part) —
/// the caller throws `RangeError`.
#[must_use]
pub fn f64_to_bigint_exact(y: f64) -> Option<JsBigInt> {
    if !y.is_finite() || y.trunc() != y {
        return None;
    }
    if y == 0.0 {
        return Some(JsBigInt::from(0));
    }
    let (m, e) = f64_to_int_scale(y);
    // y = m * 2^e is an integer, so e ≥ 0 or m is divisible by 2^(-e).
    #[allow(clippy::cast_sign_loss)]
    if e >= 0 {
        Some(m << (e as usize))
    } else {
        Some(m >> ((-e) as usize))
    }
}

/// Exact ordering between a BigInt and a Number (IsLessThan's mixed rule).
/// `None` iff `y` is NaN.
#[must_use]
pub fn bigint_cmp_f64(x: &JsBigInt, y: f64) -> Option<Ordering> {
    if y.is_nan() {
        return None;
    }
    if y == f64::INFINITY {
        return Some(Ordering::Less);
    }
    if y == f64::NEG_INFINITY {
        return Some(Ordering::Greater);
    }
    let (m, e) = f64_to_int_scale(y);
    // sign(x - m*2^e): scale both sides into exact integers.
    let ord = if e >= 0 {
        #[allow(clippy::cast_sign_loss)]
        let scaled = &m << (e as usize);
        x.cmp(&scaled)
    } else {
        #[allow(clippy::cast_sign_loss)]
        let scaled_x = x << ((-e) as usize);
        scaled_x.cmp(&m)
    };
    Some(ord)
}

/// BigInt == Number (loose equality's mixed rule): equal iff exact real values
/// coincide (never for a non-finite Number).
#[must_use]
pub fn bigint_eq_f64(x: &JsBigInt, y: f64) -> bool {
    if !y.is_finite() {
        return false;
    }
    bigint_cmp_f64(x, y) == Some(Ordering::Equal)
}

/// BigInt.asUintN(bits, x) — `x mod 2^bits`, non-negative. `None` iff `bits`
/// is too large to materialize (a sound refusal for the pathological case).
#[must_use]
pub fn as_uint_n(bits: u64, x: &JsBigInt) -> Option<JsBigInt> {
    if bits == 0 {
        return Some(JsBigInt::from(0));
    }
    if bits > AS_N_CAP {
        // Only the no-wrap case (a non-negative value already inside the range)
        // is answerable without building the modulus.
        if x.sign() != Sign::Minus && x.bits() <= bits {
            return Some(x.clone());
        }
        return None;
    }
    #[allow(clippy::cast_possible_truncation)]
    let modulus = JsBigInt::from(1) << (bits as usize);
    let mut r = x % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    Some(r)
}

/// BigInt.asIntN(bits, x) — the `bits`-bit two's-complement wrap.
#[must_use]
pub fn as_int_n(bits: u64, x: &JsBigInt) -> Option<JsBigInt> {
    if bits == 0 {
        return Some(JsBigInt::from(0));
    }
    if bits > AS_N_CAP {
        // Fits in the signed range iff the magnitude has fewer than `bits` bits.
        if x.bits() < bits {
            return Some(x.clone());
        }
        return None;
    }
    let u = as_uint_n(bits, x)?;
    #[allow(clippy::cast_possible_truncation)]
    let bits_u = bits as usize;
    let half = JsBigInt::from(1) << (bits_u - 1);
    if u >= half {
        let modulus = JsBigInt::from(1) << bits_u;
        Some(u - modulus)
    } else {
        Some(u)
    }
}

/// The Number closest to a BigInt (the `Number(bigint)` conversion, 21.1.1.1
/// step 1.b — 𝔽(ℝ(prim))). Correctly rounded via the decimal round-trip;
/// magnitudes beyond the f64 range give ±Infinity.
#[must_use]
pub fn bigint_to_f64(b: &JsBigInt) -> f64 {
    b.to_string().parse::<f64>().unwrap_or(f64::INFINITY)
}

/// The signed 64-bit wrap of a BigInt (BigInt64Array element / DataView
/// setBigInt64 store).
#[must_use]
pub fn bigint_to_i64_wrap(x: &JsBigInt) -> i64 {
    let w = as_int_n(64, x).unwrap_or_else(|| JsBigInt::from(0));
    i64::try_from(&w).unwrap_or(0)
}

/// The unsigned 64-bit wrap of a BigInt (BigUint64Array element / DataView
/// setBigUint64 store).
#[must_use]
pub fn bigint_to_u64_wrap(x: &JsBigInt) -> u64 {
    let w = as_uint_n(64, x).unwrap_or_else(|| JsBigInt::from(0));
    u64::try_from(&w).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_parsing() {
        assert_eq!(parse_bigint_literal("123n").unwrap(), JsBigInt::from(123));
        assert_eq!(parse_bigint_literal("0x1Fn").unwrap(), JsBigInt::from(31));
        assert_eq!(parse_bigint_literal("0o17n").unwrap(), JsBigInt::from(15));
        assert_eq!(parse_bigint_literal("0b101n").unwrap(), JsBigInt::from(5));
        assert_eq!(parse_bigint_literal("1_000n").unwrap(), JsBigInt::from(1000));
        assert_eq!(parse_bigint_literal("0n").unwrap(), JsBigInt::from(0));
    }

    #[test]
    fn string_conversion() {
        let u = |s: &str| s.encode_utf16().collect::<Vec<u16>>();
        assert_eq!(string_to_bigint(&u("")).unwrap(), JsBigInt::from(0));
        assert_eq!(string_to_bigint(&u("   ")).unwrap(), JsBigInt::from(0));
        assert_eq!(string_to_bigint(&u(" 42 ")).unwrap(), JsBigInt::from(42));
        assert_eq!(string_to_bigint(&u("-7")).unwrap(), JsBigInt::from(-7));
        assert_eq!(string_to_bigint(&u("0x10")).unwrap(), JsBigInt::from(16));
        assert_eq!(string_to_bigint(&u("010")).unwrap(), JsBigInt::from(10));
        assert!(string_to_bigint(&u("1.5")).is_none());
        assert!(string_to_bigint(&u("0x")).is_none());
        assert!(string_to_bigint(&u("-0x10")).is_none());
        assert!(string_to_bigint(&u("1e5")).is_none());
        assert!(string_to_bigint(&u("abc")).is_none());
    }

    #[test]
    fn arithmetic_and_errors() {
        let a = JsBigInt::from(10);
        let b = JsBigInt::from(3);
        assert_eq!(bigint_binary(BigOp::Add, &a, &b).unwrap(), JsBigInt::from(13));
        assert_eq!(bigint_binary(BigOp::Div, &a, &b).unwrap(), JsBigInt::from(3));
        assert_eq!(bigint_binary(BigOp::Rem, &a, &b).unwrap(), JsBigInt::from(1));
        // Truncated division / sign-of-dividend remainder (matches JS).
        let na = JsBigInt::from(-10);
        assert_eq!(bigint_binary(BigOp::Div, &na, &b).unwrap(), JsBigInt::from(-3));
        assert_eq!(bigint_binary(BigOp::Rem, &na, &b).unwrap(), JsBigInt::from(-1));
        assert_eq!(bigint_binary(BigOp::Pow, &a, &JsBigInt::from(3)).unwrap(), JsBigInt::from(1000));
        assert_eq!(
            bigint_binary(BigOp::Div, &a, &JsBigInt::from(0)),
            Err(BigErr::DivZero)
        );
        assert_eq!(
            bigint_binary(BigOp::Pow, &a, &JsBigInt::from(-1)),
            Err(BigErr::NegExponent)
        );
    }

    #[test]
    fn shifts_and_bitwise() {
        let a = JsBigInt::from(1);
        assert_eq!(bigint_binary(BigOp::Shl, &a, &JsBigInt::from(4)).unwrap(), JsBigInt::from(16));
        let b = JsBigInt::from(-5);
        // -5 >> 1 = -3 (arithmetic / floor).
        assert_eq!(bigint_binary(BigOp::Shr, &b, &JsBigInt::from(1)).unwrap(), JsBigInt::from(-3));
        // 5 >> 1000 = 0.
        assert_eq!(
            bigint_binary(BigOp::Shr, &JsBigInt::from(5), &JsBigInt::from(1000)).unwrap(),
            JsBigInt::from(0)
        );
        // -1 & 5 = 5 (two's complement).
        assert_eq!(
            bigint_binary(BigOp::And, &JsBigInt::from(-1), &JsBigInt::from(5)).unwrap(),
            JsBigInt::from(5)
        );
        assert_eq!(bigint_not(&JsBigInt::from(5)), JsBigInt::from(-6));
    }

    #[test]
    fn as_int_uint_n() {
        // asUintN(8, 256) = 0; asUintN(8, -1) = 255.
        assert_eq!(as_uint_n(8, &JsBigInt::from(256)).unwrap(), JsBigInt::from(0));
        assert_eq!(as_uint_n(8, &JsBigInt::from(-1)).unwrap(), JsBigInt::from(255));
        // asIntN(8, 255) = -1; asIntN(8, 128) = -128.
        assert_eq!(as_int_n(8, &JsBigInt::from(255)).unwrap(), JsBigInt::from(-1));
        assert_eq!(as_int_n(8, &JsBigInt::from(128)).unwrap(), JsBigInt::from(-128));
        assert_eq!(as_int_n(0, &JsBigInt::from(5)).unwrap(), JsBigInt::from(0));
        assert_eq!(bigint_to_i64_wrap(&JsBigInt::from(-1)), -1);
        assert_eq!(bigint_to_u64_wrap(&JsBigInt::from(-1)), u64::MAX);
    }

    #[test]
    fn mixed_comparison() {
        assert_eq!(bigint_cmp_f64(&JsBigInt::from(2), 2.5), Some(Ordering::Less));
        assert_eq!(bigint_cmp_f64(&JsBigInt::from(3), 2.5), Some(Ordering::Greater));
        assert_eq!(bigint_cmp_f64(&JsBigInt::from(2), 2.0), Some(Ordering::Equal));
        assert_eq!(bigint_cmp_f64(&JsBigInt::from(0), f64::NAN), None);
        assert!(bigint_eq_f64(&JsBigInt::from(2), 2.0));
        assert!(!bigint_eq_f64(&JsBigInt::from(2), 2.5));
        assert!(!bigint_eq_f64(&JsBigInt::from(0), f64::INFINITY));
    }
}
