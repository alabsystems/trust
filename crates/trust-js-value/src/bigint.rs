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

use std::cmp::Ordering;

pub use num_bigint::BigInt as JsBigInt;
use num_bigint::Sign;

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
        '\t' | '\u{b}' | '\u{c}' | ' ' | '\u{a0}' | '\u{feff}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
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
    // Every branch goes through the capped parser: a source literal is the
    // most exposed materialization path in this module (one token, unbounded
    // digits), so it must not be the one place `BIT_CAP` is not enforced.
    if let Some(rest) = cleaned.strip_prefix("0x").or_else(|| cleaned.strip_prefix("0X")) {
        return parse_radix_no_sign_with_cap(rest, 16, BIT_CAP);
    }
    if let Some(rest) = cleaned.strip_prefix("0o").or_else(|| cleaned.strip_prefix("0O")) {
        return parse_radix_no_sign_with_cap(rest, 8, BIT_CAP);
    }
    if let Some(rest) = cleaned.strip_prefix("0b").or_else(|| cleaned.strip_prefix("0B")) {
        return parse_radix_no_sign_with_cap(rest, 2, BIT_CAP);
    }
    parse_radix_no_sign_with_cap(&cleaned, 10, BIT_CAP)
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
    let v = parse_radix_no_sign_with_cap(body, 10, BIT_CAP)?;
    Some(if neg { -v } else { v })
}

fn parse_radix_no_sign(digits: &str, radix: u32) -> Option<JsBigInt> {
    parse_radix_no_sign_with_cap(digits, radix, BIT_CAP)
}

/// Parse `digits` in `radix`, refusing anything whose value cannot fit in
/// `bit_cap` bits — BEFORE allocating it.
///
/// `BIT_CAP` used to guard only the two ops that blow up multiplicatively
/// (pow, shift). The PARSE side was uncapped, so a single source literal was
/// an unbounded allocation: `JsBigInt::parse_bytes` on N digits materializes
/// ~N*log2(radix) bits with nothing to stop it, and every literal in an
/// analyzed program reaches this path.
///
/// The screen is a LOWER bound on the result's bit length derived from the
/// significant digit count, so it can only reject values that are certainly
/// over the cap — the exact `value.bits()` check afterwards handles the
/// boundary. Leading zeros are stripped first so `0000...1` is not refused for
/// its length. The decimal bound uses 10^28 > 2^93 (i.e. >= 93/28 bits per
/// digit); binary/octal/hex are exact.
fn parse_radix_no_sign_with_cap(digits: &str, radix: u32, bit_cap: u64) -> Option<JsBigInt> {
    if digits.is_empty() || !digits.bytes().all(|b| (b as char).is_digit(radix)) {
        return None;
    }
    let significant = digits.trim_start_matches('0');
    if significant.is_empty() {
        return Some(JsBigInt::from(0));
    }
    let digit_count = u64::try_from(significant.len()).ok()?;
    let minimum_bits = match radix {
        2 => digit_count,
        8 => digit_count.saturating_sub(1).saturating_mul(3).saturating_add(1),
        10 => digit_count
            .saturating_sub(1)
            .saturating_mul(93)
            .checked_div(28)?
            .saturating_add(1),
        16 => digit_count.saturating_sub(1).saturating_mul(4).saturating_add(1),
        _ => return None,
    };
    if minimum_bits > bit_cap {
        return None;
    }
    let value = JsBigInt::parse_bytes(significant.as_bytes(), radix)?;
    (value.bits() <= bit_cap).then_some(value)
}

/// Refuse an OPERAND already larger than the cap.
fn ensure_operand_within_cap(value: &JsBigInt, bit_cap: u64) -> Result<(), BigErr> {
    if value.bits() > bit_cap {
        Err(BigErr::TooLarge)
    } else {
        Ok(())
    }
}

/// Refuse a RESULT larger than the cap, after materializing it.
fn checked_materialized(value: JsBigInt, bit_cap: u64) -> Result<JsBigInt, BigErr> {
    ensure_operand_within_cap(&value, bit_cap)?;
    Ok(value)
}

/// Multiply, refusing before allocating when the product certainly overflows
/// the cap: for nonzero magnitudes of m and n bits the product has at least
/// m + n - 1 bits.
fn checked_mul(x: &JsBigInt, y: &JsBigInt, bit_cap: u64) -> Result<JsBigInt, BigErr> {
    if bigint_is_zero(x) || bigint_is_zero(y) {
        return Ok(JsBigInt::from(0));
    }
    let minimum_bits = x.bits().saturating_add(y.bits()).saturating_sub(1);
    if minimum_bits > bit_cap {
        return Err(BigErr::TooLarge);
    }
    checked_materialized(x * y, bit_cap)
}

/// A BigInt::* binary operation. EVERY materializing path enforces `BIT_CAP`,
/// not just the shift/exponent blowups.
pub fn bigint_binary(op: BigOp, x: &JsBigInt, y: &JsBigInt) -> Result<JsBigInt, BigErr> {
    bigint_binary_with_cap(op, x, y, BIT_CAP)
}

fn bigint_binary_with_cap(
    op: BigOp,
    x: &JsBigInt,
    y: &JsBigInt,
    bit_cap: u64,
) -> Result<JsBigInt, BigErr> {
    ensure_operand_within_cap(x, bit_cap)?;
    ensure_operand_within_cap(y, bit_cap)?;
    match op {
        BigOp::Add => checked_materialized(x + y, bit_cap),
        BigOp::Sub => checked_materialized(x - y, bit_cap),
        BigOp::Mul => checked_mul(x, y, bit_cap),
        BigOp::Div => {
            if bigint_is_zero(y) {
                Err(BigErr::DivZero)
            } else {
                checked_materialized(x / y, bit_cap)
            }
        }
        BigOp::Rem => {
            if bigint_is_zero(y) {
                Err(BigErr::DivZero)
            } else {
                checked_materialized(x % y, bit_cap)
            }
        }
        BigOp::Pow => bigint_pow_with_cap(x, y, bit_cap),
        BigOp::And => checked_materialized(x & y, bit_cap),
        BigOp::Or => checked_materialized(x | y, bit_cap),
        BigOp::Xor => checked_materialized(x ^ y, bit_cap),
        BigOp::Shl => bigint_shift_with_cap(x, y, true, bit_cap),
        BigOp::Shr => bigint_shift_with_cap(x, y, false, bit_cap),
    }
}

/// BigInt::exponentiate — `y` must be non-negative (the caller rejects a
/// negative exponent with `RangeError`). Exponentiation by squaring, bounded
/// by an estimated result-size cap.
fn bigint_pow(base: &JsBigInt, exp: &JsBigInt) -> Result<JsBigInt, BigErr> {
    bigint_pow_with_cap(base, exp, BIT_CAP)
}

fn bigint_pow_with_cap(base: &JsBigInt, exp: &JsBigInt, bit_cap: u64) -> Result<JsBigInt, BigErr> {
    if exp.sign() == Sign::Minus {
        return Err(BigErr::NegExponent);
    }
    // `|base| <= 1` never grows, so an exponent too large to fit in a u64 is
    // still answerable for 0/1/-1 and must not be refused as TooLarge.
    let base_bits = base.bits();
    if base_bits <= 1 {
        let odd = exp.bit(0);
        return Ok(if bigint_is_zero(base) {
            if bigint_is_zero(exp) { JsBigInt::from(1) } else { JsBigInt::from(0) }
        } else if base.sign() == Sign::Minus && odd {
            JsBigInt::from(-1)
        } else {
            JsBigInt::from(1)
        });
    }
    let e = u64::try_from(exp).map_err(|_| BigErr::TooLarge)?;
    if base_bits > 0 && base_bits.saturating_mul(e) > bit_cap {
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
    bigint_shift_with_cap(x, y, left, BIT_CAP)
}

fn bigint_shift_with_cap(
    x: &JsBigInt,
    y: &JsBigInt,
    left: bool,
    bit_cap: u64,
) -> Result<JsBigInt, BigErr> {
    // Determine the effective direction and non-negative magnitude.
    let (grow, mag) = if y.sign() == Sign::Minus { (!left, -y) } else { (left, y.clone()) };
    if grow {
        // A growing shift beyond the size cap is refused (never a wrong value).
        if mag.bits() > 40 {
            return Err(BigErr::TooLarge);
        }
        let n = usize::try_from(&mag).map_err(|_| BigErr::TooLarge)?;
        if (x.bits().saturating_add(n as u64)) > bit_cap {
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
    let (mantissa, e) =
        if exp == 0 { (mant, -1074_i64) } else { (mant | (1u64 << 52), exp - 1075) };
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
    if e >= 0 { Some(m << (e as usize)) } else { Some(m >> ((-e) as usize)) }
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
        assert_eq!(
            bigint_binary(BigOp::Pow, &a, &JsBigInt::from(3)).unwrap(),
            JsBigInt::from(1000)
        );
        assert_eq!(bigint_binary(BigOp::Div, &a, &JsBigInt::from(0)), Err(BigErr::DivZero));
        assert_eq!(bigint_binary(BigOp::Pow, &a, &JsBigInt::from(-1)), Err(BigErr::NegExponent));
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

    /// #bigint-materialization-cap: `BIT_CAP` used to guard only pow and
    /// shift. Every other materializing op — and, worse, the PARSE path —
    /// allocated without a bound, so a single source literal or one `*` was
    /// an unbounded allocation.
    #[test]
    fn materialization_cap_covers_every_binary_op() {
        const TEST_CAP: u64 = 64;
        let edge = JsBigInt::from(1_u8) << 63;
        let negative_edge = -&edge;

        // Add/Sub carry past the cap.
        assert_eq!(
            bigint_binary_with_cap(BigOp::Add, &edge, &edge, TEST_CAP),
            Err(BigErr::TooLarge)
        );
        assert_eq!(
            bigint_binary_with_cap(BigOp::Sub, &edge, &negative_edge, TEST_CAP),
            Err(BigErr::TooLarge)
        );

        // Mul is refused from the m+n-1 lower bound, before allocating.
        let square_base = JsBigInt::from(1_u8) << 32;
        assert_eq!(
            bigint_binary_with_cap(BigOp::Mul, &square_base, &square_base, TEST_CAP),
            Err(BigErr::TooLarge)
        );

        // An OPERAND already over the cap is refused whatever the op — even
        // when the result would be small.
        let oversized = JsBigInt::from(1_u8) << 64;
        assert_eq!(
            bigint_binary_with_cap(BigOp::Mul, &oversized, &JsBigInt::from(0), TEST_CAP),
            Err(BigErr::TooLarge)
        );

        // Pow and shift keep their existing behaviour under the threaded cap.
        assert_eq!(
            bigint_binary_with_cap(BigOp::Pow, &JsBigInt::from(3), &JsBigInt::from(41), TEST_CAP),
            Err(BigErr::TooLarge)
        );
        // main's pow screen is the conservative `base_bits * exponent`, so the
        // accepted boundary for base 3 (2 bits) at a 64-bit cap is e = 32, not
        // the ~63 the exact bit length would allow. Asserting the conservative
        // boundary keeps this test about the CAP rather than about the
        // estimator's tightness.
        assert_eq!(
            bigint_binary_with_cap(BigOp::Pow, &JsBigInt::from(3), &JsBigInt::from(32), TEST_CAP),
            Ok(JsBigInt::from(1_853_020_188_851_841_u64))
        );
        assert_eq!(
            bigint_binary_with_cap(BigOp::Shl, &JsBigInt::from(1), &JsBigInt::from(65), TEST_CAP),
            Err(BigErr::TooLarge)
        );

        // Under the cap everything still computes.
        assert_eq!(
            bigint_binary_with_cap(BigOp::Mul, &JsBigInt::from(6), &JsBigInt::from(7), TEST_CAP),
            Ok(JsBigInt::from(42))
        );
    }

    /// `|base| <= 1` never grows, so an exponent too large for a u64 must
    /// still answer rather than refuse.
    #[test]
    fn unit_bases_answer_for_exponents_beyond_u64() {
        let huge_odd = (JsBigInt::from(1_u8) << 64) + 1;
        assert_eq!(
            bigint_binary_with_cap(BigOp::Pow, &JsBigInt::from(-1), &huge_odd, 128),
            Ok(JsBigInt::from(-1))
        );
        assert_eq!(
            bigint_binary_with_cap(BigOp::Pow, &JsBigInt::from(1), &huge_odd, 128),
            Ok(JsBigInt::from(1))
        );
    }

    /// The parse path is the most exposed materialization in this module: one
    /// token, unbounded digits. It must refuse before allocating.
    #[test]
    fn parsers_refuse_values_beyond_the_materialization_cap() {
        // 2^24 bits is the cap; a binary literal of 2^24 + 1 digits is over it.
        let over = "1".repeat((BIT_CAP + 1) as usize);
        assert_eq!(parse_bigint_literal(&format!("0b{over}n")), None);
        assert_eq!(parse_radix_no_sign_with_cap(&over, 2, BIT_CAP), None);

        // Leading zeros are not significant and must not cause a refusal.
        let padded = format!("{}{}", "0".repeat(4096), "1");
        assert_eq!(parse_radix_no_sign_with_cap(&padded, 2, BIT_CAP), Some(JsBigInt::from(1)));

        // All-zero input is zero, not an error.
        assert_eq!(parse_radix_no_sign_with_cap("0000", 10, BIT_CAP), Some(JsBigInt::from(0)));

        // Ordinary literals are unaffected, in every radix.
        assert_eq!(parse_bigint_literal("255n"), Some(JsBigInt::from(255)));
        assert_eq!(parse_bigint_literal("0xffn"), Some(JsBigInt::from(255)));
        assert_eq!(parse_bigint_literal("0o377n"), Some(JsBigInt::from(255)));
        assert_eq!(parse_bigint_literal("0b1111_1111n"), Some(JsBigInt::from(255)));

        // A small cap rejects a value that the default cap accepts.
        assert_eq!(parse_radix_no_sign_with_cap("1000000", 10, 8), None);
        assert_eq!(parse_radix_no_sign_with_cap("200", 10, 8), Some(JsBigInt::from(200)));
    }
}
