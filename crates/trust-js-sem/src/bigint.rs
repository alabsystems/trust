// The BigInt primitive (6.1.6.2): arbitrary-precision integers and the exact
// ECMA-262 operations over them. The numeric backend is `num-bigint` (an
// existing vetted workspace dependency); every operation here is written from
// the spec and adversarially checked against a real engine's BigInt.
//
// Two's-complement bitwise/shift semantics, truncating division, sign-of-
// dividend remainder, and radix `toString` are all exactly num-bigint's, which
// was verified digit-for-digit against Node 24 before this module was built on
// it. Anything that would allocate an unboundedly large intermediate (huge
// exponent/shift/product) is a sound refusal (`BigErr::Refuse`) rather than a
// denial-of-service or a guess; division/remainder by zero and a negative
// exponent are the spec's RangeError, never a panic.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::value::Units;
use num_bigint::{BigInt, Sign};
use std::cmp::Ordering;

/// The most bits any modeled BigInt magnitude may occupy. Operations whose
/// result would exceed this refuse (a sound `NoCoverage`) rather than risk
/// exhausting memory: ~1,048,576 bits is ~315,000 decimal digits, far beyond
/// anything a conformance test needs, yet a hard bound on allocation.
pub const MAX_BITS: u64 = 1 << 20;

/// The failure modes of a BigInt operation, mapped by the interpreter to a
/// thrown RangeError / TypeError or a sound refusal.
#[derive(Debug, Clone)]
pub enum BigErr {
    /// Division/remainder by zero, a negative exponent, or a negative
    /// asIntN/asUintN bit count → RangeError (6.1.6.2.x).
    Range,
    /// BigInt unsigned right shift, or a mixed-type operation the caller
    /// detected → TypeError.
    Type,
    /// Out of the modeled slice (an intermediate that would exceed `MAX_BITS`).
    Refuse(String),
}

#[must_use]
pub fn is_zero(a: &BigInt) -> bool {
    a.sign() == Sign::NoSign
}

#[must_use]
pub fn zero() -> BigInt {
    BigInt::from(0)
}

// -- arithmetic --------------------------------------------------------------

fn guard_bits(bits: u64, what: &str) -> Result<(), BigErr> {
    if bits > MAX_BITS {
        Err(BigErr::Refuse(format!(
            "BigInt {what} result exceeds {MAX_BITS}-bit model cap"
        )))
    } else {
        Ok(())
    }
}

pub fn add(a: &BigInt, b: &BigInt) -> Result<BigInt, BigErr> {
    guard_bits(a.bits().max(b.bits()) + 1, "add")?;
    Ok(a + b)
}

pub fn sub(a: &BigInt, b: &BigInt) -> Result<BigInt, BigErr> {
    guard_bits(a.bits().max(b.bits()) + 1, "subtract")?;
    Ok(a - b)
}

pub fn mul(a: &BigInt, b: &BigInt) -> Result<BigInt, BigErr> {
    guard_bits(a.bits() + b.bits() + 1, "multiply")?;
    Ok(a * b)
}

/// BigInt::divide (6.1.6.2.4): truncation toward zero; `/ 0n` → RangeError.
pub fn div(a: &BigInt, b: &BigInt) -> Result<BigInt, BigErr> {
    if is_zero(b) {
        return Err(BigErr::Range);
    }
    Ok(a / b)
}

/// BigInt::remainder (6.1.6.2.5): the sign follows the dividend; `% 0n` →
/// RangeError.
pub fn rem(a: &BigInt, b: &BigInt) -> Result<BigInt, BigErr> {
    if is_zero(b) {
        return Err(BigErr::Range);
    }
    Ok(a % b)
}

/// BigInt::exponentiate (6.1.6.2.3): a negative exponent is a RangeError; an
/// astronomically large result is a sound refusal.
pub fn pow(a: &BigInt, e: &BigInt) -> Result<BigInt, BigErr> {
    match e.sign() {
        Sign::Minus => Err(BigErr::Range),
        Sign::NoSign => Ok(BigInt::from(1)),
        Sign::Plus => {
            // Base special cases keep the size bound meaningful.
            let abits = a.bits();
            if abits == 0 {
                return Ok(zero()); // 0n ** positive = 0n
            }
            if abits == 1 {
                // a is ±1.
                if a.sign() == Sign::Minus {
                    // (-1) ** e: odd exponent → -1, even → 1.
                    let odd = e.bit(0);
                    return Ok(BigInt::from(if odd { -1 } else { 1 }));
                }
                return Ok(BigInt::from(1));
            }
            let Some(n) = mag_to_usize(e) else {
                return Err(BigErr::Refuse("BigInt exponent too large".to_string()));
            };
            // |a|^n has at most abits*n bits.
            guard_bits((abits).saturating_mul(n as u64), "exponentiate")?;
            let exp = u32::try_from(n)
                .map_err(|_| BigErr::Refuse("BigInt exponent too large".to_string()))?;
            Ok(a.pow(exp))
        }
    }
}

#[must_use]
pub fn neg(a: &BigInt) -> BigInt {
    -a
}

/// BigInt::bitwiseNOT (6.1.6.2.2): ~a = -(a + 1).
#[must_use]
pub fn bitnot(a: &BigInt) -> BigInt {
    !a
}

#[must_use]
pub fn bitand(a: &BigInt, b: &BigInt) -> BigInt {
    a & b
}

#[must_use]
pub fn bitor(a: &BigInt, b: &BigInt) -> BigInt {
    a | b
}

#[must_use]
pub fn bitxor(a: &BigInt, b: &BigInt) -> BigInt {
    a ^ b
}

/// The shift magnitude as a `usize`, or None if it does not fit (i.e. it is
/// astronomically large).
fn mag_to_usize(s: &BigInt) -> Option<usize> {
    let digits = s.magnitude().to_u64_digits();
    match digits.len() {
        0 => Some(0),
        1 => usize::try_from(digits[0]).ok(),
        _ => None,
    }
}

/// BigInt::leftShift (6.1.6.2.9). A negative shift count shifts right.
pub fn shl(a: &BigInt, s: &BigInt) -> Result<BigInt, BigErr> {
    match s.sign() {
        Sign::NoSign => Ok(a.clone()),
        Sign::Plus => {
            if is_zero(a) {
                return Ok(zero());
            }
            let Some(n) = mag_to_usize(s) else {
                return Err(BigErr::Refuse("BigInt left-shift count too large".to_string()));
            };
            guard_bits(a.bits().saturating_add(n as u64), "left-shift")?;
            Ok(a << n)
        }
        Sign::Minus => shr_by_pos(a, s),
    }
}

/// BigInt::signedRightShift (6.1.6.2.10). A negative shift count shifts left.
pub fn shr(a: &BigInt, s: &BigInt) -> Result<BigInt, BigErr> {
    match s.sign() {
        Sign::NoSign => Ok(a.clone()),
        Sign::Plus => shr_by_pos(a, s),
        Sign::Minus => {
            // Shift left by |s|.
            if is_zero(a) {
                return Ok(zero());
            }
            let Some(n) = mag_to_usize(s) else {
                return Err(BigErr::Refuse("BigInt right-shift count too large".to_string()));
            };
            guard_bits(a.bits().saturating_add(n as u64), "left-shift")?;
            Ok(a << n)
        }
    }
}

/// Arithmetic right shift by |s| (s treated as a positive magnitude).
fn shr_by_pos(a: &BigInt, s: &BigInt) -> Result<BigInt, BigErr> {
    if is_zero(a) {
        return Ok(zero());
    }
    match mag_to_usize(s) {
        Some(n) => {
            // Beyond the magnitude, an arithmetic shift saturates to 0 (a ≥ 0)
            // or -1 (a < 0).
            if (n as u64) > a.bits() {
                return Ok(if a.sign() == Sign::Minus {
                    BigInt::from(-1)
                } else {
                    zero()
                });
            }
            Ok(a >> n)
        }
        None => Ok(if a.sign() == Sign::Minus {
            BigInt::from(-1)
        } else {
            zero()
        }),
    }
}

/// BigInt::unsignedRightShift (6.1.6.2.11): always a TypeError.
#[must_use]
pub fn ushr_type_error() -> BigErr {
    BigErr::Type
}

// -- BigInt.asIntN / asUintN (20.2.2.1 / .2) --------------------------------

/// BigInt.asUintN(bits, x): x modulo 2^bits, in [0, 2^bits).
#[must_use]
pub fn as_uint_n(bits: u64, x: &BigInt) -> BigInt {
    if bits == 0 {
        return zero();
    }
    let modulus = BigInt::from(1) << usize::try_from(bits).unwrap_or(usize::MAX);
    let mut r = x % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    r
}

/// BigInt.asIntN(bits, x): x modulo 2^bits, interpreted as a signed value in
/// [-2^(bits-1), 2^(bits-1)).
#[must_use]
pub fn as_int_n(bits: u64, x: &BigInt) -> BigInt {
    if bits == 0 {
        return zero();
    }
    let bs = usize::try_from(bits).unwrap_or(usize::MAX);
    let modulus = BigInt::from(1) << bs;
    let mut r = x % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    let half = BigInt::from(1) << (bs - 1);
    if r >= half {
        r -= &modulus;
    }
    r
}

/// The low 64 bits of x as a `u64` (x modulo 2^64) — the stored byte pattern
/// of a BigInt64/BigUint64 typed-array element (identical for both; only the
/// interpretation on read differs).
#[must_use]
pub fn to_u64_wrapping(x: &BigInt) -> u64 {
    as_uint_n(64, x)
        .magnitude()
        .to_u64_digits()
        .first()
        .copied()
        .unwrap_or(0)
}

// -- ToString / radix --------------------------------------------------------

/// BigInt::toString(x, radix) (6.1.6.2.23). `radix` must be in 2..=36 (the
/// caller validates and raises RangeError otherwise). Lowercase digits, a
/// leading `-` for negatives — exactly the ECMA-262 form.
#[must_use]
pub fn to_string_radix(a: &BigInt, radix: u32) -> String {
    a.to_str_radix(radix)
}

/// ToString(BigInt) for the general coercion path (7.1.17): decimal.
#[must_use]
pub fn to_units_decimal(a: &BigInt) -> Units {
    crate::value::units_from_str(&a.to_str_radix(10))
}

// -- Number(bigint) : round-half-to-even to the nearest f64 -----------------

/// 𝔽(ℝ(x)) for a BigInt x (used by `Number(bigint)`): the nearest f64,
/// ties to even, ±Infinity on overflow. Exact, implemented directly on the
/// magnitude bits (no `num-traits`).
#[must_use]
pub fn to_f64(a: &BigInt) -> f64 {
    let sign = a.sign();
    if sign == Sign::NoSign {
        return 0.0;
    }
    let neg = sign == Sign::Minus;
    let mag = a.magnitude();
    let nbits = mag.bits(); // ≥ 1
    if nbits <= 53 {
        // Fits exactly in an f64.
        let digits = mag.to_u64_digits();
        let v = digits.first().copied().unwrap_or(0);
        #[allow(clippy::cast_precision_loss)] // v < 2^53: exact
        let f = v as f64;
        return if neg { -f } else { f };
    }
    let k = nbits - 1; // index of the top set bit
    let drop = k - 52; // low bits to discard
    let drop_us = usize::try_from(drop).unwrap_or(usize::MAX);
    // Top 53 bits form the candidate mantissa in [2^52, 2^53).
    let top = mag >> drop_us;
    let mut mantissa = top.to_u64_digits().first().copied().unwrap_or(0);
    // Round to nearest, ties to even, from the discarded low `drop` bits.
    let low = mag - (&top << drop_us);
    let half = num_bigint::BigUint::from(1u8) << (drop_us - 1);
    let round_up = match low.cmp(&half) {
        Ordering::Greater => true,
        Ordering::Less => false,
        Ordering::Equal => (mantissa & 1) == 1, // tie → to even
    };
    let mut exp = k; // unbiased exponent of the leading bit
    if round_up {
        mantissa += 1;
        if mantissa == (1u64 << 53) {
            // Carry out of the mantissa: renormalize.
            mantissa >>= 1;
            exp += 1;
        }
    }
    let exp_field = exp + 1023;
    if exp_field >= 2047 {
        return if neg { f64::NEG_INFINITY } else { f64::INFINITY };
    }
    let frac = mantissa & ((1u64 << 52) - 1);
    let bits = (u64::from(neg) << 63) | (exp_field << 52) | frac;
    f64::from_bits(bits)
}

/// ToBigInt(number) (7.1.13): the number must be an integral f64, else a
/// RangeError; ±Infinity / NaN are RangeErrors.
pub fn from_integral_f64(n: f64) -> Result<BigInt, BigErr> {
    if !n.is_finite() || n.trunc() != n {
        return Err(BigErr::Range);
    }
    Ok(from_integral_f64_unchecked(n))
}

/// The BigInt equal to an already-known integral f64.
fn from_integral_f64_unchecked(n: f64) -> BigInt {
    if n == 0.0 {
        return zero();
    }
    let (mant, e) = decompose_f64(n);
    if e >= 0 {
        mant << usize::try_from(e).unwrap_or(0)
    } else {
        // n integral ⇒ the low -e bits of mant are zero, so this is exact.
        mant >> usize::try_from(-e).unwrap_or(0)
    }
}

/// Decompose a finite f64 into `(m, e)` with `value = m * 2^e` exactly; `m`
/// is a signed BigInt, `e` an integer. Zero → (0, 0).
fn decompose_f64(b: f64) -> (BigInt, i64) {
    let bits = b.to_bits();
    let neg = (bits >> 63) == 1;
    let raw_exp = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & 0x000f_ffff_ffff_ffff;
    let (mant, e) = if raw_exp == 0 {
        (frac, -1074) // subnormal (or zero)
    } else {
        (frac | 0x0010_0000_0000_0000, raw_exp - 1075)
    };
    let mut m = BigInt::from(mant);
    if neg {
        m = -m;
    }
    (m, e)
}

// -- exact BigInt vs Number comparison (7.2.13 / 7.2.15) ---------------------

/// Compare ℝ(a) (BigInt) with ℝ(b) (Number). `None` iff b is NaN. Exact.
#[must_use]
pub fn cmp_f64(a: &BigInt, b: f64) -> Option<Ordering> {
    if b.is_nan() {
        return None;
    }
    if b == f64::INFINITY {
        return Some(Ordering::Less); // a < +∞
    }
    if b == f64::NEG_INFINITY {
        return Some(Ordering::Greater); // a > -∞
    }
    let (m, e) = decompose_f64(b);
    // Compare a vs m*2^e by clearing the power of two into a common integer.
    let (lhs, rhs) = if e >= 0 {
        (a.clone(), m << usize::try_from(e).unwrap_or(0))
    } else {
        (a << usize::try_from(-e).unwrap_or(0), m)
    };
    Some(lhs.cmp(&rhs))
}

/// ℝ(a) = ℝ(b) exactly (BigInt vs Number).
#[must_use]
pub fn eq_f64(a: &BigInt, b: f64) -> bool {
    cmp_f64(a, b) == Some(Ordering::Equal)
}

// -- StringToBigInt (7.1.4.1) ------------------------------------------------

fn is_str_ws(c: u16) -> bool {
    matches!(
        c,
        0x09 | 0x0b | 0x0c | 0x20 | 0xa0 | 0xfeff | 0x1680
            | 0x2000..=0x200a
            | 0x202f | 0x205f | 0x3000 | 0x0a | 0x0d | 0x2028 | 0x2029
    )
}

/// StringToBigInt (7.1.4.1): a trimmed StrIntegerLiteral. `None` iff the
/// string is not a valid integer literal (the caller maps that to `undefined`
/// / SyntaxError as appropriate). Empty/whitespace-only → 0n. No decimal
/// point, exponent, numeric separator, or `n` suffix is accepted.
#[must_use]
pub fn string_to_bigint(u: &[u16]) -> Option<BigInt> {
    // Trim leading/trailing StrWhiteSpace.
    let mut start = 0;
    let mut end = u.len();
    while start < end && is_str_ws(u[start]) {
        start += 1;
    }
    while end > start && is_str_ws(u[end - 1]) {
        end -= 1;
    }
    let s = &u[start..end];
    if s.is_empty() {
        return Some(zero());
    }
    // Radix prefixes admit no sign.
    let ascii: Option<String> = s
        .iter()
        .map(|&c| u8::try_from(c).ok().map(char::from))
        .collect();
    let text = ascii?; // any non-ASCII code unit ⇒ not an integer literal
    let bytes = text.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'0' {
        let radix = match bytes[1] {
            b'x' | b'X' => Some(16u32),
            b'o' | b'O' => Some(8),
            b'b' | b'B' => Some(2),
            _ => None,
        };
        if let Some(radix) = radix {
            let digits = &text[2..];
            if digits.is_empty() || !digits.bytes().all(|d| (d as char).is_digit(radix)) {
                return None;
            }
            return checked_parse(digits.as_bytes(), radix);
        }
    }
    // Optional sign, then decimal digits.
    let (neg, body) = match bytes.first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text.as_str()),
    };
    if body.is_empty() || !body.bytes().all(|d| d.is_ascii_digit()) {
        return None;
    }
    let mag = checked_parse(body.as_bytes(), 10)?;
    Some(if neg { -mag } else { mag })
}

/// Parse `digits` in `radix`, refusing (None) a magnitude beyond `MAX_BITS`.
fn checked_parse(digits: &[u8], radix: u32) -> Option<BigInt> {
    // Cheap upper bound on the resulting bit count before allocating fully:
    // each digit contributes at most ceil(log2(radix)) bits.
    let per_digit = 64 - (u64::from(radix) - 1).leading_zeros();
    if (digits.len() as u64).saturating_mul(u64::from(per_digit)) > MAX_BITS {
        return None;
    }
    BigInt::parse_bytes(digits, radix)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    fn b(s: &str) -> BigInt {
        BigInt::from_str(s).unwrap()
    }

    #[test]
    fn arithmetic_and_errors() {
        assert_eq!(add(&b("5"), &b("2")).unwrap(), b("7"));
        assert_eq!(div(&b("-7"), &b("2")).unwrap(), b("-3"));
        assert_eq!(rem(&b("-7"), &b("2")).unwrap(), b("-1"));
        assert!(matches!(div(&b("1"), &b("0")), Err(BigErr::Range)));
        assert!(matches!(rem(&b("1"), &b("0")), Err(BigErr::Range)));
        assert!(matches!(pow(&b("2"), &b("-1")), Err(BigErr::Range)));
        assert_eq!(pow(&b("2"), &b("10")).unwrap(), b("1024"));
        assert_eq!(pow(&b("-1"), &b("3")).unwrap(), b("-1"));
        assert_eq!(pow(&b("-1"), &b("4")).unwrap(), b("1"));
    }

    #[test]
    fn bitwise_two_complement() {
        assert_eq!(bitand(&b("-5"), &b("3")), b("3"));
        assert_eq!(bitor(&b("-5"), &b("3")), b("-5"));
        assert_eq!(bitxor(&b("-5"), &b("3")), b("-8"));
        assert_eq!(bitnot(&b("5")), b("-6"));
        assert_eq!(bitnot(&b("-5")), b("4"));
        assert_eq!(shl(&b("-5"), &b("1")).unwrap(), b("-10"));
        assert_eq!(shr(&b("-5"), &b("1")).unwrap(), b("-3"));
        assert_eq!(shr(&b("-1"), &b("1")).unwrap(), b("-1"));
        // Negative shift counts reflect.
        assert_eq!(shl(&b("-5"), &b("-1")).unwrap(), b("-3"));
        assert_eq!(shr(&b("5"), &b("-1")).unwrap(), b("10"));
        // Huge right shift saturates.
        assert_eq!(shr(&b("-3"), &b("1000000000000000000000")).unwrap(), b("-1"));
        assert_eq!(shr(&b("3"), &b("1000000000000000000000")).unwrap(), b("0"));
    }

    #[test]
    fn as_int_uint_n() {
        assert_eq!(as_int_n(8, &b("256")), b("0"));
        assert_eq!(as_int_n(8, &b("255")), b("-1"));
        assert_eq!(as_int_n(8, &b("128")), b("-128"));
        assert_eq!(as_uint_n(8, &b("-1")), b("255"));
        assert_eq!(as_uint_n(0, &b("123")), b("0"));
        assert_eq!(as_int_n(0, &b("123")), b("0"));
    }

    #[test]
    fn number_conversion_round_half_even() {
        assert_eq!(to_f64(&b("10")), 10.0);
        assert_eq!(to_f64(&b("0")), 0.0);
        assert_eq!(to_f64(&b("9007199254740992")), 9_007_199_254_740_992.0);
        // 2^53 + 1 rounds to 2^53 (ties to even).
        assert_eq!(to_f64(&b("9007199254740993")), 9_007_199_254_740_992.0);
        assert_eq!(to_f64(&pow(&b("2"), &b("1024")).unwrap()), f64::INFINITY);
        assert_eq!(to_f64(&(-pow(&b("2"), &b("1024")).unwrap())), f64::NEG_INFINITY);
        assert_eq!(from_integral_f64(1.0).unwrap(), b("1"));
        assert_eq!(from_integral_f64(9_007_199_254_740_992.0).unwrap(), b("9007199254740992"));
        assert!(matches!(from_integral_f64(1.5), Err(BigErr::Range)));
        assert!(matches!(from_integral_f64(f64::NAN), Err(BigErr::Range)));
    }

    #[test]
    fn compare_to_number() {
        assert_eq!(cmp_f64(&b("1"), 2.0), Some(Ordering::Less));
        assert_eq!(cmp_f64(&b("1"), 1.0), Some(Ordering::Equal));
        assert_eq!(cmp_f64(&b("1"), 1.5), Some(Ordering::Less));
        assert_eq!(cmp_f64(&b("2"), 1.5), Some(Ordering::Greater));
        assert_eq!(cmp_f64(&b("1"), f64::NAN), None);
        assert_eq!(cmp_f64(&b("1"), f64::INFINITY), Some(Ordering::Less));
        // The decimal 1.8446744073709552e19 rounds to EXACTLY 2^64 as an f64,
        // so the comparison is Equal (matching Node's `(2n**64n) > that` being
        // false); a genuinely larger f64 compares Less.
        let two64 = pow(&b("2"), &b("64")).unwrap();
        assert_eq!(cmp_f64(&two64, 1.8446744073709552e19), Some(Ordering::Equal));
        assert_eq!(cmp_f64(&two64, 2.0e19), Some(Ordering::Less));
        assert!(eq_f64(&b("1"), 1.0));
        assert!(!eq_f64(&b("1"), 1.5));
    }

    #[test]
    fn string_to_bigint_grammar() {
        let s = |t: &str| string_to_bigint(&crate::value::units_from_str(t));
        assert_eq!(s(""), Some(b("0")));
        assert_eq!(s("   "), Some(b("0")));
        assert_eq!(s("123"), Some(b("123")));
        assert_eq!(s("  123  "), Some(b("123")));
        assert_eq!(s("0x1f"), Some(b("31")));
        assert_eq!(s("0o17"), Some(b("15")));
        assert_eq!(s("0b101"), Some(b("5")));
        assert_eq!(s("-5"), Some(b("-5")));
        assert_eq!(s("+5"), Some(b("5")));
        assert_eq!(s("-0"), Some(b("0")));
        assert_eq!(s("1.5"), None);
        assert_eq!(s("1e3"), None);
        assert_eq!(s("1_000"), None);
        assert_eq!(s("Infinity"), None);
        assert_eq!(s("abc"), None);
        assert_eq!(s("12n"), None);
        assert_eq!(s("0xg"), None);
    }
}
