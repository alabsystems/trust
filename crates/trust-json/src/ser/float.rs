// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Byte-exact JSON float rendering.
//!
//! # What "byte-exact" means here, and why it is not obvious
//!
//! `serde_json` does not use `{}`/`{:e}` to print floats. It calls
//! `zmij::Buffer::format_finite`, and `zmij` is a Schubfach implementation with
//! its OWN notation rules. Three separate things had to be measured rather
//! than assumed (all measurements are reproduced as tests in
//! `tests/differential_json.rs`):
//!
//! 1. **The fixed/exponential threshold differs between `f32` and `f64`.**
//!    `zmij` renders in positional notation when the scientific exponent lies
//!    in `-5..=15` for `f64` but `-6..=12` for `f32`. So `1e-6f64` prints as
//!    `1e-6` while `1e-6f32` prints as `0.000001`, and `1e13f64` prints as
//!    `10000000000000.0` while `1e13f32` prints as `1e+13`. A single shared
//!    threshold is wrong for one of the two types no matter which you pick.
//!
//! 2. **The exponent carries an explicit sign and no zero padding**: `1e+16`,
//!    `1e-6`, `5e-324`, `1.7976931348623157e+308`. `ryu` — which `serde_json`
//!    used before the `zmij` swap — writes `1e16` with no `+`. Any code that
//!    reads this file to "restore ryu compatibility" is reverting a byte
//!    change, not fixing one.
//!
//! 3. **Positional output always carries a fractional part**: `1.0`, `100.0`,
//!    `1000000000000000.0`, and `0.0`/`-0.0` for the zeroes. It is never `1`.
//!
//! # Where the digits come from, and the one correction that is needed
//!
//! The DIGITS are taken from the standard library: `format!("{:e}", v)` yields
//! the shortest decimal that round-trips, which is the same digit string every
//! shortest-round-trip algorithm produces — *except at exact ties*, where two
//! adjacent decimals of the minimal length are equidistant from the value and
//! the algorithms are free to pick either.
//!
//! Measured over 2 998 571 random finite `f64` bit patterns: std and `zmij`
//! disagreed on 759 of them (0.025%), and every sampled disagreement was an
//! exact tie — e.g. `0x4307098d6fca6a8a`, whose exact value is
//! `810553441865041.25`, where std prints `...41.3` and `zmij` prints
//! `...41.2`. **`zmij` breaks ties to even; std breaks them away from zero.**
//!
//! `retie_to_even` below detects the tie exactly and corrects it. The detection
//! needs no bignum, because of the following fact:
//!
//! > Write the value exactly as `m * 2^p` with `m` ODD. A decimal `M * 10^w`
//! > with `M` odd equals it **only if `w == p`** — and then `M = m / 5^p` when
//! > `p >= 0`, or `M = m * 5^(-p)` when `p < 0`.
//!
//! *Proof.* `M * 10^w = M * 2^w * 5^w`. Both `M` and `5^w` are odd, so the
//! 2-adic valuation of the right side is `w`; the 2-adic valuation of `m * 2^p`
//! is `p`. Hence `w = p`, and cancelling `2^p` leaves `m = M * 5^p`. ∎
//!
//! A tie means the value is exactly `(10*D - 5) * 10^(e-n)` (or
//! `(10*D + 5) * 10^(e-n)`) where `D` is the `n`-digit significand and `e` the
//! scientific exponent — a decimal whose significand is odd, since it ends in
//! 5. So the whole test is one exponent comparison plus one exact division or
//! multiplication by a power of five, all in `u64`/`u128`.
//!
//! Nothing here is a heuristic: the differential test formats several million
//! values through both implementations and compares the bytes.

use core::fmt::Write as _;

/// Scientific-exponent range, INCLUSIVE, in which `zmij` uses positional
/// notation for `f64`. Measured, not derived — see the module docs.
const F64_FIXED_EXP: (i32, i32) = (-5, 15);

/// The same range for `f32`. It is NOT the same range. See the module docs.
const F32_FIXED_EXP: (i32, i32) = (-6, 12);

/// The maximum number of significant decimal digits a shortest-round-trip
/// rendering can need: 17 for `f64`, 9 for `f32`.
const MAX_DIGITS: usize = 17;

/// A stack buffer that renders one float, mirroring `zmij::Buffer`.
///
/// Sized for the longest output either type can produce. The extremes are
/// `-0.00000<17 digits>` (24 bytes, `f64` at exponent -5) and
/// `-1.2345678901234567e-308` (24 bytes); 32 leaves headroom and keeps the
/// struct one cache line.
pub struct FloatBuffer {
    bytes: [u8; 32],
    len: usize,
}

impl Default for FloatBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl FloatBuffer {
    #[must_use]
    pub const fn new() -> Self {
        FloatBuffer {
            bytes: [0; 32],
            len: 0,
        }
    }

    /// Renders a FINITE `f64` exactly as `serde_json` renders it.
    ///
    /// # Panics
    /// Debug-asserts that `value` is finite. Callers are the JSON serializer,
    /// which maps NaN and the infinities to `null` before reaching here — the
    /// same contract `zmij::Buffer::format_finite` states.
    pub fn format_finite_f64(&mut self, value: f64) -> &str {
        debug_assert!(value.is_finite(), "format_finite_f64 on a non-finite");
        let mut sci = SciBuf::new();
        // `{:e}` on a float is infallible; the buffer is sized for the longest
        // possible rendering, so the write cannot fail either.
        let _ = write!(sci, "{value:e}");
        let mut d = Decimal::parse(sci.as_str());
        d.retie_to_even_f64(value);
        self.render(&d, F64_FIXED_EXP)
    }

    /// Renders a FINITE `f32` exactly as `serde_json` renders it.
    ///
    /// # Panics
    /// Debug-asserts that `value` is finite; see [`Self::format_finite_f64`].
    pub fn format_finite_f32(&mut self, value: f32) -> &str {
        debug_assert!(value.is_finite(), "format_finite_f32 on a non-finite");
        let mut sci = SciBuf::new();
        let _ = write!(sci, "{value:e}");
        let mut d = Decimal::parse(sci.as_str());
        d.retie_to_even_f32(value);
        self.render(&d, F32_FIXED_EXP)
    }

    fn render(&mut self, d: &Decimal, fixed: (i32, i32)) -> &str {
        self.len = 0;
        if d.neg {
            self.push(b'-');
        }
        let digits = &d.digits[..d.n];
        if d.exp >= fixed.0 && d.exp <= fixed.1 {
            if d.exp < 0 {
                self.push(b'0');
                self.push(b'.');
                for _ in 0..(-d.exp - 1) {
                    self.push(b'0');
                }
                self.push_all(digits);
            } else {
                // Number of digits before the point.
                let int_len = d.exp as usize + 1;
                if d.n <= int_len {
                    self.push_all(digits);
                    for _ in 0..(int_len - d.n) {
                        self.push(b'0');
                    }
                    self.push(b'.');
                    self.push(b'0');
                } else {
                    self.push_all(&digits[..int_len]);
                    self.push(b'.');
                    self.push_all(&digits[int_len..]);
                }
            }
        } else {
            self.push(digits[0]);
            if d.n > 1 {
                self.push(b'.');
                self.push_all(&digits[1..]);
            }
            self.push(b'e');
            self.push(if d.exp < 0 { b'-' } else { b'+' });
            let mut mag = d.exp.unsigned_abs();
            // The exponent is at most 3 decimal digits (|exp| <= 324).
            let mut tmp = [0u8; 4];
            let mut k = 0;
            loop {
                tmp[k] = b'0' + (mag % 10) as u8;
                mag /= 10;
                k += 1;
                if mag == 0 {
                    break;
                }
            }
            while k > 0 {
                k -= 1;
                self.push(tmp[k]);
            }
        }
        // Every byte written above is ASCII.
        core::str::from_utf8(&self.bytes[..self.len]).unwrap_or("")
    }

    #[inline]
    fn push(&mut self, b: u8) {
        // The buffer is sized for the worst case of both types; a full buffer
        // would be a rendering bug, and silently truncating would be a byte
        // divergence, so assert rather than saturate.
        debug_assert!(self.len < self.bytes.len(), "FloatBuffer overflow");
        if self.len < self.bytes.len() {
            self.bytes[self.len] = b;
            self.len += 1;
        }
    }

    #[inline]
    fn push_all(&mut self, bs: &[u8]) {
        for &b in bs {
            self.push(b);
        }
    }
}

/// A shortest-round-trip decimal: `+/- 0.digits * 10^(exp+1)`, i.e. the value
/// is `digits[0] . digits[1..] * 10^exp`.
struct Decimal {
    neg: bool,
    digits: [u8; MAX_DIGITS],
    n: usize,
    exp: i32,
}

impl Decimal {
    /// Parses the output of `{:e}`, which is `[-]d[.ddd]e[-]dd`.
    fn parse(sci: &str) -> Decimal {
        let b = sci.as_bytes();
        let mut i = 0;
        let neg = b[0] == b'-';
        if neg {
            i = 1;
        }
        let mut digits = [0u8; MAX_DIGITS];
        let mut n = 0;
        while i < b.len() && b[i] != b'e' {
            if b[i] != b'.' {
                debug_assert!(n < MAX_DIGITS, "more than {MAX_DIGITS} shortest digits");
                if n < MAX_DIGITS {
                    digits[n] = b[i];
                    n += 1;
                }
            }
            i += 1;
        }
        // Skip the 'e'.
        i += 1;
        let eneg = b[i] == b'-';
        if eneg {
            i += 1;
        }
        let mut exp: i32 = 0;
        while i < b.len() {
            exp = exp * 10 + i32::from(b[i] - b'0');
            i += 1;
        }
        if eneg {
            exp = -exp;
        }
        Decimal {
            neg,
            digits,
            n,
            exp,
        }
    }

    /// `digits` read as an integer. `n <= 17` so this always fits.
    fn significand(&self) -> u64 {
        let mut d: u64 = 0;
        for &c in &self.digits[..self.n] {
            d = d * 10 + u64::from(c - b'0');
        }
        d
    }

    fn set_significand(&mut self, mut d: u64) {
        for k in (0..self.n).rev() {
            self.digits[k] = b'0' + (d % 10) as u8;
            d /= 10;
        }
        debug_assert_eq!(d, 0, "re-tied significand changed digit count");
    }

    fn retie_to_even_f64(&mut self, value: f64) {
        let bits = value.abs().to_bits();
        let raw_exp = ((bits >> 52) & 0x7ff) as i32;
        let raw_mant = bits & ((1u64 << 52) - 1);
        let (mant, p) = if raw_exp == 0 {
            (raw_mant, -1074)
        } else {
            (raw_mant | (1u64 << 52), raw_exp - 1075)
        };
        self.retie(mant, p);
    }

    fn retie_to_even_f32(&mut self, value: f32) {
        let bits = value.abs().to_bits();
        let raw_exp = ((bits >> 23) & 0xff) as i32;
        let raw_mant = u64::from(bits & ((1u32 << 23) - 1));
        let (mant, p) = if raw_exp == 0 {
            (raw_mant, -149)
        } else {
            (raw_mant | (1u64 << 23), raw_exp - 150)
        };
        self.retie(mant, p);
    }

    /// The tie correction proper. `mant * 2^p` is the EXACT magnitude of the
    /// value. See the module docs for why `w == p` is necessary and sufficient.
    fn retie(&mut self, mant: u64, p: i32) {
        if mant == 0 {
            return; // zero: `{:e}` gives "0e0", which renders as "0.0"
        }
        let d = self.significand();
        // Only an ODD last digit can be wrong: on a tie, round-half-even picks
        // the even neighbour, and std's round-half-away already picked it when
        // the neighbour it picked is even.
        if d % 2 == 0 {
            return;
        }
        // Normalise the exact value to an ODD significand.
        let mut m = mant;
        let mut p = p;
        while m % 2 == 0 {
            m >>= 1;
            p += 1;
        }
        // Place value of the digit one past the last kept digit.
        let w = self.exp - self.n as i32;
        if w != p {
            return;
        }
        let Some(exact) = odd_decimal_significand(m, p) else {
            return;
        };
        // Halfway BELOW `d` (std rounded up into an odd digit): take `d - 1`.
        if exact == d * 10 - 5 {
            self.set_significand(d - 1);
            return;
        }
        // Halfway ABOVE `d`. std's tie rule does not produce this, but a
        // future std that broke ties downward would, and the correction is the
        // same shape. Guarded so a carry (which the minimality of `n` makes
        // impossible) can never silently change the digit count.
        if exact == d * 10 + 5 && (d + 1) < pow10_u64(self.n) {
            self.set_significand(d + 1);
        }
    }
}

/// `m * 5^p` for `p < 0`, or `m / 5^(-p)` for `p >= 0` when the division is
/// exact — i.e. the odd significand of the exact decimal expansion of
/// `m * 2^p`. `None` when no such value below `10^18` exists, which is the
/// common case and means "cannot be a tie".
fn odd_decimal_significand(m: u64, p: i32) -> Option<u64> {
    // A tie candidate is `10*D +/- 5` with `D < 10^17`, so it is `< 10^18`.
    const LIMIT: u64 = 1_000_000_000_000_000_000;
    if p >= 0 {
        // Need 5^p | m. m < 2^53 < 5^23, so p > 22 admits nothing.
        if p > 22 {
            return None;
        }
        let mut v = m;
        for _ in 0..p {
            if v % 5 != 0 {
                return None;
            }
            v /= 5;
        }
        (v < LIMIT).then_some(v)
    } else {
        let mut v = m;
        for _ in 0..(-p) {
            v = v.checked_mul(5)?;
            if v >= LIMIT {
                return None;
            }
        }
        Some(v)
    }
}

fn pow10_u64(n: usize) -> u64 {
    let mut v = 1u64;
    for _ in 0..n {
        v *= 10;
    }
    v
}

/// A `core::fmt::Write` sink over a stack buffer, so rendering a float does not
/// allocate. `{:e}` on an `f64` is at most 24 bytes
/// (`-1.2345678901234567e-308`); 32 is the same headroom `FloatBuffer` keeps.
struct SciBuf {
    bytes: [u8; 32],
    len: usize,
}

impl SciBuf {
    fn new() -> Self {
        SciBuf {
            bytes: [0; 32],
            len: 0,
        }
    }
    fn as_str(&self) -> &str {
        core::str::from_utf8(&self.bytes[..self.len]).unwrap_or("")
    }
}

impl core::fmt::Write for SciBuf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let b = s.as_bytes();
        if self.len + b.len() > self.bytes.len() {
            return Err(core::fmt::Error);
        }
        self.bytes[self.len..self.len + b.len()].copy_from_slice(b);
        self.len += b.len();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f64s(v: f64) -> String {
        FloatBuffer::new().format_finite_f64(v).to_string()
    }
    fn f32s(v: f32) -> String {
        FloatBuffer::new().format_finite_f32(v).to_string()
    }

    #[test]
    fn positional_always_has_a_fraction() {
        assert_eq!(f64s(0.0), "0.0");
        assert_eq!(f64s(-0.0), "-0.0");
        assert_eq!(f64s(1.0), "1.0");
        assert_eq!(f64s(-1.0), "-1.0");
        assert_eq!(f64s(100.0), "100.0");
        assert_eq!(f64s(1e15), "1000000000000000.0");
    }

    #[test]
    fn exponent_is_signed_and_unpadded() {
        assert_eq!(f64s(1e16), "1e+16");
        assert_eq!(f64s(1e-6), "1e-6");
        assert_eq!(f64s(5e-324), "5e-324");
        assert_eq!(f64s(f64::MAX), "1.7976931348623157e+308");
        assert_eq!(f64s(f64::MIN), "-1.7976931348623157e+308");
    }

    #[test]
    fn the_two_types_have_different_thresholds() {
        // The whole point of F32_FIXED_EXP != F64_FIXED_EXP.
        assert_eq!(f64s(1e-6), "1e-6");
        assert_eq!(f32s(1e-6), "0.000001");
        assert_eq!(f64s(1e13), "10000000000000.0");
        assert_eq!(f32s(1e13), "1e+13");
    }

    #[test]
    fn ties_round_to_even() {
        // 0x4307098d6fca6a8a is exactly 810553441865041.25 — equidistant from
        // ...41.2 and ...41.3. std prints .3; zmij prints .2.
        assert_eq!(f64s(f64::from_bits(0x4307098d6fca6a8a)), "810553441865041.2");
        assert_eq!(
            f64s(f64::from_bits(0xc2698e64d863e100)),
            "-878105248543.0312"
        );
        assert_eq!(
            f64s(f64::from_bits(0xc2eff16fc0c1e344)),
            "-280974579863322.12"
        );
    }

    #[test]
    fn subnormals_and_boundaries() {
        assert_eq!(f64s(f64::MIN_POSITIVE), "2.2250738585072014e-308");
        assert_eq!(f64s(f64::from_bits(2)), "1e-323");
        assert_eq!(f32s(f32::from_bits(1)), "1e-45");
        assert_eq!(f32s(f32::MAX), "3.4028235e+38");
        assert_eq!(f32s(f32::MIN_POSITIVE), "1.1754944e-38");
    }
}
