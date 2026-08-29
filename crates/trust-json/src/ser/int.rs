// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Byte-exact JSON integer rendering — the `itoa` replacement.
//!
//! JSON integers have exactly one spelling, so the only ways to get this wrong
//! are the boundary cases, and they are the ones that bite:
//!
//! * `i64::MIN` / `i128::MIN` have no positive counterpart, so `-v` overflows.
//!   The code below negates in the UNSIGNED domain (`unsigned_abs`), which is
//!   total.
//! * `u64::MAX` and `u128::MAX` must not lose their top digit.
//!
//! Both are pinned by tests here and re-checked against the incumbent in
//! `tests/differential_json.rs`.

/// Widest rendering: `-170141183460469231731687303715884105728` is 40 bytes.
const CAP: usize = 40;

pub struct IntBuffer {
    bytes: [u8; CAP],
    start: usize,
}

impl Default for IntBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl IntBuffer {
    #[must_use]
    pub const fn new() -> Self {
        IntBuffer {
            bytes: [0; CAP],
            start: CAP,
        }
    }

    pub fn format_u128(&mut self, mut v: u128) -> &str {
        self.start = CAP;
        loop {
            self.start -= 1;
            self.bytes[self.start] = b'0' + (v % 10) as u8;
            v /= 10;
            if v == 0 {
                break;
            }
        }
        self.finish()
    }

    pub fn format_i128(&mut self, v: i128) -> &str {
        // `unsigned_abs` is why `i128::MIN` works: `-i128::MIN` would panic.
        let neg = v < 0;
        let mag = v.unsigned_abs();
        self.format_u128(mag);
        if neg {
            self.start -= 1;
            self.bytes[self.start] = b'-';
        }
        self.finish()
    }

    #[inline]
    pub fn format_u64(&mut self, v: u64) -> &str {
        self.format_u128(u128::from(v))
    }

    #[inline]
    pub fn format_i64(&mut self, v: i64) -> &str {
        self.format_i128(i128::from(v))
    }

    fn finish(&self) -> &str {
        core::str::from_utf8(&self.bytes[self.start..]).unwrap_or("")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boundaries() {
        let mut b = IntBuffer::new();
        assert_eq!(b.format_i64(i64::MIN), "-9223372036854775808");
        assert_eq!(b.format_i64(i64::MAX), "9223372036854775807");
        assert_eq!(b.format_u64(u64::MAX), "18446744073709551615");
        assert_eq!(b.format_u64(0), "0");
        assert_eq!(b.format_i64(0), "0");
        assert_eq!(b.format_i64(-1), "-1");
        assert_eq!(
            b.format_i128(i128::MIN),
            "-170141183460469231731687303715884105728"
        );
        assert_eq!(
            b.format_u128(u128::MAX),
            "340282366920938463463374607431768211455"
        );
    }

    #[test]
    fn agrees_with_std_display_over_a_sweep() {
        let mut b = IntBuffer::new();
        let mut s: u64 = 0x9E3779B97F4A7C15;
        for _ in 0..200_000 {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
            assert_eq!(b.format_u64(s), s.to_string());
            let i = s as i64;
            assert_eq!(b.format_i64(i), i.to_string());
        }
    }
}
