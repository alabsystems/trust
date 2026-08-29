// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Division and remainder — Lean `Nat` semantics, INCLUDING division by zero.
//!
//! # READ THIS BEFORE USING `div` OR `rem`
//!
//! **`Nat::div` returns `0` on division by zero, and `Nat::rem` returns the
//! dividend.** That is not a bug and not a convenience default — it is Lean's
//! `Nat.div` / `Nat.mod`, which are TOTAL functions:
//!
//! * `Nat.div_zero : n / 0 = 0`
//! * `Nat.mod_zero : n % 0 = n`
//!
//! This crate is the runtime carrier for kernel `Nat`, so a kernel-checked
//! theorem mentioning `n / m` is a theorem about *these* total functions. If
//! the emitted binary panicked on `m = 0` instead — Rust's semantics — the
//! binary would diverge from a proposition the kernel already accepted: a
//! wrong binary, the exact defect class I4/I6 exist to make unreachable.
//!
//! Authority in the Clean kernel (both reduction lanes agree):
//! * `first-party/clean/crates/clean-kernel/src/micro/native.rs:160-161` —
//!   `"Nat.div" => nat_lit(if y.is_zero() { BigUint::ZERO } else { x / y })`,
//!   `"Nat.mod" => nat_lit(if y.is_zero() { x } else { x % y })`
//! * `first-party/clean/crates/clean-kernel/src/expr/bignat_ops.rs:73-88` —
//!   `checked_div_big` ("Returns 0 when other is zero (Lean 4 semantics)"),
//!   `checked_mod_big` ("Returns self when other is zero (Lean 4 semantics)")
//! * `first-party/clean/crates/clean-kernel/src/tc/reduction/nat.rs:268-275`
//!
//! Note the Euclidean identity `n = m * (n / m) + n % m` holds for EVERY `m`
//! under these semantics — at `m = 0` it reads `n = 0 * 0 + n`. That identity
//! is pinned for zero and nonzero divisors in `tests/lean_semantics.rs`.
//!
//! Callers that want Rust-shaped division (refuse a zero divisor) use
//! [`Nat::checked_div`] / [`Nat::checked_rem`] / [`Nat::checked_div_rem`].

use alloc::vec::Vec;

use crate::Nat;

impl Nat {
    /// `self / other`, floor division, with **`n / 0 = 0`** — Lean's
    /// `Nat.div`, exactly. See the module docs for why and for the
    /// clean-kernel authority. Rust-shaped refusal: [`Nat::checked_div`].
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn div(&self, other: &Self) -> Self {
        match self.checked_div_rem(other) {
            Some((q, _)) => q,
            None => Self::ZERO, // Nat.div_zero: n / 0 = 0
        }
    }

    /// `self % other`, with **`n % 0 = n`** — Lean's `Nat.mod`, exactly. See
    /// the module docs for why and for the clean-kernel authority.
    /// Rust-shaped refusal: [`Nat::checked_rem`].
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn rem(&self, other: &Self) -> Self {
        match self.checked_div_rem(other) {
            Some((_, r)) => r,
            None => self.clone(), // Nat.mod_zero: n % 0 = n
        }
    }

    /// `(self / other, self % other)` under Lean semantics: a zero divisor
    /// yields `(0, self)`, so the Euclidean identity
    /// `self = other * q + r` holds for every divisor.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn div_rem(&self, other: &Self) -> (Self, Self) {
        match self.checked_div_rem(other) {
            Some(pair) => pair,
            None => (Self::ZERO, self.clone()),
        }
    }

    /// `self / other`, **checked**: `None` when `other` is zero.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        self.checked_div_rem(other).map(|(q, _)| q)
    }

    /// `self % other`, **checked**: `None` when `other` is zero.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn checked_rem(&self, other: &Self) -> Option<Self> {
        self.checked_div_rem(other).map(|(_, r)| r)
    }

    /// Quotient and remainder, **checked**: `None` when `other` is zero.
    ///
    /// For a nonzero divisor this is the one place quotient/remainder are
    /// computed; `div`, `rem`, `div_rem` and the other `checked_*` variants
    /// all delegate here, so the Lean-vs-checked split is a policy on top of
    /// a single arithmetic, never two arithmetics.
    ///
    /// Restoring shift-subtract long division (single-limb divisors take a
    /// word-at-a-time fast lane). Postconditions, pinned in tests:
    /// `self = other * q + r` and `r < other`.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn checked_div_rem(&self, other: &Self) -> Option<(Self, Self)> {
        if other.is_zero() {
            return None;
        }
        if self < other {
            return Some((Self::ZERO, self.clone()));
        }
        if other.limbs.len() == 1 {
            let (q, r) = self.div_rem_limb(other.limbs[0]);
            return Some((q, Self::from_u64(r)));
        }

        let mut remainder = self.clone();
        let mut quotient = alloc::vec![0u64; self.limbs.len()];
        // self >= other here, so this cannot underflow.
        let mut shift = self.bit_length() - other.bit_length();
        loop {
            let candidate = other.shl_bits(shift);
            if remainder >= candidate {
                remainder = remainder
                    .checked_sub(&candidate)
                    .expect("invariant: remainder >= candidate was just compared");
                quotient[shift / 64] |= 1u64 << (shift % 64);
            }
            if shift == 0 {
                break;
            }
            shift -= 1;
        }
        Some((Self::from_limbs(quotient), remainder))
    }

    /// Quotient and remainder by a single nonzero limb — word-at-a-time long
    /// division, most significant limb first.
    ///
    /// Internal. The Lean zero-divisor policy lives in the public wrappers;
    /// this helper demands a nonzero divisor outright.
    pub(crate) fn div_rem_limb(&self, divisor: u64) -> (Self, u64) {
        debug_assert!(divisor != 0, "div_rem_limb requires a nonzero divisor");
        let mut out = alloc::vec![0u64; self.limbs.len()];
        let mut rem: u128 = 0;
        for i in (0..self.limbs.len()).rev() {
            let cur = (rem << 64) | u128::from(self.limbs[i]);
            out[i] = (cur / u128::from(divisor)) as u64;
            rem = cur % u128::from(divisor);
        }
        (Self::from_limbs(out), rem as u64)
    }

    /// `self << shift` (bits) — internal, used by the long division.
    pub(crate) fn shl_bits(&self, shift: usize) -> Self {
        if self.is_zero() {
            return Self::ZERO;
        }
        let limb_shift = shift / 64;
        let bit_shift = shift % 64;
        let mut out: Vec<u64> = alloc::vec![0u64; self.limbs.len() + limb_shift + 1];
        for (i, &l) in self.limbs.iter().enumerate() {
            if bit_shift == 0 {
                out[i + limb_shift] |= l;
            } else {
                out[i + limb_shift] |= l << bit_shift;
                out[i + limb_shift + 1] |= l >> (64 - bit_shift);
            }
        }
        Self::from_limbs(out)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use crate::Nat;

    #[test]
    fn division_by_zero_is_zero_and_mod_by_zero_is_the_dividend() {
        // Nat.div_zero / Nat.mod_zero — the loud case. Pinned against the
        // kernel citations again in tests/lean_semantics.rs.
        let n = Nat::from_u64(42);
        assert_eq!(n.div(&Nat::ZERO), Nat::ZERO);
        assert_eq!(n.rem(&Nat::ZERO), n);
        assert_eq!(Nat::ZERO.div(&Nat::ZERO), Nat::ZERO);
        assert_eq!(Nat::ZERO.rem(&Nat::ZERO), Nat::ZERO);
        assert_eq!(n.div_rem(&Nat::ZERO), (Nat::ZERO, n.clone()));
    }

    #[test]
    fn checked_division_refuses_exactly_the_zero_divisor() {
        let n = Nat::from_u64(42);
        assert_eq!(n.checked_div(&Nat::ZERO), None);
        assert_eq!(n.checked_rem(&Nat::ZERO), None);
        assert_eq!(n.checked_div_rem(&Nat::ZERO), None);
        assert_eq!(n.checked_div(&Nat::from_u64(5)), Some(Nat::from_u64(8)));
        assert_eq!(n.checked_rem(&Nat::from_u64(5)), Some(Nat::from_u64(2)));
    }

    #[test]
    fn single_limb_division_matches_hardware() {
        for (a, b) in [(0u64, 1u64), (7, 3), (u64::MAX, 10), (1, u64::MAX), (u64::MAX, u64::MAX)] {
            let (q, r) = Nat::from_u64(a).div_rem(&Nat::from_u64(b));
            assert_eq!(q, Nat::from_u64(a / b), "{a} / {b}");
            assert_eq!(r, Nat::from_u64(a % b), "{a} % {b}");
        }
    }

    #[test]
    fn multi_limb_division_crosses_the_boundary_exactly() {
        // 2^128 / 2^64 = 2^64, remainder 0.
        let two_128 = Nat::from_limbs(vec![0, 0, 1]);
        let two_64 = Nat::from_limbs(vec![0, 1]);
        assert_eq!(two_128.div_rem(&two_64), (two_64.clone(), Nat::ZERO));
        // (2^128 - 1) / 7 fits u128 exactly — hardware is the reference.
        let x = Nat::from_limbs(vec![u64::MAX, u64::MAX]);
        let (q, r) = x.div_rem(&Nat::from_u64(7));
        assert_eq!(q.to_decimal(), std::format!("{}", u128::MAX / 7));
        assert_eq!(r.to_decimal(), std::format!("{}", u128::MAX % 7));
    }

    #[test]
    fn the_euclidean_identity_holds_with_a_multi_limb_divisor() {
        // Forces the shift-subtract lane (divisor wider than one limb).
        let x = Nat::from_limbs(vec![0xDEAD_BEEF, u64::MAX, 0x1234_5678, 9]);
        let d = Nat::from_limbs(vec![u64::MAX, 3]);
        let (q, r) = x.div_rem(&d);
        assert!(r < d, "remainder must be strictly below the divisor");
        assert_eq!(d.mul(&q).add(&r), x, "x = d*q + r must reconstruct exactly");
        // And the quotient is not the degenerate one.
        assert!(!q.is_zero());
    }

    #[test]
    fn dividend_smaller_than_divisor_yields_zero_quotient() {
        let small = Nat::from_u64(5);
        let big = Nat::from_limbs(vec![0, 1]);
        assert_eq!(small.div_rem(&big), (Nat::ZERO, small.clone()));
    }

    #[test]
    fn shl_bits_is_exact_across_limb_boundaries() {
        assert_eq!(Nat::one().shl_bits(64), Nat::from_limbs(vec![0, 1]));
        assert_eq!(Nat::one().shl_bits(0), Nat::one());
        assert_eq!(Nat::ZERO.shl_bits(1000), Nat::ZERO);
        // (2^64 - 1) << 1 = 2^65 - 2.
        assert_eq!(Nat::from_u64(u64::MAX).shl_bits(1), Nat::from_limbs(vec![u64::MAX - 1, 1]));
    }
}
