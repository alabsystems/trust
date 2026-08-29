// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Addition, subtraction, multiplication — Lean `Nat` semantics.
//!
//! The one divergence-prone operation here is subtraction, and it is the most
//! important semantic in the crate: **Lean's `Nat.sub` is truncated at zero**,
//! so [`Nat::sub`] — the primary — is truncated too. See its docs for the
//! authority chain.

use alloc::vec::Vec;

use crate::Nat;

impl Nat {
    /// `self + other`. Ordinary natural-number addition: arbitrary precision,
    /// so no overflow exists and no wrap is possible.
    ///
    /// Matches Lean's `Nat.add` (clean-kernel: `src/micro/native.rs:157`,
    /// `nat_lit(x + y)` over `BigUint`).
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn add(&self, other: &Self) -> Self {
        let (long, short) = if self.limbs.len() >= other.limbs.len() {
            (&self.limbs, &other.limbs)
        } else {
            (&other.limbs, &self.limbs)
        };
        let mut out = Vec::with_capacity(long.len() + 1);
        let mut carry = 0u64;
        for (i, &a) in long.iter().enumerate() {
            let b = short.get(i).copied().unwrap_or(0);
            let (s1, c1) = a.overflowing_add(b);
            let (s2, c2) = s1.overflowing_add(carry);
            out.push(s2);
            carry = u64::from(c1) + u64::from(c2);
        }
        if carry != 0 {
            out.push(carry);
        }
        Self::from_limbs(out)
    }

    /// `self - other`, **TRUNCATED AT ZERO** — this is Lean's `Nat.sub`,
    /// exactly, and it is the PRIMARY subtraction of this crate on purpose.
    ///
    /// # Semantics
    ///
    /// `a.sub(b)` is `a - b` when `b <= a`, and **`0` when `b > a`**. In Lean:
    /// `Nat.sub_eq_zero_of_le : n ≤ m → n - m = 0` — natural subtraction is
    /// total by truncation, not by panicking and not by going negative.
    ///
    /// # Authority
    ///
    /// This matches the Clean kernel's reducers limb for limb:
    /// * `first-party/clean/crates/clean-kernel/src/micro/native.rs:158` —
    ///   `"Nat.sub" => nat_lit(if x >= y { x - y } else { BigUint::ZERO })`
    /// * `first-party/clean/crates/clean-kernel/src/tc/reduction/nat.rs:258-260`
    ///   — "Lean Nat subtraction is truncated (floored) at zero", via
    ///   `saturating_sub_big`.
    ///
    /// A kernel-checked theorem about `a - b` is a theorem about THIS
    /// operation. Emitting a panicking or wrapping subtraction instead would
    /// make the binary disagree with the proposition the kernel checked —
    /// a wrong binary, not a failed proof. Callers that want to *observe*
    /// underflow instead of truncating have [`Nat::checked_sub`].
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn sub(&self, other: &Self) -> Self {
        self.checked_sub(other).unwrap_or(Self::ZERO)
    }

    /// Alias for [`Nat::sub`], under the name Rust callers reach for.
    ///
    /// On ℕ, "saturating at zero" and Lean's truncated `Nat.sub` are the same
    /// function; the alias exists so a reader grepping for Rust-flavored
    /// saturation finds the semantics already pinned rather than adding a
    /// second subtraction.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn saturating_sub(&self, other: &Self) -> Self {
        self.sub(other)
    }

    /// `self - other`, **checked**: `None` when `other > self`.
    ///
    /// This is the variant for callers that must *distinguish* underflow from
    /// a genuine zero (Rust's `u64::checked_sub` shape). It is deliberately
    /// not the primary: the carrier semantics are Lean's, and Lean's `Nat.sub`
    /// truncates. The two variants relate exactly:
    /// `checked_sub(a, b) == None` iff `b > a`, which is the strict half of the
    /// domain on which Lean's truncated `a - b` is `0`
    /// (`Nat.sub_eq_zero_of_le`).
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        if self < other {
            return None;
        }
        let mut out = Vec::with_capacity(self.limbs.len());
        let mut borrow = 0u64;
        for (i, &a) in self.limbs.iter().enumerate() {
            let b = other.limbs.get(i).copied().unwrap_or(0);
            let (d1, b1) = a.overflowing_sub(b);
            let (d2, b2) = d1.overflowing_sub(borrow);
            out.push(d2);
            borrow = u64::from(b1) + u64::from(b2);
        }
        debug_assert_eq!(borrow, 0, "self >= other was checked above");
        Some(Self::from_limbs(out))
    }

    /// `self * other`. Ordinary natural-number multiplication: arbitrary
    /// precision, no overflow exists, no wrap is possible.
    ///
    /// Matches Lean's `Nat.mul` (clean-kernel: `src/micro/native.rs:159`).
    /// Schoolbook limb multiplication with `u128` intermediates — chosen for
    /// auditability; this is a correctness-critical runtime, not a
    /// number-theory library.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::ZERO;
        }
        let mut out = alloc::vec![0u64; self.limbs.len() + other.limbs.len()];
        for (i, &a) in self.limbs.iter().enumerate() {
            if a == 0 {
                continue;
            }
            let mut carry: u128 = 0;
            for (j, &b) in other.limbs.iter().enumerate() {
                let cur = u128::from(out[i + j]) + u128::from(a) * u128::from(b) + carry;
                out[i + j] = cur as u64; // low 64 bits; the high bits are `carry`
                carry = cur >> 64;
            }
            let mut k = i + other.limbs.len();
            while carry != 0 {
                let cur = u128::from(out[k]) + carry;
                out[k] = cur as u64;
                carry = cur >> 64;
                k += 1;
            }
        }
        Self::from_limbs(out)
    }

    /// `self * m` for a single limb — internal, used by the decimal parser.
    #[must_use]
    pub(crate) fn mul_limb(&self, m: u64) -> Self {
        if m == 0 || self.is_zero() {
            return Self::ZERO;
        }
        let mut out = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry: u128 = 0;
        for &l in &self.limbs {
            let cur = u128::from(l) * u128::from(m) + carry;
            out.push(cur as u64);
            carry = cur >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        Self::from_limbs(out)
    }

    /// `self + a` for a single limb — internal, used by the decimal parser.
    #[must_use]
    pub(crate) fn add_limb(&self, a: u64) -> Self {
        let mut out = self.limbs.clone();
        let mut carry = a;
        for l in &mut out {
            if carry == 0 {
                break;
            }
            let (s, c) = l.overflowing_add(carry);
            *l = s;
            carry = u64::from(c);
        }
        if carry != 0 {
            out.push(carry);
        }
        Self::from_limbs(out)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use crate::Nat;

    #[test]
    fn add_carries_across_the_limb_boundary() {
        // 2^64 - 1 + 1 = 2^64 — the carry must create a second limb.
        let sum = Nat::from_u64(u64::MAX).add(&Nat::one());
        assert_eq!(sum, Nat::from_limbs(vec![0, 1]));
        // ... and a full carry chain: (2^128 - 1) + 1 = 2^128.
        let sum = Nat::from_limbs(vec![u64::MAX, u64::MAX]).add(&Nat::one());
        assert_eq!(sum, Nat::from_limbs(vec![0, 0, 1]));
    }

    #[test]
    fn add_is_commutative_regardless_of_limb_count() {
        let a = Nat::from_limbs(vec![u64::MAX, 7]);
        let b = Nat::from_u64(12345);
        assert_eq!(a.add(&b), b.add(&a));
    }

    #[test]
    fn sub_borrows_across_the_limb_boundary() {
        // 2^64 - 1 = u64::MAX — the borrow must consume the second limb.
        let diff = Nat::from_limbs(vec![0, 1]).sub(&Nat::one());
        assert_eq!(diff, Nat::from_u64(u64::MAX));
        // 2^128 - 2^64 = [0, u64::MAX] by definition of the limb layout.
        let diff = Nat::from_limbs(vec![0, 0, 1]).sub(&Nat::from_limbs(vec![0, 1]));
        assert_eq!(diff, Nat::from_limbs(vec![0, u64::MAX]));
    }

    #[test]
    fn sub_truncates_at_zero_like_lean_nat_sub() {
        // The load-bearing semantic. Pinned again, against the kernel
        // citations, in tests/lean_semantics.rs.
        assert_eq!(Nat::from_u64(3).sub(&Nat::from_u64(5)), Nat::ZERO);
        assert_eq!(Nat::ZERO.sub(&Nat::one()), Nat::ZERO);
        let huge = Nat::from_limbs(vec![1, 2, 3]);
        assert_eq!(Nat::from_u64(9).sub(&huge), Nat::ZERO);
        assert_eq!(huge.sub(&huge), Nat::ZERO);
        assert_eq!(huge.saturating_sub(&huge), Nat::ZERO);
    }

    #[test]
    fn checked_sub_refuses_exactly_underflow() {
        assert_eq!(Nat::from_u64(3).checked_sub(&Nat::from_u64(5)), None);
        assert_eq!(Nat::from_u64(5).checked_sub(&Nat::from_u64(3)), Some(Nat::from_u64(2)));
        // Equal values are NOT underflow: a - a = 0 is a real zero.
        assert_eq!(Nat::from_u64(5).checked_sub(&Nat::from_u64(5)), Some(Nat::ZERO));
    }

    #[test]
    fn mul_crosses_limbs_exactly() {
        // 2^64 * 2^64 = 2^128.
        let two_64 = Nat::from_limbs(vec![0, 1]);
        assert_eq!(two_64.mul(&two_64), Nat::from_limbs(vec![0, 0, 1]));
        // u64::MAX ^ 2 fits u128 exactly — hardware is the reference.
        let reference = u128::from(u64::MAX) * u128::from(u64::MAX);
        let product = Nat::from_u64(u64::MAX).mul(&Nat::from_u64(u64::MAX));
        assert_eq!(product.to_decimal(), std::format!("{reference}"));
    }

    #[test]
    fn mul_by_zero_is_zero_and_by_one_is_identity() {
        let big = Nat::from_limbs(vec![3, 2, 1]);
        assert_eq!(big.mul(&Nat::ZERO), Nat::ZERO);
        assert_eq!(Nat::ZERO.mul(&big), Nat::ZERO);
        assert_eq!(big.mul(&Nat::one()), big);
    }

    #[test]
    fn internal_limb_helpers_agree_with_the_general_ops() {
        let a = Nat::from_limbs(vec![u64::MAX, u64::MAX, 41]);
        assert_eq!(a.mul_limb(10_000), a.mul(&Nat::from_u64(10_000)));
        assert_eq!(a.add_limb(u64::MAX), a.add(&Nat::from_u64(u64::MAX)));
        assert_eq!(a.mul_limb(0), Nat::ZERO);
        assert_eq!(a.add_limb(0), a);
    }
}
