// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The Trust-owned arbitrary-precision natural number** — the runtime half
//! of increment I6 of
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`.
//!
//! # What this is
//!
//! [`Nat`] is an unsigned, unbounded integer over little-endian `u64` limbs,
//! written to be the **runtime carrier for Clean/Lean `Nat`**. Per §5b of the
//! design of record, the default carrier for an unbounded Clean type is a
//! Trust-owned bignum; `trust-clean-carrier` refuses `Nat` today because that
//! bignum did not exist. This crate is it.
//!
//! # Semantics: Lean's `Nat`, EXACTLY
//!
//! Every operation matches Lean's `Nat` operation on the nose, because a value
//! this crate produces is a value a verified binary emits. A "more sensible"
//! semantic here (panicking division, underflow errors) would be a semantic
//! **mismatch with the proposition the kernel checked** — i.e. a wrong binary,
//! the exact failure mode I4/I6 exist to make unreachable. The divergence-prone
//! cases, each pinned by tests against the authoritative definitions in
//! `first-party/clean/crates/clean-kernel`:
//!
//! | Operation | Lean semantics | Clean-kernel authority |
//! |---|---|---|
//! | [`Nat::sub`] | **truncated at zero**: `a - b = 0` when `b > a` (`Nat.sub_eq_zero_of_le`) | `src/micro/native.rs:158`, `src/tc/reduction/nat.rs:258-260` (`saturating_sub_big`) |
//! | [`Nat::div`] | **division by zero returns 0**: `n / 0 = 0` (`Nat.div_zero`) | `src/micro/native.rs:160`, `src/expr/bignat_ops.rs:73-78` (`checked_div_big`) |
//! | [`Nat::rem`] | **mod by zero returns the dividend**: `n % 0 = n` (`Nat.mod_zero`) | `src/micro/native.rs:161`, `src/expr/bignat_ops.rs:83-88` (`checked_mod_big`) |
//! | [`Nat::add`] / [`Nat::mul`] | ordinary ℕ arithmetic — arbitrary precision, **no wrap is possible** | `src/micro/native.rs:157,159` |
//! | `==` / `<` / `<=` | ordinary ℕ order (`Nat.beq`, `Nat.blt`, `Nat.ble`) | `src/micro/native.rs` (`Nat.beq`/`Nat.ble`) |
//!
//! Callers that want Rust-shaped fail-fast behavior instead have the
//! `checked_*` variants ([`Nat::checked_sub`], [`Nat::checked_div`],
//! [`Nat::checked_rem`], [`Nat::checked_div_rem`]), which return `None` in
//! exactly the cases where Lean's total functions and Rust's partial ones
//! disagree. Nothing in this crate wraps, truncates a limb, or guesses.
//!
//! # What is deliberately NOT here
//!
//! * **No negative numbers.** This is ℕ, not ℤ. Clean `Int` needs its own
//!   carrier decision; pretending `Nat` covers it is how sign bugs ship.
//! * **No dependency on `clean-kernel`.** The kernel's `BigNat` and this
//!   runtime are two independently-authored implementations of one semantics.
//!   The agreement tests in `tests/` are evidence *because* no code is shared —
//!   the same independence argument the frozen R functor rests on.
//! * **No `std`.** `#![no_std]` + `alloc`, like every runtime a user program
//!   is forced to link.
//!
//! # Representation
//!
//! Little-endian `u64` limbs, canonical: no most-significant zero limbs, and
//! zero is the empty limb vector. Canonicity is an invariant maintained by
//! every constructor, which is what lets `Eq`/`Hash` be derived structurally.

#![no_std]
// I6 sysroot shipping. When library/sysroot builds this crate into the shipped
// standard-library sysroot (feature `rustc-dep-of-std`), the std build passes
// `-Zforce-unstable-if-unmarked`, which would gate every unmarked item — and
// user `extern crate trust_bignum` itself — behind the `rustc_private` nightly
// feature. `staged_api` + the `#[stable]` markings below declare the surface
// stable instead. EVERY stability attribute in this crate, crate-level and
// per-item, is behind `cfg_attr(feature = "rustc-dep-of-std", ...)`: outside
// the std build, `stable`/`staged_api` are themselves unstable attributes, and
// the plain-cargo fast lane of this crate must stay green on a stock
// toolchain. (Plan step 8 as amended by review defect 4.)
#![cfg_attr(feature = "rustc-dep-of-std", feature(staged_api))]
#![cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]

extern crate alloc;

#[cfg(test)]
extern crate std;

mod arith;
mod decimal;
mod divmod;

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
pub use decimal::ParseNatError;

use alloc::vec::Vec;
use core::cmp::Ordering;

/// An arbitrary-precision unsigned integer with Lean `Nat` semantics.
///
/// See the crate docs for the semantics table and the clean-kernel citations.
/// The canonical-form invariant (no trailing zero limbs; zero is the empty
/// vector) is maintained by every constructor, so derived structural equality
/// IS value equality.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
pub struct Nat {
    /// Little-endian limbs. Canonical: `limbs.last() != Some(&0)`.
    pub(crate) limbs: Vec<u64>,
}

impl Nat {
    /// Zero — the empty limb vector.
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub const ZERO: Self = Self { limbs: Vec::new() };

    /// One.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn one() -> Self {
        Self::from_u64(1)
    }

    /// Construct from a `u64`. Total — every `u64` is a `Nat`.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn from_u64(value: u64) -> Self {
        if value == 0 { Self::ZERO } else { Self { limbs: alloc::vec![value] } }
    }

    /// Convert to `u64`, **checked**: `None` when the value does not fit.
    ///
    /// This is the only direction that can lose information, so it is the only
    /// direction that can refuse. There is no `to_u64_wrapping` and there will
    /// not be one: a wrapped carrier value is a wrong binary that every
    /// downstream proof still accepts.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0]),
            _ => None,
        }
    }

    /// Construct from little-endian `u64` limbs, normalizing to canonical form.
    ///
    /// Public for interop with other limb-based representations (the kernel's
    /// `BigNat::limbs()` is the same layout). Trailing zero limbs are accepted
    /// and stripped; they denote the same value.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn from_limbs(mut limbs: Vec<u64>) -> Self {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        Self { limbs }
    }

    /// The canonical little-endian limbs. Empty for zero; the last limb is
    /// never zero otherwise.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn limbs(&self) -> &[u64] {
        &self.limbs
    }

    /// Is this zero?
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    /// The position of the highest set bit plus one; `0` for zero.
    ///
    /// `bit_length() <= 64` is exactly "fits in a `u64`".
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn bit_length(&self) -> usize {
        match self.limbs.last() {
            None => 0,
            Some(&top) => (self.limbs.len() - 1) * 64 + (64 - top.leading_zeros() as usize),
        }
    }
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl From<u64> for Nat {
    fn from(value: u64) -> Self {
        Self::from_u64(value)
    }
}

// ---------------------------------------------------------------------------
// Order — ordinary ℕ order, i.e. Lean's `Nat.blt` / `Nat.ble` / `Nat.beq`
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl Ord for Nat {
    fn cmp(&self, other: &Self) -> Ordering {
        // Canonical form makes the limb count a magnitude comparison; equal
        // counts compare lexicographically from the most significant limb.
        self.limbs
            .len()
            .cmp(&other.limbs.len())
            .then_with(|| self.limbs.iter().rev().cmp(other.limbs.iter().rev()))
    }
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// ---------------------------------------------------------------------------
// Rendering — decimal, exactly, at any precision
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl core::fmt::Display for Nat {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.to_decimal())
    }
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl core::fmt::Debug for Nat {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // The decimal value, not the limbs: a test failure that prints
        // `Nat(340282366920938463463374607431768211456)` is actionable,
        // `Nat { limbs: [0, 0, 1] }` makes the reader do the base conversion.
        write!(f, "Nat({})", self.to_decimal())
    }
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl core::str::FromStr for Nat {
    type Err = ParseNatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_decimal(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn zero_is_the_empty_limb_vector() {
        assert!(Nat::ZERO.is_zero());
        assert_eq!(Nat::from_u64(0), Nat::ZERO);
        assert_eq!(Nat::ZERO.limbs(), &[] as &[u64]);
        assert_eq!(Nat::default(), Nat::ZERO);
    }

    #[test]
    fn from_limbs_normalizes_to_canonical_form() {
        assert_eq!(Nat::from_limbs(vec![5, 0, 0]), Nat::from_u64(5));
        assert_eq!(Nat::from_limbs(vec![0, 0, 0]), Nat::ZERO);
        assert_eq!(Nat::from_limbs(vec![]), Nat::ZERO);
        // ... and equality is therefore representation-independent.
        assert_eq!(Nat::from_limbs(vec![7, 0]).limbs(), &[7]);
    }

    #[test]
    fn to_u64_is_checked_never_wrapping() {
        assert_eq!(Nat::from_u64(0).to_u64(), Some(0));
        assert_eq!(Nat::from_u64(u64::MAX).to_u64(), Some(u64::MAX));
        // 2^64: one limb too many. Refused, not wrapped to 0.
        assert_eq!(Nat::from_limbs(vec![0, 1]).to_u64(), None);
    }

    #[test]
    fn bit_length_is_exact_at_the_limb_boundary() {
        assert_eq!(Nat::ZERO.bit_length(), 0);
        assert_eq!(Nat::from_u64(1).bit_length(), 1);
        assert_eq!(Nat::from_u64(u64::MAX).bit_length(), 64);
        assert_eq!(Nat::from_limbs(vec![0, 1]).bit_length(), 65);
    }

    #[test]
    fn order_is_natural_number_order() {
        let two_64 = Nat::from_limbs(vec![0, 1]);
        assert!(Nat::from_u64(u64::MAX) < two_64);
        assert!(two_64 > Nat::ZERO);
        assert_eq!(two_64.cmp(&two_64), Ordering::Equal);
        // Equal limb counts: most significant limb decides.
        assert!(Nat::from_limbs(vec![9, 1]) < Nat::from_limbs(vec![0, 2]));
        // Same top limb: lower limb decides.
        assert!(Nat::from_limbs(vec![1, 1]) < Nat::from_limbs(vec![2, 1]));
    }

    #[test]
    fn debug_prints_the_decimal_value() {
        let two_128 = Nat::from_limbs(vec![0, 0, 1]);
        assert_eq!(
            std::format!("{two_128:?}"),
            "Nat(340282366920938463463374607431768211456)"
        );
    }
}
