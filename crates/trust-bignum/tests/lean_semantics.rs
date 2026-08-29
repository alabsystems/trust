// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The Lean `Nat` semantics, pinned case by case against the authoritative
//! definitions in `first-party/clean/crates/clean-kernel` (read 2026-08-19):
//!
//! * `src/micro/native.rs:157-161` — the micro reducer:
//!   `Nat.add`, `Nat.sub` (truncated), `Nat.mul`,
//!   `Nat.div` (`n/0 = 0`), `Nat.mod` (`n%0 = n`).
//! * `src/tc/reduction/nat.rs:258-275` — the main kernel lane: the same three
//!   verdicts via `saturating_sub_big` / `checked_div_big` / `checked_mod_big`.
//! * `src/expr/bignat_ops.rs:73-88` — the BigNat primitives those call, whose
//!   doc comments state the Lean 4 semantics explicitly.
//!
//! **These tests are the carrier's semantic contract.** If one of them fails
//! after an edit, the edit changed what an emitted binary computes for an
//! operation the kernel has already proved things about. That is a wrong
//! binary, not a red test to accommodate.

use trust_bignum::Nat;

fn nat(text: &str) -> Nat {
    Nat::from_decimal(text).expect("test constant must parse")
}

// ---------------------------------------------------------------------------
// Nat.sub — truncated at zero
// ---------------------------------------------------------------------------

/// `Nat.sub_eq_zero_of_le : n ≤ m → n - m = 0`.
/// Kernel: micro/native.rs:158 `if x >= y { x - y } else { BigUint::ZERO }`.
#[test]
fn sub_underflow_is_zero_never_a_panic_and_never_negative() {
    assert_eq!(Nat::from_u64(3).sub(&Nat::from_u64(5)), Nat::ZERO);
    assert_eq!(Nat::ZERO.sub(&Nat::from_u64(1)), Nat::ZERO);
    assert_eq!(Nat::ZERO.sub(&Nat::ZERO), Nat::ZERO);
    // Multi-limb underflow truncates identically — no partial borrow escapes.
    let huge = nat("340282366920938463463374607431768211456"); // 2^128
    assert_eq!(Nat::from_u64(u64::MAX).sub(&huge), Nat::ZERO);
    // Off-by-one at the boundary: (n) - (n+1) = 0, (n+1) - n = 1.
    let n = nat("18446744073709551615");
    let n1 = nat("18446744073709551616");
    assert_eq!(n.sub(&n1), Nat::ZERO);
    assert_eq!(n1.sub(&n), Nat::from_u64(1));
}

/// `Nat.sub_self : n - n = 0` — a genuine zero, not an underflow.
#[test]
fn sub_of_equal_values_is_a_real_zero() {
    let n = nat("99999999999999999999999999999999999999");
    assert_eq!(n.sub(&n), Nat::ZERO);
    // ... which checked_sub distinguishes from underflow:
    assert_eq!(n.checked_sub(&n), Some(Nat::ZERO));
    assert_eq!(n.checked_sub(&n.add(&Nat::from_u64(1))), None);
}

/// `Nat.sub_add_cancel : m ≤ n → n - m + m = n` — subtraction inverts
/// addition exactly on the non-truncated half of the domain.
#[test]
fn sub_add_cancel_on_the_defined_domain() {
    let n = nat("123456789012345678901234567890123456789");
    let m = nat("98765432109876543210");
    assert_eq!(n.sub(&m).add(&m), n);
}

// ---------------------------------------------------------------------------
// Nat.div / Nat.mod — total, with the zero-divisor verdicts
// ---------------------------------------------------------------------------

/// `Nat.div_zero : n / 0 = 0`.
/// Kernel: micro/native.rs:160; bignat_ops.rs:73-78 ("Returns 0 when other is
/// zero (Lean 4 semantics)").
#[test]
fn division_by_zero_returns_zero_exactly_as_lean_nat_div() {
    assert_eq!(Nat::ZERO.div(&Nat::ZERO), Nat::ZERO);
    assert_eq!(Nat::from_u64(5).div(&Nat::ZERO), Nat::ZERO);
    assert_eq!(Nat::from_u64(u64::MAX).div(&Nat::ZERO), Nat::ZERO);
    let huge = nat("340282366920938463463374607431768211455");
    assert_eq!(huge.div(&Nat::ZERO), Nat::ZERO);
}

/// `Nat.mod_zero : n % 0 = n`.
/// Kernel: micro/native.rs:161; bignat_ops.rs:83-88 ("Returns self when other
/// is zero (Lean 4 semantics)").
#[test]
fn mod_by_zero_returns_the_dividend_exactly_as_lean_nat_mod() {
    assert_eq!(Nat::ZERO.rem(&Nat::ZERO), Nat::ZERO);
    assert_eq!(Nat::from_u64(5).rem(&Nat::ZERO), Nat::from_u64(5));
    let huge = nat("340282366920938463463374607431768211455");
    assert_eq!(huge.rem(&Nat::ZERO), huge);
}

/// `Nat.div_add_mod : m * (n / m) + n % m = n` — and under the Lean
/// zero-divisor verdicts it holds for m = 0 too: `0 * 0 + n = n`.
#[test]
fn the_euclidean_identity_holds_for_every_divisor_including_zero() {
    let dividends = [
        Nat::ZERO,
        Nat::from_u64(1),
        Nat::from_u64(41),
        Nat::from_u64(u64::MAX),
        nat("18446744073709551616"),
        nat("123456789012345678901234567890123456789012345678901234567890"),
    ];
    let divisors = [
        Nat::ZERO, // the case Rust panics on and Lean defines
        Nat::from_u64(1),
        Nat::from_u64(2),
        Nat::from_u64(7),
        Nat::from_u64(u64::MAX),
        nat("18446744073709551616"),
        nat("99999999999999999999999999999"),
    ];
    for n in &dividends {
        for m in &divisors {
            let (q, r) = n.div_rem(m);
            assert_eq!(m.mul(&q).add(&r), *n, "m * (n/m) + n%m must equal n for n={n}, m={m}");
            if !m.is_zero() {
                assert!(r < *m, "n % m < m must hold for nonzero m (n={n}, m={m})");
            } else {
                assert_eq!(q, Nat::ZERO, "n / 0 = 0");
                assert_eq!(r, *n, "n % 0 = n");
            }
        }
    }
}

/// `Nat.div_one : n / 1 = n` and `Nat.mod_one : n % 1 = 0`.
#[test]
fn division_by_one_is_identity() {
    let n = nat("340282366920938463463374607431768211457");
    assert_eq!(n.div(&Nat::from_u64(1)), n);
    assert_eq!(n.rem(&Nat::from_u64(1)), Nat::ZERO);
}

/// `Nat.zero_div : 0 / n = 0` and `Nat.zero_mod : 0 % n = 0`.
#[test]
fn zero_divided_by_anything_is_zero() {
    for m in [Nat::ZERO, Nat::from_u64(7), nat("18446744073709551616")] {
        assert_eq!(Nat::ZERO.div(&m), Nat::ZERO);
        assert_eq!(Nat::ZERO.rem(&m), Nat::ZERO);
    }
}

// ---------------------------------------------------------------------------
// The checked variants — the Rust-shaped lane must refuse EXACTLY the cases
// where Lean's total functions and Rust's partial ones disagree.
// ---------------------------------------------------------------------------

#[test]
fn checked_variants_refuse_exactly_the_lean_divergence_points() {
    let a = Nat::from_u64(3);
    let b = Nat::from_u64(5);
    // Underflow: Lean truncates, Rust-shaped refuses.
    assert_eq!(a.checked_sub(&b), None);
    assert_eq!(a.sub(&b), Nat::ZERO);
    // Zero divisor: Lean defines, Rust-shaped refuses.
    assert_eq!(b.checked_div(&Nat::ZERO), None);
    assert_eq!(b.div(&Nat::ZERO), Nat::ZERO);
    assert_eq!(b.checked_rem(&Nat::ZERO), None);
    assert_eq!(b.rem(&Nat::ZERO), b);
    // Everywhere else the two lanes agree value-for-value.
    assert_eq!(b.checked_sub(&a), Some(b.sub(&a)));
    assert_eq!(b.checked_div(&a), Some(b.div(&a)));
    assert_eq!(b.checked_rem(&a), Some(b.rem(&a)));
}

// ---------------------------------------------------------------------------
// Comparison and equality — Nat.beq / Nat.blt / Nat.ble are ordinary ℕ order
// ---------------------------------------------------------------------------

#[test]
fn comparison_is_by_value_never_by_representation() {
    // The same value built three ways is one value.
    let via_decimal = nat("18446744073709551616");
    let via_limbs = Nat::from_limbs(vec![0, 1]);
    let via_arith = Nat::from_u64(u64::MAX).add(&Nat::from_u64(1));
    assert_eq!(via_decimal, via_limbs);
    assert_eq!(via_limbs, via_arith);
    // Order across a limb-count boundary.
    assert!(Nat::from_u64(u64::MAX) < via_decimal);
    assert!(via_decimal <= via_arith);
    assert!(nat("340282366920938463463374607431768211456") > via_decimal);
}
