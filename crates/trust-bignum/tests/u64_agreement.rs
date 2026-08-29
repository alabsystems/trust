// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! On the domain `Nat` shares with `u64`, every operation must agree with
//! hardware arithmetic — hardware is the independent reference this crate did
//! not write. Sums and products are compared in `u128`, where they are always
//! exact for `u64` operands, so nothing here depends on the crate under test.
//!
//! The sweep runs a fixed boundary set crossed with a deterministic xorshift64
//! sequence — no external property-testing dependency, same coverage idea.

use trust_bignum::Nat;

/// Boundary values plus a deterministic pseudo-random sweep.
fn interesting_u64s() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        2,
        3,
        9,
        10,
        63,
        64,
        255,
        256,
        999,
        1_000,
        u64::from(u32::MAX) - 1,
        u64::from(u32::MAX),
        u64::from(u32::MAX) + 1,
        10_000_000_000_000_000_000, // 10^19, the decimal chunk size
        u64::MAX - 1,
        u64::MAX,
    ];
    // xorshift64: deterministic, seeds the sweep with spread-out magnitudes.
    let mut state = 0x243F_6A88_85A3_08D3_u64; // pi digits, nothing up the sleeve
    for _ in 0..60 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        values.push(state);
        values.push(state >> 32); // also cover the small half of the range
    }
    values
}

#[test]
fn add_agrees_with_u128_hardware_on_the_shared_domain() {
    for &a in &interesting_u64s() {
        for &b in &interesting_u64s() {
            let expected = u128::from(a) + u128::from(b);
            let got = Nat::from_u64(a).add(&Nat::from_u64(b));
            assert_eq!(got.to_decimal(), expected.to_string(), "{a} + {b}");
        }
    }
}

#[test]
fn sub_agrees_with_u64_saturating_sub_on_the_shared_domain() {
    // Lean's truncated Nat.sub restricted to u64 IS u64::saturating_sub.
    for &a in &interesting_u64s() {
        for &b in &interesting_u64s() {
            let got = Nat::from_u64(a).sub(&Nat::from_u64(b));
            assert_eq!(got.to_u64(), Some(a.saturating_sub(b)), "{a} - {b}");
            // And the checked lane against u64's checked lane.
            let got = Nat::from_u64(a).checked_sub(&Nat::from_u64(b));
            assert_eq!(got.map(|n| n.to_u64()), a.checked_sub(b).map(Some), "{a} -? {b}");
        }
    }
}

#[test]
fn mul_agrees_with_u128_hardware_on_the_shared_domain() {
    for &a in &interesting_u64s() {
        for &b in &interesting_u64s() {
            let expected = u128::from(a) * u128::from(b);
            let got = Nat::from_u64(a).mul(&Nat::from_u64(b));
            assert_eq!(got.to_decimal(), expected.to_string(), "{a} * {b}");
        }
    }
}

#[test]
fn div_and_rem_agree_with_hardware_for_nonzero_divisors() {
    for &a in &interesting_u64s() {
        for &b in &interesting_u64s() {
            if b == 0 {
                // The one point where Lean and Rust semantics part ways —
                // pinned in tests/lean_semantics.rs, asserted here so the
                // sweep states it too rather than skipping silently.
                assert_eq!(Nat::from_u64(a).div(&Nat::ZERO), Nat::ZERO);
                assert_eq!(Nat::from_u64(a).rem(&Nat::ZERO), Nat::from_u64(a));
                continue;
            }
            let (q, r) = Nat::from_u64(a).div_rem(&Nat::from_u64(b));
            assert_eq!(q.to_u64(), Some(a / b), "{a} / {b}");
            assert_eq!(r.to_u64(), Some(a % b), "{a} % {b}");
        }
    }
}

#[test]
fn comparison_and_equality_agree_with_u64() {
    for &a in &interesting_u64s() {
        for &b in &interesting_u64s() {
            assert_eq!(Nat::from_u64(a).cmp(&Nat::from_u64(b)), a.cmp(&b), "cmp({a}, {b})");
            assert_eq!(Nat::from_u64(a) == Nat::from_u64(b), a == b, "eq({a}, {b})");
        }
    }
}

#[test]
fn u64_round_trip_is_the_identity() {
    for &a in &interesting_u64s() {
        assert_eq!(Nat::from_u64(a).to_u64(), Some(a));
        assert_eq!(Nat::from(a), Nat::from_u64(a));
    }
}

#[test]
fn decimal_agrees_with_u64_formatting_and_parsing() {
    for &a in &interesting_u64s() {
        assert_eq!(Nat::from_u64(a).to_decimal(), a.to_string());
        assert_eq!(Nat::from_decimal(&a.to_string()), Ok(Nat::from_u64(a)));
    }
}

/// Algebraic identities on values just past the shared domain, where hardware
/// can no longer be the reference — the identities themselves are.
#[test]
fn algebraic_identities_hold_past_u64() {
    let mut state = 0x1319_8A2E_0370_7344_u64; // more pi
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..40 {
        let a = Nat::from_limbs(vec![next(), next(), next() % 4]);
        let b = Nat::from_limbs(vec![next(), next() % 16]);
        // Commutativity.
        assert_eq!(a.add(&b), b.add(&a));
        assert_eq!(a.mul(&b), b.mul(&a));
        // Add/sub cancel on the defined domain (a + b >= b always).
        assert_eq!(a.add(&b).sub(&b), a);
        // Distributivity ties mul to add.
        let c = Nat::from_u64(next());
        assert_eq!(a.add(&b).mul(&c), a.mul(&c).add(&b.mul(&c)));
        // Division reconstructs.
        if !b.is_zero() {
            let (q, r) = a.div_rem(&b);
            assert_eq!(b.mul(&q).add(&r), a);
            assert!(r < b);
        }
        // Decimal round trip.
        assert_eq!(Nat::from_decimal(&a.to_decimal()), Ok(a.clone()));
    }
}
