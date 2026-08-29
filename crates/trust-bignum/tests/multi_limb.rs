// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Every operation exercised on values strictly above 2^64, where the limb
//! machinery (carry, borrow, cross products, shift-subtract) is actually in
//! play. References are u128 hardware where the result fits, and definitional
//! limb layouts (`from_limbs`) where it does not — never the crate against
//! itself.

use trust_bignum::Nat;

fn nat(text: &str) -> Nat {
    Nat::from_decimal(text).expect("test constant must parse")
}

const TWO_64: &str = "18446744073709551616";
const TWO_128: &str = "340282366920938463463374607431768211456";

#[test]
fn add_multi_limb_with_full_carry_propagation() {
    // (2^128 - 1) + 1 = 2^128: the carry must ripple through two MAX limbs.
    let a = Nat::from_limbs(vec![u64::MAX, u64::MAX]);
    assert_eq!(a.add(&Nat::from_u64(1)), nat(TWO_128));
    // Mixed widths: 2^128 + u64::MAX, reference in exact decimal.
    assert_eq!(
        nat(TWO_128).add(&Nat::from_u64(u64::MAX)).to_decimal(),
        "340282366920938463481821351505477763071" // 2^128 + 2^64 - 1
    );
}

#[test]
fn sub_multi_limb_with_full_borrow_propagation() {
    // 2^128 - 1: the borrow must ripple through two zero limbs.
    assert_eq!(nat(TWO_128).sub(&Nat::from_u64(1)), Nat::from_limbs(vec![u64::MAX, u64::MAX]));
    // 2^128 - 2^64 = [0, MAX] by the limb layout definition.
    assert_eq!(nat(TWO_128).sub(&nat(TWO_64)), Nat::from_limbs(vec![0, u64::MAX]));
    // Truncation with multi-limb operands on BOTH sides.
    assert_eq!(nat(TWO_64).sub(&nat(TWO_128)), Nat::ZERO);
    assert_eq!(nat(TWO_64).checked_sub(&nat(TWO_128)), None);
}

#[test]
fn mul_multi_limb_cross_products() {
    // 2^64 * 2^64 = 2^128 — the pure cross-limb product.
    assert_eq!(nat(TWO_64).mul(&nat(TWO_64)), nat(TWO_128));
    // (2^64 - 1) * (2^64 + 1) = 2^128 - 1 — fits u128, hardware reference.
    let expected = u128::MAX; // 2^128 - 1
    assert_eq!(
        Nat::from_u64(u64::MAX).mul(&nat("18446744073709551617")).to_decimal(),
        expected.to_string()
    );
    // A cross-limb square past u128: 2^128 * 2^128 = 2^256, against the
    // well-known decimal expansion of 2^256.
    assert_eq!(
        nat(TWO_128).mul(&nat(TWO_128)).to_decimal(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639936"
    );
}

#[test]
fn div_multi_limb_both_lanes() {
    // Single-limb divisor lane: (2^128 - 1) / 7 — fits u128, hardware reference.
    let x = Nat::from_limbs(vec![u64::MAX, u64::MAX]);
    let (q, r) = x.div_rem(&Nat::from_u64(7));
    assert_eq!(q.to_decimal(), (u128::MAX / 7).to_string());
    assert_eq!(r.to_decimal(), (u128::MAX % 7).to_string());
    // Multi-limb divisor lane (shift-subtract): 2^128 / 2^64 = 2^64.
    assert_eq!(nat(TWO_128).div(&nat(TWO_64)), nat(TWO_64));
    // Non-trivial multi-limb divisor, reconstruction is the proof.
    let d = Nat::from_limbs(vec![12345, 67890]);
    let (q, r) = x.div_rem(&d);
    assert_eq!(d.mul(&q).add(&r), x);
    assert!(r < d);
}

#[test]
fn rem_multi_limb_including_the_zero_divisor_verdict() {
    // (2^128) % (2^64 + 1): 2^128 = (2^64+1)(2^64-1) + 1, so remainder 1.
    assert_eq!(nat(TWO_128).rem(&nat("18446744073709551617")), Nat::from_u64(1));
    // Lean zero-divisor verdict with a multi-limb dividend.
    assert_eq!(nat(TWO_128).rem(&Nat::ZERO), nat(TWO_128));
    assert_eq!(nat(TWO_128).div(&Nat::ZERO), Nat::ZERO);
}

#[test]
fn comparison_multi_limb() {
    assert!(nat(TWO_128) > nat(TWO_64));
    assert!(nat(TWO_64) < nat("18446744073709551617"));
    // Same limb count, decided below the top limb.
    assert!(Nat::from_limbs(vec![1, 7]) < Nat::from_limbs(vec![2, 7]));
    assert_eq!(nat(TWO_128), Nat::from_limbs(vec![0, 0, 1]));
}

#[test]
fn to_u64_refuses_multi_limb_values() {
    assert_eq!(nat(TWO_64).to_u64(), None);
    assert_eq!(nat(TWO_128).to_u64(), None);
    assert_eq!(nat(TWO_64).sub(&Nat::from_u64(1)).to_u64(), Some(u64::MAX));
}

#[test]
fn decimal_round_trip_multi_limb() {
    // A 100-digit value: parse, round trip, and survive arithmetic.
    let hundred_digits = "1234567890".repeat(10);
    let n = nat(&hundred_digits);
    assert_eq!(n.to_decimal(), hundred_digits);
    assert_eq!(n.limbs().len(), 6, "a 100-digit value is six limbs");
    // Round trip composes with arithmetic: (n * 10^19 + 7) renders as the
    // digits of n followed by eighteen zeros and a 7.
    let shifted = n.mul(&nat("10000000000000000000")).add(&Nat::from_u64(7));
    assert_eq!(shifted.to_decimal(), format!("{hundred_digits}0000000000000000007"));
}
