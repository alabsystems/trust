// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CONTROL (e) — THE BIGNUM CARRIER (I6).
//!
//! `Nat`'s default carrier is the Trust-owned bignum runtime,
//! `trust_bignum::Nat` (`Ty::BignumNat`). This control pins the GRANT and,
//! more importantly, the four boundaries the grant must not move:
//!
//! 1. `Nat` at a **fixed width** stays `Narrowing` — forever. The grant is at
//!    the exact unbounded type only; a width request is never "close enough".
//! 2. `Int` did not ride along — a ℕ runtime is not a ℤ carrier, and that
//!    holds even when `trust_bignum::Nat` is requested by name.
//! 3. The witness says what it rests on: `TrustedRuntimeAgreement`, an
//!    unbounded-exact width — a TCB disclosure, not a proof claim.
//! 4. The refusal that used to say "wait for the bignum carrier" now carries
//!    the fix (v7/D3): take the default carrier, with no source change.

use clean_kernel::{Expr, Name};
use trust_clean_carrier::{
    carrier_at, carrier_for, carrier_signature_for, CarrierRefused,
};
use trust_symbols::{CarrierEvidence, CarrierWidth};
use trust_types::Ty;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

// ---------------------------------------------------------------------------
// 1. The grant
// ---------------------------------------------------------------------------

#[test]
fn nat_default_carrier_is_the_bignum_runtime() {
    let carrier = carrier_for(&c("Nat")).expect("I6: Nat has a default carrier");
    assert_eq!(carrier.rust(), &Ty::BignumNat);
    assert_eq!(carrier.evidence(), CarrierEvidence::Total);
    assert_eq!(carrier.witness().clean_type(), "Nat");
    assert_eq!(carrier.witness().rust_carrier(), "trust_bignum::Nat");
    assert_eq!(carrier.witness().width(), CarrierWidth::UnboundedExact);
    // The witness discloses the trust basis in its own rendering.
    assert!(
        carrier.witness().to_string().contains("trusted runtime"),
        "the witness must say it rests on a trusted runtime: {}",
        carrier.witness()
    );
}

#[test]
fn nat_at_the_exact_bignum_request_grants_too() {
    // The requested-type lane agrees with the default lane on the exact type —
    // the same one-decision-procedure property every other grant has.
    let at = carrier_at(&c("Nat"), &Ty::BignumNat).expect("the exact request is the default");
    let default = carrier_for(&c("Nat")).expect("granted above");
    assert_eq!(at, default, "the two lanes must produce the SAME carrier");
}

#[test]
fn nat_to_nat_signature_is_bignum_in_every_position() {
    let sig = carrier_signature_for(&Expr::arrow(c("Nat"), c("Nat")))
        .expect("Nat -> Nat carries positionally");
    assert_eq!(sig.arity(), 1);
    assert_eq!(*sig.arguments()[0].rust(), Ty::BignumNat);
    assert_eq!(*sig.result().rust(), Ty::BignumNat);
    assert_eq!(sig.witnesses().count(), 2);
    assert!(sig.witnesses().all(|w| w.width() == CarrierWidth::UnboundedExact));
}

#[test]
fn mixed_nat_and_uint64_signature_carries_positionally() {
    let sig = carrier_signature_for(&Expr::arrow(c("Nat"), c("UInt64")))
        .expect("Nat -> UInt64: each position takes its own exact carrier");
    assert_eq!(*sig.arguments()[0].rust(), Ty::BignumNat);
    assert_eq!(*sig.result().rust(), u64_ty());
    // ... and the two witnesses carry DIFFERENT width kinds, honestly.
    assert_eq!(sig.arguments()[0].witness().width(), CarrierWidth::UnboundedExact);
    assert_eq!(sig.result().witness().width(), CarrierWidth::Bits(64));
}

// ---------------------------------------------------------------------------
// 2. The boundaries that must not move
// ---------------------------------------------------------------------------

#[test]
fn nat_at_u64_stays_narrowing_forever() {
    // THE ratchet that must never flip: the bignum grant is at the exact
    // unbounded type; a fixed-width request is still the miscompile, refused.
    for width in [8_u32, 16, 32, 64] {
        let err = carrier_at(&c("Nat"), &Ty::Int { width, signed: false })
            .expect_err("Nat at a fixed width is a narrowing, bignum carrier or not");
        assert!(matches!(err, CarrierRefused::Narrowing { .. }), "{err:?}");
    }
}

#[test]
fn int_gets_nothing_even_when_the_bignum_is_requested_by_name() {
    // A ℕ runtime is not a ℤ carrier. `Int` has no exact carrier, so the
    // unbounded-exact lane cannot fire for it — and trust-symbols' pinned
    // pairing table refuses `("Int", "trust_bignum::Nat")` independently,
    // so editing THIS crate's table alone could not change the answer.
    let err = carrier_at(&c("Int"), &Ty::BignumNat)
        .expect_err("Int at trust_bignum::Nat must be refused");
    assert!(matches!(err, CarrierRefused::Interpretation { .. }), "{err:?}");
    assert!(carrier_for(&c("Int")).is_err(), "Int has no default carrier either");
}

#[test]
fn a_fixed_width_clean_type_is_not_carried_by_the_bignum() {
    // The other direction of the same rule: `UInt64` at `trust_bignum::Nat`
    // preserves every value but not the wrap modulus — refused, naming the
    // exact carrier.
    let err = carrier_at(&c("UInt64"), &Ty::BignumNat)
        .expect_err("UInt64's carrier is u64, not the bignum");
    assert!(matches!(err, CarrierRefused::Interpretation { .. }), "{err:?}");
    assert!(err.to_string().contains("u64"), "must name the exact carrier: {err}");
}

// ---------------------------------------------------------------------------
// 3. The refusal texts carry the fix (v7/D3)
// ---------------------------------------------------------------------------

#[test]
fn the_nat_narrowing_refusal_now_offers_the_bignum_fix() {
    let err = carrier_at(&c("Nat"), &u64_ty()).expect_err("still refused");
    let text = err.to_string();
    assert!(
        text.contains("trust_bignum::Nat"),
        "the refusal must offer the carrier that exists now: {text}"
    );
    assert!(!text.contains("NOT currently an option"), "the stale text must be gone: {text}");
    assert!(text.contains("options:"), "v7/D3: {text}");
}

#[test]
fn a_fixed_width_narrowing_is_not_offered_the_bignum_fix() {
    // Amendment 8's guard, exercised: `UInt64 -> u32` is a machine-width
    // narrowing whose fixes are the width options; offering the bignum there
    // would be a wrong fix.
    let err = carrier_at(&c("UInt64"), &Ty::Int { width: 32, signed: false })
        .expect_err("UInt64 -> u32 is a narrowing");
    let text = err.to_string();
    assert!(matches!(err, CarrierRefused::Narrowing { .. }), "{err:?}");
    assert!(
        !text.contains("trust_bignum::Nat"),
        "a fixed-width narrowing must not be offered the bignum: {text}"
    );
}

#[test]
fn the_int_narrowing_refusal_names_the_boundary_not_a_wrong_fix() {
    // `Int -> i64`: unbounded narrowing, but the bignum is NOT its fix.
    let err = carrier_at(&c("Int"), &Ty::Int { width: 64, signed: true })
        .expect_err("Int -> i64 is refused");
    let text = err.to_string();
    assert!(matches!(err, CarrierRefused::Narrowing { .. }), "{err:?}");
    assert!(
        !text.contains("take `Nat`'s default carrier"),
        "Int must not be told to take the Nat carrier as ITS fix: {text}"
    );
    assert!(
        text.contains("carries `Nat`"),
        "the boundary — the bignum carries Nat only — should be stated: {text}"
    );
}
