//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I6 ACCEPTANCE — THE `Nat` PROJECTION.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §5b.)
//!
//! The island below is BYTE-IDENTICAL to a `def` that refused at I5: `Nat` had
//! no carrier, `carrier_signature_for` returned the `NoTotalCarrier` refusal,
//! and a call produced `E0425` with the "no bignum carrier in this toolchain
//! today" note. That identity is the acceptance criterion — nothing about the
//! declaration changed; the TOOLCHAIN grew the carrier:
//!
//!   * `trust_bignum::Nat` (crates/trust-bignum) is the runtime, shipped into
//!     the sysroot by `library/sysroot`;
//!   * the compiler injects the crate (`CStore::trust_load_bignum_carrier`,
//!     `CrateOrigin::Injected`, sysroot-residency-checked) when a mint carries
//!     `Nat`, and feeds `fn_sig` at the `Nat` ADT from the one stored `DefId`;
//!   * the emitted body is the same d01 projection every other carrier gets —
//!     `_0 = move _1; return` — and `Operand::Move` is load-bearing here for
//!     the first time: `Nat` is NOT `Copy`, so this fixture is also the probe
//!     that the emitter moves rather than copies a non-Copy carrier.
//!
//! Two values cross the boundary on purpose:
//!
//!   * a small one, whose round trip a fixed-width carrier could also have
//!     survived;
//!   * `2^64` exactly — one past `u64::MAX` — which no fixed-width carrier can
//!     represent. `Nat -> u64` narrowing stays REFUSED forever (I4's
//!     `Narrowing`, pinned by control_a and control_1); this value is the
//!     witness that the granted carrier is genuinely unbounded, not a clamped
//!     or wrapped 64-bit lane wearing a bignum name.
//!
//! `-Z trust-verify=off` mirrors `clean_origin_call_parity.rs`: the mint, the
//! injection, the emission and the faithfulness gate must all run WITHOUT the
//! verifier switched on — the gate is not allowed to hide behind the switch.
//! The verify-on measurement is the sibling's job (see
//! `clean_origin_verify_on.rs` for the u64 precedent).

extern crate trust_bignum;

mod m {
    clean {
        def keep (n : Nat) : Nat := n
    }
}

fn main() {
    // The small value. `from_u64` is total; `to_u64` is the checked direction.
    let small = trust_bignum::Nat::from_u64(3);
    let out = crate::m::keep(small);
    assert_eq!(out.to_u64(), Some(3), "the emitted body must be the identity projection");

    // 2^64 — representable by NO fixed-width carrier this compiler can grant.
    let big = trust_bignum::Nat::from_decimal("18446744073709551616")
        .expect("a decimal numeral one past u64::MAX parses");
    let expected = trust_bignum::Nat::from_decimal("18446744073709551616").unwrap();
    let out = crate::m::keep(big);
    assert_eq!(
        out.to_u64(),
        None,
        "a value past u64::MAX must come back unclamped and unwrapped — \
         Some(_) here means a 64-bit lane is impersonating the bignum carrier"
    );
    assert_eq!(out, expected, "the projection must return the argument value unchanged");
    assert_eq!(out.to_decimal(), "18446744073709551616");
}
