// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CONTROL (b) — THE DEFEQ-INSUFFICIENCY DEMONSTRATION.
//!
//! The decision doc's claim, verbatim:
//!
//! > Kernel defeq does NOT subsume representation faithfulness. A `Nat -> u64`
//! > extraction composed with a `u64 -> Nat` admission is **defeq-equal while
//! > the binary wraps**.
//!
//! This file is that claim executed, against the REAL
//! `clean_kernel::TypeChecker` — not a Rust imitation of definitional equality.
//! It establishes three things in order:
//!
//! 1. **The kernel is satisfied.** `UInt64.toNat (UInt64.ofNat (2^64))` is
//!    definitionally equal to `0`. The extraction (`Nat -> UInt64`) composed
//!    with the admission (`UInt64 -> Nat`) type-checks and reduces, and defeq
//!    says yes.
//! 2. **The value wrapped.** `2^64` and `0` are DIFFERENT Clean naturals — the
//!    kernel itself says they are not defeq — yet the round trip identifies
//!    them. So a gate that admits `Nat` at `u64` on the strength of a defeq
//!    check admits a term whose emitted value is wrong.
//! 3. **The carrier obligation is what catches it.** `carrier_at(Nat, u64)`
//!    refuses, and it refuses BEFORE any kernel gate runs.
//!
//! Step 3 is why I4 is not redundant with I5's gate: I5's gate can only ask
//! the kernel, and step 1 is what the kernel answers.

use clean_kernel::{BigNat, Environment, Expr, ExprKind, Literal, Name, TypeChecker};
use trust_clean_carrier::{carrier_at, CarrierRefused};
use trust_types::Ty;

/// `Nat`, the unbounded Clean natural.
fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// The Clean natural `2^64` — one past the largest `u64`.
fn two_to_the_64() -> Expr {
    // Little-endian limbs: 0 in the low word, 1 in the high word.
    Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(vec![0, 1]))))
}

/// `UInt64.toNat (UInt64.ofNat n)` — the extraction composed with the admission.
fn round_trip(n: Expr) -> Expr {
    let of_nat = Expr::const_(Name::from_string("UInt64.ofNat"), vec![]);
    let to_nat = Expr::const_(Name::from_string("UInt64.toNat"), vec![]);
    Expr::app(to_nat, Expr::app(of_nat, n))
}

fn env_with_uints() -> Environment {
    let mut env = Environment::new();
    env.init_uint_types().expect("UInt8/16/32/64 must initialize");
    env
}

#[test]
fn step_1_the_kernel_is_satisfied_by_the_wrapping_round_trip() {
    let env = env_with_uints();
    let tc = TypeChecker::new(&env);

    let wrapped = round_trip(two_to_the_64());
    let zero = Expr::nat_lit(0);

    assert!(
        tc.is_def_eq(&wrapped, &zero),
        "THE PREMISE OF THIS CONTROL FAILED: the kernel did not identify \
         `UInt64.toNat (UInt64.ofNat (2^64))` with `0`. If this ever fails, the \
         defeq-insufficiency argument needs re-deriving against the kernel as it \
         now behaves — do NOT weaken the assertion."
    );
}

#[test]
fn step_2_the_two_clean_values_are_not_equal() {
    let env = env_with_uints();
    let tc = TypeChecker::new(&env);

    assert!(
        !tc.is_def_eq(&two_to_the_64(), &Expr::nat_lit(0)),
        "`2^64` and `0` must be distinct Clean naturals — otherwise there is no \
         wrap to demonstrate"
    );

    // ... and yet their round trips are identified. That is the wrap, stated as
    // a kernel fact.
    assert!(
        tc.is_def_eq(&round_trip(two_to_the_64()), &round_trip(Expr::nat_lit(0))),
        "the `Nat -> u64 -> Nat` round trip must collapse `2^64` onto `0`"
    );
}

#[test]
fn step_3_the_carrier_obligation_catches_what_defeq_did_not() {
    // The kernel said yes (step 1). The carrier says no, and says so without
    // consulting the kernel at all.
    let refusal = carrier_at(&nat_ty(), &Ty::Int { width: 64, signed: false }).expect_err(
        "defeq passing on the round trip is exactly why the carrier obligation \
         is SEPARATE: `Nat -> u64` must still be refused",
    );

    assert!(
        matches!(refusal, CarrierRefused::Narrowing { .. }),
        "expected the narrowing refusal; got {refusal:?}"
    );
}

#[test]
fn step_4_a_defeq_only_gate_would_have_admitted_it() {
    // Spelled out as an executable statement of the counterfactual, so the
    // argument does not live only in a comment: a gate whose whole test is "does
    // the kernel accept the composed round trip" returns ADMIT here.
    let env = env_with_uints();
    let tc = TypeChecker::new(&env);

    let defeq_only_gate_admits =
        tc.is_def_eq(&round_trip(two_to_the_64()), &Expr::nat_lit(0));
    let carrier_gate_admits =
        carrier_at(&nat_ty(), &Ty::Int { width: 64, signed: false }).is_ok();

    assert!(defeq_only_gate_admits, "the defeq-only gate admits (step 1)");
    assert!(!carrier_gate_admits, "the carrier gate refuses (step 3)");
    assert_ne!(
        defeq_only_gate_admits, carrier_gate_admits,
        "the two gates must DISAGREE on this input — that disagreement IS the \
         proof that defeq does not subsume representation faithfulness"
    );
}

#[test]
fn step_5_the_out_of_range_value_is_named_with_its_width() {
    // A refusal about a specific out-of-range value must name the value and the
    // width (task rule; v7/D3). `2^64` at `u64`.
    let value = BigNat::from_limbs(vec![0, 1]);
    let refusal = trust_clean_carrier::representable_at(&value, 64)
        .expect_err("2^64 does not fit in 64 bits");
    let text = refusal.to_string();
    assert!(
        text.contains("18446744073709551616"),
        "the refusal must name the VALUE: {text}"
    );
    assert!(text.contains("64"), "the refusal must name the WIDTH: {text}");
    assert!(text.contains("options:"), "v7/D3: must offer options: {text}");
}
