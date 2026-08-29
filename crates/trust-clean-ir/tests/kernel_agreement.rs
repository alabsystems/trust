// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! THE KERNEL AGREEMENT CHECK for the Clean -> TrustIR lane.
//!
//! The sibling test file executes the emitted TrustIR and compares against what
//! the declaration means *according to this test's author*. That catches a lot,
//! but the expected value is written by the same hand that wrote the emitter,
//! so it is not an independent verdict.
//!
//! This file removes the author from the loop. For concrete inputs it:
//!
//!   1. runs the emitted TrustIR through `trust_ir::interpret` — TrustIR's own
//!      reference interpreter — to get a value `v`;
//!   2. asks the CIC KERNEL to reduce the Clean application `f a₀ … aₙ` in the
//!      island environment, via `trust_certify::clean_island::
//!      unfold_island_application`, which type-checks the application against
//!      the definition's Pi telescope and reduces with the kernel's own WHNF;
//!   3. checks `f a₀ … aₙ ≡ <v at the carrier>` by kernel DEFINITIONAL
//!      EQUALITY (`TypeChecker::is_def_eq`).
//!
//! Nothing in that loop is this crate's code. Both oracles predate it and
//! neither was written against it.
//!
//! # What this establishes, and what it does not
//!
//! It is a POINTWISE agreement check, not the faithfulness gate. It witnesses
//! that emitted TrustIR and the Clean `def` agree at the inputs tried; it does
//! not quantify over all inputs, and it does not reflect the emitted body back
//! into a Clean term the way `trust-clean-origin::admit_lowering` does for MIR.
//! A body that agrees on every input tried here and diverges elsewhere would
//! pass. That is a real gap and it is why the crate's `GATING` section still
//! says this lane is not proof-carrying.
//!
//! What it does buy is the property that matters most in practice for the one
//! direction that PRODUCES A VALUE: a wrong-argument projection, an inverted de
//! Bruijn index, a signed-for-unsigned predicate, a swapped select arm, or a
//! non-wrapping add cannot survive it, because the kernel disagrees at the
//! first input that distinguishes them.

use clean_kernel::{Environment, Expr, Name, TypeChecker};
use trust_certify::clean_island::unfold_island_application;
use trust_clean_ir::emit_clean_origin_function;
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// `UInt64.ofNat n` — the carrier-typed Clean value for a `u64`.
fn uint64(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), Expr::nat_lit(n))
}

/// Run the emitted TrustIR at `args`, then require the KERNEL to agree.
///
/// Returns the interpreter's value so a caller can additionally pin it, but the
/// assertion that matters is the defeq one: it is the kernel, not this test,
/// that decides whether the emitted body computed the declaration.
fn kernel_agrees(decl: &str, name: &str, args: &[u64]) -> u64 {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).expect("the declaration must plan");
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
        .expect("the shape must be spelled by this producer");

    // ── side 1: what the emitted TrustIR computes ──────────────────────────
    let interp = Interpreter::new();
    let values: Vec<_> = args
        .iter()
        .map(|a| InterpretValue::int(Ty::U64, i128::from(*a)).expect("u64 argument"))
        .collect();
    let outcome = interp.execute_function(&f, values).expect("the emitted TrustIR must execute");
    let produced =
        u64::try_from(outcome.returns[0].as_int().expect("an integer result").as_unsigned())
            .expect("a u64 carrier result");

    // ── side 2: what the KERNEL says the declaration is at those inputs ────
    let kernel_args: Vec<Expr> = args.iter().copied().map(uint64).collect();
    let reduced = unfold_island_application(&env, name, &kernel_args)
        .expect("the application must type-check and unfold in the island environment");

    // ── the agreement, decided by the kernel ───────────────────────────────
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&reduced, &uint64(produced)),
        "KERNEL DISAGREEMENT for `{name}` at {args:?}: the emitted TrustIR computed {produced}, \
         but the kernel reduced the Clean application to a term not definitionally equal to \
         `UInt64.ofNat {produced}`. This is a wrong binary, not a failed proof — the emitted \
         body and the Clean `def` denote different functions.\n  reduced: {reduced:?}"
    );
    produced
}

#[test]
fn kernel_agrees_with_emitted_projection() {
    assert_eq!(
        kernel_agrees("def pick (a : UInt64) (b : UInt64) : UInt64 := a", "pick", &[7, 9]),
        7
    );
    assert_eq!(kernel_agrees("def snd (a : UInt64) (b : UInt64) : UInt64 := b", "snd", &[7, 9]), 9);
}

#[test]
fn kernel_agrees_with_emitted_constant() {
    assert_eq!(kernel_agrees("def seven (a : UInt64) : UInt64 := 7", "seven", &[3]), 7);
}

#[test]
fn kernel_agrees_with_emitted_arithmetic_including_the_wrap() {
    let add = "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b";
    assert_eq!(kernel_agrees(add, "sum", &[2, 3]), 5);
    // The wrap decided by the KERNEL rather than by this test's arithmetic:
    // Clean `UInt64` addition wraps at 2^64, and if the emitted TrustIR did
    // anything else the defeq fails here.
    assert_eq!(kernel_agrees(add, "sum", &[u64::MAX, 1]), 0);

    let sub = "def diff (a : UInt64) (b : UInt64) : UInt64 := a - b";
    assert_eq!(kernel_agrees(sub, "diff", &[9, 4]), 5);
    assert_eq!(kernel_agrees(sub, "diff", &[0, 1]), u64::MAX);
}

#[test]
fn kernel_agrees_with_emitted_composition() {
    let comp = "def comp (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a";
    assert_eq!(kernel_agrees(comp, "comp", &[3, 4]), 21);
    assert_eq!(kernel_agrees(comp, "comp", &[0, 5]), 0);
}

#[test]
fn kernel_agrees_with_emitted_select_on_both_branches_and_the_high_bit() {
    let minu = "def minu (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b";
    assert_eq!(kernel_agrees(minu, "minu", &[3, 9]), 3);
    assert_eq!(kernel_agrees(minu, "minu", &[9, 3]), 3);
    assert_eq!(kernel_agrees(minu, "minu", &[5, 5]), 5);
    // The unsigned/signed distinction, decided by the kernel: Clean `UInt64`
    // `<` is unsigned, so the minimum of (MAX, 1) is 1. An emitted `Slt` would
    // answer MAX and the kernel would reject it here.
    assert_eq!(kernel_agrees(minu, "minu", &[u64::MAX, 1]), 1);
}

/// **The gate is not vacuous.**
///
/// Every assertion above passes. That is only evidence if the same check would
/// FAIL on a wrong answer — a defeq that returns `true` for everything would
/// look identical from the outside. So this drives the kernel comparison
/// directly with values the emitted body did not produce and requires the
/// kernel to reject them.
///
/// This is the control for the whole file. If it ever passes with the
/// assertions inverted, the agreement checks above are measuring nothing.
#[test]
fn the_kernel_check_rejects_wrong_answers() {
    let decl = "def minu (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b";
    let env = env_with(decl);
    let tc = TypeChecker::new(&env);

    let args = [3u64, 9u64];
    let kernel_args: Vec<Expr> = args.iter().copied().map(uint64).collect();
    let reduced = unfold_island_application(&env, "minu", &kernel_args).expect("unfolds");

    // The right answer is accepted...
    assert!(tc.is_def_eq(&reduced, &uint64(3)), "the correct value must be accepted");

    // ...and these are the exact wrong answers the plausible bugs produce.
    for (wrong, bug) in [
        (9u64, "returning the OTHER argument — an inverted de Bruijn index"),
        (4u64, "an off-by-one"),
        (0u64, "a zero/uninitialised result"),
        (u64::MAX, "a signed comparison reading the high bit as negative"),
    ] {
        assert!(
            !tc.is_def_eq(&reduced, &uint64(wrong)),
            "the kernel must REJECT {wrong} for minu(3, 9) — otherwise this file's agreement \
             checks would pass for a body with the bug: {bug}"
        );
    }
}

/// The same control at the wrapping boundary, where the arithmetic is least
/// intuitive and a producer is most likely to be wrong: `MAX + 1` is `0` in
/// Clean `UInt64`, and `MAX`, `1`, and `2^64` spellings must not be accepted
/// in its place.
#[test]
fn the_kernel_check_rejects_wrong_answers_at_the_wrap() {
    let decl = "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b";
    let env = env_with(decl);
    let tc = TypeChecker::new(&env);

    let kernel_args = vec![uint64(u64::MAX), uint64(1)];
    let reduced = unfold_island_application(&env, "sum", &kernel_args).expect("unfolds");

    assert!(tc.is_def_eq(&reduced, &uint64(0)), "MAX + 1 wraps to 0 in Clean UInt64");
    for wrong in [1u64, u64::MAX, 2] {
        assert!(
            !tc.is_def_eq(&reduced, &uint64(wrong)),
            "the kernel must REJECT {wrong} for sum(MAX, 1); a saturating or trapping emission \
             would produce exactly these"
        );
    }
}

// ─── EXHAUSTIVE agreement at a narrow carrier ──────────────────────────────
//
// Everything above is POINTWISE: it witnesses agreement at inputs someone chose,
// and a body that agrees there and diverges elsewhere would pass. At `UInt8` the
// carrier is finite, so that gap closes by construction — checking all 256 (or
// all 65 536) inputs is quantification over the ENTIRE domain of the type, not a
// sample of it.
//
// This is not a proof for `UInt64`: it establishes the emitted body computes the
// declaration for every `u8` input, not for every width. But for these
// declarations the emitted TrustIR is width-parametric — the same shape arm, with
// the width read from the carrier signature — so an arm that is right at `u8` for
// every input and wrong at `u64` has to be wrong in the width mapping
// specifically, which `clean_carrier_width_selects_the_trust_ir_type` pins
// separately.

fn uint8(n: u8) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt8.ofNat"), vec![]), Expr::nat_lit(u64::from(n)))
}

/// Emit once, then check EVERY input of the `UInt8` domain against the kernel.
fn exhaustive_u8_unary(decl: &str, name: &str) {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).expect("plans");
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0)).expect("emits");
    let interp = Interpreter::new();
    let tc = TypeChecker::new(&env);

    for a in 0u8..=u8::MAX {
        let arg = InterpretValue::int(Ty::U8, i128::from(a)).expect("u8 argument");
        let outcome = interp.execute_function(&f, vec![arg]).expect("executes");
        let produced = u8::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
            .expect("u8 result");

        let reduced = unfold_island_application(&env, name, &[uint8(a)]).expect("unfolds");
        assert!(
            tc.is_def_eq(&reduced, &uint8(produced)),
            "KERNEL DISAGREEMENT for `{name}`({a}): emitted TrustIR computed {produced}, which \
             is not definitionally equal to what the kernel reduced the Clean application to"
        );
    }
}

#[test]
fn exhaustive_u8_projection_agrees_on_every_input() {
    exhaustive_u8_unary("def idu (a : UInt8) : UInt8 := a", "idu");
}

#[test]
fn exhaustive_u8_constant_agrees_on_every_input() {
    exhaustive_u8_unary("def k (a : UInt8) : UInt8 := 200", "k");
}

/// Every input where the wrap actually bites: `a + 200` wraps for all
/// `a > 55`, so this covers both sides of the boundary exhaustively.
#[test]
fn exhaustive_u8_wrapping_add_agrees_on_every_input() {
    exhaustive_u8_unary("def bump (a : UInt8) : UInt8 := a + 200", "bump");
}

/// The whole 2-argument domain: 65 536 inputs, each decided by the kernel.
/// This is the strongest statement this file makes — for `minu` at `UInt8`
/// there is no input at which the emitted TrustIR and the Clean `def` differ.
#[test]
fn exhaustive_u8_select_agrees_on_the_entire_two_argument_domain() {
    let decl = "def minu8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b";
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, "minu8").expect("plans");
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0)).expect("emits");
    let interp = Interpreter::new();
    let tc = TypeChecker::new(&env);

    for a in 0u8..=u8::MAX {
        for b in 0u8..=u8::MAX {
            let args = vec![
                InterpretValue::int(Ty::U8, i128::from(a)).expect("u8"),
                InterpretValue::int(Ty::U8, i128::from(b)).expect("u8"),
            ];
            let outcome = interp.execute_function(&f, args).expect("executes");
            let produced =
                u8::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
                    .expect("u8 result");

            let reduced =
                unfold_island_application(&env, "minu8", &[uint8(a), uint8(b)]).expect("unfolds");
            assert!(
                tc.is_def_eq(&reduced, &uint8(produced)),
                "KERNEL DISAGREEMENT for minu8({a}, {b}): emitted {produced}"
            );
        }
    }
}

/// The same exhaustive sweep at `UInt16`: all 65 536 inputs.
///
/// Why a second width rather than more declarations at one width. The claim
/// these arms rest on is that they are WIDTH-PARAMETRIC — one shape arm, with
/// the width read from the carrier signature — so being right at `u8` for every
/// input is evidence about the arm, not only about `u8`. That is an argument,
/// and an argument is worth testing. Running the identical sweep at a second
/// width turns "the arm should be width-parametric" into a measurement: a
/// width-mapping bug that happened to be invisible at 8 bits has a second
/// chance to show here, at a width with a different `ofNat` reduction and a
/// different wrap point.
fn exhaustive_u16_unary(decl: &str, name: &str) {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).expect("plans");
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0)).expect("emits");
    let interp = Interpreter::new();
    let tc = TypeChecker::new(&env);
    let uint16 = |n: u16| {
        Expr::app(
            Expr::const_(Name::from_string("UInt16.ofNat"), vec![]),
            Expr::nat_lit(u64::from(n)),
        )
    };

    for a in 0u16..=u16::MAX {
        let arg = InterpretValue::int(Ty::U16, i128::from(a)).expect("u16 argument");
        let outcome = interp.execute_function(&f, vec![arg]).expect("executes");
        let produced = u16::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
            .expect("u16 result");

        let reduced = unfold_island_application(&env, name, &[uint16(a)]).expect("unfolds");
        assert!(
            tc.is_def_eq(&reduced, &uint16(produced)),
            "KERNEL DISAGREEMENT for `{name}`({a}) at UInt16: emitted {produced}"
        );
    }
}

#[test]
fn exhaustive_u16_projection_agrees_on_every_input() {
    exhaustive_u16_unary("def idu16 (a : UInt16) : UInt16 := a", "idu16");
}

/// The wrap at a DIFFERENT boundary than the u8 sweep: `a + 60000` wraps for
/// all `a > 5535`. A width mapping that silently used 8 bits would compute a
/// different value for most of this domain.
#[test]
fn exhaustive_u16_wrapping_add_agrees_on_every_input() {
    exhaustive_u16_unary("def bump16 (a : UInt16) : UInt16 := a + 60000", "bump16");
}
