// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 2 — THE FROZEN-R MUTATION FIXTURE.**
//!
//! The increment's own statement of what this file must establish:
//!
//! > a deliberate one-construct mistranslation injected into the LOWERING must
//! > be caught by the gate. **If it is not, R has been co-authored and the gate
//! > is decoration.**
//!
//! The gate compares two independently-produced terms:
//!
//! * **side A** — the Clean `def`'s own body, read out of the kernel
//!   `Environment`. It never passes through the lowering.
//! * **side B** — `R(lowered)`, the emitted body reflected back into Clean by
//!   the frozen R functor.
//!
//! This file builds a correct side B, checks the gate ADMITS it, then mutates
//! **one construct** and checks the gate REFUSES. Both halves are required: a
//! gate that refuses everything is as useless as one that admits everything,
//! and only the pair distinguishes a real decision from a constant function.
//!
//! # Scope, stated honestly
//!
//! Side B is constructed directly here rather than produced by a Clean->MIR
//! lowering, **because no such lowering exists** — see blocker 3 in the crate
//! docs. So this control establishes that **the gate catches a one-construct
//! mistranslation**; it does not establish that any real lowering is faithful,
//! because there is no real lowering to be faithful. When the lowering lands,
//! it feeds side B and this control becomes an end-to-end one with no change to
//! the gate.
//!
//! What it does establish is the property the whole lane rests on: the gate's
//! verdict tracks the CONTENT of the lowered body, so a lowering cannot slip a
//! mistranslation past it. That is exactly the claim that would be false if R
//! were co-authored against this lane.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING R
//!
//! `crates/trust-clean/src/reflect.rs` and `source_reflect.rs` are **frozen**
//! against this lane. If a future change makes the mutated body pass, the defect
//! is in the gate or in R — never in this fixture. Do not weaken an assertion,
//! and do not delete a case.

use clean_kernel::{BinderInfo, Environment, Expr, Name, TypeChecker};
use trust_clean_carrier::carrier_at;
use trust_clean_origin::{check_faithful, GateRefusal};
use trust_types::Ty;

/// `UInt64`, the Clean fixed-width type that actually carries.
fn uint64_ty() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

/// The carrier for `UInt64` at `u64` — I4's total carrier, and the type the
/// gate admits at.
fn u64_carrier() -> trust_clean_carrier::Carrier {
    carrier_at(&uint64_ty(), &Ty::Int { width: 64, signed: false })
        .expect("UInt64 -> u64 is the exact-width carrier and must be granted")
}

/// An environment holding `def double (a : UInt64) : UInt64 := UInt64.add a a`,
/// inserted through the FULL kernel check.
///
/// `UInt64.add` is used rather than a bare identity so the mutation has a real
/// construct to swap: the mistranslation below replaces the operator, which is
/// precisely the class of one-construct error a lowering makes.
fn env_with_double() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_uint_arith()
        .expect("UInt8/16/32/64 plus wrapping add/sub/mul must initialize");

    let body = correct_lowering();

    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("double"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
        value: body.clone(),
        is_reducible: true,
    })
    .expect("`double` must be admissible: it is a well-typed UInt64 -> UInt64 definition");

    (env, body)
}

/// Side B, CORRECT: `fun a => UInt64.add a a`.
///
/// This is what a faithful lowering of `double`, reflected back through R,
/// must produce.
fn correct_lowering() -> Expr {
    let a = Expr::bvar(0);
    Expr::lam(
        BinderInfo::Default,
        uint64_ty(),
        Expr::app(Expr::app(Expr::const_(Name::from_string("UInt64.add"), vec![]), a.clone()), a),
    )
}

/// Side B, MISTRANSLATED BY EXACTLY ONE CONSTRUCT: `fun a => UInt64.mul a a`.
///
/// `add` -> `mul`. Nothing else changes: same binder, same type, same arity,
/// same argument order. The two agree on `0` and on `2`, which is what makes
/// this a good mutation — a gate that sampled a few inputs could easily miss
/// it, and a defeq decision cannot.
fn mistranslated_lowering() -> Expr {
    let a = Expr::bvar(0);
    Expr::lam(
        BinderInfo::Default,
        uint64_ty(),
        Expr::app(Expr::app(Expr::const_(Name::from_string("UInt64.mul"), vec![]), a.clone()), a),
    )
}

#[test]
fn half_1_the_gate_admits_the_faithful_lowering() {
    let (env, _) = env_with_double();

    let admitted = check_faithful(&env, "double", &correct_lowering(), &u64_carrier())
        .expect("the gate must ADMIT a lowering that agrees with the Clean definition");

    assert_eq!(admitted.name(), "double");
    assert_eq!(
        admitted.admitted_at(),
        &Ty::Int { width: 64, signed: false },
        "the agreement must be admitted AT THE CARRIER TYPE (`u64`), never at the \
         Clean type — I4 exists because those two can disagree while defeq is satisfied"
    );
}

#[test]
fn half_2_the_gate_catches_the_one_construct_mistranslation() {
    let (env, _) = env_with_double();

    let refusal = check_faithful(&env, "double", &mistranslated_lowering(), &u64_carrier())
        .expect_err(
            "THE GATE IS DECORATION IF THIS PASSES. A lowering that computes `a * a` \
             was accepted for a definition that says `a + a`. Do NOT make this test \
             pass by editing `crates/trust-clean/src/reflect.rs` — R is frozen against \
             this lane, and a gate that agrees with a co-authored R is testing a round \
             trip, not a semantics.",
        );

    assert!(
        matches!(refusal, GateRefusal::Disagreement { .. }),
        "expected a disagreement verdict; got {refusal:?}"
    );
    assert_eq!(refusal.name(), "double");
}

#[test]
fn half_3_the_mutation_is_genuinely_one_construct_and_genuinely_different() {
    // Guard against the mutation quietly becoming a no-op — e.g. if `UInt64.mul`
    // were ever aliased to `UInt64.add`, this control would go green while
    // testing nothing. Ask the kernel directly.
    let (env, _) = env_with_double();
    let type_checker = TypeChecker::new(&env);

    assert!(
        !type_checker.is_def_eq(&correct_lowering(), &mistranslated_lowering()),
        "THE PREMISE OF THIS CONTROL FAILED: the kernel considers `a + a` and `a * a` \
         definitionally equal, so the mutation is not a mistranslation at all and \
         half_2 proves nothing. Re-derive the mutation before trusting this file."
    );

    // ...and they really do differ on a concrete carrier value: 3 + 3 = 6, 3 * 3 = 9.
    let three = Expr::app(
        Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let applied_correct = Expr::app(correct_lowering(), three.clone());
    let applied_mutated = Expr::app(mistranslated_lowering(), three);

    assert!(
        !type_checker.is_def_eq(&applied_correct, &applied_mutated),
        "`double 3` must differ between the faithful and mistranslated lowerings"
    );
}

#[test]
fn half_4_a_declaration_with_no_definition_body_is_refused() {
    // An axiom asserts a type without exhibiting a value. There is nothing for
    // emitted code to agree with, so the gate must refuse rather than compare
    // against whatever happens to be in the environment.
    let mut env = Environment::new();
    env.init_uint_arith()
        .expect("UInt8/16/32/64 plus wrapping add/sub/mul must initialize");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: Name::from_string("assumed"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
    })
    .expect("an axiom of function type is admissible");

    let refusal = check_faithful(&env, "assumed", &correct_lowering(), &u64_carrier())
        .expect_err("an axiom has no body and must never be emitted");

    assert!(
        matches!(refusal, GateRefusal::NoCleanBody { .. }),
        "expected NoCleanBody; got {refusal:?}"
    );
}

#[test]
fn half_5_an_unknown_name_is_refused_rather_than_vacuously_admitted() {
    let (env, _) = env_with_double();

    let refusal = check_faithful(&env, "no_such_def", &correct_lowering(), &u64_carrier())
        .expect_err("an unknown name must refuse, never admit vacuously");

    assert!(
        matches!(
            refusal,
            GateRefusal::NoCleanBody { .. } | GateRefusal::SideANotKernelChecked { .. }
        ),
        "expected a refusal naming the missing declaration; got {refusal:?}"
    );
}
