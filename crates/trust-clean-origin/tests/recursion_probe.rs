// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **C10→C11 — THE RECURSION BOUNDARY AND ITS PROOF-CHECKED CLOSURE.**
//!
//! First measures whether definitional equality can identify a recursive
//! definition, then exercises the deliberately separate structural-induction
//! fallback in `check_faithful`. The campaign required the raw measurement
//! before any recursive emission was sequenced; both the refusal boundary and
//! the proof-checked closure remain pinned here.
//!
//! Ground (scouted 2026-08-20, recorded in the campaign plan): the kernel has
//! NO recursive declaration form — `Declaration` is
//! Definition/Axiom/Theorem/Opaque, `add_decl` type-checks the value before
//! the name exists, and "recursive definitions" are recursor FOLDS
//! (`Nat.rec` applications; `WellFounded.fix` is itself a reducible
//! Definition over `Acc.rec`). `Nat.pred` — installed by `init_nat` as
//! exactly such a fold — is the measurement subject, so this file measures
//! the real thing the prelude ships, not a bespoke construction.
//!
//! The findings, each pinned below (2b and 3 are MEASURED refinements of the
//! grounding's prediction, which keyed on "symbolic major" without asking
//! which position the fold recurses on):
//!
//! 1. CLOSED literals compute: iota fires (literals expand to constructor
//!    form), so `pred 3 ≡ 2` — a recursive def IS identifiable with a closed
//!    form, by COMPUTING it.
//! 2. A CONSTRUCTOR-HEADED symbolic major still computes: `pred (succ n) ≡ n`
//!    under a binder — iota needs a constructor head, not a closed term.
//! 2b. A nested fold whose RECURSION argument is closed computes all the way
//!    down (`sub n 1 ≡ pred n`), with the other argument symbolic throughout.
//! 3. A SYMBOLIC RECURSION ARGUMENT is stuck, and defeq has no inductive
//!    reasoning: `n + 0 ≡ n` admits, `0 + n ≡ n` is refused — the same
//!    identity, decided purely by which side the variable sits on. This is
//!    the Stage-5 verdict: a recursive shape cannot ride the defeq gate.
//!    C11 closes exactly the structural identity case with a real `Nat.rec`
//!    proof. Automation proposes the term; the kernel rechecks it and an audit
//!    excluding every non-foundational domain/trust assumption is mandatory. A false constant mutation is
//!    refused, so this is neither defeq relabelling nor an accept-all fallback.
//!
//! Side B remains independently non-recursive: the compiler emits an ordinary
//! parameter projection and the gate proves the recursive side A extensionally
//! equal to it. General recursive bodies still have neither an emitted shape
//! nor a proof and therefore refuse.

use clean_kernel::{Declaration, Environment, Expr, Name, TypeChecker};
use trust_clean_carrier::carrier_for;
use trust_clean_origin::{FaithfulnessMethod, check_faithful};

fn env_nat() -> Environment {
    // The raw defeq measurements need only Nat, but the induction search also
    // needs the Eq/classical bridge declarations before it can propose a
    // closed recursor proof for the kernel to re-check.
    let mut env = Environment::new();
    env.init_nat().expect("Nat + its recursors must init");
    env.init_eq().expect("Eq must init for the induction goal");
    env.init_classical().expect("the induction search bridge must init");
    env
}

fn nat_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Finding 1: the kernel identifies a recursive def with a closed form by
/// COMPUTING it — `Nat.pred 3 ≡ 2`, three iota steps.
#[test]
fn closed_literal_recursor_fold_admits() {
    let env = env_nat();
    let tc = TypeChecker::new(&env);
    let pred3 = Expr::app(nat_const("Nat.pred"), Expr::nat_lit(3));
    assert!(
        tc.is_def_eq(&pred3, &Expr::nat_lit(2)),
        "iota must reduce the fold at a closed literal"
    );
    // And the negative: computing gives the RIGHT answer, not just an answer.
    assert!(!tc.is_def_eq(&pred3, &Expr::nat_lit(3)), "pred 3 is not 3");
}

/// Finding 2: iota fires on a CONSTRUCTOR-HEADED major even under a binder —
/// `fun n => Nat.pred (Nat.succ n)` is identified with `fun n => n`. The
/// boundary is constructor-headedness, not closedness.
#[test]
fn constructor_headed_symbolic_major_still_computes() {
    let env = env_nat();
    let tc = TypeChecker::new(&env);
    let nat = nat_const("Nat");
    let pred_succ = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat.clone(),
        Expr::app(nat_const("Nat.pred"), Expr::app(nat_const("Nat.succ"), Expr::bvar(0))),
    );
    let identity = Expr::lam(clean_kernel::BinderInfo::Default, nat, Expr::bvar(0));
    assert!(
        tc.is_def_eq(&pred_succ, &identity),
        "iota must fire on `succ n` — the major is constructor-headed"
    );
}

/// Finding 2b — identification reaches through NESTED folds when the
/// recursion argument is closed. `fun n => Nat.sub n 1 ≡ fun n => Nat.pred n`
/// IS identified: `Nat.sub` recurses on its (closed) subtrahend, so the fold
/// computes down to `pred` with the other argument symbolic throughout.
///
/// MEASURED CORRECTION (2026-08-20): the C10 grounding predicted this pair
/// stuck. Wrong — the prediction keyed on "symbolic major" without asking
/// WHICH position the fold recurses on. The boundary is not "any symbolic
/// argument": it is "the RECURSION argument is symbolic". Finding 3 pins
/// that boundary with a pair where the recursion argument really is the
/// symbolic one.
#[test]
fn nested_fold_with_closed_recursion_argument_still_computes() {
    let env = env_nat();
    let tc = TypeChecker::new(&env);
    let nat = nat_const("Nat");
    let pred_n = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat.clone(),
        Expr::app(nat_const("Nat.pred"), Expr::bvar(0)),
    );
    let sub_n_1 = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat,
        Expr::apps(nat_const("Nat.sub"), [Expr::bvar(0), Expr::nat_lit(1)]),
    );
    assert!(
        tc.is_def_eq(&pred_n, &sub_n_1),
        "sub recurses on the closed subtrahend; the fold must compute to pred"
    );
}

/// Finding 3 — THE STAGE-5 VERDICT PIN: when the RECURSION argument is
/// symbolic, the fold is stuck and the kernel has NO fixpoint/inductive
/// reasoning. Measured on the definitional pair every textbook uses:
/// `n + 0 ≡ n` holds by computation (`Nat.add` recurses on its second
/// argument, here the closed `0`) — but `0 + n ≡ n` REQUIRES INDUCTION, and
/// defeq refuses it. Same function, same identity, opposite verdicts purely
/// by which side the variable sits on: identification happens only by
/// computing, never by reasoning about the fixpoint.
///
/// Consequence, held by this pin: a `Recursive` CleanOriginShape cannot ride
/// the defeq gate — for a symbolic-input equivalence the gate would refuse
/// every faithful emission (fail-closed over-rejection, sound but useless),
/// and any workaround that closed the inputs would check finitely many
/// points of an infinite claim. The check must be EXTENDED (fixpoint /
/// functional induction in the trust root's lane) before the generator may
/// emit one. If this pin ever goes GREEN, the kernel acquired a new
/// equational power — re-measure the whole Stage-5 design space before
/// trusting it.
#[test]
fn symbolic_recursion_argument_is_stuck_no_fixpoint_reasoning() {
    let mut env = env_nat();
    let tc = TypeChecker::new(&env);
    let nat = nat_const("Nat");
    let lam = |body| Expr::lam(clean_kernel::BinderInfo::Default, nat.clone(), body);
    let identity = lam(Expr::bvar(0));

    // The computing direction: recursion argument closed.
    let n_plus_0 = lam(Expr::apps(nat_const("Nat.add"), [Expr::bvar(0), Expr::nat_lit(0)]));
    assert!(
        tc.is_def_eq(&n_plus_0, &identity),
        "n + 0 computes: the recursion argument is the closed 0"
    );

    // The stuck direction: recursion argument symbolic. Extensionally the
    // same identity; definitionally out of reach without induction.
    let zero_plus_n = lam(Expr::apps(nat_const("Nat.add"), [Expr::nat_lit(0), Expr::bvar(0)]));
    assert!(
        !tc.is_def_eq(&zero_plus_n, &identity),
        "MEASURED BOUNDARY: 0 + n ≡ n requires induction, and defeq must refuse it"
    );

    // The faithfulness gate closes that measured boundary with a genuine
    // recursor proof. Side A is a fully kernel-checked definition; side B is
    // the independently reflected projection. The returned evidence records
    // induction rather than laundering it as defeq.
    drop(tc);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("zero_plus"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), nat.clone()),
        value: zero_plus_n,
        is_reducible: true,
    })
    .expect("zero_plus definition must kernel-check");
    let nat_carrier = carrier_for(&nat).expect("Nat has the exact bignum carrier");
    let faithful = check_faithful(&env, "zero_plus", &identity, &nat_carrier)
        .expect("a kernel-checked structural induction proof closes 0+n=n");
    assert_eq!(faithful.method(), FaithfulnessMethod::StructuralInduction);

    // Anti-vacuity: the same proof lane must not certify a false equation.
    let always_zero = lam(nat_const("Nat.zero"));
    assert!(
        check_faithful(&env, "zero_plus", &always_zero, &nat_carrier).is_err(),
        "induction must distinguish the faithful projection from a wrong constant"
    );
}

#[test]
fn recursive_candidate_alone_cannot_enable_the_induction_lane() {
    let mut env = env_nat();
    let nat = nat_const("Nat");
    let identity = Expr::lam(clean_kernel::BinderInfo::Default, nat.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("plain_identity"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), nat.clone()),
        value: identity,
        is_reducible: true,
    })
    .expect("plain identity definition");

    // This candidate is extensionally equal, but only the candidate delegates
    // to Nat.rec. The bounded fallback is a lane for a recursive CLEAN source;
    // a lowering cannot buy proof search by injecting a recursor of its own.
    let recursive_candidate = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat.clone(),
        Expr::apps(nat_const("Nat.add"), [Expr::nat_lit(0), Expr::bvar(0)]),
    );
    let carrier = carrier_for(&nat).expect("Nat bignum carrier");
    assert!(
        check_faithful(&env, "plain_identity", &recursive_candidate, &carrier).is_err(),
        "a recursive candidate must not widen a non-recursive Clean definition"
    );
}
