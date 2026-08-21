// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **C10 — THE RECURSION PROBE (probe only, no compiler work).**
//!
//! Measures, at the kernel, whether definitional equality — the SAME judgment
//! `check_faithful` applies (`gate.rs`: `TypeChecker::is_def_eq` on side A's
//! body against the reflected lowering) — can identify a RECURSIVE definition
//! with anything at all. The campaign plan's Stage 5 named this the single
//! riskiest step and required the measurement BEFORE any `Recursive` shape is
//! sequenced.
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
//!    the Stage-5 verdict: a `Recursive` shape cannot ride the defeq gate —
//!    the check must be EXTENDED (fixpoint/functional induction) before the
//!    generator may emit one (v7/D2: capability extends the CHECK, never
//!    trust). Fail-closed today: the refusal direction is over-rejection.
//!
//! No side-B route exists either — none of the four `admit_*` producers can
//! mint a recursive term (their fragment is flat arithmetic + parameter
//! select), so recursion is doubly outside the fragment: no reflection path
//! (probe g's category) AND no identification judgment for symbolic inputs.

use clean_kernel::{Environment, Expr, Name, TypeChecker};

fn env_nat() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("Nat + its recursors must init");
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
    let identity =
        Expr::lam(clean_kernel::BinderInfo::Default, nat, Expr::bvar(0));
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
    let env = env_nat();
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
}
