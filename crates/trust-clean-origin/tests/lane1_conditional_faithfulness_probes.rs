// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **LANE 1 — is a CONDITIONAL faithfulness claim reachable at the kernel?**
//!
//! Measurement only. Nothing here is a fix, and nothing here edits side B's
//! frozen producers or the recognizer.
//!
//! The question: `check_faithful` decides `sideA ≡ sideB`. For `gcd`'s `a % b`
//! at a SYMBOLIC `b`, can the kernel instead be asked for
//! `∀ a b, b ≠ 0 → sideA a b = sideB a b`?
//!
//! Sub-questions, in the order the brief poses them:
//!   (a) which spellings of `b ≠ 0` does the prelude support at UInt64?
//!   (b) can the implication be PROVED, and by what machinery?
//!   (c) are `UInt64.mod a b` and the Rust-side lowering ALREADY defeq at an
//!       open `b` — i.e. do they differ only at `b = 0`, or everywhere?

#![allow(clippy::doc_markdown)]

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name, TypeChecker};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::check_faithful;
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::Ty;

// ───────────────────────── side A: the REAL island elaborator ─────────────────

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn island_try(sources: &[&str]) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    if batch.is_rejected() {
        return Err(format!("{batch:?}"));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn carrier_of(bits: u32) -> Carrier {
    carrier_at(&uint_ty(bits), &Ty::Int { width: bits, signed: false })
        .expect("UIntN -> uN is the exact-width carrier and must be granted")
}

fn machine(bits: u32) -> Domain {
    Domain::Machine(match bits {
        8 => MachineUIntWidth::U8,
        16 => MachineUIntWidth::U16,
        32 => MachineUIntWidth::U32,
        64 => MachineUIntWidth::U64,
        other => panic!("{other} is not a machine width this battery measures"),
    })
}

fn definition_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("`{name}` must be a definition with a value"))
}

/// Mint through the FROZEN producer, or hand back its own refusal verbatim.
fn mint_expr(env: &Environment, rendering: &str, arity: usize, bits: u32) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let parameters: Vec<String> = (0..arity).map(|index| format!("p{index}")).collect();
    let refs: Vec<&str> = parameters.iter().map(String::as_str).collect();
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        "trust__lane1__reflected",
        rendering,
        &refs,
        &machine(bits),
    )?;
    Ok(scratch
        .get_const(&Name::from_string("trust__lane1__reflected"))
        .and_then(|c| c.value.clone())
        .expect("an accepted declaration carries a value"))
}

// ═══════ P1 — WHAT DOES `b ≠ 0` LOOK LIKE AT UInt64? ═══════

/// **(a)** Which hypothesis spellings does the prelude actually admit?
///
/// The test is deliberately weak on purpose: the CONCLUSION is `rfl`-true
/// regardless (`a % b = a % b`), so what is being measured is only whether the
/// hypothesis TYPE elaborates and lands in a `Sort`. A spelling that fails
/// here cannot appear in a conditional faithfulness goal at all.
#[test]
fn lane1_p1_which_spellings_of_b_ne_zero_elaborate_at_uint64() {
    let candidates: &[(&str, &str)] = &[
        ("b ≠ 0", "b ≠ 0"),
        ("b ≠ (0 : UInt64)", "b ≠ (0 : UInt64)"),
        ("Ne b 0", "Ne b 0"),
        ("¬ (b = 0)", "¬ (b = 0)"),
        ("Not (b = 0)", "Not (b = 0)"),
        ("b = 0 → False", "b = 0 → False"),
        ("(b == 0) = false", "(b == 0) = false"),
        ("(b == 0) = Bool.false", "(b == 0) = Bool.false"),
        ("UInt64.toNat b ≠ 0", "UInt64.toNat b ≠ 0"),
        ("Nat.lt 0 (UInt64.toNat b)", "Nat.lt 0 (UInt64.toNat b)"),
        ("0 < UInt64.toNat b", "0 < UInt64.toNat b"),
        ("UInt64.toNat b > 0", "UInt64.toNat b > 0"),
        ("0 < b", "0 < b"),
        ("UInt64.lt 0 b", "UInt64.lt 0 b"),
    ];

    let mut supported = Vec::new();
    let mut refused = Vec::new();
    for (label, spelling) in candidates {
        let source = format!(
            "theorem tp1 (a : UInt64) (b : UInt64) (h : {spelling}) : a % b = a % b := rfl"
        );
        match island_try(&[&source]) {
            Ok(_) => {
                supported.push(*label);
                eprintln!("LANE1-P1 | {label:<28} | ELABORATES");
            }
            Err(diagnostics) => {
                let first = diagnostics.lines().next().unwrap_or("<no diagnostic>").to_owned();
                refused.push((*label, first.clone()));
                eprintln!("LANE1-P1 | {label:<28} | REFUSED: {}", &first[..first.len().min(160)]);
            }
        }
    }
    eprintln!(
        "LANE1-P1 | SUMMARY | {} of {} spellings elaborate: {:?}",
        supported.len(),
        candidates.len(),
        supported
    );
    assert!(
        !supported.is_empty(),
        "if NO spelling of `b ≠ 0` elaborates at UInt64, a conditional faithfulness goal \
         cannot even be STATED and lane 1 is closed at (a). Refusals: {refused:?}"
    );
}

// ═══════ P2 — (c) ARE THE TWO SIDES ALREADY DEFEQ AT AN OPEN DIVISOR? ═══════

/// **THE LOAD-BEARING MEASUREMENT.**
///
/// Side A is `def m (a b : UInt64) : UInt64 := a % b`, elaborated by the real
/// island. The Rust-side lowering form is the one `trust_spec_elab::elab_term`
/// builds for a machine-width `%` — `{C}.ofNat (Nat.mod ({C}.toNat x) d)` —
/// with the divisor position at `{C}.toNat b` instead of a Nat literal.
///
/// If those two are defeq at an OPEN `b`, then the conditional claim is not
/// what is missing: the unconditional one already holds, and the `b ≠ 0`
/// obligation belongs somewhere other than the kernel comparison.
#[test]
fn lane1_p2_side_a_and_the_rust_side_lowering_at_an_open_divisor() {
    let env = island(&[
        "def m (a : UInt64) (b : UInt64) : UInt64 := a % b",
        "def mrust (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b))",
        "def d (a : UInt64) (b : UInt64) : UInt64 := a / b",
        "def drust (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.div (UInt64.toNat a) (UInt64.toNat b))",
    ]);

    let side_a_mod = definition_value(&env, "m");
    let side_b_mod = definition_value(&env, "mrust");
    let side_a_div = definition_value(&env, "d");
    let side_b_div = definition_value(&env, "drust");

    eprintln!("LANE1-P2 | side A (`a % b`)          = {side_a_mod}");
    eprintln!("LANE1-P2 | side B (ofNat/Nat.mod)    = {side_b_mod}");

    let checker = TypeChecker::new(&env);
    let mod_defeq = checker.is_def_eq(&side_a_mod, &side_b_mod);
    let mod_spent = checker.heartbeat_spent();
    drop(checker);
    let checker = TypeChecker::new(&env);
    let div_defeq = checker.is_def_eq(&side_a_div, &side_b_div);
    drop(checker);

    eprintln!(
        "LANE1-P2 | is_def_eq(a % b, ofNat (Nat.mod (toNat a) (toNat b))) = {mod_defeq} \
         (heartbeat spent: {mod_spent})"
    );
    eprintln!("LANE1-P2 | is_def_eq(a / b, ofNat (Nat.div (toNat a) (toNat b))) = {div_defeq}");

    // The ANTI-VACUITY control: a term that is NOT the lowering must be refused
    // by the same checker, so a `true` above is not a broken `is_def_eq`.
    let env_wrong = island(&[
        "def m (a : UInt64) (b : UInt64) : UInt64 := a % b",
        "def wrong (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.mod (UInt64.toNat b) (UInt64.toNat a))",
    ]);
    let checker = TypeChecker::new(&env_wrong);
    let swapped = checker
        .is_def_eq(&definition_value(&env_wrong, "m"), &definition_value(&env_wrong, "wrong"));
    drop(checker);
    assert!(
        !swapped,
        "the swapped-operand lowering must NOT be defeq to `a % b`; if it is, this probe's \
         positive half measured a broken `is_def_eq` rather than a real identification"
    );
    eprintln!("LANE1-P2 | CONTROL: swapped-operand lowering is defeq = {swapped} (must be false)");

    // …and the same statement put to the ISLAND, which is the elaborator the
    // pipeline actually drives.
    for (label, statement) in [
        (
            "unconditional `%`",
            "theorem u1 (a : UInt64) (b : UInt64) : \
             a % b = UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b)) := rfl",
        ),
        (
            "unconditional `/`",
            "theorem u2 (a : UInt64) (b : UInt64) : \
             a / b = UInt64.ofNat (Nat.div (UInt64.toNat a) (UInt64.toNat b)) := rfl",
        ),
    ] {
        let outcome = island_try(&[statement]);
        eprintln!("LANE1-P2 | island: {label:<20} by rfl = {}", outcome.is_ok());
    }

    // What the FROZEN producer does with a symbolic divisor — recorded, never
    // edited. This is the second, independent blocker.
    match mint_expr(&env, "p0 % p1", 2, 64) {
        Ok(term) => eprintln!("LANE1-P2 | the frozen producer MINTS `p0 % p1`: {term}"),
        Err(refusal) => eprintln!("LANE1-P2 | the frozen producer REFUSES `p0 % p1`: {refusal}"),
    }
    match mint_expr(&env, "p0 % 3", 1, 64) {
        Ok(term) => eprintln!("LANE1-P2 | the frozen producer mints `p0 % 3`: {term}"),
        Err(refusal) => eprintln!("LANE1-P2 | the frozen producer refuses `p0 % 3`: {refusal}"),
    }
}

// ═══════ P3 — DOES THE GATE ITSELF ADMIT AT AN OPEN DIVISOR? ═══════

/// The gate, unmodified, with a HAND-BUILT side B in the Rust-side lowering
/// shape. A hand-built side B is not evidence about the producer — the producer
/// refuses (p2) — but it IS evidence about what `check_faithful` decides when
/// handed that term.
#[test]
fn lane1_p3_check_faithful_at_a_symbolic_divisor() {
    let env = island(&[
        "def m (a : UInt64) (b : UInt64) : UInt64 := a % b",
        "def mrust (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b))",
        "def mwrong (a : UInt64) (b : UInt64) : UInt64 := a",
    ]);
    let carrier = carrier_of(64);

    let faithful = check_faithful(&env, "m", &definition_value(&env, "mrust"), &carrier);
    eprintln!(
        "LANE1-P3 | check_faithful(m, ofNat (Nat.mod (toNat a) (toNat b))) = {}",
        match &faithful {
            Ok(token) => format!("ADMIT via {:?}", token.method()),
            Err(refusal) => format!("REFUSED: {refusal:?}"),
        }
    );

    let wrong = check_faithful(&env, "m", &definition_value(&env, "mwrong"), &carrier);
    eprintln!("LANE1-P3 | CONTROL: check_faithful(m, `fun a b => a`) is_err = {}", wrong.is_err());
    assert!(
        wrong.is_err(),
        "if the identity is admitted for `a % b`, this probe measured a broken gate"
    );

    // And the same question with side B literally the elaborated `a % b`, which
    // is what a producer that simply re-elaborated the surface would mint.
    let same = check_faithful(&env, "m", &definition_value(&env, "m"), &carrier);
    eprintln!(
        "LANE1-P3 | check_faithful(m, <the elaborated `a % b` itself>) = {}",
        match &same {
            Ok(token) => format!("ADMIT via {:?}", token.method()),
            Err(refusal) => format!("REFUSED: {refusal:?}"),
        }
    );
}

// ═══════ P4 — (a)+(b) THE CONDITIONAL PROPOSITION, STATED AND PROVED ═══════

/// State `b ≠ 0 → sideA = sideB` in every spelling p1 admitted, and try to
/// prove it — first with `rfl`, then with `fun .. => rfl`, then with the
/// automation engine over a kernel-built goal.
#[test]
fn lane1_p4_the_conditional_proposition_in_the_kernel() {
    // ── the ISLAND route: the conditional, by rfl ───────────────────────────
    let hypotheses = [
        "b ≠ 0",
        "¬ (b = 0)",
        "(b == 0) = false",
        "UInt64.toNat b ≠ 0",
        "Nat.lt 0 (UInt64.toNat b)",
        "0 < UInt64.toNat b",
    ];
    for spelling in hypotheses {
        let statement = format!(
            "theorem c1 (a : UInt64) (b : UInt64) (h : {spelling}) : \
             a % b = UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b)) := rfl"
        );
        let outcome = island_try(&[&statement]);
        eprintln!(
            "LANE1-P4 | conditional `%` under `{spelling}` by rfl = {}",
            match &outcome {
                Ok(_) => "PROVED".to_owned(),
                Err(diagnostics) => {
                    let first = diagnostics.lines().next().unwrap_or("").to_owned();
                    format!("FAILED: {}", &first[..first.len().min(200)])
                }
            }
        );
    }

    // The ANTI-VACUITY control: a conditional whose CONCLUSION is false must
    // NOT be provable, hypothesis or no hypothesis.
    let bogus =
        island_try(&["theorem c2 (a : UInt64) (b : UInt64) (h : b ≠ 0) : a % b = a := rfl"]);
    eprintln!("LANE1-P4 | CONTROL: `b ≠ 0 → a % b = a` by rfl is_err = {}", bogus.is_err());
    assert!(
        bogus.is_err(),
        "a false conclusion under a true hypothesis must not check; if it does, every \
         `PROVED` above measured nothing"
    );

    // ── the KERNEL route: build the goal as an Expr and put it to clean-auto ─
    let env = island(&[
        "def m (a : UInt64) (b : UInt64) : UInt64 := a % b",
        "def mrust (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b))",
    ]);
    let u64_ty = uint_ty(64);
    let side_a = definition_value(&env, "m");
    let side_b = definition_value(&env, "mrust");
    let checker = TypeChecker::new(&env);
    // Under two binders `a = BVar(1)`, `b = BVar(0)`.
    let applied_a = checker.whnf(&Expr::apps(side_a.clone(), [Expr::bvar(1), Expr::bvar(0)]));
    let applied_b = checker.whnf(&Expr::apps(side_b.clone(), [Expr::bvar(1), Expr::bvar(0)]));
    drop(checker);

    let eq = |lhs: Expr, rhs: Expr, ty: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty, lhs, rhs],
        )
    };
    let conclusion = eq(applied_a.clone(), applied_b.clone(), u64_ty.clone());

    // The hypothesis, spelled `Ne b 0` if the kernel has `Ne`, else
    // `(b = 0) -> False`. Both are built and both are tried.
    let zero = mint_zero(&env, 64);
    let hyp_ne = Expr::apps(
        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
        [u64_ty.clone(), Expr::bvar(0), zero.clone()],
    );
    let hyp_arrow_false = Expr::pi(
        BinderInfo::Default,
        eq(Expr::bvar(0), zero.clone(), u64_ty.clone()),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    for (label, hypothesis) in [("Ne b 0", hyp_ne), ("(b = 0) -> False", hyp_arrow_false)] {
        // ∀ (a b : UInt64), <hyp> → <conclusion>. The conclusion is under one
        // extra binder once the hypothesis binder is added, so it is lifted.
        let body = Expr::pi(BinderInfo::Default, hypothesis, lift_one(&conclusion));
        let goal = Expr::pi(
            BinderInfo::Default,
            u64_ty.clone(),
            Expr::pi(BinderInfo::Default, u64_ty.clone(), body),
        );

        let checker = TypeChecker::new(&env);
        let well_formed = checker.infer_type(&goal).is_ok();
        drop(checker);
        eprintln!("LANE1-P4 | kernel goal under `{label}`: types as a proposition = {well_formed}");
        if !well_formed {
            continue;
        }

        let engine = AutomationEngine::new();
        let found = engine.auto_prove(&env, &goal, Duration::from_secs(5), None);
        match found {
            Some(result) => {
                let checker = TypeChecker::new(&env);
                let rechecked = checker.check_type(result.proof_term(), &goal).is_ok();
                drop(checker);
                eprintln!(
                    "LANE1-P4 | clean-auto under `{label}`: PROOF FOUND, kernel re-check = \
                     {rechecked}, strategy = {}",
                    result.proof_text()
                );
                // A proof clean-auto found that the kernel then rejects is an
                // automation defect, never a measurement to print and move past.
                assert!(
                    rechecked,
                    "clean-auto under `{label}` returned a proof the kernel REJECTS on \
                     re-check (strategy = {})",
                    result.proof_text()
                );
            }
            None => eprintln!("LANE1-P4 | clean-auto under `{label}`: no proof within 5s"),
        }
    }

    // …and the same goal WITHOUT the hypothesis, which is the real comparison.
    let unconditional = Expr::pi(
        BinderInfo::Default,
        u64_ty.clone(),
        Expr::pi(BinderInfo::Default, u64_ty.clone(), conclusion),
    );
    let checker = TypeChecker::new(&env);
    let refl_proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [u64_ty.clone(), applied_a.clone()],
    );
    let refl_closed = Expr::lam(
        BinderInfo::Default,
        u64_ty.clone(),
        Expr::lam(BinderInfo::Default, u64_ty.clone(), refl_proof),
    );
    let by_refl = checker.check_type(&refl_closed, &unconditional).is_ok();
    drop(checker);
    eprintln!(
        "LANE1-P4 | UNCONDITIONAL `∀ a b, a % b = ofNat (Nat.mod (toNat a) (toNat b))` \
         closes by Eq.refl = {by_refl}"
    );
}

/// `Eq.refl`-shaped lift: raise every loose bvar by one, for the extra
/// hypothesis binder. The conclusion mentions `BVar(0)`/`BVar(1)` only.
fn lift_one(expr: &Expr) -> Expr {
    fn go(expr: &Expr, cutoff: u32) -> Expr {
        match expr.kind() {
            ExprKind::BVar(index) if *index >= cutoff => Expr::bvar(index + 1),
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_) => expr.clone(),
            ExprKind::App(f, a) => Expr::app(go(f, cutoff), go(a, cutoff)),
            ExprKind::Lam(bi, ty, body) => Expr::lam(*bi, go(ty, cutoff), go(body, cutoff + 1)),
            ExprKind::Pi(bi, ty, body) => Expr::pi(*bi, go(ty, cutoff), go(body, cutoff + 1)),
            ExprKind::MData(_, inner) => go(inner, cutoff),
            other => panic!("lift_one is not defined over {other:?}"),
        }
    }
    go(expr, 0)
}

/// The kernel term for `(0 : UInt{bits})`, read out of the real elaborator so
/// this probe does not invent a numeral spelling.
fn mint_zero(env: &Environment, bits: u32) -> Expr {
    let _ = env;
    let zero_env = island(&[&format!("def lane1_zero : UInt{bits} := 0")]);
    definition_value(&zero_env, "lane1_zero")
}
