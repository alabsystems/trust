// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R7 — the ARITY WIDENING measurement, and the `nat.param` row it produced.**
//!
//! Every side A here comes from `trust_certify::clean_island::CleanIslandSession`
//! — the exact pipeline `clean_origin_mir` drives — so an ISLAND rejection and a
//! CALL-lane refusal are never confused for one another (the `r2_session_probes`
//! discipline, and `r6_nat_mul_probes`' harness verbatim).
//!
//! # The question, and the measured answer
//!
//! R2 landed a well-founded lane that is **single-parameter**: the measure is
//! the sole parameter, side B's functional binds exactly two binders
//! (`x`, `rec`), and the recursive slot is used as an exactly-TWO-argument
//! self-call. `gcd` — the ranked next target — is two-parameter, and R6 (q1)
//! measured that it ELABORATES at this pin: what refuses it is this crate's
//! reader, not the elaborator.
//!
//! This file measures the shape a two-parameter well-founded recursion with a
//! **one-parameter measure** actually has, so the widening is written against
//! the elaborator's own lowering rather than against a guess. Phase 2 of
//! `first-party/clean`'s well-founded lowering (already in this pin — no pin
//! move, no `compiler/**` edit) produces:
//!
//! ```text
//! fun (a b : Nat) =>
//!   @WellFounded.fix.{1,1} Nat (fun n => Nat -> Nat) rel hwf F (bvar 1) (bvar 0)
//!   where F = fun (n : Nat) (rec : (y : Nat) -> Nat.lt y n -> Nat -> Nat) (b : Nat) =>
//!               dite Nat (0 < n) _ (fun h => … rec (n-1) prf <b'> …) (fun _ => …)
//! ```
//!
//! Seven spine arguments where R2 reads five or six; an ARROW motive where R2
//! demands `fun _ => Nat`; a THREE-binder functional where R2 peels two; a
//! THREE-argument `rec` where R2's reader, the gate's `walk_functional` and the
//! gate's `rebuild_functional` each independently require exactly two.
//!
//! # The kernel probe, run BEFORE the producer (q3)
//!
//! The widening's one new identification is **positional**: side B renders
//! source parameter `i` as a de Bruijn index into the functional's own binder
//! telescope, and the whole layout is only sound if the kernel DECIDES
//! parameter order rather than tolerating it. `nat.mul`'s discipline, applied
//! to a selection: `sel a b = b := rfl` must ADMIT and the same-shaped
//! `sel a b = a := rfl` must be REFUSED. Both are measured here, and the
//! order-sensitivity is re-measured on the real fixture at its own values
//! (`dbl 3 1 = 8` vs `dbl 1 3 = 6`), because a fixture whose value is symmetric
//! in its two parameters would make every operand-order control vacuous.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_origin::emit::plan_clean_origin_body;

// ═══════════════════════════════════════════════════════════════════════════
// harness — `r6_nat_mul_probes`' verbatim
// ═══════════════════════════════════════════════════════════════════════════

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(240).collect()
}

fn row(tag: &str, name: &str, source: &str) {
    match island(source) {
        Err(why) => eprintln!("ROW {tag:<12} | ISLAND REJECTS | {}", first_line(&why)),
        Ok(env) => {
            let call = match plan_clean_origin_body(&env, name) {
                Ok(plan) => format!("PLANS {:?}", plan.shape()),
                Err(refusal) => format!("CALL REFUSES | {}", first_line(&refusal.note())),
            };
            eprintln!("ROW {tag:<12} | ISLAND OK      | {call}");
        }
    }
}

fn render(expr: &Expr, depth: usize) -> String {
    if depth == 0 {
        return "…".to_owned();
    }
    match expr.kind() {
        ExprKind::MData(_, inner) => render(inner, depth),
        ExprKind::BVar(i) => format!("#{i}"),
        ExprKind::FVar(_) => "fvar".to_owned(),
        ExprKind::Sort(_) => "Sort".to_owned(),
        ExprKind::Lit(l) => format!("lit({l:?})"),
        ExprKind::Const(n, _) => n.to_string(),
        ExprKind::Lam(_, ty, body) => {
            format!("(fun : {} => {})", render(ty, depth - 1), render(body, depth - 1))
        }
        ExprKind::Pi(_, ty, body) => {
            format!("({} -> {})", render(ty, depth - 1), render(body, depth - 1))
        }
        ExprKind::App(..) => {
            let head = expr.get_app_fn();
            let mut args: Vec<String> =
                expr.get_app_args_iter().map(|a| render(a, depth - 1)).collect();
            args.reverse();
            format!("({} {})", render(head, depth - 1), args.join(" "))
        }
        other => format!("<{other:?}>"),
    }
}

fn strip(expr: &Expr) -> &Expr {
    match expr.kind() {
        ExprKind::MData(_, inner) => strip(inner),
        _ => expr,
    }
}

/// Peel every leading lambda, returning the count and the body.
fn peel(expr: &Expr) -> (usize, &Expr) {
    let mut n = 0;
    let mut cursor = strip(expr);
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        n += 1;
        cursor = strip(inner);
    }
    (n, cursor)
}

fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut head = strip(expr);
    while let ExprKind::App(f, a) = head.kind() {
        args.push(strip(a));
        head = strip(f);
    }
    args.reverse();
    (head, args)
}

/// Print the full spine anatomy the widening is written against.
fn anatomy(tag: &str, name: &str, source: &str) {
    let env = match island(source) {
        Err(why) => {
            eprintln!("ANATOMY {tag} | ISLAND REJECTS | {}", first_line(&why));
            return;
        }
        Ok(env) => env,
    };
    let Some(value) = env.get_const(&Name::from_string(name)).and_then(|c| c.value.clone()) else {
        eprintln!("ANATOMY {tag} | no value");
        return;
    };
    let (outer_lams, cursor) = peel(&value);
    let (head, args) = uncurry(cursor);
    eprintln!(
        "ANATOMY {tag} | outer_lams={outer_lams} head={} args={}",
        render(head, 2),
        args.len()
    );
    for (i, a) in args.iter().enumerate() {
        eprintln!("   arg[{i}] = {}", render(a, 6));
    }
    if args.len() >= 5 {
        let (fl, fbody) = peel(args[4]);
        eprintln!("   F: leading lambdas = {fl}");
        let (dh, da) = uncurry(fbody);
        eprintln!("   F body head = {} ({} args)", render(dh, 2), da.len());
        if da.len() == 5 {
            for (label, arm) in [("then", da[3]), ("else", da[4])] {
                let (_, abody) = peel(arm);
                let (ah, aa) = uncurry(abody);
                eprintln!("   {label} arm: head = {} ({} args)", render(ah, 2), aa.len());
                eprintln!("   {label} arm full = {}", render(abody, 7));
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE FIXTURES
// ═══════════════════════════════════════════════════════════════════════════

/// **THE DRIVER FIXTURE.** Two parameters, a ONE-parameter measure, the
/// accumulator genuinely CHANGED at the self-call, and each parameter used at
/// most once per arm (so the emitted body's move discipline holds without a
/// clone). Computes `a + b`.
pub const ADD_ACC: &str = "def addAcc (a b : Nat) : Nat := \
                           if h : 0 < a then addAcc (a - 1) (b + 1) else b\n\
                           termination_by a";

/// **THE ORDER-SENSITIVE FIXTURE.** `addAcc` computes `a + b`, which is
/// symmetric in its parameters — so an operand-swap mutation control taken on
/// it alone would be measuring nothing about the parameter LAYOUT. `dbl`
/// computes `b * 2^a`, where `dbl 3 1 = 8` and `dbl 1 3 = 6`.
pub const DBL: &str = "def dbl (a b : Nat) : Nat := \
                       if h : 0 < a then dbl (a - 1) (b * 2) else b\n\
                       termination_by a";

/// The measure on the SECOND parameter, so the layout is not written against
/// `measure_index = 0` by accident.
pub const ADD_ACC2: &str = "def addAcc2 (a b : Nat) : Nat := \
                            if h : 0 < b then addAcc2 (a + 1) (b - 1) else a\n\
                            termination_by b";

/// R2's single-parameter baseline — must be UNMOVED by the widening.
pub const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                                 if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                                 termination_by n";

/// The ADVERSARIAL control: `b` is used TWICE in the nonzero arm (once in the
/// value, once as the threaded argument), which the emitted body cannot express
/// — the emitter has no clone and the second use borrows a local the self-call
/// has already moved. Must stay REFUSED.
pub const SCALE: &str = "def scale (a b : Nat) : Nat := \
                         if h : 0 < a then b + scale (a - 1) b else 0\n\
                         termination_by a";

/// The TRAP the increment must not use as its evidence: this degenerate form
/// is absorbed by the INDUCTIVE-PROJECTION lane (it equals `fun a b => b`), so
/// it plans today and proves nothing about the well-founded reader.
pub const THREAD: &str = "def thread (a b : Nat) : Nat := \
                          if h : 0 < a then thread (a - 1) b else b\n\
                          termination_by a";

// ═══════════════════════════════════════════════════════════════════════════
// (q1) the SHAPES — what the widening is written against
// ═══════════════════════════════════════════════════════════════════════════

#[test]
#[ignore = "measurement instrument: prints the elaborated well-founded spine's anatomy, \
            asserts none; run with --ignored --nocapture"]
fn probe_q1_two_parameter_wf_anatomy() {
    anatomy("q1 addAcc", "addAcc", ADD_ACC);
    anatomy("q1 dbl", "dbl", DBL);
    anatomy("q1 addAcc2", "addAcc2", ADD_ACC2);
    anatomy("q1 cds", "countdownSum", COUNTDOWN_SUM);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q2) the CALL-lane verdicts, before and after
// ═══════════════════════════════════════════════════════════════════════════

#[test]
#[ignore = "measurement instrument: prints the island and call-lane verdicts, asserts none; run with --ignored --nocapture"]
fn probe_q2_call_lane_rows() {
    row("q2 addAcc", "addAcc", ADD_ACC);
    row("q2 dbl", "dbl", DBL);
    row("q2 addAcc2", "addAcc2", ADD_ACC2);
    row("q2 cds", "countdownSum", COUNTDOWN_SUM);
    row("q2 scale", "scale", SCALE);
    row("q2 thread", "thread", THREAD);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q3) THE KERNEL PROBE — parameter ORDER is the kernel's decision
// ═══════════════════════════════════════════════════════════════════════════

/// **Run BEFORE the `nat.param` producer was written**, the `nat.mul`
/// discipline (`r6` q7) applied to a POSITIONAL identification.
///
/// The widening's whole soundness rests on side B rendering source parameter
/// `i` at the de Bruijn index the functional's binder telescope puts it at. If
/// the kernel did not DECIDE parameter order — if it identified `sel a b` with
/// both `a` and `b` — then every arity-indexed layout below would be a
/// spelling assumption rather than a checked fact, and the operand-order
/// mutation controls would be rubber stamps.
#[test]
fn probe_q3_kernel_decides_parameter_order() {
    let ok = island(
        "def sel (a b : Nat) : Nat := b\n\
         theorem selRight (a b : Nat) : sel a b = b := rfl\n\
         theorem selFlip (a b : Nat) : sel b a = a := rfl",
    );
    eprintln!("ROW q3 order       | {}", if ok.is_ok() { "KERNEL ADMITS" } else { "REFUSED" });
    assert!(ok.is_ok(), "`sel a b = b` must close by rfl: {:?}", ok.err());

    // MUTATION CONTROL at the same layer — otherwise the admit above is a
    // rubber stamp rather than a decision.
    let bad =
        island("def sel (a b : Nat) : Nat := b\ntheorem selWrong (a b : Nat) : sel a b = a := rfl");
    eprintln!(
        "ROW q3 mutation    | {}",
        if bad.is_err() { "REFUSED (good)" } else { "ADMITTED!!" }
    );
    assert!(bad.is_err(), "`sel a b = a` must be REFUSED — parameter order must be DECIDED");
}

// ═══════════════════════════════════════════════════════════════════════════
// (q4) the VALUES the run-pass fixture asserts — pinned at the KERNEL first
// ═══════════════════════════════════════════════════════════════════════════

/// `tests/ui/trust/clean_origin_wf_rec_arity.rs` asserts that the EMITTED
/// binary computes these. Each is a closed `rfl` at the real kernel, so the
/// fixture's expected values and the declaration's meaning cannot drift apart.
///
/// The refuting controls are not optional — without them, `rfl` closing on
/// every row would be evidence of nothing. `dbl`'s two rows additionally pin
/// that the two parameters are NOT interchangeable at the kernel.
#[test]
fn probe_q4_values_at_the_kernel() {
    let sources = format!(
        "{ADD_ACC}\n{DBL}\n\
         theorem addAcc_0_0 : addAcc 0 0 = 0 := rfl\n\
         theorem addAcc_0_7 : addAcc 0 7 = 7 := rfl\n\
         theorem addAcc_3_4 : addAcc 3 4 = 7 := rfl\n\
         theorem addAcc_9_1 : addAcc 9 1 = 10 := rfl\n\
         theorem dbl_0_5 : dbl 0 5 = 5 := rfl\n\
         theorem dbl_3_1 : dbl 3 1 = 8 := rfl\n\
         theorem dbl_1_3 : dbl 1 3 = 6 := rfl\n\
         theorem dbl_5_2 : dbl 5 2 = 64 := rfl"
    );
    island(&sources).expect("every value must COMPUTE by kernel reduction");

    for bad in [
        "theorem addAcc_bad : addAcc 3 4 = 8 := rfl",
        // THE ORDER ROW: `dbl` is NOT symmetric, and the kernel says so.
        "theorem dbl_bad : dbl 3 1 = 6 := rfl",
        "theorem dbl_sym : dbl 1 3 = 8 := rfl",
    ] {
        let refused = island(&format!("{ADD_ACC}\n{DBL}\n{bad}"));
        assert!(refused.is_err(), "`{bad}` must be REFUSED, or the rows above are a rubber stamp");
    }
    eprintln!(
        "ROW q4 values      | addAcc/dbl COMPUTE at the kernel; dbl 3 1 = 6 and dbl 1 3 = 8 \
         REFUSED (parameter order is DECIDED)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (q5) the TRAP — `thread` is absorbed elsewhere and is not evidence
// ═══════════════════════════════════════════════════════════════════════════

/// BEFORE the widening, the obvious "minimal two-parameter fixture" — the
/// accumulator threaded UNCHANGED — was refused by the well-founded reader and
/// fell through to the INDUCTIVE-PROJECTION lane, which proves it equal to
/// `fun a b => b` and plans it as `InductiveProjection { projected: 1 }`.
/// Measured on this file's first run, before a line of the widening existed.
///
/// **AFTER the widening it plans through the WELL-FOUNDED lane instead**, and
/// this probe records that as a measured lane change rather than leaving it to
/// be discovered. The change is a consequence, not a choice: the well-founded
/// recogniser runs first in `plan_clean_origin_body`'s chain, so widening it to
/// arity 2 moves every body it can now read off the fall-through lane. Nothing
/// about the verdict weakens — both lanes end at a kernel gate, the WF one at
/// `check_faithful_wf_functional` with side A's decrease proofs borrowed — and
/// `control_16`'s battery is taken on `dbl`, which neither lane's fall-through
/// can absorb.
///
/// The standing warning survives the change: `thread` is still NOT evidence for
/// the widening, because a body the projection lane can also prove says nothing
/// about whether the well-founded reader read it correctly.
#[test]
fn probe_q5_the_threaded_unchanged_fixture_changed_lanes() {
    let env = island(THREAD).expect("thread elaborates");
    let plan = plan_clean_origin_body(&env, "thread").expect("thread plans on one lane or another");
    eprintln!("ROW q5 thread      | PLANS {:?}", plan.shape());
    assert!(
        matches!(
            plan.shape(),
            trust_clean_origin::emit::CleanOriginShape::WellFoundedNatRec { .. }
        ),
        "MEASURED 2026-08-26: after R3a the widened well-founded reader claims this body \
         before the inductive-projection fall-through sees it. If this ever reads \
         `InductiveProjection` again, the widening has narrowed and the reason must be \
         found, not re-baselined."
    );
}
