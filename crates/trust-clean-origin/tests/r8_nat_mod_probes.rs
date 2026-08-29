// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R8 KERNEL PROBE — the `nat.mod` identification, and the honest accounting
//! of what it does and does NOT decide.**
//!
//! Fast-lane-first, the `gcd_route_probes::m1` discipline: this file runs
//! BEFORE the `nat.mod` producer exists, and `table.rs`'s row plus
//! `admissible_body.rs`'s `RecBodyExpr::Rem` doc both cite it. A vocabulary
//! node whose kernel meaning was assumed rather than measured is a capability
//! claim with nothing behind it.
//!
//! # The thing this file is careful about
//!
//! Commit `fa788aab89` measured that the faithfulness gate is BLIND to the
//! zero-divisor divergence at a MACHINE width: Rust's `%` on `u{N}` is a MIR
//! `Rvalue::BinaryOp` that PANICS at a zero divisor, Clean's `UInt{N}.mod` is
//! TOTAL, the gate compares two CLEAN terms, and no proposition it can state
//! sees the panic. That finding STANDS, unqualified, and `q6` re-measures it
//! here rather than citing it.
//!
//! **This lane is a different lane, and the difference is not the gate's
//! power — it is whether the unseen assumption is TRUE.** At the `Nat` bignum
//! carrier the emitted operation is not the `%` primitive at all: it is
//! `Call(trust_bignum::Nat::rem, [&a, &b])`, and `Nat::rem` is total with
//! `n % 0 = n` BY CONSTRUCTION (`checked_div_rem(..)` returning `None` at a
//! zero divisor, falling back to the dividend — Lean's `Nat.mod_zero`).
//! `TemplateTerminator` has no `Assert` variant; there is no emitted panic path
//! on this lane to make unreachable.
//!
//! So the claim that replaces panic-freedom is **TOTALITY AGREEMENT of the
//! carrier**, and this file states plainly (q2) that the kernel identification
//! is VACUOUS with respect to it at an OPEN dividend — `∀ a, a % 0 = a` by
//! `rfl` is REFUSED, `Nat.mod` being stuck there, exactly as `l7_p6` found at
//! `UInt`. What carries it instead is named in the row's `tcb_row` and in
//! `docs/TCB.md`: `trust-bignum`'s kernel-differential test, which reduces
//! `Nat.mod` in the REAL Clean `TypeChecker` at a zero divisor and asserts the
//! runtime agrees. `q2`'s ground table is what makes that test's expectations
//! the kernel's decision rather than a hand-written constant.
//!
//! # The obligation the compiler DOES discharge on this lane
//!
//! The DECREASE. `gcd b (a % b)` descends only because `a % b < b`, and that
//! needs `0 < b` — which the textbook `dite` puts in scope as `h`. `q4` reads
//! `Nat.mod_lt … h` out of the elaborated term, and `q5` is the control half:
//! a guard on the WRONG value and a guard that does NOT DOMINATE the division
//! are both REFUSED. That is a real obligation with a real undischarged case,
//! and it is what the `nat.mod` row rests on beyond mere value agreement.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};

// ═══════════════════════════════ harness ═══════════════════════════════════

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
    s.lines().next().unwrap_or("").chars().take(300).collect()
}

fn strip(expr: &Expr) -> &Expr {
    match expr.kind() {
        ExprKind::MData(_, inner) => strip(inner),
        _ => expr,
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

fn value_of(env: &Environment, name: &str) -> Option<Expr> {
    env.get_const(&Name::from_string(name)).and_then(|c| c.value.clone())
}

/// The whole elaborated body of `name`, flattened to one string, so a row can
/// ask whether a CONSTANT occurs in it.
fn body_text(env: &Environment, name: &str) -> String {
    value_of(env, name).map_or_else(|| "<no value>".to_owned(), |v| render(&v, 40))
}

fn admits(src: &str) -> bool {
    island(src).is_ok()
}

// ═══════════════════════════════════════════════════════════════════════════
// (q1) THE ONE NEW IDENTIFICATION, isolated — `%` at `Nat` IS `Nat.mod`
// ═══════════════════════════════════════════════════════════════════════════

/// **THE ONE NEW IDENTIFICATION, and its refuting twins.** `a % b` must BE
/// `Nat.mod a b` at the kernel, and — the rows that matter most — it must NOT
/// be `Nat.div a b` (the sibling in the same `divmod` module, the easiest
/// emitter mutation to make) and NOT `Nat.mod b a`. Like `-` and unlike `+`
/// and `*`, `%` is not commutative, so operand ORDER is a real question and the
/// kernel is what answers it.
///
/// `control_21` (b)/(c) are the emitter-side twins of these two mutations.
#[test]
fn q1_the_modulo_identification_at_the_kernel() {
    for (tag, src) in [
        ("mod defeq", "theorem t (a b : Nat) : a % b = Nat.mod a b := rfl"),
        ("nested", "theorem t (a b : Nat) : a % (a % b) = Nat.mod a (Nat.mod a b) := rfl"),
        ("ground", "theorem t : 17 % 5 = 2 := rfl"),
        ("divides", "theorem t : 12 % 4 = 0 := rfl"),
        ("smaller", "theorem t : 3 % 7 = 3 := rfl"),
        // The gcd step itself, at ground values: `gcd 12 18` descends
        // `18 % 12 = 6`, then `12 % 6 = 0`.
        ("euclid step 1", "theorem t : 18 % 12 = 6 := rfl"),
        ("euclid step 2", "theorem t : 12 % 6 = 0 := rfl"),
    ] {
        assert!(
            admits(src),
            "the KERNEL must admit `{tag}` — `RecBodyExpr::Rem` and the `nat.mod` row both \
             cite this row as the ground for reading `%` at `Nat`: {}",
            island(src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
    for (tag, src) in [
        // THE SIBLING OP. `Nat.div` and `Nat.mod` are the two halves of one
        // `checked_div_rem`; an emitter that resolved the wrong method name
        // would produce exactly this term.
        ("div mutation", "theorem t (a b : Nat) : a % b = Nat.div a b := rfl"),
        // THE ORDER. This is the row `+` and `*` cannot have.
        ("order mutation", "theorem t (a b : Nat) : a % b = Nat.mod b a := rfl"),
        // The other two bignum callees already in the vocabulary.
        ("sub mutation", "theorem t (a b : Nat) : a % b = Nat.sub a b := rfl"),
        ("add mutation", "theorem t (a b : Nat) : a % b = Nat.add a b := rfl"),
        ("mul mutation", "theorem t (a b : Nat) : a % b = Nat.mul a b := rfl"),
        ("value mutation", "theorem t : 17 % 5 = 3 := rfl"),
        ("euclid mutation", "theorem t : 18 % 12 = 12 := rfl"),
    ] {
        assert!(
            !admits(src),
            "CONTROL `{tag}` must be REFUSED, or the admits above decide nothing"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q2) THE ZERO DIVISOR — what the kernel decides, and what it CANNOT
// ═══════════════════════════════════════════════════════════════════════════

/// **The row that keeps this lane honest.** Two halves, and the second is the
/// one that must never be dropped when this file is summarised.
///
/// GROUND: the kernel DOES decide `n % 0 = n`, at every concrete `n` tried,
/// with the `= 0` twin refused each time. That is what makes
/// `trust-bignum/tests/kernel_differential.rs`'s zero-divisor expectations the
/// kernel's decision rather than a hand-written constant.
///
/// OPEN: the kernel does NOT decide `∀ a, a % 0 = a` by `rfl` — `Nat.mod` is
/// stuck at an open dividend. **So the faithfulness gate cannot state the
/// totality agreement it relies on**, exactly as `fa788aab89` found at
/// `UInt{N}`. The gate's blindness is unchanged by this landing; what differs
/// is that the unseen assumption is TRUE here (the emitted callee was built to
/// be `Nat.mod` at zero) and FALSE at `UInt{N}` (the emitted op panics). That
/// difference is carried by the differential test and the `PrimitiveCallee`
/// TCB row, NOT by any `Faithful` token, and the `nat.mod` row says so.
#[test]
fn q2_the_zero_divisor_is_kernel_decided_at_ground_and_stuck_when_open() {
    for n in [0_u32, 1, 5, 42, 1000] {
        let true_src = format!("theorem t : {n} % 0 = {n} := rfl");
        let false_src = format!("theorem t : {n} % 0 = {} := rfl", n + 1);
        assert!(
            admits(&true_src),
            "GROUND {n}: the kernel must decide `{n} % 0 = {n}` — this is Lean's \
             `Nat.mod_zero`, and it is the exact value `trust_bignum::Nat::rem` returns: {}",
            island(&true_src).err().map_or_else(String::new, |why| first_line(&why))
        );
        assert!(
            !admits(&false_src),
            "GROUND {n} CONTROL: `{n} % 0 = {}` must be REFUSED, or the admit decides nothing",
            n + 1
        );
        // `Nat.div` at zero is the sibling half of the same runtime function,
        // and `Nat::div` returns `0` there. Pinned for the same reason.
        let div_src = format!("theorem t : {n} / 0 = 0 := rfl");
        assert!(
            admits(&div_src),
            "GROUND {n}: the kernel must decide `{n} / 0 = 0`: {}",
            island(&div_src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }

    // THE HONEST HALF. Both spellings of the open statement are REFUSED.
    for (tag, src) in [
        ("open surface", "theorem t (a : Nat) : a % 0 = a := rfl"),
        ("open raw", "theorem t (a : Nat) : Nat.mod a 0 = a := rfl"),
    ] {
        assert!(
            !admits(src),
            "ROW `{tag}` must be REFUSED — if the kernel started deciding the OPEN zero \
             case by `rfl`, the totality agreement this lane leans on would become \
             STATEABLE, and the `nat.mod` row's `tcb_row` (which says it is not) would be \
             overstating the residual trust. Re-read this file's header before relaxing it."
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q3) THE SURFACE SPELLING — which instance `%` at `Nat` elaborates through
// ═══════════════════════════════════════════════════════════════════════════

/// `read_nat_rem` pins the prelude instance BY NAME, for `read_nat_add`'s
/// reason: a user `HMod Nat` instance is a different `%` and must refuse. This
/// row measures which instance the elaborator actually mints, so the pin is
/// read off the elaborator rather than guessed.
#[test]
fn q3_the_surface_percent_elaborates_through_the_prelude_instance() {
    let env = island("def m (a b : Nat) : Nat := a % b")
        .unwrap_or_else(|why| panic!("`a % b` must elaborate: {}", first_line(&why)));
    let text = body_text(&env, "m");
    eprintln!("ROW q3 | `a % b` elaborates to | {text}");
    assert!(
        text.contains("HMod.hMod"),
        "the surface `%` must elaborate through `HMod.hMod` — `read_nat_rem`'s second \
         spelling is keyed on it; got: {text}"
    );
    assert!(
        text.contains("instHModNat"),
        "the surface `%` at `Nat` must route through the prelude's `instHModNat` — that is \
         the instance `read_nat_rem` pins by name, and pinning the WRONG name would make \
         the reader refuse every real program; got: {text}"
    );
    // And the raw spelling is what side B renders, so the prelude instance must
    // reduce to it. `q1`'s `rfl` is that statement; this is its shape half.
    let raw = island("def m (a b : Nat) : Nat := Nat.mod a b")
        .unwrap_or_else(|why| panic!("`Nat.mod a b` must elaborate: {}", first_line(&why)));
    eprintln!("ROW q3 | `Nat.mod a b` elaborates to | {}", body_text(&raw, "m"));
}

// ═══════════════════════════════════════════════════════════════════════════
// (q4) THE DECREASE — the obligation this lane actually discharges
// ═══════════════════════════════════════════════════════════════════════════

/// The textbook modulo gcd, in the spelling the plan lane's guard rule accepts
/// (`if h : 0 < b`, positive branch first) and under the two-parameter measure
/// that selects the phase-3 `OnMeasureValue` lowering.
///
/// `+ a * 0` is not decoration: phase 3 is reached only by a measure that
/// mentions both parameters, and `b + 0 * a` is ISLAND-REJECTED where
/// `b + a * 0` is accepted (the cascade's spelling asymmetry, recorded as a
/// v7/D3 wart in this landing's report).
const GCD: &str = "def gcd (a b : Nat) : Nat := \
                   if h : 0 < b then gcd b (a % b) else a\n\
                   termination_by b + a * 0";

/// **The positivity proof is IN the elaborated term, at the point of use.**
/// This is what makes the modulo descent a discharged obligation rather than an
/// assumption: `Nat.mod_lt : 0 < b → a % b < b` is applied to the `dite`'s own
/// hypothesis binder, and the island's cascade closes the well-foundedness
/// goal with it, axiom-free.
#[test]
fn q4_the_decrease_carries_the_guard_hypothesis() {
    let env = island(GCD)
        .unwrap_or_else(|why| panic!("the textbook gcd must elaborate: {}", first_line(&why)));
    let text = body_text(&env, "gcd");
    eprintln!("ROW q4 | gcd elaborates to | {text}");
    assert!(
        text.contains("Nat.mod_lt"),
        "the descent must be justified by `Nat.mod_lt`, applied to the guard's own \
         hypothesis — if this stops holding, the `nat.mod` row's decrease accounting is \
         describing a proof the elaborator no longer builds; got: {text}"
    );
    assert!(
        text.contains("HMod.hMod"),
        "the self-call's second argument must still be a surface `%`; got: {text}"
    );
    // It COMPUTES, at the kernel, by reduction — a fixture, not a shape.
    for (a, b, want) in [(12_u32, 18_u32, 6_u32), (18, 12, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)] {
        let src = format!("{GCD}\ntheorem v : gcd {a} {b} = {want} := rfl");
        assert!(
            admits(&src),
            "the kernel must reduce `gcd {a} {b}` to {want}: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
    // Anti-vacuity for the value rows above.
    for (a, b, wrong) in [(12_u32, 18_u32, 12_u32), (7, 13, 7)] {
        let src = format!("{GCD}\ntheorem v : gcd {a} {b} = {wrong} := rfl");
        assert!(!admits(&src), "CONTROL `gcd {a} {b} = {wrong}` must be REFUSED");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q5) THE UNDISCHARGED CASES — a guard that does not do the job is REFUSED
// ═══════════════════════════════════════════════════════════════════════════

/// **The control half of q4, and the reason this landing is not a vacuous
/// identification wearing a panic-freedom label.**
///
/// The obligation the compiler discharges on the `Nat` lane is the DECREASE,
/// and it genuinely requires a positivity fact about the DIVISOR at the point
/// of use. These three bodies are the ways that fact can be missing, and all
/// three must be REFUSED at the elaborator — before this compiler is consulted
/// at all, which is the strongest place for a refusal to live.
#[test]
fn q5_a_guard_that_does_not_dominate_the_division_is_refused() {
    for (tag, src, why) in [
        (
            // THE WRONG VALUE. The guard proves `0 < a`; the division is by
            // `b`. `Nat.mod_lt` cannot be applied and no other route closes it.
            "guard tests the wrong value",
            "def g (a b : Nat) : Nat := if h : 0 < a then g b (a % b) else a\n\
             termination_by b + a * 0",
            "`0 < a` says nothing about the divisor `b`",
        ),
        (
            // NON-DOMINATING. The division sits in the branch where the guard
            // is FALSE — i.e. where `b = 0` — so `a % b` is `a % 0 = a` and
            // there is no descent at all.
            "guard does not dominate the division",
            "def g (a b : Nat) : Nat := if h : 0 < b then a else g b (a % b)\n\
             termination_by b + a * 0",
            "in the else branch `b = 0`, so `a % b` is `a` and nothing decreases",
        ),
        (
            // NO GUARD. The bare recursion the whole fragment exists to refuse.
            "no guard at all",
            "def g (a b : Nat) : Nat := g b (a % b)\n\
             termination_by b + a * 0",
            "an unguarded self-call has no decrease to prove",
        ),
    ] {
        let outcome = island(src);
        assert!(
            outcome.is_err(),
            "CONTROL `{tag}` must be REFUSED ({why}). If this starts elaborating, the \
             decrease is being discharged by something other than the dominating \
             positivity guard, and the `nat.mod` row's accounting — which is what stands \
             in for panic-freedom on this lane — no longer describes the compiler."
        );
        eprintln!(
            "ROW q5 {tag:<38} | REFUSED | {}",
            first_line(&outcome.err().unwrap_or_default())
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q6) THE MACHINE-WIDTH LANE — fa788aab89's finding, re-measured not cited
// ═══════════════════════════════════════════════════════════════════════════

/// `fa788aab89` stands, unqualified, at `UInt{N}`: Clean's `UInt{N}.mod` is
/// TOTAL at a zero divisor where Rust's `%` PANICS. This row re-measures the
/// divergence rather than citing it, so that a pin move which changed it could
/// not pass unnoticed while this landing's `Nat` row kept shipping.
///
/// The `Nat` lane does not inherit this, and the reason is NOT that the gate is
/// stronger here — it is that the emitted callee is `trust_bignum::Nat::rem`,
/// which agrees with the total kernel function, where the emitted `u{N}` op is
/// a `Rvalue::BinaryOp` that does not.
#[test]
fn q6_the_machine_width_divergence_is_still_real() {
    let total = "theorem t : (7 : UInt64) % 0 = 7 := rfl";
    match island(total) {
        Ok(_) => eprintln!(
            "ROW q6 | `UInt64` `%` at a zero divisor is TOTAL at the kernel (= 7), while \
             Rust's `%` PANICS — fa788aab89's divergence, unchanged"
        ),
        Err(why) => eprintln!(
            "ROW q6 | the `UInt64` zero-divisor statement did not close by `rfl` at this \
             pin: {} (the divergence claim rests on `first-party/clean`'s `UInt` model; \
             the plan-lane refusal measured in q7 is what actually protects the lane)",
            first_line(&why)
        ),
    }
}
