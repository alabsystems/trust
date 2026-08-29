// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R3b FORMULATION SURVEY — the four `gcd` formulations, and why the fuel
//! form is the one that landed.**
//!
//! Promoted from a probe on 2026-08-27. Measured at the elaborator
//! (`CleanIslandSession`, the exact pipeline `clean_origin_mir` drives) and at
//! the Trust readers (`plan_clean_origin_body`), at the CURRENT superproject
//! pin. Harness verbatim from `r6_nat_mul_probes` /
//! `r7_arity_widening_probes`, so an ISLAND rejection and a CALL-lane refusal
//! are never confused — which is the whole point: three of the four candidates
//! die at the ELABORATOR, not at this compiler, and a survey that conflated the
//! two would have sent R3b to rewrite the wrong layer.
//!
//! | form | verdict at this pin |
//! |---|---|
//! | (a) two-call subtractive, `termination_by a + b` | ISLAND rejects: no decreasing proof was found |
//! | (b) **branch-free 2-arg, `termination_by a + 2*b`** | **ELABORATES, PLANS, EMITS and RUNS** — see the R3d note below |
//! | (c) one-call swap `g b (a - b)` | ISLAND rejects: the measure genuinely does not decrease |
//! | (d) fuel-carried `gcdF f a b`, `termination_by f` | ELABORATES and PLANS; superseded as the CALLED form by (b) |
//! | the ratified `gcd b (a % b)`, `termination_by b` | ELABORATES; the CALL lane refuses — on the phase-2 `n - 1` belt since §R8, no longer on `HMod.hMod` |
//! | **the ratified `gcd b (a % b)`, `termination_by b + a * 0`** | **ELABORATES, PLANS, EMITS and RUNS** — §R8, see the note below |
//!
//! **THE REFUSALS IN (a)–(c) ARE NOT THIS COMPILER'S.** They are recorded here
//! as assertions so that the day `first-party/clean` gains the sum-measure
//! lowering, these rows FAIL and the survey gets re-ranked instead of silently
//! staying stale. That is the intended signal, not a regression.
//!
//! # RE-RANKED 2026-08-27 — that day arrived, and this is the re-rank
//!
//! The pin now carries `wf_recursion::sum_measure` (`first-party/clean`
//! `6adb7beeb`), so **"a measure over more than one parameter is not lowered"
//! is no longer true of any row here** and the two assertions that pinned it
//! failed, exactly as the paragraph above intended. Measured at the new pin,
//! every multi-parameter row in (a) and (b) — `a + b`, `(a + b)`, `a + 2 * b`,
//! `a + b + b`, and the `min`/`max` surface spelling of the same map — now
//! reaches the DECREASE and dies there:
//!
//! > no decreasing proof was found for a recursive call site (tried: hypothesis
//! > lookup, `Nat.sub_lt`, `Nat.mod_lt` … then sum congruence via
//! > `Nat.add_lt_add_left`/`_right`/`Nat.add_lt_add`, then omega, simp_arith)
//!
//! **The ranking was unchanged and the reason for it moved one layer.** (d) was
//! still the form that elaborated and planned; what blocked (b) was no longer
//! the LOWERING but the discharge CASCADE — `((a-b)+(b-a)) + 2*(a-(a-b)) <
//! a + 2*b` given `0 < b` matched none of its lemmas. That is a strictly better
//! place for a blocker to be, and it is where the `gcd` increment then worked.
//!
//! # RE-RANKED AGAIN 2026-08-27 (§R3d) — (b) OVERTAKES (d)
//!
//! The prediction above came true from the other end. `first-party/clean`
//! `4f7bdab766` gained three general cascade tiers — sum positivity, the strict
//! linear residual, and a case split on `Nat.le_total` that substitutes the
//! larger parameter — and `termination_by a + 2 * b` now DISCHARGES,
//! axiom-free. `a + b + b` is the same measure spelled differently and
//! discharges too; `a + b` alone still does not, and neither does any
//! one-parameter measure, so the boundary is a real one and p3 keeps those rows.
//!
//! With the measure discharged, (b) is a phase-3 body and this compiler plans,
//! emits and gates it (`gcd_phase3_probes`, `control_18_wf_sum_measure_emitter_
//! mutation`). **(d)'s two-argument surface was a Rust wrapper supplying
//! `a + 2b` and therefore carried no proof claim about the recursion; (b)'s
//! two-argument surface IS the recursion.** That is the whole reason the ranking
//! moved.
//!
//! The reader side, unblocked earlier by the lowering itself, has its own file:
//! `tests/phase3_spine_reader_probes.rs`.
//!
//! **THE MODULO ROW — corrected 2026-08-28 (§R8), because the claim that used
//! to sit here was over-general in a precise way.**
//!
//! It used to read: "must NOT be 'fixed': commit `fa788aab89` measured that the
//! faithfulness gate is BLIND to the zero-divisor divergence between Clean's
//! total `Nat.mod` and Rust's panicking `%`. That refusal IS the safety."
//!
//! The first sentence is true **at a MACHINE WIDTH** and is unmoved: at
//! `UInt{N}` the emitted `%` is an `Rvalue::BinaryOp` carrying a panicking
//! zero-divisor `Assert`, the gate compares two TOTAL Clean terms and cannot
//! state the difference, and the plan-lane refusal is what prevents a false
//! verify. `control_21` (h) pins that refusal still firing and
//! `r8_nat_mod_probes` q6 re-measures the divergence itself.
//!
//! It was generalised to `Nat`, where it does not hold. At the bignum carrier
//! the emitted operation is `Call(trust_bignum::Nat::rem, [&a, &b])` —
//! `TemplateTerminator` has no `Assert` variant — and `Nat::rem` returns the
//! DIVIDEND at a zero divisor (Lean's `Nat.mod_zero`). **There is no emitted
//! panic path on that lane to be unsafe about.** So the `HMod.hMod` vocabulary
//! gap was never the safety property; it was a gap, and §R8 closed it.
//!
//! What replaces panic-freedom there is TOTALITY AGREEMENT of the carrier,
//! carried by `trust-bignum`'s kernel-differential test and the
//! `PrimitiveCallee` TCB row — **not** by a `Faithful` token, since the kernel
//! identification is vacuous at an open dividend (q2). The obligation the
//! compiler actually discharges is the DECREASE, and its undischarged cases
//! (guard on the wrong value, guard not dominating the division, no guard) are
//! REFUSED — `control_21` (f), and q5.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_origin::emit::plan_clean_origin_body;

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

/// Assert that a source is rejected by the ELABORATOR (not by this compiler),
/// and that the reason still mentions `expect`. Used for the candidates that
/// die at `first-party/clean`: if one of them starts elaborating, the pin has
/// gained a capability and this survey must be re-ranked.
fn assert_island_rejects(tag: &str, source: &str, expect: &str) {
    match island(source) {
        Ok(_) => panic!(
            "ROW {tag}: this now ELABORATES at the current pin. The formulation survey in \
             this file's header ranks the `gcd` candidates on the assumption that it does \
             not — re-rank it, and re-read `docs/design/2026-07-09-two-language-spec-\
             surface.md`'s sum-measure notes, before assuming R3b's fuel form is still the \
             cheapest route."
        ),
        Err(why) => assert!(
            why.contains(expect),
            "ROW {tag}: expected the elaborator to refuse with {expect:?}, got: {}",
            first_line(&why)
        ),
    }
}

/// Assert that a source ELABORATES and that THIS compiler's call lane refuses
/// it, with a reason mentioning `expect`.
fn assert_call_refuses(tag: &str, name: &str, source: &str, expect: &str) {
    let env = island(source)
        .unwrap_or_else(|why| panic!("ROW {tag}: must elaborate: {}", first_line(&why)));
    let refusal = plan_clean_origin_body(&env, name)
        .err()
        .unwrap_or_else(|| panic!("ROW {tag}: the call lane must REFUSE this"));
    assert!(
        refusal.note().contains(expect),
        "ROW {tag}: expected a refusal mentioning {expect:?}, got: {}",
        first_line(&refusal.note())
    );
}

fn row(tag: &str, name: &str, source: &str) {
    match island(source) {
        Err(why) => eprintln!("ROW {tag:<16} | ISLAND REJECTS | {}", first_line(&why)),
        Ok(env) => {
            let call = match plan_clean_origin_body(&env, name) {
                Ok(plan) => format!("PLANS {:?}", plan.shape()),
                Err(refusal) => format!("CALL REFUSES | {}", first_line(&refusal.note())),
            };
            eprintln!("ROW {tag:<16} | ISLAND OK      | {call}");
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
    eprintln!("ANATOMY {tag} | outer_lams={outer_lams} head={} args={}", render(head, 2), args.len());
    for (i, a) in args.iter().enumerate() {
        eprintln!("   arg[{i}] = {}", render(a, 5));
    }
    if args.len() >= 5 {
        let (fl, fbody) = peel(args[4]);
        eprintln!("   F: leading lambdas = {fl}");
        let (dh, da) = uncurry(fbody);
        eprintln!("   F body head = {} ({} args)", render(dh, 2), da.len());
        if da.len() == 5 {
            for (label, arm) in [("then", da[3]), ("else", da[4])] {
                let (_, abody) = peel(arm);
                eprintln!("   {label} arm full = {}", render(abody, 9));
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (p1) THE KERNEL PROBE — run BEFORE any producer. General truncated `-`.
// ═══════════════════════════════════════════════════════════════════════════

/// The single new identification every candidate below rests on: a general
/// `a - b` (both operands symbolic) is `Nat.sub a b`, and `Nat.sub` TRUNCATES
/// exactly as `trust_bignum::Nat::sub` does (`checked_sub(..).unwrap_or(ZERO)`).
#[test]
fn p1_kernel_decides_general_truncated_subtraction() {
    let ok = island(
        "theorem subSpelling (a b : Nat) : a - b = Nat.sub a b := rfl\n\
         theorem subTrunc : 1 - 3 = 0 := rfl\n\
         theorem minSpelling (a b : Nat) : a - (a - b) = Nat.sub a (Nat.sub a b) := rfl",
    );
    assert!(
        ok.is_ok(),
        "the KERNEL must decide general truncated `-`; `RecBodyExpr::Sub` rests on it: {}",
        ok.err().map_or_else(String::new, |why| first_line(&why))
    );

    for bad in [
        "theorem subWrong (a b : Nat) : a - b = Nat.add a b := rfl",
        // ORDER: `Nat.sub` is not symmetric and the kernel must say so.
        "theorem subFlip : 3 - 1 = 1 - 3 := rfl",
        // TRUNCATION is not saturation-at-one or anything else.
        "theorem subTruncWrong : 1 - 3 = 1 := rfl",
    ] {
        assert!(island(bad).is_err(), "CONTROL must be REFUSED: {bad}");
    }

    // **A MEASURED NON-FACT, recorded because I asserted it by mistake and the
    // kernel corrected me.** `a - (a + 1) = 0` is TRUE of `Nat`, but it is not
    // DEFINITIONAL: with `a` symbolic neither side reduces, so `rfl` does not
    // close it and it needs induction. That is the exact line this whole lane
    // sits on — the emitted `-` is faithful because CLOSED applications reduce
    // (`1 - 3 = 0` above), not because truncation is a symbolic rewrite. A
    // reader that "knew" truncation symbolically would be claiming a power the
    // kernel does not grant here.
    assert!(
        island("theorem subTrunc2 (a : Nat) : a - (a + 1) = 0 := rfl").is_err(),
        "if this now closes by `rfl`, `Nat.sub`'s reduction behaviour changed and every \
         claim in this file about what is definitional needs re-measuring"
    );

    // min / max / |diff| in the +,- vocabulary — the identities the step map
    // is built from, decided at the kernel on concrete values.
    let ids = island(
        "theorem min1 : 3 - (3 - 5) = 3 := rfl\n\
         theorem min2 : 5 - (5 - 3) = 3 := rfl\n\
         theorem diff1 : (3 - 5) + (5 - 3) = 2 := rfl\n\
         theorem diff2 : (5 - 3) + (3 - 5) = 2 := rfl",
    );
    assert!(
        ids.is_ok(),
        "`min` and `|diff|` in the `+`/`-` vocabulary are what the emitted step map computes; \
         the kernel must decide them: {}",
        ids.err().map_or_else(String::new, |why| first_line(&why))
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (p2) the RATIFIED example and the two-call subtractive family
// ═══════════════════════════════════════════════════════════════════════════

const GCD_MOD: &str = "def gcd (a b : Nat) : Nat := \
                       if h : 0 < b then gcd b (a % b) else a\n\
                       termination_by b";

/// The SAME body under a two-parameter measure, which selects the phase-3
/// (`OnMeasureValue`) lowering. §R8, 2026-08-28 — this one EMITS.
const GCD_MOD_PHASE3: &str = "def gcd (a b : Nat) : Nat := \
                              if h : 0 < b then gcd b (a % b) else a\n\
                              termination_by b + a * 0";

#[test]
fn p2_ratified_and_two_call_subtractive() {
    // THE RATIFIED MODULO FORM, at a SINGLE-parameter measure. It elaborates
    // and the CALL lane still refuses it — **but the reason moved, and the
    // reason it used to give was over-general.**
    //
    // Until §R8 this row refused on `HMod.hMod` being outside the arm
    // vocabulary, and the comment here said the refusal was `fa788aab89`'s
    // zero-divisor safety and "must NOT be fixed". That conflated two
    // different things. `fa788aab89`'s finding is about a MACHINE WIDTH, where
    // Rust's `%` lowers to an `Rvalue::BinaryOp` carrying a panicking `Assert`
    // that the gate cannot see; it is unmoved and still fires
    // (`control_21` (h), and `r8_nat_mod_probes` q6 re-measures the divergence).
    // At the `Nat` bignum carrier the emitted operation is
    // `Call(trust_bignum::Nat::rem, ..)`, which is TOTAL — there is no panic
    // path — so the vocabulary gap was never the safety property, it was just a
    // gap.
    //
    // What refuses THIS body now is the phase-2 belt: `OnParameter` requires
    // the decreasing argument to be exactly `n - 1`, and `a % b` is not. That
    // is a real, still-load-bearing rule, so the row keeps asserting a refusal
    // — it just names the rule that actually does the work.
    assert_call_refuses("p2 gcd%", "gcd", GCD_MOD, "DECREASING argument is not `n - 1`");

    // …and the SAME body under a two-parameter measure now PLANS, which is the
    // capability §R8 landed. Kept beside the refusal deliberately: the pair is
    // what shows the surviving refusal is about the LOWERING and not about `%`.
    let phase3 = island(GCD_MOD_PHASE3).expect("the phase-3 spelling must elaborate");
    assert!(
        plan_clean_origin_body(&phase3, "gcd").is_ok(),
        "the textbook modulo `gcd` under `termination_by b + a * 0` must PLAN — this is \
         §R8's capability, and `control_21` gates its emission end to end"
    );

    // (a) two-call subtractive, every measure spelling.
    let two_branch = |measure: &str| {
        format!(
            "def gcdSub (a b : Nat) : Nat := \
             if h : 0 < b then (if a >= b then gcdSub (a - b) b else gcdSub a (b - a)) else a\n\
             termination_by {measure}"
        )
    };
    // A MULTI-PARAMETER measure is refused BY THE ELABORATOR — since the
    // sum-measure landing (re-ranked 2026-08-27, see the header) at the
    // DECREASE rather than at the lowering. The two-branch map shrinks `a` in
    // one arm and `b` in the other, so the sum obligation needs a case split
    // the cascade does not do.
    for m in ["a + b", "(a + b)", "a + 2 * b"] {
        assert_island_rejects(&format!("p2 2call {m}"), &two_branch(m), "no decreasing proof");
    }
    // …and a single-parameter measure does not decrease either. Both refusals
    // now read the same; what distinguishes them is WHY, and the survey's
    // ranking (header) is what records that.
    for m in ["b", "a"] {
        assert_island_rejects(
            &format!("p2 2call {m}"),
            &two_branch(m),
            "no decreasing proof",
        );
    }

    // (c) one-call with swap: DEAD, and not because of Trust — the measure
    // genuinely does not decrease under `g b (a - b)`.
    assert_island_rejects(
        "p2 swap",
        "def gcdSwap (a b : Nat) : Nat := \
         if h : 0 < b then gcdSwap b (a - b) else a\n\
         termination_by b",
        "no decreasing proof",
    );
    // `gcdSwap2` fails at the DECLARATION, so the reported error is the
    // cascade ("Unknown constant: gcdSwap2") rather than a measure diagnosis.
    // Asserted as a plain rejection for that reason: pinning a substring here
    // would pin the shape of a cascade, not a decision.
    let swap2 = island(
        "def gcdSwap2 (a b : Nat) : Nat := \
         if h : 0 < b then gcdSwap2 b (a - b) else a\n\
         termination_by a + b",
    );
    assert!(
        swap2.is_err(),
        "ROW p2 swap2: the swap form must not elaborate at this pin — if it does, the \
         survey in this file's header must be re-ranked"
    );
    eprintln!("ROW p2 swap2 | ISLAND REJECTS | {}", first_line(&swap2.unwrap_err()));
}

// ═══════════════════════════════════════════════════════════════════════════
// (p3) (b) the ONE-CALL BRANCH-FREE subtractive form, direct 2-arg
// ═══════════════════════════════════════════════════════════════════════════
//
//   T(a,b) = (|a-b|, min a b),  base b = 0 -> a
//   |a-b| = (a - b) + (b - a)   min a b = a - (a - b)      (truncated `-`)
//   measure a + 2*b  strictly decreases by b on the guarded branch.

const GCD_BRANCHFREE: &str = "def gcdB (a b : Nat) : Nat := \
                              if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a\n\
                              termination_by a + 2 * b";

#[test]
fn p3_branch_free_direct_two_arg() {
    // A TWO-PARAMETER measure — refused by the ELABORATOR. This is the row
    // that decides R3b's route: the branch-free map is exactly what the fuel
    // form computes, so the ONLY thing separating (b) from (d) is whether
    // termination is carried by a sum measure or by a countdown parameter.
    //
    // RE-RANKED 2026-08-27 (see the header): before the sum-measure landing
    // this row died at the LOWERING ("a measure over more than one parameter");
    // it now reaches the DISCHARGE and dies there. The obligation
    // `((a-b)+(b-a)) + 2*(a-(a-b)) < a + 2*b` given `0 < b` matches none of the
    // cascade's lemmas (`Nat.sub_lt`, `Nat.add_lt_add_left`/`_right`,
    // `Nat.mod_lt`), which is exactly what was predicted before the pin moved.
    //
    // **RE-RANKED AGAIN 2026-08-27 (R3d), and this one is the finish.** The pin
    // moved to `first-party/clean` `4f7bdab766`, whose cascade gained three
    // general tiers — sum positivity, the strict linear residual, and a case
    // split on `Nat.le_total` that substitutes the larger parameter — and
    // `a + 2 * b` DISCHARGES. This row therefore splits: the two measures the
    // cascade can now prove elaborate AND plan; the ones it still cannot are
    // unchanged, and are kept so the boundary stays visible.
    for m in ["a + 2 * b", "a + b + b"] {
        let src = format!(
            "def gcdB (a b : Nat) : Nat := \
             if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a\n\
             termination_by {m}"
        );
        let env = island(&src).unwrap_or_else(|why| {
            panic!(
                "ROW p3 bf {m}: the pin's cascade must still discharge this measure — it is what \
                 makes the two-argument `gcd` callable at all (`gcd_phase3_probes`): {}",
                first_line(&why)
            )
        });
        let plan = plan_clean_origin_body(&env, "gcdB").unwrap_or_else(|refusal| {
            panic!("ROW p3 bf {m}: …and the CALL lane must plan it: {}", first_line(&refusal.note()))
        });
        assert_eq!(
            format!("{:?}", plan.shape()),
            "WellFoundedNatRec { zero_value: Param(0), nonzero_value: Rec, \
             rec_args: [Add(Sub(Param(0), Decreasing), Sub(Decreasing, Param(0))), \
             Sub(Param(0), Sub(Param(0), Decreasing))], measure_index: 1, \
             lowering: OnMeasureValue }",
            "ROW p3 bf {m}: both spellings of the same measure must give ONE plan"
        );
        eprintln!("ROW p3 bf {m:<10} | ISLAND OK | PLANS (phase 3)");
    }
    // `a + b` alone does NOT decrease under this map (`|a-b| + min a b` is
    // `max a b`, which is not below `a + b` when one of them is 0), and the
    // cascade says so rather than this compiler.
    for m in ["a + b"] {
        let src = format!(
            "def gcdB (a b : Nat) : Nat := \
             if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a\n\
             termination_by {m}"
        );
        assert_island_rejects(&format!("p3 bf {m}"), &src, "no decreasing proof");
    }
    // A one-parameter measure does not decrease under this map.
    for m in ["b", "a"] {
        let src = format!(
            "def gcdB (a b : Nat) : Nat := \
             if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a\n\
             termination_by {m}"
        );
        assert_island_rejects(&format!("p3 bf {m}"), &src, "no decreasing proof");
    }
    // The min/max SURFACE spelling of the same map fails identically, so the
    // blocker is the measure and not the `-` spelling.
    for m in ["a + 2 * b", "a + b"] {
        let src = format!(
            "def gcdM (a b : Nat) : Nat := \
             if h : 0 < b then gcdM (max a b - min a b) (min a b) else a\n\
             termination_by {m}"
        );
        assert_island_rejects(&format!("p3 minmax {m}"), &src, "no decreasing proof");
    }
    let _ = GCD_BRANCHFREE;
}

// ═══════════════════════════════════════════════════════════════════════════
// (p4) (d) THE FUEL FORM — one guard, one self-call, measure arg is `Pred`
// ═══════════════════════════════════════════════════════════════════════════
//
// The same branch-free Euclid map, with termination carried by a COUNTDOWN
// parameter. `(a,b)` reaches the fixed point `(g,0)` and STAYS there, so any
// fuel >= the step count returns `gcd a b`.

const GCD_FUEL: &str = "def gcdF (f a b : Nat) : Nat := \
                        if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
                        termination_by f";

/// A 2-arg surface written as a Clean wrapper over the fuelled loop.
const GCD_WRAPPER: &str = "def gcdF (f a b : Nat) : Nat := \
                           if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
                           termination_by f\n\
                           def gcd2 (a b : Nat) : Nat := gcdF (a + b + b) a b";

#[test]
fn p4_fuel_form() {
    anatomy("p4 gcdF", "gcdF", GCD_FUEL);
    // THE WINNER. Before R3b this row read "CALL REFUSES | its self-call
    // argument subtracts from something other than the recursion's own
    // parameter"; it now PLANS. `control_17` is its mutation battery and
    // `tests/ui/trust/clean_origin_wf_rec_gcd.rs` runs it.
    let env = island(GCD_FUEL).expect("the fuel form must elaborate at this pin");
    assert!(
        plan_clean_origin_body(&env, "gcdF").is_ok(),
        "the fuel form must PLAN — this is what R3b landed: {}",
        plan_clean_origin_body(&env, "gcdF").err().map_or_else(String::new, |r| first_line(&r.note()))
    );

    // …and the CLEAN-side 2-argument wrapper still does NOT, which is why the
    // wrapper in the run-pass fixture is written in RUST. There is no emittable
    // shape for a Clean `def` that calls a sibling Clean `def`.
    assert_call_refuses("p4 wrapper", "gcd2", GCD_WRAPPER, "outside the emittable fragment");
    row("p4 wrapper-loop", "gcdF", GCD_WRAPPER);
}

// ═══════════════════════════════════════════════════════════════════════════
// (p5) DOES THE FUEL FORM GENUINELY COMPUTE gcd? kernel reduction, several
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn p5_fuel_form_values_at_the_kernel() {
    // Small fuels first, so a heartbeat/reduction wall is visible as a WALL
    // and not mistaken for a wrong value.
    for (fuel, a, b, want) in [
        (1_u32, 5_u32, 0_u32, 5_u32),
        (2, 0, 5, 5),
        (4, 2, 2, 2),
        (6, 4, 6, 2),
        (10, 4, 6, 2),
        (8, 7, 3, 1),
        (13, 7, 3, 1),
        (10, 12, 18, 6),
        (48, 12, 18, 6),
    ] {
        let src = format!("{GCD_FUEL}\ntheorem v : gcdF {fuel} {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "`gcdF {fuel} {a} {b}` must reduce to `{want}` at the kernel: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }

    // REFUTING CONTROLS — without these the rows above are a rubber stamp.
    for (fuel, a, b, wrong) in [(10_u32, 4_u32, 6_u32, 3_u32), (48, 12, 18, 12), (13, 7, 3, 3)] {
        let src = format!("{GCD_FUEL}\ntheorem v : gcdF {fuel} {a} {b} = {wrong} := rfl");
        assert!(
            island(&src).is_err(),
            "CONTROL: `gcdF {fuel} {a} {b} = {wrong}` is false and must be REFUSED"
        );
    }

    // And through the two-argument wrapper, which is where the fuel bound
    // `a + b + b` is supplied. (`gcd_final_probes` carries the full table.)
    for (a, b, want) in [(12_u32, 18_u32, 6_u32), (7, 3, 1), (0, 5, 5)] {
        let src = format!("{GCD_WRAPPER}\ntheorem w : gcd2 {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "`gcd2 {a} {b}` must reduce to `{want}`: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (p6) FEATURE ISOLATION — which single feature does each candidate need?
// ═══════════════════════════════════════════════════════════════════════════

/// **FEATURE ISOLATION — which single feature each candidate needed.** Written
/// while R3b was still a plan; kept, and turned into assertions, because it is
/// what says the widening is the SUM of two independent capabilities rather
/// than one `gcd`-shaped special case. All four now plan.
fn assert_plans(tag: &str, name: &str, source: &str) {
    let env = island(source)
        .unwrap_or_else(|why| panic!("ROW {tag}: must elaborate: {}", first_line(&why)));
    assert!(
        plan_clean_origin_body(&env, name).is_ok(),
        "ROW {tag}: must PLAN after R3b: {}",
        plan_clean_origin_body(&env, name).err().map_or_else(String::new, |r| first_line(&r.note()))
    );
}

#[test]
fn p6_feature_isolation() {
    // (i) a general `a - b` as a THREADED (non-measure) self-call argument,
    //     with everything else exactly `addAcc`.
    assert_plans(
        "p6 sub-arg",
        "subArg",
        "def subArg (a b : Nat) : Nat := \
         if h : 0 < a then subArg (a - 1) (b - a) else b\n\
         termination_by a",
    );
    // (ii) a general `a - b` in the nonzero VALUE — and this row turned out to
    //      be the `scale` hazard wearing a `-`, which is why it is asserted as
    //      a REFUSAL. `b` is handed to the self-call BY ITSELF (a move) and is
    //      also read by the enclosing `b - a`, which the emitter would lower to
    //      a borrow AFTER the call. The move-aware rule catches it, exactly as
    //      it catches `scale`; I expected this one to plan and the compiler was
    //      right. Its planning twin is (iii) below, where the repeated
    //      parameter is never moved.
    assert_call_refuses(
        "p6 sub-val",
        "subVal",
        "def subVal (a b : Nat) : Nat := \
         if h : 0 < a then (b - a) + subVal (a - 1) b else b\n\
         termination_by a",
        "BY ITSELF",
    );
    // (iii) a parameter used MORE THAN ONCE in the arm (the `scale` hazard),
    //       but only ever in ARGUMENTS — never in the value after the call.
    assert_plans(
        "p6 reuse",
        "reuse",
        "def reuse (a b : Nat) : Nat := \
         if h : 0 < a then reuse (a - 1) (b + b) else b\n\
         termination_by a",
    );
    // (iv) ARITY 3 with the R3a vocabulary only (no new node) — is arity 3
    //      already reachable end to end?
    assert_plans(
        "p6 arity3",
        "acc3",
        "def acc3 (a b c : Nat) : Nat := \
         if h : 0 < a then acc3 (a - 1) (b + 1) (c + b) else c\n\
         termination_by a",
    );
    anatomy("p6 arity3", "acc3", "def acc3 (a b c : Nat) : Nat := \
         if h : 0 < a then acc3 (a - 1) (b + 1) (c + b) else c\n\
         termination_by a");
    // (v) the R3a baseline, which must be UNMOVED by the widening.
    assert_plans(
        "p6 addAcc",
        "addAcc",
        "def addAcc (a b : Nat) : Nat := \
         if h : 0 < a then addAcc (a - 1) (b + 1) else b\n\
         termination_by a",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (p7) the FULL refusal texts (v7/D3: does the refusal carry the fix?)
// ═══════════════════════════════════════════════════════════════════════════

/// **v7/D3 — a refusal must carry the fix, with options.** The modulo form is
/// the one `gcd` a user is most likely to write, so its refusal is the one that
/// most needs to be actionable. Printed in full (it is worth reading) and
/// asserted on the properties that make it a v7/D3 refusal rather than an
/// "unsupported".
#[test]
fn p7_refusal_texts() {
    let env = island(GCD_MOD).expect("the modulo form elaborates");
    let note = plan_clean_origin_body(&env, "gcd")
        .err()
        .expect("the modulo form must refuse")
        .note();
    eprintln!("\n──── NOTE for the RATIFIED `gcd b (a % b)` ────\n{note}\n");
    assert!(note.contains("options:"), "a refusal without options is an 'unsupported': {note}");
    assert!(
        note.contains("ensures"),
        "…and must name the reach-it-from-the-other-side route: {note}"
    );
    assert!(
        note.contains("truncated `-`"),
        "…and, since R3b, the stated vocabulary must include `-`, or the fragment \
         description quoted to users is stale: {note}"
    );

    // The winner, for contrast: it PLANS, so there is no refusal to read.
    let env = island(GCD_FUEL).expect("the fuel form elaborates");
    eprintln!(
        "\n──── `gcdF` PLANS {:?}\n",
        plan_clean_origin_body(&env, "gcdF").expect("gcdF plans").shape()
    );
}
