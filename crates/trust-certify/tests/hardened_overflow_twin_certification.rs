// The hardened `Overflow(Add)` twin and its primary: TWO SYNTAXES FOR ONE
// PROPOSITION, and only one of them is kernel-certifiable.
//
// Subject: `tests/self-proof/strict-pass-frontier/blocked.rs`
//
// ```rust
// pub fn add_guarded(a: i32, b: i32) -> i32 {
//     if a >  1_000_000 { return 0; }
//     if a < -1_000_000 { return 0; }
//     if b >  1_000_000 { return 0; }
//     if b < -1_000_000 { return 0; }
//     a + b
// }
// ```
//
// Under the default `unix_hardened` profile that body emits TWO obligations at
// the same span, both VIOLATION formulas (a solver discharges them by proving
// UNSAT):
//
//   * `[arithmetic_overflow_add]`                   -> PROVED (interval), kernel-certified
//   * `[hardened_panic_boundary] Overflow(Add)`     -> PROVED (interval), NOT certified
//
// so the crate fails the strict lane with
// `[hardened_panic_boundary] UNKNOWN (interval): Proved label lacked exact
// kernel/native proof authority`.
//
// The formulas below are the EXACT formulas stage1 `trustc` at 31ccf1b56 hands
// `trust_certify::certify_vc`, captured with
//
// ```text
// TRUST_DUMP_V2_VC=1 trustc --crate-type=lib --edition 2021 -Ztrust-verify=on \
//   -Ztrust-verify-profile=unix_hardened -C overflow-checks=yes \
//   --emit=metadata -o /dev/null blocked.rs
// ```
//
// They are LOGICALLY EQUIVALENT and BOTH UNSAT — z3 4.x agrees on both, and a
// mutation of the fixture (guard bound raised to 2_000_000_000) turns BOTH SAT
// with the same witness `a = 147483648, b = 2000000000` that `ay-in-process`
// reports. So no engine is wrong about the mathematics. The two differ only in
// how the out-of-range core is SPELLED:
//
//   primary: `Or([ Lt(a+b, i32::MIN), Gt(a+b, i32::MAX) ])`
//   twin:    `Not(And([ Le(i32::MIN, a+b), Le(a+b, i32::MAX) ]))`
//            plus a definition of the fresh checked-op overflow flag
//            `_7.1 <-> (a+b < i32::MIN | a+b > i32::MAX)`, which occurs nowhere
//            else in the formula.
//
// This test pins that asymmetry so it cannot move unobserved. It is a COVERAGE
// record, not a soundness bug: declining to certify is fail-closed.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use trust_types::{
    BinOp, Formula, HardenedVcCategory, Sort, SourceSpan, Ty, VcKind, VerificationCondition,
};

fn span() -> SourceSpan {
    SourceSpan {
        file: "blocked.rs".to_string(),
        line_start: 24,
        col_start: 4,
        line_end: 24,
        col_end: 9,
    }
}

/// `[arithmetic_overflow_add]` — the per-statement arithmetic-safety row.
fn primary_violation() -> Formula {
    Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_4".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::Eq(Box::new(Formula::Var("_5".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_6".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::And(vec![Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_4".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::Eq(Box::new(Formula::Var("_5".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_6".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::Or(vec![Formula::Lt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(-2147483648))), Formula::Gt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(2147483647)))])])])])])])])
}

/// `[hardened_panic_boundary] mir_assert::Overflow(Add)` — the `unix_hardened` twin.
fn twin_violation() -> Formula {
    Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_4".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::Eq(Box::new(Formula::Var("_5".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Eq(Box::new(Formula::Var("_6".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::And(vec![Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(1000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-1000000))))), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_7.1".to_string(), Sort::Bool)), Box::new(Formula::Or(vec![Formula::Lt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(-2147483648))), Formula::Gt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(2147483647)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Not(Box::new(Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int))))), Formula::Le(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(2147483647)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))])])])])])])
}

fn primary_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        function: "add_guarded".into(),
        location: span(),
        formula: primary_violation(),
        contract_metadata: None,
        obligation: None,
    }
}

fn twin_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Add)".to_string(),
            detail: "attempt to add with overflow".to_string(),
        },
        function: "add_guarded".into(),
        location: span(),
        formula: twin_violation(),
        contract_metadata: None,
        obligation: None,
    }
}

/// The primary certifies. This is the control: without it a decline on the twin
/// would only say "the kernel certified nothing today".
#[test]
fn primary_arithmetic_overflow_row_is_kernel_certified() {
    assert!(
        trust_certify::certify_vc(&primary_vc()).is_some(),
        "the per-statement arithmetic-overflow violation must kernel-certify; \
         if this fails the twin comparison below proves nothing"
    );
}

/// The twin does not — TODAY. Both formulas are UNSAT (z3-confirmed), so this
/// is a certifier COVERAGE boundary, not a refutation and not a soundness bug.
///
/// WHEN THIS FLIPS: `blocked.rs` starts passing `targo trust check`, and
/// `scripts/trust_strict_pass_frontier.sh`'s `run blocked expect-fail` must be
/// updated deliberately, with the measurement that justified it.
#[test]
fn hardened_overflow_twin_is_not_kernel_certified_today() {
    assert!(
        trust_certify::certify_vc(&twin_vc()).is_none(),
        "the hardened Overflow(Add) twin now certifies — if this is the intended \
         improvement, flip blocked.rs to expect-pass in \
         scripts/trust_strict_pass_frontier.sh and update this test"
    );
}

/// The discriminator is the FORMULA, not the `VcKind`. Cross the kinds over the
/// formulas: certification follows the formula in both directions.
///
/// This is what rules out "the certifier refuses hardened rows on principle".
#[test]
fn certification_follows_the_formula_not_the_vc_kind() {
    let mut hardened_kind_primary_formula = twin_vc();
    hardened_kind_primary_formula.formula = primary_violation();
    assert!(
        trust_certify::certify_vc(&hardened_kind_primary_formula).is_some(),
        "a HardenedBoundary row carrying the PRIMARY formula must certify: the \
         certifier does not discriminate on VcKind"
    );

    let mut primary_kind_twin_formula = primary_vc();
    primary_kind_twin_formula.formula = twin_violation();
    assert!(
        trust_certify::certify_vc(&primary_kind_twin_formula).is_none(),
        "an ArithmeticOverflow row carrying the TWIN formula must still decline: \
         the gap is the formula shape"
    );
}

// ---------------------------------------------------------------------------
// WHICH CONJUNCT IS THE BLOCKER — and the answer refuted the hypothesis I
// pre-registered.
//
// The twin differs from the primary in exactly two places, so each was changed
// ALONE, on the twin's own formula, and the certifier asked again. Both
// rewrites preserve the proposition (De Morgan; dropping the definition of a
// Bool variable that occurs in no other conjunct), so a flip is a
// certifier-COVERAGE fact, not a semantic one.
//
// PRE-REGISTERED (2026-08-27): "neither rewrite alone recovers the twin".
// MEASURED: WRONG. De Morgan alone recovers it; the flag definition is inert.
//
//   de-morgan only          -> certified = TRUE     <- the sole blocker
//   flag-def dropped only   -> certified = false
//
// So the whole gap is one spelling. `hardened.rs:761` builds the violation as
// `Formula::Not(Box::new(in_range.clone()))` — a NEGATED CONJUNCTION — while the
// per-statement lane emits the De Morgan dual `Or([Lt(sum, lo), Gt(sum, hi)])`.
// `certify_disjunctive_contradiction` scans the normalized conjunct pool for
// `Formula::Or(..)` (`lib.rs`, `let Formula::Or(disjuncts) = candidate else
// { continue }`), so the negated conjunction never reaches the recognizer that
// would refute it — and the kernel certifies nothing it was never handed.
//
// DO NOT "FIX" THIS BY RELAXING THE CERTIFIER. The safety control at the bottom
// of this file is the bar any normalization must clear: the same rewrite applied
// to a violation that is genuinely SAT must still certify NOTHING.
// ---------------------------------------------------------------------------

/// `Not(And([Le(lo, s), Le(s, hi)]))` -> `Or([Lt(s, lo), Gt(s, hi)])`, everywhere.
fn demorgan(f: &Formula) -> Formula {
    match f {
        Formula::Not(inner) => match inner.as_ref() {
            Formula::And(cs) if cs.len() == 2 => match (&cs[0], &cs[1]) {
                (Formula::Le(lo, s1), Formula::Le(s2, hi)) if s1 == s2 => Formula::Or(vec![
                    Formula::Lt(s1.clone(), lo.clone()),
                    Formula::Gt(s2.clone(), hi.clone()),
                ]),
                _ => Formula::Not(Box::new(demorgan(inner))),
            },
            _ => Formula::Not(Box::new(demorgan(inner))),
        },
        Formula::And(cs) => Formula::And(cs.iter().map(demorgan).collect()),
        Formula::Or(cs) => Formula::Or(cs.iter().map(demorgan).collect()),
        other => other.clone(),
    }
}

/// Drop every `Eq(Var(_, Bool), Or([..]))` conjunct — the checked-op overflow
/// flag definition. In this body `_7.1` occurs in no other conjunct, so the
/// equation constrains nothing and dropping it cannot change satisfiability.
fn drop_overflow_flag_defs(f: &Formula) -> Formula {
    match f {
        Formula::And(cs) => Formula::And(
            cs.iter()
                .filter(|c| {
                    !matches!(c, Formula::Eq(l, r)
                        if matches!(l.as_ref(), Formula::Var(_, Sort::Bool))
                            && matches!(r.as_ref(), Formula::Or(_)))
                })
                .map(drop_overflow_flag_defs)
                .collect(),
        ),
        Formula::Or(cs) => Formula::Or(cs.iter().map(drop_overflow_flag_defs).collect()),
        Formula::Not(inner) => Formula::Not(Box::new(drop_overflow_flag_defs(inner))),
        other => other.clone(),
    }
}

/// THE LOCATED CAUSE: De Morgan alone recovers the twin.
#[test]
fn de_morgan_alone_recovers_the_twin() {
    let mut vc = twin_vc();
    vc.formula = demorgan(&twin_violation());
    assert_ne!(vc.formula, twin_violation(), "the rewrite must actually change the formula");
    assert!(
        trust_certify::certify_vc(&vc).is_some(),
        "de Morgan no longer recovers the twin — the located cause has moved; \
         re-run the isolation before trusting any plan built on it"
    );
}

/// The overflow-flag definition is NOT the blocker: dropping it changes nothing.
#[test]
fn dropping_the_overflow_flag_definition_alone_does_not_recover_the_twin() {
    let mut vc = twin_vc();
    vc.formula = drop_overflow_flag_defs(&twin_violation());
    assert_ne!(vc.formula, twin_violation(), "the rewrite must actually change the formula");
    assert!(
        trust_certify::certify_vc(&vc).is_none(),
        "dropping the flag definition now recovers the twin — the cause is no \
         longer the De Morgan spelling alone"
    );
}

// ---------------------------------------------------------------------------
// SAFETY CONTROL — the bar any De Morgan normalization must clear.
//
// The formula below is the SAME hardened `Overflow(Add)` twin for the mutation
// of `blocked.rs` whose guard bound is raised to 2_000_000_000, where `a + b`
// GENUINELY overflows. z3 4.x reports it SAT with `a = 147483648,
// b = 2000000000`, and the shipping compiler reports
// `[hardened_panic_boundary] FAILED (ay-in-process); counterexample:
// … a = 2000000000, b = 147483648` — a model that SATISFIES every guard, so the
// refutation is real and reachable, not an over-rejection.
//
// It must certify NOTHING, before or after the rewrite. If a future
// normalization makes this certify, that normalization ships a false PROVE.
// ---------------------------------------------------------------------------

/// The genuinely-overflowing twin, exactly as `trustc` emits it.
fn overflowing_twin_violation() -> Formula {
    Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2000000000))))), Formula::Eq(Box::new(Formula::Var("_4".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-2000000000))))), Formula::Eq(Box::new(Formula::Var("_5".to_string(), Sort::Bool)), Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2000000000))))), Formula::Eq(Box::new(Formula::Var("_6".to_string(), Sort::Bool)), Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-2000000000))))), Formula::And(vec![Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2000000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-2000000000))))), Formula::Not(Box::new(Formula::Gt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2000000000))))), Formula::Not(Box::new(Formula::Lt(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-2000000000))))), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(-2147483648))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_7.1".to_string(), Sort::Bool)), Box::new(Formula::Or(vec![Formula::Lt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(-2147483648))), Formula::Gt(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(2147483647)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Not(Box::new(Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int))))), Formula::Le(Box::new(Formula::Add(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int)))), Box::new(Formula::Int(2147483647)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(-2147483648)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(2147483647)))])])])])])])
}

#[test]
fn a_genuinely_overflowing_twin_certifies_nothing_before_or_after_de_morgan() {
    let mut raw = twin_vc();
    raw.formula = overflowing_twin_violation();
    assert!(
        trust_certify::certify_vc(&raw).is_none(),
        "FALSE PROVE: a violation z3 reports SAT was kernel-certified"
    );

    let mut rewritten = twin_vc();
    rewritten.formula = demorgan(&overflowing_twin_violation());
    assert_ne!(
        rewritten.formula,
        overflowing_twin_violation(),
        "the rewrite must actually change the formula, or this control is vacuous"
    );
    assert!(
        trust_certify::certify_vc(&rewritten).is_none(),
        "FALSE PROVE: De Morgan normalization certified a SATISFIABLE violation — \
         `a = 147483648, b = 2000000000` really does overflow i32"
    );
}

// ---------------------------------------------------------------------------
// THE SECOND RECOGNIZER — the regression #222 could plausibly have caused, and
// did not.
//
// `blocked.rs`'s twin declines, but `widen_add.rs`'s twin CERTIFIES today with
// the very `Not(And([Le, Le]))` spelling #222 replaced — a different recognizer
// closes it, because there the operand bounds come from `as u16` casts rather
// than from dominating `if` guards. So "the certifier cannot see a negated
// conjunction" is FALSE in general, and a producer-side re-spelling that fixed
// `blocked` while breaking `widen_add` would have traded one silent coverage
// hole for another.
//
// Measured before the producer change landed: before=true, after=true. This
// pins the BEFORE half as a live control (a recognizer that stopped firing
// would make the AFTER half vacuous) and the AFTER half as the regression bar.
// The formula is the exact one stage1 `trustc` at 80bf87210 handed
// `certify_vc` for `widen_add.rs`, captured with `TRUST_DUMP_V2_VC=1`.
// ---------------------------------------------------------------------------

/// `[hardened_panic_boundary] mir_assert::Overflow(Add)` for `widen_add.rs`'s
/// `(a as u16) + (b as u16)`, in the PRE-#222 negated-conjunction spelling.
fn widen_add_twin_violation_pre_222() -> Formula {
    Formula::And(vec![Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::And(vec![Formula::Ge(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(0))), Formula::Le(Box::new(Formula::Var("a".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::Ge(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(0))), Formula::Le(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::Or(vec![Formula::Gt(Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int)))), Box::new(Formula::Int(65535))), Formula::Eq(Box::new(Formula::Var("_0".to_string(), Sort::Int)), Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int)))))]), Formula::Le(Box::new(Formula::Var("_0".to_string(), Sort::Int)), Box::new(Formula::Int(510))), Formula::Le(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(255))), Formula::Le(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Int(255))), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_5.1".to_string(), Sort::Bool)), Box::new(Formula::Or(vec![Formula::Lt(Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int)))), Box::new(Formula::Int(0))), Formula::Gt(Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int)))), Box::new(Formula::Int(65535)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_3".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(65535)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_4".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Int(65535)))]), Formula::And(vec![Formula::Eq(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("a".to_string(), Sort::Int))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_3".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::Eq(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Var("b".to_string(), Sort::Int))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_4".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::Not(Box::new(Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int))))), Formula::Le(Box::new(Formula::Add(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Var("_4".to_string(), Sort::Int)))), Box::new(Formula::Int(65535)))]))), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_3".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(65535)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_4".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Int(65535)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_3".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_3".to_string(), Sort::Int)), Box::new(Formula::Int(255)))]), Formula::And(vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("_4".to_string(), Sort::Int))), Formula::Le(Box::new(Formula::Var("_4".to_string(), Sort::Int)), Box::new(Formula::Int(255)))])])])])])])])
}

fn widen_add_twin_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Add)".to_string(),
            detail: "attempt to add with overflow".to_string(),
        },
        function: "add_u8".into(),
        location: SourceSpan {
            file: "widen_add.rs".to_string(),
            line_start: 39,
            col_start: 4,
            line_end: 39,
            col_end: 4,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn the_cast_range_recognizer_survives_the_canonical_respelling() {
    // CONTROL: the pre-#222 spelling really does certify here. Without this the
    // assertion below would pass even if the recognizer had died entirely.
    assert!(
        trust_certify::certify_vc(&widen_add_twin_vc(widen_add_twin_violation_pre_222()))
            .is_some(),
        "control lost: `widen_add`'s twin no longer certifies in its ORIGINAL \
         negated-conjunction spelling, so the comparison below proves nothing"
    );

    let respelled = demorgan(&widen_add_twin_violation_pre_222());
    assert_ne!(
        respelled,
        widen_add_twin_violation_pre_222(),
        "the rewrite must actually change the formula, or this test is vacuous"
    );
    assert!(
        trust_certify::certify_vc(&widen_add_twin_vc(respelled)).is_some(),
        "REGRESSION: the canonical disjunctive spelling that #222 made the \
         producer emit LOSES `widen_add`'s certification — the fix would be \
         trading `blocked.rs`'s coverage hole for this one"
    );
}
