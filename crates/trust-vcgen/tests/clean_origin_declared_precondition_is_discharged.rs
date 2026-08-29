// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The caller-side precondition on a minted Clean-origin `def`, end to end
//! through the VC lane — and the two controls it is not allowed to pass
//! without.**
//!
//! The seam `fa788aab89` named: *"a caller-side precondition on the minted
//! `DefId` … its discharge is an ordinary Rust obligation, never a `Faithful`
//! token."* The producing half is `trust_clean_carrier`'s hypothesis lift
//! (`def safe_rem (a b : UInt64) (h : b ≠ 0)` → obligation `arg1 != 0`); this
//! file is the consuming half.
//!
//! # CONTROL 1 — a call site that VIOLATES the precondition must FAIL
//!
//! Not "must emit a row". A row that is satisfiable by construction proves
//! nothing, and the concurrency lane's `reach_a AND reach_b AND true`
//! obligations are the standing example of a label that reads like a claim. So
//! the violating call site is put to the REAL solver and must come back
//! refuted, and the SAME machinery on a call site that satisfies the
//! precondition must come back discharged. Either half alone is passable by a
//! broken implementation: one by emitting `false`, the other by emitting
//! `true`.
//!
//! # CONTROL 2 — a summary that cannot carry the precondition publishes nothing
//!
//! `650674bc71`'s rule, extended one layer up. That commit closed the DB layer:
//! a preconditioned definitional summary is withheld from the L0 subset and the
//! withholding is RECORDED, so call sites owe a fail-closed row instead of
//! silently reporting clean. The layer this file adds is the PRODUCER: a
//! Clean-origin summary whose obligations cannot all be rendered must not
//! publish its value facts either. `clean_origin_summary` is that rule made
//! structural — there is no argument order that publishes half.

use trust_types::clean_origin_precondition::{CleanOriginPrecondition, PreconditionOperand};
use trust_types::*;
use trust_vcgen::{
    FunctionSummary, SummaryDatabase, clean_origin_declared_precondition,
    clean_origin_declared_preconditions, clean_origin_summary,
    generate_callsite_precondition_vcs,
};

const CALLEE: &str = "clean_origin::safe_rem";

/// The formals a Clean-origin summary uses. Synthetic, exactly as the
/// compiler's producer mints them — they are substituted away wholesale at
/// rebinding and never reach a solver namespace.
fn formals() -> Vec<String> {
    vec!["__trust_clean_origin_arg0".to_string(), "__trust_clean_origin_arg1".to_string()]
}

/// `(h : b ≠ 0)` on a two-argument declaration: `arg1 != 0` at `u64`.
fn divisor_nonzero() -> CleanOriginPrecondition {
    CleanOriginPrecondition::not_equal(
        PreconditionOperand::Argument(1),
        PreconditionOperand::Literal(0),
        64,
        "b ≠ 0 : UInt64",
    )
}

/// The definitional value fact the plan authorizes (`_0 == arg0`). Its content
/// is not what this file is about; it is here so the summary is a REAL
/// Clean-origin summary — one that carries definitional authority — rather than
/// a precondition-only stub that would never have ridden the L0 lane anyway.
fn definitional_value_fact() -> Formula {
    Formula::Eq(
        Box::new(Formula::var("_0", Sort::Int)),
        Box::new(Formula::var("__trust_clean_origin_arg0", Sort::Int)),
    )
}

fn clean_origin_summary_of_record() -> FunctionSummary {
    clean_origin_summary(CALLEE, formals(), vec![definitional_value_fact()], &[divisor_nonzero()])
        .expect("`arg1 != 0` at u64 over two formals is renderable")
}

/// `fn caller(n: u64) -> u64 { safe_rem(n, <divisor>) }`.
fn caller_passing(divisor: Operand) -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "clean_origin_precondition_test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: CALLEE.to_string(),
                        args: vec![Operand::Copy(Place::local(1)), divisor],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                        callee_identity: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn db_of(summary: FunctionSummary) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(summary);
    db
}

fn precondition_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).collect()
}

/// Put the rows to the REAL solver. `true` = at least one obligation is
/// refuted, i.e. the call site FAILS.
fn any_refuted(vcs: &[VerificationCondition]) -> bool {
    let router = trust_router::Router::deterministic_in_process_ay(30_000);
    router
        .verify_all(vcs)
        .into_iter()
        .any(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
}

// ---------------------------------------------------------------------------
// CONTROL 1 — the violating call site FAILS, the satisfying one does not
// ---------------------------------------------------------------------------

#[test]
fn a_call_site_that_violates_the_declared_precondition_is_refuted() {
    let vcs = generate_callsite_precondition_vcs(
        &caller_passing(Operand::Constant(ConstValue::Uint(0, 64))),
        &db_of(clean_origin_summary_of_record()),
    );

    let rows = precondition_rows(&vcs);
    assert_eq!(
        rows.len(),
        1,
        "every call site owes exactly one row per declared obligation; got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );

    assert!(
        any_refuted(&vcs),
        "`safe_rem(n, 0)` VIOLATES `b ≠ 0` and must be REFUTED by the solver. A row that \
         merely exists is not a check — the obligation has to be decidable against the \
         caller's actuals."
    );
}

#[test]
fn a_call_site_that_satisfies_the_declared_precondition_discharges() {
    // The anti-vacuity half. Without it, an implementation that emitted a
    // constant-`false` obligation would pass the test above.
    let vcs = generate_callsite_precondition_vcs(
        &caller_passing(Operand::Constant(ConstValue::Uint(3, 64))),
        &db_of(clean_origin_summary_of_record()),
    );

    assert_eq!(precondition_rows(&vcs).len(), 1, "the row is still owed, and still generated");
    assert!(
        !any_refuted(&vcs),
        "`safe_rem(n, 3)` SATISFIES `b ≠ 0` and must discharge — an obligation nothing can \
         discharge is over-rejection, not verification"
    );
}

#[test]
fn a_symbolic_divisor_the_caller_cannot_bound_is_refuted() {
    // `safe_rem(n, n)` with `n` unconstrained: the caller has NOT established
    // `n != 0`, so the obligation is not discharged. This is the case the gcd
    // route actually needs — a symbolic divisor is exactly what the plan lane's
    // variable-divisor refusal is about — and it must fail closed at the
    // CALLER, which is the whole point of moving the obligation here.
    let vcs = generate_callsite_precondition_vcs(
        &caller_passing(Operand::Copy(Place::local(1))),
        &db_of(clean_origin_summary_of_record()),
    );
    assert_eq!(precondition_rows(&vcs).len(), 1);
    assert!(
        any_refuted(&vcs),
        "an unbounded symbolic divisor must not discharge `b ≠ 0`"
    );
}

#[test]
fn the_obligation_is_an_ordinary_precondition_row_and_never_a_faithfulness_token() {
    let vcs = generate_callsite_precondition_vcs(
        &caller_passing(Operand::Constant(ConstValue::Uint(0, 64))),
        &db_of(clean_origin_summary_of_record()),
    );
    let row = precondition_rows(&vcs)[0];
    assert!(
        matches!(row.kind, VcKind::Precondition { .. }),
        "the discharge is an ORDINARY Rust obligation. `fa788aab89`: never a `Faithful` \
         token — the kernel gate compares two Clean terms and is blind to this."
    );
    assert_eq!(row.function.as_ref(), "caller", "the obligation is charged to the CALLER");
}

// ---------------------------------------------------------------------------
// CONTROL 2 — a summary that cannot carry the precondition publishes NOTHING
// ---------------------------------------------------------------------------

#[test]
fn a_producer_that_cannot_render_an_obligation_publishes_no_summary_at_all() {
    // `Argument(4)` on a two-formal declaration: the call site has no actual to
    // substitute there. Rendering it would leave a free variable in `¬P[σ]`
    // (spuriously SAT — a VIOLATION row about a proposition nobody stated), and
    // SKIPPING it would hand the caller the value fact with no guard.
    let unrenderable = CleanOriginPrecondition::not_equal(
        PreconditionOperand::Argument(4),
        PreconditionOperand::Literal(0),
        64,
        "e ≠ 0",
    );

    assert!(
        clean_origin_summary(CALLEE, formals(), vec![definitional_value_fact()], &[unrenderable])
            .is_none(),
        "the VALUE FACT must not be published without its guard — there is no argument \
         order that publishes half"
    );
}

#[test]
fn one_unrenderable_obligation_sinks_the_whole_set() {
    // ALL-OR-NOTHING. Returning the renderable subset is strictly worse than
    // returning nothing: a partially-guarded summary reads to every downstream
    // consumer exactly like a fully-guarded one.
    let good = divisor_nonzero();
    let bad = CleanOriginPrecondition::not_equal(
        PreconditionOperand::Argument(0),
        // 2^64 does not fit `u64`.
        PreconditionOperand::Literal(1u128 << 64),
        64,
        "a ≠ 2^64",
    );

    assert!(clean_origin_declared_preconditions(&[good.clone()], &formals()).is_some());
    assert!(clean_origin_declared_preconditions(&[good.clone(), bad.clone()], &formals()).is_none());
    assert!(clean_origin_declared_preconditions(&[bad, good], &formals()).is_none());
}

#[test]
fn every_renderer_refusal_is_a_refusal_and_not_a_guess() {
    let cases: Vec<(&str, CleanOriginPrecondition)> = vec![
        (
            "argument index past the formals",
            CleanOriginPrecondition::not_equal(
                PreconditionOperand::Argument(2),
                PreconditionOperand::Literal(0),
                64,
                "",
            ),
        ),
        (
            "literal outside the carrier width",
            CleanOriginPrecondition::not_equal(
                PreconditionOperand::Argument(0),
                PreconditionOperand::Literal(256),
                8,
                "",
            ),
        ),
        (
            "width 0",
            CleanOriginPrecondition::not_equal(
                PreconditionOperand::Argument(0),
                PreconditionOperand::Literal(0),
                0,
                "",
            ),
        ),
        (
            "width past 64",
            CleanOriginPrecondition::not_equal(
                PreconditionOperand::Argument(0),
                PreconditionOperand::Literal(0),
                128,
                "",
            ),
        ),
    ];
    for (why, precondition) in cases {
        assert!(
            clean_origin_declared_precondition(&precondition, &formals()).is_none(),
            "{why}: must refuse rather than pick a reading"
        );
    }

    // The positive control, so none of the above can pass because of a typo in
    // the fixture builder.
    let ok = clean_origin_declared_precondition(&divisor_nonzero(), &formals())
        .expect("the in-range obligation renders");
    assert_eq!(
        ok,
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::var("__trust_clean_origin_arg1", Sort::Int)),
            Box::new(Formula::Int(0)),
        ))),
        "the obligation is spelled over the FORMAL the call site substitutes"
    );
}

// ---------------------------------------------------------------------------
// CONTROL 2, continued — the `650674bc71` DB layer, now reached by a REAL
// Clean-origin summary rather than a hand-built stand-in
// ---------------------------------------------------------------------------

#[test]
fn the_l0_subset_withholds_the_clean_origin_summary_and_records_it() {
    // `650674bc71` built its fixture by hand because no producer minted one.
    // This is the same assertion against the summary the producer actually
    // mints, so the two cannot drift.
    let subset = db_of(clean_origin_summary_of_record()).definitional_precondition_free_subset();

    assert!(
        subset.get(CALLEE).is_none(),
        "the value fact must not ride L0 without its guard"
    );
    assert_eq!(
        subset.l0_withheld_precondition_count(CALLEE),
        Some(1),
        "the withholding must be RECORDED, or the call sites cannot fail closed"
    );
    assert!(!subset.is_empty(), "a withholding DB still owes its call sites a row");
}

#[test]
fn an_l0_call_site_to_a_withheld_clean_origin_callee_fails_closed() {
    let subset = db_of(clean_origin_summary_of_record()).definitional_precondition_free_subset();
    let vcs = generate_callsite_precondition_vcs(
        &caller_passing(Operand::Constant(ConstValue::Uint(0, 64))),
        &subset,
    );

    let withheld: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "L0WithheldPreconditionedSummary")
        })
        .collect();
    assert_eq!(
        withheld.len(),
        1,
        "an L0 caller that VIOLATES the obligation must get the fail-closed row, not \
         silence; got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );

    // v7/D3: the row carries the fix.
    let VcKind::UnsupportedMir { detail, .. } = &withheld[0].kind else { unreachable!() };
    assert!(
        detail.contains("L1Functional"),
        "the refusal must name the level at which the guard IS checked:\n{detail}"
    );
}

#[test]
fn the_clean_origin_summary_without_a_hypothesis_is_not_withheld() {
    // The anti-over-rejection control. A Clean-origin `def` with no hypothesis
    // binder carries no obligation, so its value facts ride L0 exactly as they
    // did before this lane existed.
    let plain = clean_origin_summary(CALLEE, formals(), vec![definitional_value_fact()], &[])
        .expect("no obligations to render");
    let subset = db_of(plain).definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_some(), "nothing to withhold, so nothing is withheld");
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), None);
}
