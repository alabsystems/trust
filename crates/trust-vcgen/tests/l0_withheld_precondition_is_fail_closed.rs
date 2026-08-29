//! Out-of-crate regression for the L0 definitional-summary lane's FAIL-OPEN.
//!
//! `SummaryDatabase::definitional_precondition_free_subset` is the DB an
//! L0Safety caller verifies against (compiler:
//! `trust_verify.rs` — `let vc_summaries = ... else { &l0_definitional_summaries }`).
//! It admitted only `preconditions.is_empty()`, and a definitional summary that
//! DOES carry a precondition therefore fell out of the DB *entirely and
//! silently*. Withholding the VALUE FACT is right and is kept — a fact that
//! cannot travel with its guard must not travel at all. Withholding the GUARD
//! with no trace was fail-OPEN: every call-site producer takes a `NO-SUMMARY`
//! arm on a missing name and emits nothing, so a caller that VIOLATES the
//! callee's precondition was reported CLEAN.
//!
//! These tests pin the fixed behaviour from OUTSIDE the crate, through the
//! public API only, and each one FAILS against the pre-fix tree (the withheld
//! call site produced zero rows of any kind).

use trust_types::*;
use trust_vcgen::{
    FunctionSummary, SummaryDatabase, generate_callsite_precondition_vcs,
    generate_vcs_with_discharge_and_summaries_configured_with_context, modular_vcgen,
};

const CALLEE: &str = "clean_origin::div";

/// `fn divide(n: u64) -> u64 { div(n, 0) }` — a call that VIOLATES a callee
/// `requires(divisor > 0)`. The divisor is the literal `0`.
fn caller_dividing_by_zero() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "l0_withheld_test::divide".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("q".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        callee_identity: None,
                        func: CALLEE.to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 64)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
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

fn formals() -> Vec<String> {
    vec!["a0".to_string(), "a1".to_string()]
}

/// `requires(a1 > 0)` — the divisor guard.
fn divisor_positive() -> Formula {
    Formula::Gt(Box::new(Formula::var("a1", Sort::Int)), Box::new(Formula::Int(0)))
}

/// A rebindable DEFINITIONAL clause (free vars ⊆ {`_0`} ∪ formals).
fn definitional_value_fact() -> Formula {
    Formula::Eq(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::var("a0", Sort::Int)))
}

/// The shape the divisor lane would mint: definitional value fact PLUS the
/// precondition that keeps the emitted body from dividing by zero.
fn preconditioned_definitional_summary() -> FunctionSummary {
    FunctionSummary::new(CALLEE)
        .with_param_names(formals())
        .with_precondition(divisor_positive())
        .with_definitional_postcondition(definitional_value_fact())
}

fn db_of(summary: FunctionSummary) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(summary);
    db
}

fn withheld_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "L0WithheldPreconditionedSummary")
        })
        .collect()
}

#[test]
fn l0_subset_records_the_summary_it_refuses_to_carry() {
    let db = db_of(preconditioned_definitional_summary());
    let subset = db.definitional_precondition_free_subset();

    // Unchanged half: the VALUE FACT does not ride L0 without its guard.
    assert!(
        subset.get(CALLEE).is_none(),
        "a precondition-carrying summary must not hand L0 its value fact"
    );
    // Fixed half: the refusal is RECORDED, not silent.
    assert_eq!(
        subset.l0_withheld_precondition_count(CALLEE),
        Some(1),
        "the withheld guard must be recorded so the call sites can fail closed"
    );
    assert_eq!(subset.l0_withheld_names().collect::<Vec<_>>(), vec![CALLEE]);
    // A DB holding only a withholding is NOT "adds nothing to any caller VC":
    // the compiler's cache-key gate and the write-set builder both early-out on
    // `is_empty()`, and skipping generation would skip the row below.
    assert!(!subset.is_empty(), "a withholding DB still owes its call sites a row");
}

#[test]
fn violating_call_site_is_not_clean_on_the_production_l0_lane() {
    let caller = caller_dividing_by_zero();
    let subset =
        db_of(preconditioned_definitional_summary()).definitional_precondition_free_subset();

    // The producer the compiler's whole-function pipeline drives.
    let vcs = generate_callsite_precondition_vcs(&caller, &subset);
    assert_eq!(
        withheld_rows(&vcs).len(),
        1,
        "the withheld call site must mint exactly one fail-closed row, got: {vcs:?}"
    );
    // v7/D3: the refusal carries its fix.
    let VcKind::UnsupportedMir { detail, .. } = &withheld_rows(&vcs)[0].kind else {
        unreachable!("filtered above")
    };
    assert!(detail.contains(CALLEE), "the row must name the callee: {detail}");
    assert!(
        detail.contains("L1Functional"),
        "the row must name the level that checks the guard: {detail}"
    );

    // And end to end, through the exact entry the compiler calls: the call site
    // resolves to a NON-PROVED obligation. `UnsupportedMir` is an `L0Safety`
    // kind, so unlike a `VcKind::Precondition` row it cannot be filtered away by
    // an L0 run.
    let context = trust_vcgen::VcgenContext::for_function(caller.def_path.clone());
    let (solver_vcs, discharged) =
        generate_vcs_with_discharge_and_summaries_configured_with_context(
            &caller, &subset, false, &context,
        );
    let surviving = trust_vcgen::filter_vcs_by_level(solver_vcs, ProofLevel::L0Safety);
    let withheld_unknown = discharged.iter().any(|(vc, result)| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == "L0WithheldPreconditionedSummary")
            && matches!(result, VerificationResult::Unknown { .. })
    });
    assert!(
        withheld_unknown || !withheld_rows(&surviving).is_empty(),
        "the violating call site must reach the verdict as unknown, never clean"
    );
    assert!(
        !discharged.iter().any(|(vc, result)| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "L0WithheldPreconditionedSummary")
                && matches!(result, VerificationResult::Proved { .. })
        }),
        "a withheld guard can never be discharged as proved"
    );
}

#[test]
fn withheld_call_site_fails_closed_on_the_modular_lane_too() {
    let caller = caller_dividing_by_zero();
    let subset =
        db_of(preconditioned_definitional_summary()).definitional_precondition_free_subset();

    let result = modular_vcgen(&caller, &subset);
    assert_eq!(
        withheld_rows(&result.precondition_vcs).len(),
        1,
        "modular_vcgen reads the same DB by name and must answer the withholding identically"
    );
    assert_eq!(result.assumptions_injected, 0, "no value fact without its guard");
    assert_eq!(result.havoced_calls, 1);
}

#[test]
fn raising_the_level_checks_the_guard_instead_of_withholding_it() {
    // The fix the refusal advertises: at L1Functional the caller verifies
    // against the FULL DB, where the precondition is a real obligation.
    let caller = caller_dividing_by_zero();
    let full = db_of(preconditioned_definitional_summary());

    let vcs = generate_callsite_precondition_vcs(&caller, &full);
    assert!(withheld_rows(&vcs).is_empty(), "nothing is withheld from the full DB");
    assert!(
        vcs.iter()
            .any(|vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == CALLEE)),
        "the L1 lane must mint the real precondition obligation: {vcs:?}"
    );
}

// ---- anti-vacuity controls: the row must not fire where it must not ----

#[test]
fn precondition_free_definitional_summary_still_rides_l0_untouched() {
    let caller = caller_dividing_by_zero();
    let subset = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_definitional_postcondition(definitional_value_fact()),
    )
    .definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_some(), "the L0 lane keeps its precondition-free summaries");
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), None);
    assert!(
        withheld_rows(&generate_callsite_precondition_vcs(&caller, &subset)).is_empty(),
        "no withholding, no row"
    );
    assert_eq!(
        modular_vcgen(&caller, &subset).assumptions_injected,
        1,
        "the definitional value fact must still be assumed at L0"
    );
}

#[test]
fn an_ordinary_contracted_callee_is_not_withheld() {
    // A plain `#[requires]` summary never rode the L0 lane in the first place
    // (no definitional authority), so recording it would be pure
    // over-rejection: every L0 call to a contracted callee would go unknown.
    let caller = caller_dividing_by_zero();
    let subset = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_precondition(divisor_positive())
            .with_postcondition(definitional_value_fact()),
    )
    .definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_none());
    assert_eq!(
        subset.l0_withheld_precondition_count(CALLEE),
        None,
        "only summaries that WOULD have ridden L0 are withheld"
    );
    assert!(subset.is_empty(), "an all-dropped subset carries nothing and owes nothing");
    assert!(withheld_rows(&generate_callsite_precondition_vcs(&caller, &subset)).is_empty());
}

#[test]
fn mixed_provenance_summary_is_not_withheld_either() {
    // `with_postcondition` permanently strips definitional authority (mixed
    // provenance fails closed), so this summary is in the same class as the
    // ordinary contracted one above — dropped, not withheld.
    let subset = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_precondition(divisor_positive())
            .with_definitional_postcondition(definitional_value_fact())
            .with_postcondition(definitional_value_fact()),
    )
    .definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_none());
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), None);
}
