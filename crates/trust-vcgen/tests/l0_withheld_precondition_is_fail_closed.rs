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
                        callee_key: None,
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
        tuple_layouts: Default::default(),
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
fn an_ordinary_contracted_callee_is_withheld_and_charged() {
    // Trust (2026-10-03): a plain `requires` summary has no definitional value
    // fact to withhold, but its CALLEE assumed the clause at entry and elided
    // the checks it proved under it. Dropping the summary unrecorded left the
    // L0 call site with NO row, so a caller violating the clause read clean
    // while the callee ran with its checks gone (MEASURED on stage 1 of
    // `782780ea0d`: `p() { add1(u32::MAX) }` at `-Ztrust-verify-level=0` built
    // exit 0 under certify and returned `0`). This test pinned that drop as
    // "not over-rejection" until then; it now pins the recorded withholding.
    let caller = caller_dividing_by_zero();
    let full = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_precondition(divisor_positive())
            .with_postcondition(definitional_value_fact()),
    );
    assert!(
        full.owes_caller_preconditions(&caller_dividing_by_zero()),
        "the compiler lifts a caller of this callee to L1"
    );
    let subset = full.definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_none(), "an ordinary clause still never rides L0");
    assert_eq!(
        subset.l0_withheld_precondition_count(CALLEE),
        Some(1),
        "every preconditioned summary the L0 subset drops is recorded"
    );
    assert!(!subset.is_empty(), "a withholding DB still owes its call sites a row");
    assert_eq!(
        withheld_rows(&generate_callsite_precondition_vcs(&caller, &subset)).len(),
        1,
        "the violating L0 call site mints the fail-closed row, not silence"
    );
}

#[test]
fn mixed_provenance_summary_is_withheld_too() {
    // `with_postcondition` permanently strips definitional authority (mixed
    // provenance fails closed), so this summary is in the same class as the
    // ordinary contracted one above — dropped from the subset AND recorded.
    let subset = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_precondition(divisor_positive())
            .with_definitional_postcondition(definitional_value_fact())
            .with_postcondition(definitional_value_fact()),
    )
    .definitional_precondition_free_subset();

    assert!(subset.get(CALLEE).is_none());
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), Some(1));
}

#[test]
fn a_contracted_callee_with_no_precondition_owes_nothing() {
    // The anti-over-rejection control for the bit the compiler lifts on: a
    // summary with an `ensures` and no `requires` charges no call site, so it
    // neither lifts its caller nor is recorded as a withholding.
    let full = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_postcondition(definitional_value_fact()),
    );
    assert!(!full.owes_caller_preconditions(&caller_dividing_by_zero()));
    let subset = full.definitional_precondition_free_subset();
    assert!(subset.get(CALLEE).is_none());
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), None);
    assert!(subset.is_empty(), "an all-dropped precondition-free subset owes nothing");
    assert!(!subset.owes_caller_preconditions(&caller_dividing_by_zero()));
}

#[test]
fn owes_caller_preconditions_reads_every_preconditioned_summary() {
    // The bit `effective_max_level` lifts on: true for a definitional,
    // a guarded and an ordinary preconditioned summary alike, and for a DB that
    // holds only a recorded withholding — each under the name the caller calls.
    let caller = caller_dividing_by_zero();
    assert!(db_of(preconditioned_definitional_summary()).owes_caller_preconditions(&caller));
    assert!(
        db_of(
            FunctionSummary::new(CALLEE)
                .with_param_names(formals())
                .with_precondition(divisor_positive())
                .with_verified_callee_postcondition(definitional_value_fact()),
        )
        .owes_caller_preconditions(&caller),
        "a guarded summary rides L0 with its value fact, but its call still owes the clause"
    );
    assert!(
        db_of(
            FunctionSummary::new(CALLEE)
                .with_param_names(formals())
                .with_precondition(divisor_positive()),
        )
        .owes_caller_preconditions(&caller),
        "a `requires` with no `ensures` is the measured shape (`add1`)"
    );
    let withheld_only =
        db_of(preconditioned_definitional_summary()).definitional_precondition_free_subset();
    assert!(withheld_only.get(CALLEE).is_none());
    assert!(withheld_only.owes_caller_preconditions(&caller));
    assert!(!SummaryDatabase::new().owes_caller_preconditions(&caller));
}

/// `fn relay(n: u64) -> u64 { w(n) }` — a call to a function with no summary
/// precondition of its own (`w`), which is where the compiler's transitive-trace
/// closure registers the summary of `w`'s OWN callee beside it.
fn caller_of_an_intermediate() -> VerifiableFunction {
    let mut caller = caller_dividing_by_zero();
    caller.name = "relay".to_string();
    caller.def_path = "l0_withheld_test::relay".to_string();
    let Terminator::Call { func, args, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!("block 0 of the base caller is its call")
    };
    *func = "l0_withheld_test::w".to_string();
    args.truncate(1);
    caller
}

#[test]
fn a_precondition_the_caller_does_not_call_owes_nothing() {
    // Trust (review of the level-0 lift, 2026-10-03): the compiler's DB for a
    // caller holds the summaries of the callees OF an attached callee body too
    // (the transitive-trace closure), with their authored `requires`, and no
    // call-site producer mints a row for a name the caller never calls. Asked over
    // the whole DB, the bit lifted such a caller to L1: on the stage 1 of
    // `6011b74bad`, `p(b: bool) { if b { p(b) } else { w(3) } }` got the level-1
    // termination charge at `-Ztrust-verify-level=0` because `w` calls a
    // `requires` function (`tests/ui/trust/l0_callsite_lift_scope.rs`).
    let caller = caller_of_an_intermediate();
    let mut db = db_of(
        FunctionSummary::new(CALLEE)
            .with_param_names(formals())
            .with_precondition(divisor_positive()),
    );
    db.insert(FunctionSummary::new("l0_withheld_test::w").with_param_names(vec!["a0".into()]));
    assert!(
        !db.owes_caller_preconditions(&caller),
        "a preconditioned summary under a name the caller never calls lifts nothing"
    );
    assert!(
        generate_callsite_precondition_vcs(&caller, &db).iter().all(|vc| {
            !matches!(&vc.kind, VcKind::Precondition { .. })
                && !matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == "L0WithheldPreconditionedSummary")
        }),
        "and the producer the bit stands for mints no row for it"
    );
    // The same summary, recorded as withheld in the level-0 subset, owes nothing
    // to this caller either: the withheld row is minted only at a call to it.
    assert!(!db.definitional_precondition_free_subset().owes_caller_preconditions(&caller));
    // Control: the caller that DOES call it owes it.
    assert!(db.owes_caller_preconditions(&caller_dividing_by_zero()));
}
