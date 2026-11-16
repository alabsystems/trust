// gate-rca deadline (2026-10-17, B class): the compiler's constructor reconciliation
// (`step_by_constructor::reconcile_bundle`) asked the caller-side precondition producer
// once PER constructor member, each time with a one-summary database, and so rebuilt the
// root's whole-body analyses (its two-pass path-definition fixpoint above all) once per
// member: 99.8 % of a 2.5-minute native bundle construction on the candidate gate's
// `aterm_conformance::measure::scan::scan_frames`. It now asks
// `generate_callsite_precondition_vcs_for_each` once, which computes the caller-only
// analyses once and the summary-dependent half per database.
//
// These rows pin that the batch is an exact replacement: on real stage-1 dumps (with
// calls, loops, cells and unions), element `i` of the batch is byte-for-byte the
// single-database producer's answer for database `i`, and also the answer with the
// per-function analysis memo switched off (`with_analysis_memo_disabled`), which the
// producer's own generation scope now makes live. The negative control is that the
// databases' answers differ from one another, so a batch that served one database's rows
// for every database fails the first assertion. Evidence rung: test.

use trust_types::{Formula, Terminator, VerifiableFunction, VerificationCondition};
use trust_vcgen::{
    FunctionSummary, SummaryDatabase, generate_callsite_precondition_vcs,
    generate_callsite_precondition_vcs_for_each, with_analysis_memo_disabled,
};

const FIXTURES: &[&str] = &[
    "census_budget_is_ascii",
    "census_budget_u64_stages",
    "class10_shrink_oob_mir",
    "digest_update_topup_top_up_stashed_mir",
    "escaped_seam_a7_enum_method_reseat_o0_mir",
    "slice_tuple_indexed_app_mir",
    "interior_mut_channel_guard_must_refute_local_ucell_callee_mir",
    "interior_mut_channel_guard_must_refute_cell_array_mir",
    "interior_mut_channel_union_O0_must_refute_owned_union_parked_cell_zero_arg_call_mir",
];

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// Every distinct callee of `f` with the arity of its first call, in block order.
fn callees(f: &VerifiableFunction) -> Vec<(String, usize)> {
    let mut out: Vec<(String, usize)> = Vec::new();
    for block in &f.body.blocks {
        if let Terminator::Call { func, args, .. } = &block.terminator
            && !out.iter().any(|(name, _)| name == func)
        {
            out.push((func.clone(), args.len()));
        }
    }
    out
}

/// One database whose single summary gives `callee` a precondition, so its every call
/// site mints a row carrying the caller's path definitions, guards and facts.
fn database(callee: &str, arity: usize) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new(callee.to_string())
            .with_param_names((0..arity).map(|i| format!("p{i}")).collect())
            .with_precondition(Formula::Bool(true)),
    );
    db
}

fn rendered(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| serde_json::to_string(vc).expect("a VC serializes")).collect()
}

#[test]
fn the_batch_answers_every_database_as_the_single_database_producer() {
    for name in FIXTURES {
        let f = load(name);
        let callees = callees(&f);
        assert!(callees.len() >= 2, "{name}: the row needs two callees: {callees:?}");
        let databases: Vec<SummaryDatabase> =
            callees.iter().map(|(callee, arity)| database(callee, *arity)).collect();
        let refs: Vec<&SummaryDatabase> = databases.iter().collect();

        let batch = generate_callsite_precondition_vcs_for_each(&f, &refs);
        assert_eq!(batch.len(), refs.len(), "{name}: one answer per database");
        for (index, db) in refs.iter().enumerate() {
            assert_eq!(
                rendered(&batch[index]),
                rendered(&generate_callsite_precondition_vcs(&f, db)),
                "{name}: database {index} ({}) answers differently in the batch",
                callees[index].0
            );
            assert!(!batch[index].is_empty(), "{name}: database {index} mints its call rows");
        }
        let memo_off =
            with_analysis_memo_disabled(|| generate_callsite_precondition_vcs_for_each(&f, &refs));
        for (index, (with, without)) in batch.iter().zip(&memo_off).enumerate() {
            assert_eq!(
                rendered(with),
                rendered(without),
                "{name}: database {index} depends on the analysis memo"
            );
        }
        // Negative control: the answers are database-specific.
        assert!(
            batch.windows(2).any(|pair| rendered(&pair[0]) != rendered(&pair[1])),
            "{name}: every database got the same rows, so the batch's indexing is untested"
        );
    }
}

#[test]
fn an_empty_batch_computes_nothing_and_answers_nothing() {
    let f = load(FIXTURES[0]);
    assert!(generate_callsite_precondition_vcs_for_each(&f, &[]).is_empty());
}
