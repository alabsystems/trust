//! The `rows`/`expect` harness of the real-MIR verdict tests, for a test that includes
//! it rather than copying it (`false_refutation_shapes_realmir.rs` carried its own copy
//! until 2026-10-19, for the REFERENCE_ARG_BOX_VALID premise that
//! [`rows_of_with_reference_box_premise`] now installs). Every row is produced through the
//! entry the compiler calls
//! (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`,
//! hardened profile ON) and decided by the deterministic in-process `ay` router; a
//! PROVED row can additionally be put to the Clean kernel (`trust_certify::certify_vc`).
//!
//! Included with `#[path = "support/realmir_rows.rs"] mod realmir_rows;`, so each test
//! binary compiles its own copy and may leave helpers unused.
#![allow(dead_code)]

use std::collections::HashSet;

use trust_types::{BlockId, VerifiableFunction, VerificationCondition, VerificationResult};

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

/// `tests/fixtures/{prefix}{name}_mir.json`, the compiler's own extraction.
pub fn load(prefix: &str, name: &str) -> VerifiableFunction {
    load_path(&format!("{}/tests/fixtures/{prefix}{name}_mir.json", env!("CARGO_MANIFEST_DIR")))
}

/// A fixture by its path.
pub fn load_path(path: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("fixture `{path}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{path}` must deserialize: {e}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Proved,
    Failed,
    Other,
}

#[derive(Debug, Clone)]
pub struct Row {
    /// `format!("{:?}", vc.kind)` — the kind and, for a hardened or `[unsafe]`
    /// row, its label.
    pub kind: String,
    pub line: u32,
    pub verdict: Verdict,
    pub result: String,
    /// The VC itself, for [`certified`] and for a failure message's formula.
    pub vc: VerificationCondition,
}

/// Every row of `func`, hardened profile ON. `box_deref_ops` is the compiler's
/// `collect_synthesized_box_deref_ops` nomination for the body (`(block, statement)`
/// of each synthesized `*box` read).
pub fn rows_of(func: VerifiableFunction, box_deref_ops: &[(usize, usize)]) -> Vec<Row> {
    rows_of_with_reference_box_premise(func, box_deref_ops, &[])
}

/// [`rows_of`] with the REFERENCE_ARG_BOX_VALID premise installed for the argument locals
/// `reference_box_params`, as the compiler installs it (`with_reference_box_root_params`).
/// Empty installs nothing, which is [`rows_of`].
pub fn rows_of_with_reference_box_premise(
    func: VerifiableFunction,
    box_deref_ops: &[(usize, usize)],
    reference_box_params: &[usize],
) -> Vec<Row> {
    let ops: HashSet<(BlockId, usize)> =
        box_deref_ops.iter().map(|&(b, s)| (BlockId(b), s)).collect();
    let reference_box_params = reference_box_params.to_vec();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone())
                .with_reference_box_root_params(reference_box_params);
            let db = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, true, &context, &ops,
                );
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            let decided = solver_vcs.into_iter().map(|vc| {
                let (_, result) = router
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC");
                (vc, result)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .map(|(vc, result)| Row {
                    kind: format!("{:?}", vc.kind),
                    line: vc.location.line_start,
                    verdict: match result {
                        VerificationResult::Proved { .. } => Verdict::Proved,
                        VerificationResult::Failed { .. } => Verdict::Failed,
                        _ => Verdict::Other,
                    },
                    result: format!("{result:?}"),
                    vc,
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// Every row of fixture `{prefix}{name}`.
pub fn rows(prefix: &str, name: &str, box_deref_ops: &[(usize, usize)]) -> Vec<Row> {
    rows_of(load(prefix, name), box_deref_ops)
}

/// Whether the Clean kernel re-checks `row`'s own goal (`trust_certify::certify_vc`).
pub fn certified(row: &Row) -> bool {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn({
            let vc = row.vc.clone();
            move || trust_certify::certify_vc(&vc).is_some()
        })
        .expect("spawn")
        .join()
        .expect("certification thread")
}

/// The rows at `line` whose kind debug-string contains `needle`.
pub fn at<'a>(rows: &'a [Row], line: u32, needle: &str) -> Vec<&'a Row> {
    rows.iter().filter(|r| r.line == line && r.kind.contains(needle)).collect()
}

/// Exactly `count` rows at `line` match `needle`, and every one of them has `want`.
pub fn expect(rows: &[Row], line: u32, needle: &str, count: usize, want: Verdict, why: &str) {
    let hits = at(rows, line, needle);
    assert_eq!(
        hits.len(),
        count,
        "line {line}: expected {count} `{needle}` row(s); all rows: {:#?}",
        rows.iter().map(|r| (r.line, &r.kind, r.verdict)).collect::<Vec<_>>()
    );
    for row in hits {
        assert_eq!(
            row.verdict, want,
            "line {line} `{needle}`: {why}\nresult: {}\nformula: {:?}",
            row.result, row.vc.formula
        );
    }
}

/// [`expect`] `Proved`, and every matching row kernel-certified (`want_cert`) or not.
pub fn expect_certified(
    rows: &[Row],
    line: u32,
    needle: &str,
    count: usize,
    want_cert: bool,
    why: &str,
) {
    expect(rows, line, needle, count, Verdict::Proved, why);
    for row in at(rows, line, needle) {
        assert_eq!(
            certified(row),
            want_cert,
            "line {line} `{needle}`: certified must be {want_cert}: {why}\nformula: {:?}",
            row.vc.formula
        );
    }
}

pub const PRIMARY_ADD: &str = "ArithmeticOverflow { op: Add";
pub const PRIMARY_SUB: &str = "ArithmeticOverflow { op: Sub";
pub const TWIN_ADD: &str = "mir_assert::Overflow(Add)";
pub const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";
pub const TWIN_NEG: &str = "mir_assert::OverflowNeg";
pub const NEGATION: &str = "NegationOverflow";
