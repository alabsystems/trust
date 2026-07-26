//! Whole-crate verification report builder.
//!
//! Entry point for building `JsonProofReport` from `CrateVerificationResult`,
//! including cross-function spec composition statistics.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write as FmtWrite;

use trust_types::*;

use crate::formatting::format_json_summary;
use crate::report_builder::build_json_report_with_policy;

/// Build a `JsonProofReport` from a `CrateVerificationResult`.
///
/// This is the entry point for whole-crate verification. It consumes the
/// aggregated per-function results (collected by the trust_verify MIR pass)
/// and produces the canonical JSON report with crate-level summary.
///
/// Cross-function spec composition metadata (from_notes, with_assumptions)
/// is included in the report metadata as additional timing/composition stats.
pub fn build_crate_verification_report(crate_result: &CrateVerificationResult) -> JsonProofReport {
    build_crate_verification_report_with_policy(crate_result, RuntimeCheckPolicy::Auto, true)
}

/// Build a `JsonProofReport` from a `CrateVerificationResult` with
/// explicit runtime-check policy and overflow-check configuration.
pub fn build_crate_verification_report_with_policy(
    crate_result: &CrateVerificationResult,
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
) -> JsonProofReport {
    let all_results = crate_result.all_results();
    build_json_report_with_policy(&crate_result.crate_name, &all_results, policy, overflow_checks)
}

/// Format a crate-level summary with cross-function spec composition stats.
///
/// Extends `format_json_summary` with lines showing how many VCs were
/// satisfied from cross-function notes vs. sent to the solver.
pub fn format_crate_verification_summary(
    report: &JsonProofReport,
    crate_result: &CrateVerificationResult,
) -> String {
    let mut text = format_json_summary(report);

    // Trust: Append cross-function composition stats if any specs were used.
    if crate_result.total_from_notes > 0 || crate_result.total_with_assumptions > 0 {
        text.push_str("\n  Cross-function composition:");
        let _ = write!(
            text,
            "\n    {} VCs satisfied from proved callee specs (free)",
            crate_result.total_from_notes
        );
        let _ = write!(
            text,
            "\n    {} VCs sent to solver with callee assumptions",
            crate_result.total_with_assumptions
        );
    }

    text
}

/// Trust (dep-TCB ledger, Stage 0): append the dependency trust-base ledger to
/// a crate verification summary.
///
/// `tcb_ledger_lines` are the pre-rendered rows produced by
/// `trust_proof_cert::AssumptionSet::render_tcb_ledger` — one per scoped-out
/// dependency plus the explicit `core`/`alloc`/`std` hard-skip rows. They are
/// passed as plain strings so this crate need not depend on `trust-proof-cert`.
/// An empty slice renders nothing, so the summary is unchanged when no ledger
/// is available (e.g. single-file mode, or a build with no resolvable deps).
pub fn append_dep_tcb_ledger(summary: &mut String, tcb_ledger_lines: &[String]) {
    if tcb_ledger_lines.is_empty() {
        return;
    }
    summary.push_str("\n  Dependency trust base (scoped out of verification):");
    for line in tcb_ledger_lines {
        let _ = write!(summary, "\n    {line}");
    }
}
