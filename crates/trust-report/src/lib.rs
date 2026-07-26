//! trust-report: Verification result formatting and proof objects
//!
//! Formats verification results as structured JSON proof reports.
//! JSON is the PRIMARY format — all other formats (text, HTML, terminal)
//! are derived from the canonical JSON representation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow compiler-context lints (HashMap is fine in non-query code,
// unused crate deps come from workspace inheritance)
#![allow(unknown_lints)]
#![allow(rustc::potential_query_instability)]
#![allow(rustc::default_hash_types)]
// dead_code audit: crate-level suppression removed

// ---------------------------------------------------------------------------
// Submodules
// ---------------------------------------------------------------------------

pub mod binary;
pub(crate) mod crate_report;
pub mod diagnostics;
pub(crate) mod formatting;
pub mod html;
pub mod html_report;
pub(crate) mod json_output;
pub(crate) mod legacy;
pub mod repair;
pub(crate) mod report_builder;
pub mod terminal;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Re-exports (public API)
// ---------------------------------------------------------------------------

// Constants
/// Schema version for the JSON proof report format.
/// Bump this when the schema changes in backward-incompatible ways.
pub const SCHEMA_VERSION: &str = "trust.report.v1";

/// Trust version (mirrors the workspace Cargo.toml version).
pub const TRUST_VERSION: &str = env!("CARGO_PKG_VERSION");

// JSON report builders
// Binary decompilation report adapters
pub use binary::{
    BinaryAddressRangeReport, BinaryCertificateCheckReport, BinaryDecompilationProofEvidenceReport,
    BinaryDecompilationProofGradeGateReport, BinaryDecompilationReport,
    BinaryFunctionProofGradeGateReport, BinaryFunctionReport, BinaryInstructionProvenanceReport,
    BinaryLocationReport, BinaryPreservedSymbolicFormulaReport,
    BinaryProofGradeGateRejectionReport, BinaryProofGradeGateReport, BinaryReconstructionReport,
    BinarySolverDispatchReport, BinarySourceBackpropagationGateDetailsReport,
    BinarySourceProvenanceArtifactReport, BinarySourceProvenanceProofEvidenceReport,
    BinarySourceProvenanceRecordReport, BinarySourceProvenanceRecordsReport,
    BinaryTargetValidationBlockerReport, BinaryUnsupportedLedgerReport, BinaryVerificationReport,
    build_binary_decompilation_proof_evidence_report,
    build_binary_decompilation_proof_grade_gate_report, build_binary_decompilation_report,
    build_binary_proof_grade_gate_report, build_binary_source_provenance_artifact_report,
    build_binary_unsupported_ledger_report, build_binary_verification_report,
    format_binary_decompilation_report, format_binary_decompilation_summary,
    format_binary_verification_report, format_binary_verification_summary,
};
// Crate-level verification report
pub use crate_report::{
    append_dep_tcb_ledger, build_crate_verification_report,
    build_crate_verification_report_with_policy, format_crate_verification_summary,
};
// Text formatting
pub use formatting::{
    format_json_summary, function_verdict_label, monitor_evidence_label,
    monitor_executability_label, proof_evidence_label, proof_evidence_label_with_monitor,
    proof_level_label, proof_strength_label,
};
// JSON file/streaming output
pub use json_output::{write_json_report, write_ndjson, write_ndjson_report};
// Legacy API (backward compatibility)
pub use legacy::{build_report, format_summary, write_report};
// AI-in-the-loop repair report (stable, flat, classified unsupported reasons)
pub use repair::{
    REPAIR_SCHEMA_VERSION, RepairObligation, RepairReport, RepairSort, RepairStatus, RepairSummary,
    UnsupportedReason, UnsupportedReasonReport, build_repair_report, build_repair_report_full,
    classify_unsupported_reason,
};
pub use report_builder::{
    build_json_report, build_json_report_from_annotations, build_json_report_with_policy,
};
