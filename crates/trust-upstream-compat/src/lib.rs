//! trust-upstream-compat: Upstream compatibility accounting schema.
//!
//! This crate owns the Rust-side data model for tracking where Trust matches,
//! intentionally diverges from, or waits on upstream Rust behavior.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod model;
pub mod parse;
pub mod porting;
pub mod validate;

/// Schema version for upstream compatibility accounting documents.
pub const SCHEMA_VERSION: &str = "0.1.0";

pub use model::{
    BaselineEntry, BaselineStatus, CompatibilityBaseline, CompatibilityException,
    CompatibilityExpectation, CompatibilityOutcome, CompatibilityResult,
    CompatibilityResultSummary, CompatibilitySummaryRunner, CompatibilitySurface, ExceptionClass,
    ExceptionLedger, ExceptionStatus, LocalFixAction, LocalSnapshot, ResultTotals, TestException,
    TestExceptionKind, TestExceptionLedger, TestInventory, TestInventoryEntry, TestKind,
    TestOutcome, TestProofTotals, TestResult, TestResultReport, TestSource, TrustAddedTestCommand,
    TrustAddedTestManifest, UpstreamFix, UpstreamFixLedger, UpstreamFixStatus, UpstreamSnapshot,
};
pub use parse::{
    ParseError, parse_baseline_json, parse_baseline_toml, parse_exceptions_json,
    parse_exceptions_toml, parse_result_summary_json, parse_result_summary_toml,
    parse_test_exceptions_json, parse_test_exceptions_json_for_date, parse_test_exceptions_toml,
    parse_test_exceptions_toml_for_date, parse_test_inventory_json, parse_test_inventory_toml,
    parse_test_result_report_json, parse_test_result_report_toml, parse_trust_added_tests_json,
    parse_trust_added_tests_toml, parse_upstream_fixes_json, parse_upstream_fixes_toml,
};
pub use validate::{
    AccountingBundle, TestProofBundle, ValidationFinding, ValidationResult,
    validate_accounting_bundle, validate_baseline, validate_exceptions, validate_result_summary,
    validate_test_exceptions, validate_test_exceptions_for_date, validate_test_inventory,
    validate_test_proof_bundle, validate_test_result_report, validate_trust_added_tests,
    validate_upstream_fixes, validate_upstream_revision_accounting,
};

#[cfg(test)]
mod tests;
