//! Parsers for upstream compatibility accounting documents.

use serde::de::DeserializeOwned;
use thiserror::Error;

use crate::model::{
    CompatibilityBaseline, CompatibilityResultSummary, ExceptionLedger, TestExceptionLedger,
    TestInventory, TestResultReport, TrustAddedTestManifest, UpstreamFixLedger,
};
use crate::validate::{
    ValidationFinding, validate_baseline, validate_exceptions, validate_result_summary,
    validate_test_exceptions, validate_test_exceptions_for_date, validate_test_inventory,
    validate_test_result_report, validate_trust_added_tests, validate_upstream_fixes,
};

/// Error returned when parsing or validating an accounting document.
#[derive(Debug, Error)]
pub enum ParseError {
    /// TOML decoding failed before semantic validation.
    #[error("failed to parse TOML accounting document: {0}")]
    Toml(#[from] toml::de::Error),
    /// JSON decoding failed before semantic validation.
    #[error("failed to parse JSON accounting document: {0}")]
    Json(#[from] serde_json::Error),
    /// Semantic validation rejected the decoded accounting document.
    #[error("accounting document failed validation")]
    Validation {
        /// Validation findings produced by the relevant validator.
        findings: Vec<ValidationFinding>,
    },
}

/// Parse and validate a compatibility baseline from TOML.
pub fn parse_baseline_toml(input: &str) -> Result<CompatibilityBaseline, ParseError> {
    parse_toml_with(input, validate_baseline)
}

/// Parse and validate a compatibility baseline from JSON.
pub fn parse_baseline_json(input: &str) -> Result<CompatibilityBaseline, ParseError> {
    parse_json_with(input, validate_baseline)
}

/// Parse and validate an exception ledger from TOML.
pub fn parse_exceptions_toml(input: &str) -> Result<ExceptionLedger, ParseError> {
    parse_toml_with(input, validate_exceptions)
}

/// Parse and validate an exception ledger from JSON.
pub fn parse_exceptions_json(input: &str) -> Result<ExceptionLedger, ParseError> {
    parse_json_with(input, validate_exceptions)
}

/// Parse and validate an upstream fix ledger from TOML.
pub fn parse_upstream_fixes_toml(input: &str) -> Result<UpstreamFixLedger, ParseError> {
    parse_toml_with(input, validate_upstream_fixes)
}

/// Parse and validate an upstream fix ledger from JSON.
pub fn parse_upstream_fixes_json(input: &str) -> Result<UpstreamFixLedger, ParseError> {
    parse_json_with(input, validate_upstream_fixes)
}

/// Parse and validate a result summary from TOML.
pub fn parse_result_summary_toml(input: &str) -> Result<CompatibilityResultSummary, ParseError> {
    parse_toml_with(input, validate_result_summary)
}

/// Parse and validate a result summary from JSON.
pub fn parse_result_summary_json(input: &str) -> Result<CompatibilityResultSummary, ParseError> {
    parse_json_with(input, validate_result_summary)
}

/// Parse and validate a per-test inventory from TOML.
pub fn parse_test_inventory_toml(input: &str) -> Result<TestInventory, ParseError> {
    parse_toml_with(input, validate_test_inventory)
}

/// Parse and validate a per-test inventory from JSON.
pub fn parse_test_inventory_json(input: &str) -> Result<TestInventory, ParseError> {
    parse_json_with(input, validate_test_inventory)
}

/// Parse and validate a per-test result report from TOML.
pub fn parse_test_result_report_toml(input: &str) -> Result<TestResultReport, ParseError> {
    parse_toml_with(input, validate_test_result_report)
}

/// Parse and validate a per-test result report from JSON.
pub fn parse_test_result_report_json(input: &str) -> Result<TestResultReport, ParseError> {
    parse_json_with(input, validate_test_result_report)
}

/// Parse and validate a per-test exception ledger from TOML.
pub fn parse_test_exceptions_toml(input: &str) -> Result<TestExceptionLedger, ParseError> {
    parse_toml_with(input, validate_test_exceptions)
}

/// Parse and validate a per-test exception ledger from JSON.
pub fn parse_test_exceptions_json(input: &str) -> Result<TestExceptionLedger, ParseError> {
    parse_json_with(input, validate_test_exceptions)
}

/// Parse and validate a per-test exception ledger from TOML against a validation date.
pub fn parse_test_exceptions_toml_for_date(
    input: &str,
    validation_date: &str,
) -> Result<TestExceptionLedger, ParseError> {
    parse_toml_with(input, |ledger| validate_test_exceptions_for_date(ledger, validation_date))
}

/// Parse and validate a per-test exception ledger from JSON against a validation date.
pub fn parse_test_exceptions_json_for_date(
    input: &str,
    validation_date: &str,
) -> Result<TestExceptionLedger, ParseError> {
    parse_json_with(input, |ledger| validate_test_exceptions_for_date(ledger, validation_date))
}

/// Parse and validate a Trust-added test manifest from TOML.
pub fn parse_trust_added_tests_toml(input: &str) -> Result<TrustAddedTestManifest, ParseError> {
    parse_toml_with(input, validate_trust_added_tests)
}

/// Parse and validate a Trust-added test manifest from JSON.
pub fn parse_trust_added_tests_json(input: &str) -> Result<TrustAddedTestManifest, ParseError> {
    parse_json_with(input, validate_trust_added_tests)
}

fn parse_toml_with<T, F>(input: &str, validate: F) -> Result<T, ParseError>
where
    T: DeserializeOwned,
    F: FnOnce(&T) -> Result<(), Vec<ValidationFinding>>,
{
    let document = toml::from_str(input)?;
    validate(&document).map_err(|findings| ParseError::Validation { findings })?;
    Ok(document)
}

fn parse_json_with<T, F>(input: &str, validate: F) -> Result<T, ParseError>
where
    T: DeserializeOwned,
    F: FnOnce(&T) -> Result<(), Vec<ValidationFinding>>,
{
    let document = serde_json::from_str(input)?;
    validate(&document).map_err(|findings| ParseError::Validation { findings })?;
    Ok(document)
}
