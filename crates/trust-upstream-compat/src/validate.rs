//! Semantic validators for upstream compatibility accounting documents.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::Path;

use crate::SCHEMA_VERSION;
use crate::model::{
    CompatibilityBaseline, CompatibilityException, CompatibilityOutcome,
    CompatibilityResultSummary, ExceptionLedger, ExceptionStatus, TestException, TestExceptionKind,
    TestExceptionLedger, TestInventory, TestInventoryEntry, TestOutcome, TestProofTotals,
    TestResultReport, TestSource, TrustAddedTestManifest, UpstreamFix, UpstreamFixLedger,
    UpstreamFixStatus,
};

/// Validation result type used by all validators.
pub type ValidationResult = Result<(), Vec<ValidationFinding>>;

/// One semantic validation finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationFinding {
    /// Field path that produced the finding.
    pub field: String,
    /// Human-readable validation message.
    pub message: String,
}

impl ValidationFinding {
    #[must_use]
    fn new(field: impl Into<String>, message: impl Into<String>) -> Self {
        Self { field: field.into(), message: message.into() }
    }
}

/// Cross-document accounting bundle for reference validation.
#[derive(Debug, Clone, Copy)]
pub struct AccountingBundle<'a> {
    /// Required compatibility baseline.
    pub baseline: &'a CompatibilityBaseline,
    /// Optional exception ledger.
    pub exceptions: Option<&'a ExceptionLedger>,
    /// Optional upstream fix ledger.
    pub upstream_fixes: Option<&'a UpstreamFixLedger>,
    /// Optional run summary.
    pub result_summary: Option<&'a CompatibilityResultSummary>,
    /// Optional current upstream revision used to detect unaccounted drift after
    /// the baseline snapshot.
    pub current_upstream_revision: Option<&'a str>,
}

/// Cross-document proof bundle for per-test compatibility evidence.
#[derive(Debug, Clone, Copy)]
pub struct TestProofBundle<'a> {
    /// Required per-test inventory.
    pub inventory: &'a TestInventory,
    /// Required per-test result report.
    pub results: &'a TestResultReport,
    /// Required per-test exception ledger.
    pub exceptions: &'a TestExceptionLedger,
    /// Required for release proof when the inventory contains Trust-added tests.
    pub trust_added_tests: Option<&'a TrustAddedTestManifest>,
    /// Date used to fail closed on stale active per-test exceptions.
    pub validation_date: &'a str,
    /// Whether release-grade fail-closed rules are active.
    pub release: bool,
}

/// Validate one compatibility baseline document.
pub fn validate_baseline(baseline: &CompatibilityBaseline) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &baseline.schema_version);
    require_id(&mut findings, "id", &baseline.id);

    require_non_empty(&mut findings, "upstream.channel", &baseline.upstream.channel);
    require_non_empty(&mut findings, "upstream.revision", &baseline.upstream.revision);
    if let Some(snapshot_date) = &baseline.upstream.snapshot_date {
        require_date(&mut findings, "upstream.snapshot_date", snapshot_date);
    }

    require_non_empty(&mut findings, "local.revision", &baseline.local.revision);
    if let Some(branch) = &baseline.local.branch {
        require_non_empty(&mut findings, "local.branch", branch);
    }
    if let Some(workspace) = &baseline.local.workspace {
        require_non_empty(&mut findings, "local.workspace", workspace);
    }

    if baseline.entries.is_empty() {
        findings
            .push(ValidationFinding::new("entries", "baseline must contain at least one entry"));
    }

    let mut entry_ids = BTreeSet::new();
    for (idx, entry) in baseline.entries.iter().enumerate() {
        let prefix = format!("entries[{idx}]");
        require_id(&mut findings, format!("{prefix}.id"), &entry.id);
        require_unique(&mut findings, "entries.id", &entry.id, &mut entry_ids);
        require_non_empty(&mut findings, format!("{prefix}.title"), &entry.title);
        require_non_empty(
            &mut findings,
            format!("{prefix}.upstream_artifact"),
            &entry.upstream_artifact,
        );
        if let Some(local_artifact) = &entry.local_artifact {
            require_non_empty(&mut findings, format!("{prefix}.local_artifact"), local_artifact);
        }
        require_non_empty(
            &mut findings,
            format!("{prefix}.expectation.upstream_behavior"),
            &entry.expectation.upstream_behavior,
        );
        require_non_empty(
            &mut findings,
            format!("{prefix}.expectation.local_behavior"),
            &entry.expectation.local_behavior,
        );
        require_non_empty(
            &mut findings,
            format!("{prefix}.expectation.compatibility_rule"),
            &entry.expectation.compatibility_rule,
        );
        for (label_idx, label) in entry.labels.iter().enumerate() {
            require_non_empty(&mut findings, format!("{prefix}.labels[{label_idx}]"), label);
        }
    }

    finish(findings)
}

/// Validate one exception ledger.
pub fn validate_exceptions(ledger: &ExceptionLedger) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &ledger.schema_version);

    let mut ids = BTreeSet::new();
    for (idx, exception) in ledger.exceptions.iter().enumerate() {
        validate_exception(&mut findings, exception, idx, &mut ids);
    }

    finish(findings)
}

/// Validate one upstream fix ledger.
pub fn validate_upstream_fixes(ledger: &UpstreamFixLedger) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &ledger.schema_version);
    if let Some(revision) = &ledger.tracked_until_revision {
        require_non_empty(&mut findings, "tracked_until_revision", revision);
    }

    let mut ids = BTreeSet::new();
    for (idx, fix) in ledger.fixes.iter().enumerate() {
        validate_upstream_fix(&mut findings, fix, idx, &mut ids);
    }

    finish(findings)
}

/// Validate one result summary.
pub fn validate_result_summary(summary: &CompatibilityResultSummary) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &summary.schema_version);
    require_id(&mut findings, "baseline_id", &summary.baseline_id);
    require_date(&mut findings, "generated_on", &summary.generated_on);
    if let Some(run_id) = &summary.run_id {
        require_non_empty(&mut findings, "run_id", run_id);
    }
    if let Some(repo_head) = &summary.repo_head {
        require_non_empty(&mut findings, "repo_head", repo_head);
    }
    if let Some(upstream_revision) = &summary.upstream_revision {
        require_non_empty(&mut findings, "upstream_revision", upstream_revision);
    }

    let expected_totals = summary.recount_totals();
    if summary.totals != expected_totals {
        findings.push(ValidationFinding::new(
            "totals",
            format!(
                "declared totals {:?} do not match computed totals {:?}",
                summary.totals, expected_totals
            ),
        ));
    }

    let mut result_ids = BTreeSet::new();
    for (idx, result) in summary.results.iter().enumerate() {
        let prefix = format!("results[{idx}]");
        require_id(&mut findings, format!("{prefix}.baseline_entry_id"), &result.baseline_entry_id);
        require_unique(
            &mut findings,
            "results.baseline_entry_id",
            &result.baseline_entry_id,
            &mut result_ids,
        );

        match result.outcome {
            CompatibilityOutcome::Excepted if result.exception_id.is_none() => {
                findings.push(ValidationFinding::new(
                    format!("{prefix}.exception_id"),
                    "excepted result must reference an exception",
                ));
            }
            CompatibilityOutcome::FixedUpstream if result.upstream_fix_id.is_none() => {
                findings.push(ValidationFinding::new(
                    format!("{prefix}.upstream_fix_id"),
                    "fixed_upstream result must reference an upstream fix",
                ));
            }
            CompatibilityOutcome::Compatible | CompatibilityOutcome::Divergent => {
                if result.exception_id.is_some() {
                    findings.push(ValidationFinding::new(
                        format!("{prefix}.exception_id"),
                        "compatible and divergent results must not reference an exception",
                    ));
                }
                if result.upstream_fix_id.is_some() {
                    findings.push(ValidationFinding::new(
                        format!("{prefix}.upstream_fix_id"),
                        "compatible and divergent results must not reference an upstream fix",
                    ));
                }
            }
            CompatibilityOutcome::Unknown => {}
            CompatibilityOutcome::Excepted | CompatibilityOutcome::FixedUpstream => {}
        }

        if let Some(exception_id) = &result.exception_id {
            require_id(&mut findings, format!("{prefix}.exception_id"), exception_id);
        }
        if let Some(fix_id) = &result.upstream_fix_id {
            require_id(&mut findings, format!("{prefix}.upstream_fix_id"), fix_id);
        }
        if let Some(observed) = &result.observed {
            require_non_empty(&mut findings, format!("{prefix}.observed"), observed);
        }
    }

    finish(findings)
}

/// Validate one per-test inventory document.
pub fn validate_test_inventory(inventory: &TestInventory) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &inventory.schema_version);
    require_non_empty(&mut findings, "upstream_revision", &inventory.upstream_revision);
    require_non_empty(&mut findings, "local_revision", &inventory.local_revision);
    if let Some(host) = &inventory.host {
        require_non_empty(&mut findings, "host", host);
    }
    if inventory.tests.is_empty() {
        findings.push(ValidationFinding::new("tests", "inventory must contain at least one test"));
    }

    let mut ids = BTreeSet::new();
    for (idx, test) in inventory.tests.iter().enumerate() {
        validate_inventory_entry(&mut findings, test, idx, &mut ids);
    }

    finish(findings)
}

/// Validate one per-test result report.
pub fn validate_test_result_report(report: &TestResultReport) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &report.schema_version);
    require_id(&mut findings, "inventory_id", &report.inventory_id);
    require_date(&mut findings, "generated_on", &report.generated_on);
    require_non_empty(&mut findings, "command", &report.command);

    let mut ids = BTreeSet::new();
    for (idx, result) in report.results.iter().enumerate() {
        let prefix = format!("results[{idx}]");
        require_id(&mut findings, format!("{prefix}.test_id"), &result.test_id);
        require_unique(&mut findings, "results.test_id", &result.test_id, &mut ids);
        if let Some(exception_id) = &result.exception_id {
            require_id(&mut findings, format!("{prefix}.exception_id"), exception_id);
        }
        if let Some(observed) = &result.observed {
            require_non_empty(&mut findings, format!("{prefix}.observed"), observed);
        }
        if let Some(artifact) = &result.artifact {
            require_non_empty(&mut findings, format!("{prefix}.artifact"), artifact);
        }

        match result.outcome {
            TestOutcome::Passed | TestOutcome::UpstreamInapplicable => {
                if result.exception_id.is_some() {
                    findings.push(ValidationFinding::new(
                        format!("{prefix}.exception_id"),
                        "passed and upstream_inapplicable results must not reference an exception",
                    ));
                }
            }
            TestOutcome::Failed | TestOutcome::Skipped | TestOutcome::Diffed => {}
            TestOutcome::Unknown => {}
        }
    }

    finish(findings)
}

/// Validate one per-test exception ledger.
pub fn validate_test_exceptions(ledger: &TestExceptionLedger) -> ValidationResult {
    let mut findings = Vec::new();

    validate_test_exceptions_with_date(&mut findings, ledger, None);

    finish(findings)
}

/// Validate one per-test exception ledger against an explicit validation date.
///
/// The explicit date keeps expiry checks deterministic for tests and release
/// automation instead of reading the wall clock inside the parser.
pub fn validate_test_exceptions_for_date(
    ledger: &TestExceptionLedger,
    validation_date: &str,
) -> ValidationResult {
    let mut findings = Vec::new();

    require_date(&mut findings, "validation_date", validation_date);
    let validation_date = is_yyyy_mm_dd(validation_date).then_some(validation_date);
    validate_test_exceptions_with_date(&mut findings, ledger, validation_date);

    finish(findings)
}

fn validate_test_exceptions_with_date(
    findings: &mut Vec<ValidationFinding>,
    ledger: &TestExceptionLedger,
    validation_date: Option<&str>,
) {
    validate_schema_version(findings, "schema_version", &ledger.schema_version);
    let mut ids = BTreeSet::new();
    for (idx, exception) in ledger.exceptions.iter().enumerate() {
        validate_test_exception(findings, exception, idx, &mut ids, validation_date);
    }
}

/// Validate one Trust-added test manifest.
pub fn validate_trust_added_tests(manifest: &TrustAddedTestManifest) -> ValidationResult {
    let mut findings = Vec::new();

    validate_schema_version(&mut findings, "schema_version", &manifest.schema_version);
    if manifest.commands.is_empty() {
        findings.push(ValidationFinding::new(
            "commands",
            "Trust-added test manifest must contain at least one command",
        ));
    }

    let mut ids = BTreeSet::new();
    for (idx, command) in manifest.commands.iter().enumerate() {
        let prefix = format!("commands[{idx}]");
        require_id(&mut findings, format!("{prefix}.id"), &command.id);
        require_unique(&mut findings, "commands.id", &command.id, &mut ids);
        require_non_empty(&mut findings, format!("{prefix}.command"), &command.command);
        if let Some(message) = canonical_trust_added_command_violation(&command.command) {
            findings.push(ValidationFinding::new(format!("{prefix}.command"), message));
        }
        if command.covers.is_empty() {
            findings.push(ValidationFinding::new(
                format!("{prefix}.covers"),
                "command must cover at least one inventory test id",
            ));
        }
        let mut covers = BTreeSet::new();
        for (cover_idx, test_id) in command.covers.iter().enumerate() {
            require_id(&mut findings, format!("{prefix}.covers[{cover_idx}]"), test_id);
            require_unique(&mut findings, format!("{prefix}.covers"), test_id, &mut covers);
        }
    }

    finish(findings)
}

fn forbidden_manifest_launcher(command: &str) -> Option<String> {
    command
        .split_whitespace()
        .find(|part| forbidden_python_or_shell_launcher(part))
        .map(str::to_string)
}

fn canonical_trust_added_command_violation(command: &str) -> Option<String> {
    if let Some(forbidden) = forbidden_manifest_launcher(command) {
        return Some(format!(
            "Trust-added command must use `targo trust domination trust-added`, not a Python or shell wrapper: {forbidden}"
        ));
    }

    let argv = command.split_whitespace().collect::<Vec<_>>();
    if argv.get(0..4) != Some(&["targo", "trust", "domination", "trust-added"]) {
        return Some(
            "Trust-added command must use the canonical Rust CLI prefix `targo trust domination trust-added`"
                .to_string(),
        );
    }

    let mut strict_seen = false;
    let mut release_seen = false;
    let mut mode = None;
    for part in &argv[4..] {
        match *part {
            "--strict" if mode.is_none() && !strict_seen => strict_seen = true,
            "--release" if mode.is_some() => {
                return Some(
                    "Trust-added command must place `--release` before the mode".to_string(),
                );
            }
            "--release" if release_seen => {
                return Some(
                    "Trust-added command must contain exactly one pre-mode `--release` flag"
                        .to_string(),
                );
            }
            "--release" => release_seen = true,
            option if option.starts_with('-') => {
                return Some(format!("unsupported Trust-added command option `{option}`"));
            }
            value if mode.replace(value).is_none() => {}
            value => {
                return Some(format!("unexpected trailing Trust-added command argument `{value}`"));
            }
        }
    }

    let Some(mode) = mode else {
        return Some("Trust-added command must name one trust-added mode".to_string());
    };
    if !is_canonical_trust_added_mode(mode) {
        return Some(format!("unknown Trust-added command mode `{mode}`"));
    }
    if !release_seen {
        return Some(
            "Trust-added command must contain exactly one pre-mode `--release` flag".to_string(),
        );
    }

    None
}

fn is_canonical_trust_added_mode(mode: &str) -> bool {
    matches!(
        mode,
        "quick"
            | "trustc-native"
            | "trust-added-compiletest"
            | "trust-extra"
            | "binary-decompilation-golden"
            | "native-contracts-pipeline-v2"
            | "smoke"
            | "parity"
            | "full"
            | "launch"
            | "public-distribution"
            | "prepublish"
            | "installed"
            | "installed-default"
            | "stage0-lineage"
    )
}

fn forbidden_python_or_shell_launcher(part: &str) -> bool {
    let trimmed = part.trim_matches(|ch| matches!(ch, '\'' | '"' | '`'));
    let file_name = Path::new(trimmed)
        .file_name()
        .and_then(OsStr::to_str)
        .unwrap_or(trimmed)
        .to_ascii_lowercase();
    file_name == "x.py"
        || file_name == "run_trust_superset_suite.sh"
        || file_name == "run_trust_robust_suite.sh"
        || file_name == "env"
        || file_name == "sh"
        || file_name == "bash"
        || file_name == "zsh"
        || file_name == "fish"
        || file_name == "cmd"
        || file_name == "cmd.exe"
        || file_name == "powershell"
        || file_name == "powershell.exe"
        || file_name == "pwsh"
        || file_name == "pwsh.exe"
        || file_name == "python"
        || file_name == "python3"
        || file_name.starts_with("python3.")
        || file_name.starts_with("pypy")
        || file_name.ends_with(".py")
        || file_name.ends_with(".sh")
}

/// Validate cross-document per-test proof evidence and return computed totals.
pub fn validate_test_proof_bundle(
    bundle: TestProofBundle<'_>,
) -> Result<TestProofTotals, Vec<ValidationFinding>> {
    let mut findings = Vec::new();

    collect_validation(&mut findings, validate_test_inventory(bundle.inventory));
    collect_validation(&mut findings, validate_test_result_report(bundle.results));
    collect_validation(
        &mut findings,
        validate_test_exceptions_for_date(bundle.exceptions, bundle.validation_date),
    );
    if let Some(manifest) = bundle.trust_added_tests {
        collect_validation(&mut findings, validate_trust_added_tests(manifest));
    }

    let inventory: BTreeMap<&str, &TestInventoryEntry> =
        bundle.inventory.tests.iter().map(|test| (test.id.as_str(), test)).collect();
    let result_by_test: BTreeMap<&str, _> =
        bundle.results.results.iter().map(|result| (result.test_id.as_str(), result)).collect();
    let exception_by_id: BTreeMap<&str, &TestException> = bundle
        .exceptions
        .exceptions
        .iter()
        .map(|exception| (exception.id.as_str(), exception))
        .collect();

    let mut totals =
        TestProofTotals { total: bundle.inventory.tests.len() as u64, ..Default::default() };
    for test in &bundle.inventory.tests {
        match test.source {
            TestSource::UpstreamRust => totals.upstream += 1,
            TestSource::TrustAdded => totals.trust_added += 1,
        }

        if bundle.release && test.source == TestSource::UpstreamRust {
            if test.revision.as_deref() != Some(bundle.inventory.upstream_revision.as_str()) {
                findings.push(ValidationFinding::new(
                    "tests.revision",
                    format!(
                        "release proof upstream test '{}' must record inventory upstream revision '{}'",
                        test.id, bundle.inventory.upstream_revision
                    ),
                ));
            }
            if test.source_git_blob.as_ref().is_none_or(|blob| blob.trim().is_empty()) {
                findings.push(ValidationFinding::new(
                    "tests.source_git_blob",
                    format!(
                        "release proof upstream test '{}' must record its pristine upstream Git blob",
                        test.id
                    ),
                ));
            }
        }

        match result_by_test.get(test.id.as_str()) {
            Some(result) => match result.outcome {
                TestOutcome::Passed => totals.passed += 1,
                TestOutcome::UpstreamInapplicable => {
                    totals.upstream_inapplicable += 1;
                    if test.applicable {
                        findings.push(ValidationFinding::new(
                            "results.outcome",
                            format!(
                                "test '{}' was reported upstream_inapplicable but inventory marks it applicable",
                                test.id
                            ),
                        ));
                    }
                }
                TestOutcome::Failed | TestOutcome::Skipped | TestOutcome::Diffed => {
                    if result.exception_id.is_some() {
                        totals.excepted += 1;
                    } else {
                        totals.unaccounted += 1;
                        findings.push(ValidationFinding::new(
                            "results.exception_id",
                            format!(
                                "non-pass result for '{}' must reference an active per-test exception",
                                test.id
                            ),
                        ));
                    }
                }
                TestOutcome::Unknown => {
                    totals.unaccounted += 1;
                    if bundle.release {
                        findings.push(ValidationFinding::new(
                            "results.outcome",
                            format!(
                                "release proof cannot include unknown result for '{}'",
                                test.id
                            ),
                        ));
                    }
                }
            },
            None => {
                totals.unaccounted += 1;
                findings.push(ValidationFinding::new(
                    "results",
                    format!("result report is missing inventory test '{}'", test.id),
                ));
            }
        }
    }

    for result in &bundle.results.results {
        let Some(test) = inventory.get(result.test_id.as_str()) else {
            findings.push(ValidationFinding::new(
                "results.test_id",
                format!("result references unknown inventory test '{}'", result.test_id),
            ));
            continue;
        };

        if result.outcome == TestOutcome::UpstreamInapplicable
            && test.inapplicable_reason.as_ref().is_none_or(|reason| reason.trim().is_empty())
        {
            findings.push(ValidationFinding::new(
                "tests.inapplicable_reason",
                format!(
                    "upstream-inapplicable test '{}' must record the upstream directive or host reason",
                    test.id
                ),
            ));
        }

        if let Some(exception_id) = &result.exception_id {
            match exception_by_id.get(exception_id.as_str()) {
                Some(exception) => {
                    validate_result_exception_match(&mut findings, test, result.outcome, exception);
                    if exception.status != ExceptionStatus::Active {
                        findings.push(ValidationFinding::new(
                            "results.exception_id",
                            format!("exception '{exception_id}' is not active"),
                        ));
                    }
                }
                None => findings.push(ValidationFinding::new(
                    "results.exception_id",
                    format!("result references unknown per-test exception '{exception_id}'"),
                )),
            }
        }
    }

    let result_exception_ids: BTreeSet<&str> =
        bundle.results.results.iter().filter_map(|result| result.exception_id.as_deref()).collect();
    for exception in &bundle.exceptions.exceptions {
        if !inventory.contains_key(exception.test_id.as_str()) {
            findings.push(ValidationFinding::new(
                "test_exceptions.test_id",
                format!(
                    "per-test exception '{}' references unknown inventory test '{}'",
                    exception.id, exception.test_id
                ),
            ));
        }
        if bundle.release
            && exception.status == ExceptionStatus::Active
            && !result_exception_ids.contains(exception.id.as_str())
        {
            findings.push(ValidationFinding::new(
                "test_exceptions.exceptions",
                format!(
                    "active per-test exception '{}' did not match any observed result",
                    exception.id
                ),
            ));
        }
    }

    if totals.trust_added > 0 || bundle.release {
        match bundle.trust_added_tests {
            Some(manifest) => validate_trust_added_coverage(
                &mut findings,
                bundle.inventory,
                manifest,
                bundle.release,
            ),
            None => findings.push(ValidationFinding::new(
                "trust_added_tests",
                "proof must include a Trust-added test manifest",
            )),
        }
    }

    if bundle.release && totals.unaccounted != 0 {
        findings.push(ValidationFinding::new(
            "totals.unaccounted",
            format!("release proof has {} unaccounted test result(s)", totals.unaccounted),
        ));
    }

    if findings.is_empty() { Ok(totals) } else { Err(findings) }
}

/// Validate cross-document references among a baseline, ledgers, and result summary.
pub fn validate_accounting_bundle(bundle: AccountingBundle<'_>) -> ValidationResult {
    let mut findings = Vec::new();

    collect_validation(&mut findings, validate_baseline(bundle.baseline));

    let baseline_entries: BTreeSet<&str> =
        bundle.baseline.entries.iter().map(|entry| entry.id.as_str()).collect();

    let exceptions = match bundle.exceptions {
        Some(ledger) => {
            collect_validation(&mut findings, validate_exceptions(ledger));
            Some(index_exceptions(&mut findings, ledger, &baseline_entries))
        }
        None => None,
    };

    let fixes = match bundle.upstream_fixes {
        Some(ledger) => {
            collect_validation(&mut findings, validate_upstream_fixes(ledger));
            Some(index_upstream_fixes(&mut findings, ledger, &baseline_entries))
        }
        None => None,
    };

    if let Some(summary) = bundle.result_summary {
        collect_validation(&mut findings, validate_result_summary(summary));
        if summary.baseline_id != bundle.baseline.id {
            findings.push(ValidationFinding::new(
                "result_summary.baseline_id",
                format!(
                    "summary baseline '{}' does not match baseline '{}'",
                    summary.baseline_id, bundle.baseline.id
                ),
            ));
        }

        let summary_result_entries: BTreeSet<&str> =
            summary.results.iter().map(|result| result.baseline_entry_id.as_str()).collect();
        for entry in &bundle.baseline.entries {
            if !summary_result_entries.contains(entry.id.as_str()) {
                findings.push(ValidationFinding::new(
                    "result_summary.results",
                    format!("summary is missing result for baseline entry '{}'", entry.id),
                ));
            }
        }

        for result in &summary.results {
            if !baseline_entries.contains(result.baseline_entry_id.as_str()) {
                findings.push(ValidationFinding::new(
                    "result_summary.results.baseline_entry_id",
                    format!(
                        "result references unknown baseline entry '{}'",
                        result.baseline_entry_id
                    ),
                ));
            }

            if let Some(exception_id) = &result.exception_id {
                match exceptions.as_ref().and_then(|map| map.get(exception_id.as_str())) {
                    Some(exception) => {
                        if exception.baseline_entry_id != result.baseline_entry_id {
                            findings.push(ValidationFinding::new(
                                "result_summary.results.exception_id",
                                format!(
                                    "exception '{}' belongs to baseline entry '{}', not '{}'",
                                    exception_id,
                                    exception.baseline_entry_id,
                                    result.baseline_entry_id
                                ),
                            ));
                        }
                        if exception.status != ExceptionStatus::Active {
                            findings.push(ValidationFinding::new(
                                "result_summary.results.exception_id",
                                format!("exception '{exception_id}' is not active"),
                            ));
                        }
                    }
                    None => findings.push(ValidationFinding::new(
                        "result_summary.results.exception_id",
                        format!("result references unknown exception '{exception_id}'"),
                    )),
                }
            }

            if let Some(fix_id) = &result.upstream_fix_id {
                match fixes.as_ref().and_then(|map| map.get(fix_id.as_str())) {
                    Some(fix) => {
                        if fix.baseline_entry_id != result.baseline_entry_id {
                            findings.push(ValidationFinding::new(
                                "result_summary.results.upstream_fix_id",
                                format!(
                                    "upstream fix '{}' belongs to baseline entry '{}', not '{}'",
                                    fix_id, fix.baseline_entry_id, result.baseline_entry_id
                                ),
                            ));
                        }
                        if !matches!(
                            fix.status,
                            UpstreamFixStatus::Landed
                                | UpstreamFixStatus::Released
                                | UpstreamFixStatus::Backported
                        ) {
                            findings.push(ValidationFinding::new(
                                "result_summary.results.upstream_fix_id",
                                format!("upstream fix '{fix_id}' is not landed or released"),
                            ));
                        }
                    }
                    None => findings.push(ValidationFinding::new(
                        "result_summary.results.upstream_fix_id",
                        format!("result references unknown upstream fix '{fix_id}'"),
                    )),
                }
            }
        }
    }

    if let Some(current_upstream_revision) = bundle.current_upstream_revision {
        collect_validation(
            &mut findings,
            validate_upstream_revision_accounting(
                bundle.baseline,
                bundle.upstream_fixes,
                current_upstream_revision,
            ),
        );
    }

    finish(findings)
}

/// Validate that a newer upstream revision has at least ledger-level accounting.
pub fn validate_upstream_revision_accounting(
    baseline: &CompatibilityBaseline,
    upstream_fixes: Option<&UpstreamFixLedger>,
    current_upstream_revision: &str,
) -> ValidationResult {
    let mut findings = Vec::new();

    require_non_empty(&mut findings, "current_upstream_revision", current_upstream_revision);

    let baseline_revision = revision_suffix(&baseline.upstream.revision);
    let current_revision = revision_suffix(current_upstream_revision);
    if !current_revision.is_empty() && current_revision != baseline_revision {
        match upstream_fixes {
            Some(ledger) => {
                if ledger.fixes.is_empty() && ledger.tracked_until_revision.is_none() {
                    findings.push(ValidationFinding::new(
                        "upstream_fixes.fixes",
                        format!(
                            "baseline upstream revision '{}' differs from current upstream revision '{}', but the upstream fix ledger is empty",
                            baseline.upstream.revision, current_upstream_revision
                        ),
                    ));
                }

                match ledger.tracked_until_revision.as_deref() {
                    Some(tracked_revision)
                        if revision_suffix(tracked_revision) == current_revision => {}
                    Some(tracked_revision) => findings.push(ValidationFinding::new(
                        "upstream_fixes.tracked_until_revision",
                        format!(
                            "upstream fix ledger was reviewed through '{}', not current upstream revision '{}'",
                            tracked_revision, current_upstream_revision
                        ),
                    )),
                    None => findings.push(ValidationFinding::new(
                        "upstream_fixes.tracked_until_revision",
                        format!(
                            "baseline upstream revision '{}' differs from current upstream revision '{}', but the upstream fix ledger has no reviewed-through revision",
                            baseline.upstream.revision, current_upstream_revision
                        ),
                    )),
                }
            }
            None => findings.push(ValidationFinding::new(
                "upstream_fixes",
                format!(
                    "baseline upstream revision '{}' differs from current upstream revision '{}', but no upstream fix ledger was provided",
                    baseline.upstream.revision, current_upstream_revision
                ),
            )),
        }
    }

    finish(findings)
}

fn validate_exception(
    findings: &mut Vec<ValidationFinding>,
    exception: &CompatibilityException,
    idx: usize,
    ids: &mut BTreeSet<String>,
) {
    let prefix = format!("exceptions[{idx}]");
    require_id(findings, format!("{prefix}.id"), &exception.id);
    require_unique(findings, "exceptions.id", &exception.id, ids);
    require_id(findings, format!("{prefix}.baseline_entry_id"), &exception.baseline_entry_id);
    require_non_empty(findings, format!("{prefix}.title"), &exception.title);
    require_non_empty(findings, format!("{prefix}.owner"), &exception.owner);
    require_non_empty(findings, format!("{prefix}.reason"), &exception.reason);

    if let Some(expires_on) = &exception.expires_on {
        require_date(findings, format!("{prefix}.expires_on"), expires_on);
    } else if exception.status == ExceptionStatus::Expired {
        findings.push(ValidationFinding::new(
            format!("{prefix}.expires_on"),
            "expired exception must include expires_on",
        ));
    }

    if let Some(reference) = &exception.upstream_reference {
        require_non_empty(findings, format!("{prefix}.upstream_reference"), reference);
    }
    if let Some(reference) = &exception.local_reference {
        require_non_empty(findings, format!("{prefix}.local_reference"), reference);
    }
}

fn validate_upstream_fix(
    findings: &mut Vec<ValidationFinding>,
    fix: &UpstreamFix,
    idx: usize,
    ids: &mut BTreeSet<String>,
) {
    let prefix = format!("fixes[{idx}]");
    require_id(findings, format!("{prefix}.id"), &fix.id);
    require_unique(findings, "fixes.id", &fix.id, ids);
    require_id(findings, format!("{prefix}.baseline_entry_id"), &fix.baseline_entry_id);
    require_non_empty(findings, format!("{prefix}.title"), &fix.title);
    require_non_empty(findings, format!("{prefix}.upstream_reference"), &fix.upstream_reference);

    if let Some(landed_on) = &fix.landed_on {
        require_date(findings, format!("{prefix}.landed_on"), landed_on);
    }

    if matches!(fix.status, UpstreamFixStatus::Released | UpstreamFixStatus::Backported)
        && fix.released_in.as_ref().is_none_or(|released_in| released_in.trim().is_empty())
    {
        findings.push(ValidationFinding::new(
            format!("{prefix}.released_in"),
            "released or backported upstream fix must include released_in",
        ));
    }

    if matches!(
        fix.status,
        UpstreamFixStatus::Landed | UpstreamFixStatus::Released | UpstreamFixStatus::Backported
    ) && fix.landed_on.is_none()
        && fix.landed_in_revision.as_ref().is_none_or(|revision| revision.trim().is_empty())
    {
        findings.push(ValidationFinding::new(
            format!("{prefix}.landed_in_revision"),
            "landed, released, or backported upstream fix must include landed_on or landed_in_revision",
        ));
    }

    if let Some(revision) = &fix.landed_in_revision {
        require_non_empty(findings, format!("{prefix}.landed_in_revision"), revision);
    }
    if let Some(released_in) = &fix.released_in {
        require_non_empty(findings, format!("{prefix}.released_in"), released_in);
    }
}

fn validate_inventory_entry(
    findings: &mut Vec<ValidationFinding>,
    test: &TestInventoryEntry,
    idx: usize,
    ids: &mut BTreeSet<String>,
) {
    let prefix = format!("tests[{idx}]");
    require_id(findings, format!("{prefix}.id"), &test.id);
    require_unique(findings, "tests.id", &test.id, ids);
    require_non_empty(findings, format!("{prefix}.suite"), &test.suite);
    require_non_empty(findings, format!("{prefix}.path"), &test.path);
    if let Some(revision) = &test.revision {
        require_non_empty(findings, format!("{prefix}.revision"), revision);
    }
    if let Some(source_git_blob) = &test.source_git_blob {
        require_git_object_id(findings, format!("{prefix}.source_git_blob"), source_git_blob);
    }
    if !test.applicable
        && test.inapplicable_reason.as_ref().is_none_or(|reason| reason.trim().is_empty())
    {
        findings.push(ValidationFinding::new(
            format!("{prefix}.inapplicable_reason"),
            "inapplicable tests must record the upstream directive or host reason",
        ));
    }
    if let Some(source_sha256) = &test.source_sha256 {
        require_sha256(findings, format!("{prefix}.source_sha256"), source_sha256);
    }
}

fn validate_test_exception(
    findings: &mut Vec<ValidationFinding>,
    exception: &TestException,
    idx: usize,
    ids: &mut BTreeSet<String>,
    validation_date: Option<&str>,
) {
    let prefix = format!("exceptions[{idx}]");
    require_id(findings, format!("{prefix}.id"), &exception.id);
    require_unique(findings, "exceptions.id", &exception.id, ids);
    require_id(findings, format!("{prefix}.test_id"), &exception.test_id);
    require_non_empty(findings, format!("{prefix}.suite"), &exception.suite);
    require_non_empty(findings, format!("{prefix}.path"), &exception.path);
    if let Some(revision) = &exception.revision {
        require_non_empty(findings, format!("{prefix}.revision"), revision);
    }
    require_non_empty(findings, format!("{prefix}.owner"), &exception.owner);
    require_non_empty(findings, format!("{prefix}.reason"), &exception.reason);
    require_non_empty(findings, format!("{prefix}.issue"), &exception.issue);
    require_date(findings, format!("{prefix}.reviewed_on"), &exception.reviewed_on);
    require_date(findings, format!("{prefix}.expires_on"), &exception.expires_on);
    validate_test_exception_expiry(findings, &prefix, exception, validation_date);
    if let Some(introduced_by) = &exception.introduced_by {
        require_non_empty(findings, format!("{prefix}.introduced_by"), introduced_by);
    }

    if matches!(exception.kind, TestExceptionKind::ChangedDiagnostic)
        && exception.allowed_patterns.is_empty()
    {
        findings.push(ValidationFinding::new(
            format!("{prefix}.allowed_patterns"),
            "changed_diagnostic exceptions must bound the accepted output drift",
        ));
    }
    for (pattern_idx, pattern) in exception.allowed_patterns.iter().enumerate() {
        require_non_empty(findings, format!("{prefix}.allowed_patterns[{pattern_idx}]"), pattern);
    }
}

fn validate_test_exception_expiry(
    findings: &mut Vec<ValidationFinding>,
    prefix: &str,
    exception: &TestException,
    validation_date: Option<&str>,
) {
    if exception.status != ExceptionStatus::Active
        || !is_yyyy_mm_dd(&exception.reviewed_on)
        || !is_yyyy_mm_dd(&exception.expires_on)
    {
        return;
    }

    if exception.expires_on.as_str() <= exception.reviewed_on.as_str() {
        findings.push(ValidationFinding::new(
            format!("{prefix}.expires_on"),
            "active test exception expires_on must be after reviewed_on",
        ));
    }

    if let Some(validation_date) = validation_date
        && exception.expires_on.as_str() <= validation_date
    {
        findings.push(ValidationFinding::new(
            format!("{prefix}.expires_on"),
            format!(
                "active test exception expires_on must be after validation date '{validation_date}'"
            ),
        ));
    }
}

fn validate_result_exception_match(
    findings: &mut Vec<ValidationFinding>,
    test: &TestInventoryEntry,
    outcome: TestOutcome,
    exception: &TestException,
) {
    if exception.test_id != test.id {
        findings.push(ValidationFinding::new(
            "results.exception_id",
            format!(
                "exception '{}' belongs to test '{}', not '{}'",
                exception.id, exception.test_id, test.id
            ),
        ));
    }
    if exception.suite != test.suite {
        findings.push(ValidationFinding::new(
            "test_exceptions.suite",
            format!(
                "exception '{}' suite '{}' does not match inventory suite '{}'",
                exception.id, exception.suite, test.suite
            ),
        ));
    }
    if exception.path != test.path {
        findings.push(ValidationFinding::new(
            "test_exceptions.path",
            format!(
                "exception '{}' path '{}' does not match inventory path '{}'",
                exception.id, exception.path, test.path
            ),
        ));
    }
    if exception.revision != test.revision {
        findings.push(ValidationFinding::new(
            "test_exceptions.revision",
            format!("exception '{}' revision does not match inventory", exception.id),
        ));
    }

    let kind_matches = matches!(
        (outcome, exception.kind),
        (TestOutcome::Failed, TestExceptionKind::ExpectedFail)
            | (TestOutcome::Failed, TestExceptionKind::IntentionalDivergence)
            | (TestOutcome::Skipped, TestExceptionKind::ExpectedSkip)
            | (TestOutcome::Skipped, TestExceptionKind::EnvironmentalSkip)
            | (TestOutcome::Diffed, TestExceptionKind::ChangedDiagnostic)
            | (TestOutcome::Diffed, TestExceptionKind::IntentionalDivergence)
    );
    if !kind_matches {
        findings.push(ValidationFinding::new(
            "test_exceptions.kind",
            format!(
                "exception '{}' kind {:?} does not account for outcome {:?}",
                exception.id, exception.kind, outcome
            ),
        ));
    }
}

fn validate_trust_added_coverage(
    findings: &mut Vec<ValidationFinding>,
    inventory: &TestInventory,
    manifest: &TrustAddedTestManifest,
    release: bool,
) {
    let inventory_ids: BTreeSet<&str> =
        inventory.tests.iter().map(|test| test.id.as_str()).collect();
    let trust_added_ids: BTreeSet<&str> = inventory
        .tests
        .iter()
        .filter(|test| test.source == TestSource::TrustAdded)
        .map(|test| test.id.as_str())
        .collect();
    let mut covered = BTreeSet::new();

    for command in &manifest.commands {
        if release && command.required && command.command.trim().is_empty() {
            findings.push(ValidationFinding::new(
                "trust_added_tests.commands.command",
                format!("required Trust-added command '{}' is empty", command.id),
            ));
        }

        for test_id in &command.covers {
            if !inventory_ids.contains(test_id.as_str()) {
                findings.push(ValidationFinding::new(
                    "trust_added_tests.commands.covers",
                    format!(
                        "Trust-added command '{}' covers unknown inventory test '{}'",
                        command.id, test_id
                    ),
                ));
            }
            covered.insert(test_id.as_str());
        }
    }

    for test_id in trust_added_ids {
        if !covered.contains(test_id) {
            findings.push(ValidationFinding::new(
                "trust_added_tests.commands.covers",
                format!("Trust-added inventory test '{test_id}' is not covered by any command"),
            ));
        }
    }
}

fn index_exceptions<'a>(
    findings: &mut Vec<ValidationFinding>,
    ledger: &'a ExceptionLedger,
    baseline_entries: &BTreeSet<&str>,
) -> BTreeMap<&'a str, &'a CompatibilityException> {
    let mut indexed = BTreeMap::new();
    for exception in &ledger.exceptions {
        if !baseline_entries.contains(exception.baseline_entry_id.as_str()) {
            findings.push(ValidationFinding::new(
                "exceptions.baseline_entry_id",
                format!(
                    "exception '{}' references unknown baseline entry '{}'",
                    exception.id, exception.baseline_entry_id
                ),
            ));
        }
        indexed.insert(exception.id.as_str(), exception);
    }
    indexed
}

fn index_upstream_fixes<'a>(
    findings: &mut Vec<ValidationFinding>,
    ledger: &'a UpstreamFixLedger,
    baseline_entries: &BTreeSet<&str>,
) -> BTreeMap<&'a str, &'a UpstreamFix> {
    let mut indexed = BTreeMap::new();
    for fix in &ledger.fixes {
        if !baseline_entries.contains(fix.baseline_entry_id.as_str()) {
            findings.push(ValidationFinding::new(
                "fixes.baseline_entry_id",
                format!(
                    "upstream fix '{}' references unknown baseline entry '{}'",
                    fix.id, fix.baseline_entry_id
                ),
            ));
        }
        indexed.insert(fix.id.as_str(), fix);
    }
    indexed
}

fn validate_schema_version(
    findings: &mut Vec<ValidationFinding>,
    field: impl Into<String>,
    value: &str,
) {
    if value != SCHEMA_VERSION {
        findings.push(ValidationFinding::new(
            field,
            format!("unsupported schema version '{value}', expected '{SCHEMA_VERSION}'"),
        ));
    }
}

fn require_id(findings: &mut Vec<ValidationFinding>, field: impl Into<String>, value: &str) {
    let field = field.into();
    require_non_empty(findings, field.clone(), value);
    if !value.trim().is_empty() && !is_valid_id(value) {
        findings.push(ValidationFinding::new(
            field,
            "id must contain only ASCII letters, digits, '.', '_', ':', or '-'",
        ));
    }
}

fn require_non_empty(findings: &mut Vec<ValidationFinding>, field: impl Into<String>, value: &str) {
    if value.trim().is_empty() {
        findings.push(ValidationFinding::new(field, "must not be empty"));
    }
}

fn require_unique(
    findings: &mut Vec<ValidationFinding>,
    field: impl Into<String>,
    value: &str,
    seen: &mut BTreeSet<String>,
) {
    if !seen.insert(value.to_string()) {
        findings.push(ValidationFinding::new(field, format!("duplicate id '{value}'")));
    }
}

fn require_date(findings: &mut Vec<ValidationFinding>, field: impl Into<String>, value: &str) {
    let field = field.into();
    require_non_empty(findings, field.clone(), value);
    if !value.trim().is_empty() && !is_yyyy_mm_dd(value) {
        findings.push(ValidationFinding::new(field, "date must use YYYY-MM-DD format"));
    }
}

fn require_sha256(findings: &mut Vec<ValidationFinding>, field: impl Into<String>, value: &str) {
    let field = field.into();
    require_non_empty(findings, field.clone(), value);
    let Some(hex) = value.strip_prefix("sha256:") else {
        findings.push(ValidationFinding::new(field, "digest must use sha256:<hex> format"));
        return;
    };

    if hex.len() != 64 || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        findings.push(ValidationFinding::new(
            field,
            "sha256 digest must contain exactly 64 hexadecimal characters",
        ));
    }
}

fn require_git_object_id(
    findings: &mut Vec<ValidationFinding>,
    field: impl Into<String>,
    value: &str,
) {
    let field = field.into();
    let len = value.len();
    if !(len == 40 || len == 64) || !value.chars().all(|ch| ch.is_ascii_hexdigit()) {
        findings.push(ValidationFinding::new(
            field,
            "Git object id must contain 40 or 64 hexadecimal characters",
        ));
    }
}

fn collect_validation(findings: &mut Vec<ValidationFinding>, result: ValidationResult) {
    if let Err(mut validation_findings) = result {
        findings.append(&mut validation_findings);
    }
}

fn finish(findings: Vec<ValidationFinding>) -> ValidationResult {
    if findings.is_empty() { Ok(()) } else { Err(findings) }
}

fn is_valid_id(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b':' | b'-'))
}

fn revision_suffix(value: &str) -> &str {
    value.rsplit_once(':').map_or(value, |(_, suffix)| suffix).trim()
}

fn is_yyyy_mm_dd(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 10
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || !bytes[..4].iter().all(u8::is_ascii_digit)
        || !bytes[5..7].iter().all(u8::is_ascii_digit)
        || !bytes[8..10].iter().all(u8::is_ascii_digit)
    {
        return false;
    }

    let year = parse_digits(&bytes[..4]);
    let month = parse_digits(&bytes[5..7]);
    let day = parse_digits(&bytes[8..10]);

    if year == 0 || !(1..=12).contains(&month) {
        return false;
    }

    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => return false,
    };

    (1..=max_day).contains(&day)
}

fn parse_digits(bytes: &[u8]) -> u32 {
    bytes.iter().fold(0, |acc, byte| acc * 10 + u32::from(byte - b'0'))
}

fn is_leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

#[cfg(test)]
mod tests {
    use super::canonical_trust_added_command_violation;

    #[test]
    fn canonical_trust_added_command_requires_exactly_one_pre_mode_release() {
        assert_eq!(
            canonical_trust_added_command_violation(
                "targo trust domination trust-added --release quick"
            ),
            None
        );

        for command in [
            "targo trust domination trust-added quick",
            "targo trust domination trust-added --release --release quick",
            "targo trust domination trust-added quick --release",
        ] {
            let violation = canonical_trust_added_command_violation(command)
                .expect("non-release canonical command must be rejected");
            assert!(
                violation.contains("--release"),
                "unexpected violation for {command:?}: {violation}"
            );
        }
    }
}
