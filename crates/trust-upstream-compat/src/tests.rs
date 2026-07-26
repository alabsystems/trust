use crate::validate::validate_test_exceptions_for_date;
use crate::{
    AccountingBundle, BaselineEntry, BaselineStatus, CompatibilityBaseline, CompatibilityException,
    CompatibilityExpectation, CompatibilityOutcome, CompatibilityResult,
    CompatibilityResultSummary, CompatibilitySurface, ExceptionClass, ExceptionLedger,
    ExceptionStatus, LocalFixAction, LocalSnapshot, ParseError, ResultTotals, SCHEMA_VERSION,
    TestException, TestExceptionKind, TestExceptionLedger, UpstreamFix, UpstreamFixLedger,
    UpstreamFixStatus, UpstreamSnapshot, parse_baseline_toml, parse_exceptions_toml,
    parse_result_summary_json, parse_test_exceptions_toml, parse_trust_added_tests_toml,
    parse_upstream_fixes_toml, validate_accounting_bundle, validate_baseline, validate_exceptions,
    validate_result_summary, validate_test_exceptions, validate_trust_added_tests,
    validate_upstream_revision_accounting,
};

const PRODUCTION_TEST_EXCEPTIONS: &str =
    include_str!("../../../tests/upstream-rust/test-exceptions.toml");
const PRODUCTION_TRUST_ADDED_MANIFEST: &str =
    include_str!("../../../tests/trust-added/manifest.toml");

#[test]
fn parse_baseline_toml_accepts_valid_document() {
    let baseline = parse_baseline_toml(
        r#"
schema_version = "0.1.0"
id = "baseline-2026-04-26"

[upstream]
channel = "nightly"
revision = "rust-lang-rust:abc123"
snapshot_date = "2026-04-25"

[local]
revision = "trust:def456"
branch = "main"

[[entries]]
id = "diag.E0001"
title = "borrow checker diagnostic shape"
surface = "compiler_diagnostic"
upstream_artifact = "tests/ui/borrowck/borrowck-move-error.rs"
local_artifact = "tests/ui/borrowck/borrowck-move-error.trust.rs"
status = "compatible"
labels = ["diagnostics", "borrowck"]

[entries.expectation]
upstream_behavior = "emits E0382 with primary move span"
local_behavior = "emits E0382 with matching primary move span"
compatibility_rule = "diagnostic code and primary span must match"
"#,
    )
    .expect("baseline should parse and validate");

    assert_eq!(baseline.id, "baseline-2026-04-26");
    assert_eq!(baseline.entries.len(), 1);
    assert_eq!(baseline.entries[0].surface, CompatibilitySurface::CompilerDiagnostic);
}

#[test]
fn validate_baseline_rejects_duplicate_entry_ids() {
    let mut baseline = sample_baseline();
    baseline.entries.push(baseline.entries[0].clone());

    let findings = validate_baseline(&baseline).unwrap_err();
    assert!(findings.iter().any(|finding| finding.field == "entries.id"));
}

#[test]
fn parse_exception_and_fix_ledgers_toml_accept_valid_documents() {
    let exceptions = parse_exceptions_toml(
        r#"
schema_version = "0.1.0"

[[exceptions]]
id = "exc.diag.E0001"
baseline_entry_id = "diag.E0001"
title = "diagnostic wording drift"
class = "intentional_divergence"
status = "active"
owner = "compiler-team"
reason = "local diagnostic wording is intentionally shorter"
expires_on = "2026-06-01"
upstream_reference = "rust-lang/rust#123456"
"#,
    )
    .expect("exception ledger should parse and validate");

    let fixes = parse_upstream_fixes_toml(
        r#"
schema_version = "0.1.0"
tracked_until_revision = "rust-lang-rust:feedface"

[[fixes]]
id = "fix.mir.drop-order"
baseline_entry_id = "mir.drop-order"
title = "upstream MIR drop elaboration fix"
upstream_reference = "rust-lang/rust#123457"
status = "landed"
local_action = "rebase_baseline"
landed_on = "2026-04-20"
"#,
    )
    .expect("upstream fix ledger should parse and validate");

    assert_eq!(exceptions.exceptions[0].id, "exc.diag.E0001");
    assert_eq!(fixes.tracked_until_revision.as_deref(), Some("rust-lang-rust:feedface"));
    assert_eq!(fixes.fixes[0].status, UpstreamFixStatus::Landed);
}

#[test]
fn parse_result_summary_json_validates_declared_totals() {
    let mut summary = sample_summary();
    summary.totals.total = 99;

    let json = serde_json::to_string(&summary).expect("summary should serialize");
    let err = parse_result_summary_json(&json).unwrap_err();

    match err {
        ParseError::Validation { findings } => {
            assert!(findings.iter().any(|finding| finding.field == "totals"));
        }
        other => panic!("expected validation error, got {other:?}"),
    }
}

#[test]
fn parse_result_summary_json_accepts_legacy_summary_without_provenance() {
    let summary = parse_result_summary_json(
        r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline-legacy",
  "generated_on": "2026-04-26",
  "totals": {
    "total": 1,
    "compatible": 1,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible"
    }
  ]
}"#,
    )
    .expect("legacy summaries without provenance should remain valid");

    assert_eq!(summary.generated_on, "2026-04-26");
    assert_eq!(summary.run_id, None);
    assert_eq!(summary.repo_head, None);
    assert_eq!(summary.repo_dirty, None);
    assert_eq!(summary.upstream_revision, None);
    assert!(summary.runner.is_none());

    let value = serde_json::to_value(&summary).expect("legacy summary should serialize");
    assert_eq!(value["generated_on"].as_str(), Some("2026-04-26"));
    assert!(value.get("run_id").is_none());
    assert!(value.get("repo_head").is_none());
    assert!(value.get("repo_dirty").is_none());
    assert!(value.get("upstream_revision").is_none());
    assert!(value.get("runner").is_none());
}

#[test]
fn parse_result_summary_json_round_trips_provenance_fields() {
    let summary = parse_result_summary_json(
        r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline.cli",
  "generated_on": "2026-04-26",
  "run_id": "ci-42",
  "repo_head": "0123456789abcdef0123456789abcdef01234567",
  "repo_dirty": false,
  "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "target_arch": "aarch64",
  "target_triple": "aarch64-apple-darwin",
  "host_triple": "aarch64-apple-darwin",
  "runner": {
    "implementation": "rust",
    "entrypoint": "targo trust domination upstream-tests",
    "python_used": false,
    "tool": "trust-upstream-compat",
    "argv": ["targo", "trust", "domination", "upstream-tests"],
    "metadata": {
      "profile": "release"
    }
  },
  "totals": {
    "total": 1,
    "compatible": 1,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    }
  ]
}"#,
    )
    .expect("summary with provenance should parse and validate");

    assert_eq!(summary.generated_on, "2026-04-26");
    assert_eq!(summary.run_id.as_deref(), Some("ci-42"));
    assert_eq!(summary.repo_head.as_deref(), Some("0123456789abcdef0123456789abcdef01234567"));
    assert_eq!(summary.repo_dirty, Some(false));
    assert_eq!(
        summary.upstream_revision.as_deref(),
        Some("rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
    );
    assert_eq!(summary.target_arch.as_deref(), Some("aarch64"));
    assert_eq!(summary.target_triple.as_deref(), Some("aarch64-apple-darwin"));
    assert_eq!(summary.host_triple.as_deref(), Some("aarch64-apple-darwin"));

    let runner = summary.runner.as_ref().expect("runner should be preserved");
    assert_eq!(runner.python_used, Some(false));
    assert_eq!(runner.implementation.as_ref().and_then(serde_json::Value::as_str), Some("rust"));
    assert_eq!(
        runner.entrypoint.as_ref().and_then(serde_json::Value::as_str),
        Some("targo trust domination upstream-tests")
    );
    assert_eq!(
        runner.metadata.get("argv").and_then(serde_json::Value::as_array).map(Vec::len),
        Some(4)
    );

    let value = serde_json::to_value(&summary).expect("summary should serialize");
    assert_eq!(value["generated_on"].as_str(), Some("2026-04-26"));
    assert_eq!(value["repo_dirty"].as_bool(), Some(false));
    assert_eq!(value["target_arch"].as_str(), Some("aarch64"));
    assert_eq!(value["target_triple"].as_str(), Some("aarch64-apple-darwin"));
    assert_eq!(value["host_triple"].as_str(), Some("aarch64-apple-darwin"));
    assert_eq!(value["runner"]["python_used"].as_bool(), Some(false));
    assert_eq!(value["runner"]["implementation"].as_str(), Some("rust"));
    assert_eq!(value["runner"]["argv"][0].as_str(), Some("targo"));
    assert_eq!(value["runner"]["metadata"]["profile"].as_str(), Some("release"));
}

#[test]
fn validate_result_summary_requires_outcome_references() {
    let mut summary = sample_summary();
    summary.results[0].exception_id = None;
    summary.totals = summary.recount_totals();

    let findings = validate_result_summary(&summary).unwrap_err();
    assert!(findings.iter().any(|finding| finding.field == "results[0].exception_id"));
}

#[test]
fn validate_exceptions_requires_expiry_for_expired_records() {
    let mut ledger = sample_exceptions();
    ledger.exceptions[0].status = ExceptionStatus::Expired;
    ledger.exceptions[0].expires_on = None;

    let findings = validate_exceptions(&ledger).unwrap_err();
    assert!(findings.iter().any(|finding| finding.field == "exceptions[0].expires_on"));
}

#[test]
fn parse_production_test_exception_ledger_validates_against_review_date() {
    let ledger = parse_test_exceptions_toml(PRODUCTION_TEST_EXCEPTIONS)
        .expect("production per-test exception ledger should parse and validate");

    assert!(!ledger.exceptions.is_empty(), "production ledger must contain at least one exception");
    validate_test_exceptions_for_date(&ledger, "2026-04-29")
        .expect("production per-test exception ledger should be current on 2026-04-29");
}

#[test]
fn parse_production_trust_added_manifest_uses_rust_cli_commands() {
    let manifest = parse_trust_added_tests_toml(PRODUCTION_TRUST_ADDED_MANIFEST)
        .expect("production Trust-added manifest should parse and validate");

    validate_trust_added_tests(&manifest)
        .expect("production Trust-added manifest should reject shell/Python launchers");
    assert!(!manifest.commands.is_empty(), "production manifest must cover Trust-added tests");
    assert!(
        manifest
            .commands
            .iter()
            .all(|command| { command.command.starts_with("targo trust domination trust-added") })
    );
}

#[test]
fn trust_added_manifest_rejects_noncanonical_native_command() {
    let err = parse_trust_added_tests_toml(
        r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.custom"
command = "target/debug/custom-runner"
covers = ["trust.added.custom"]
required = true
"#,
    )
    .expect_err("Trust-added manifest must require the domination trust-added CLI");

    match err {
        ParseError::Validation { findings } => assert!(findings.iter().any(|finding| {
            finding.field == "commands[0].command"
                && finding.message.contains("targo trust domination trust-added")
        })),
        other => panic!("expected validation error, got {other:?}"),
    }
}

#[test]
fn validate_test_exceptions_rejects_active_expiry_not_after_review() {
    let mut ledger = sample_test_exceptions();
    ledger.exceptions[0].reviewed_on = "2026-04-29".to_string();
    ledger.exceptions[0].expires_on = "2026-04-29".to_string();

    let findings = validate_test_exceptions(&ledger)
        .expect_err("active test exception must expire after review date");

    assert!(findings.iter().any(|finding| {
        finding.field == "exceptions[0].expires_on" && finding.message.contains("after reviewed_on")
    }));
}

#[test]
fn validate_test_exceptions_for_date_rejects_active_stale_expiry() {
    let mut ledger = sample_test_exceptions();
    ledger.exceptions[0].reviewed_on = "2026-04-01".to_string();
    ledger.exceptions[0].expires_on = "2026-04-29".to_string();

    let findings = validate_test_exceptions_for_date(&ledger, "2026-04-29")
        .expect_err("active test exception must not be stale on validation date");

    assert!(findings.iter().any(|finding| {
        finding.field == "exceptions[0].expires_on"
            && finding.message.contains("validation date '2026-04-29'")
    }));
}

#[test]
fn validate_accounting_bundle_accepts_consistent_ledgers() {
    let baseline = sample_baseline();
    let exceptions = sample_exceptions();
    let fixes = sample_fixes();
    let summary = sample_summary();

    validate_accounting_bundle(AccountingBundle {
        baseline: &baseline,
        exceptions: Some(&exceptions),
        upstream_fixes: Some(&fixes),
        result_summary: Some(&summary),
        current_upstream_revision: None,
    })
    .expect("consistent accounting bundle should validate");
}

#[test]
fn validate_accounting_bundle_rejects_dangling_references() {
    let baseline = sample_baseline();
    let exceptions = sample_exceptions();
    let fixes = sample_fixes();
    let mut summary = sample_summary();
    summary.results[0].exception_id = Some("exc.missing".to_string());
    summary.results[1].baseline_entry_id = "entry.missing".to_string();
    summary.totals = summary.recount_totals();

    let findings = validate_accounting_bundle(AccountingBundle {
        baseline: &baseline,
        exceptions: Some(&exceptions),
        upstream_fixes: Some(&fixes),
        result_summary: Some(&summary),
        current_upstream_revision: None,
    })
    .unwrap_err();

    assert!(findings.iter().any(|finding| {
        finding.field == "result_summary.results.exception_id"
            && finding.message.contains("unknown exception")
    }));
    assert!(findings.iter().any(|finding| {
        finding.field == "result_summary.results.baseline_entry_id"
            && finding.message.contains("unknown baseline entry")
    }));
}

#[test]
fn validate_accounting_bundle_rejects_summary_missing_baseline_entries() {
    let baseline = sample_baseline();
    let exceptions = sample_exceptions();
    let fixes = sample_fixes();
    let mut summary = sample_summary();
    summary.results.retain(|result| result.baseline_entry_id != "mir.drop-order");
    summary.totals = summary.recount_totals();

    let findings = validate_accounting_bundle(AccountingBundle {
        baseline: &baseline,
        exceptions: Some(&exceptions),
        upstream_fixes: Some(&fixes),
        result_summary: Some(&summary),
        current_upstream_revision: None,
    })
    .expect_err("summary must account for every baseline entry");

    assert!(findings.iter().any(|finding| {
        finding.field == "result_summary.results"
            && finding.message.contains("mir.drop-order")
            && finding.message.contains("missing result")
    }));
}

#[test]
fn validate_upstream_revision_accounting_rejects_empty_fix_ledger_after_drift() {
    let baseline = sample_baseline();
    let empty_fixes = UpstreamFixLedger {
        schema_version: SCHEMA_VERSION.to_string(),
        tracked_until_revision: None,
        fixes: vec![],
    };

    let findings = validate_upstream_revision_accounting(
        &baseline,
        Some(&empty_fixes),
        "rust-lang-rust:feedface",
    )
    .expect_err("newer upstream revision with no fix records should fail closed");

    assert!(findings.iter().any(|finding| {
        finding.field == "upstream_fixes.fixes"
            && finding.message.contains("differs from current upstream revision")
    }));
}

#[test]
fn validate_upstream_revision_accounting_accepts_empty_fix_ledger_without_drift() {
    let baseline = sample_baseline();
    let empty_fixes = UpstreamFixLedger {
        schema_version: SCHEMA_VERSION.to_string(),
        tracked_until_revision: None,
        fixes: vec![],
    };

    validate_upstream_revision_accounting(&baseline, Some(&empty_fixes), "rust-lang-rust:abc123")
        .expect("same upstream revision should not require fix records");
}

#[test]
fn validate_upstream_revision_accounting_rejects_non_empty_unreviewed_ledger_after_drift() {
    let baseline = sample_baseline();
    let fixes = sample_fixes();

    let findings =
        validate_upstream_revision_accounting(&baseline, Some(&fixes), "rust-lang-rust:feedface")
            .expect_err("newer upstream revision must require reviewed-through accounting");

    assert!(findings.iter().any(|finding| {
        finding.field == "upstream_fixes.tracked_until_revision"
            && finding.message.contains("no reviewed-through revision")
    }));
}

#[test]
fn validate_upstream_revision_accounting_accepts_reviewed_ledger_after_drift() {
    let baseline = sample_baseline();
    let mut fixes = sample_fixes();
    fixes.tracked_until_revision = Some("rust-lang-rust:feedface".to_string());

    validate_upstream_revision_accounting(&baseline, Some(&fixes), "rust-lang-rust:feedface")
        .expect("ledger reviewed through current upstream revision should validate");
}

#[test]
fn validate_upstream_revision_accounting_rejects_stale_review_marker_after_drift() {
    let baseline = sample_baseline();
    let mut fixes = sample_fixes();
    fixes.tracked_until_revision = Some("rust-lang-rust:deadbeef".to_string());

    let findings =
        validate_upstream_revision_accounting(&baseline, Some(&fixes), "rust-lang-rust:feedface")
            .expect_err("stale review marker must not account for current upstream revision");

    assert!(findings.iter().any(|finding| {
        finding.field == "upstream_fixes.tracked_until_revision"
            && finding.message.contains("not current upstream revision")
    }));
}

fn sample_baseline() -> CompatibilityBaseline {
    CompatibilityBaseline {
        schema_version: SCHEMA_VERSION.to_string(),
        id: "baseline-2026-04-26".to_string(),
        upstream: UpstreamSnapshot {
            channel: "nightly".to_string(),
            revision: "rust-lang-rust:abc123".to_string(),
            snapshot_date: Some("2026-04-25".to_string()),
        },
        local: LocalSnapshot {
            revision: "trust:def456".to_string(),
            branch: Some("main".to_string()),
            workspace: None,
        },
        entries: vec![
            BaselineEntry {
                id: "diag.E0001".to_string(),
                title: "borrow checker diagnostic shape".to_string(),
                surface: CompatibilitySurface::CompilerDiagnostic,
                upstream_artifact: "tests/ui/borrowck/borrowck-move-error.rs".to_string(),
                local_artifact: Some("tests/ui/borrowck/borrowck-move-error.trust.rs".to_string()),
                expectation: CompatibilityExpectation {
                    upstream_behavior: "emits E0382 with primary move span".to_string(),
                    local_behavior: "emits E0382 with matching primary move span".to_string(),
                    compatibility_rule: "diagnostic code and primary span must match".to_string(),
                },
                status: BaselineStatus::Diverged,
                labels: vec!["diagnostics".to_string()],
            },
            BaselineEntry {
                id: "mir.drop-order".to_string(),
                title: "drop order semantics".to_string(),
                surface: CompatibilitySurface::Mir,
                upstream_artifact: "compiler/rustc_mir_transform/src/elaborate_drops.rs"
                    .to_string(),
                local_artifact: None,
                expectation: CompatibilityExpectation {
                    upstream_behavior: "drops locals in reverse declaration order".to_string(),
                    local_behavior: "matches upstream drop ordering".to_string(),
                    compatibility_rule: "observable drop order must match upstream".to_string(),
                },
                status: BaselineStatus::Compatible,
                labels: vec!["mir".to_string()],
            },
        ],
    }
}

fn sample_exceptions() -> ExceptionLedger {
    ExceptionLedger {
        schema_version: SCHEMA_VERSION.to_string(),
        exceptions: vec![CompatibilityException {
            id: "exc.diag.E0001".to_string(),
            baseline_entry_id: "diag.E0001".to_string(),
            title: "diagnostic wording drift while spans converge".to_string(),
            class: ExceptionClass::IntentionalDivergence,
            status: ExceptionStatus::Active,
            owner: "compiler-team".to_string(),
            reason: "local diagnostic wording is intentionally shorter for verifier output"
                .to_string(),
            expires_on: Some("2026-06-01".to_string()),
            upstream_reference: Some("rust-lang/rust#123456".to_string()),
            local_reference: None,
        }],
    }
}

fn sample_fixes() -> UpstreamFixLedger {
    UpstreamFixLedger {
        schema_version: SCHEMA_VERSION.to_string(),
        tracked_until_revision: None,
        fixes: vec![UpstreamFix {
            id: "fix.mir.drop-order".to_string(),
            baseline_entry_id: "mir.drop-order".to_string(),
            title: "upstream MIR drop elaboration fix".to_string(),
            upstream_reference: "rust-lang/rust#123457".to_string(),
            status: UpstreamFixStatus::Landed,
            local_action: LocalFixAction::RebaseBaseline,
            landed_on: Some("2026-04-20".to_string()),
            landed_in_revision: Some("rust-lang-rust:feedface".to_string()),
            released_in: None,
        }],
    }
}

fn sample_test_exceptions() -> TestExceptionLedger {
    TestExceptionLedger {
        schema_version: SCHEMA_VERSION.to_string(),
        exceptions: vec![TestException {
            id: "test-exc.ui.sample".to_string(),
            test_id: "upstream.00000001.tests.ui.sample.rs".to_string(),
            suite: "ui".to_string(),
            path: "tests/ui/sample.rs".to_string(),
            revision: Some("rust-lang/rust:abc123".to_string()),
            kind: TestExceptionKind::ExpectedFail,
            status: ExceptionStatus::Active,
            owner: "@trust-release".to_string(),
            reason: "sample expected failure while porting upstream Rust tests".to_string(),
            issue: "https://github.com/rust-lang/rust/issues/1".to_string(),
            introduced_by: None,
            reviewed_on: "2026-04-29".to_string(),
            expires_on: "2026-07-28".to_string(),
            allowed_patterns: vec![],
        }],
    }
}

fn sample_summary() -> CompatibilityResultSummary {
    let results = vec![
        CompatibilityResult {
            baseline_entry_id: "diag.E0001".to_string(),
            outcome: CompatibilityOutcome::Excepted,
            observed: Some("diagnostic code and span match; wording differs".to_string()),
            exception_id: Some("exc.diag.E0001".to_string()),
            upstream_fix_id: None,
        },
        CompatibilityResult {
            baseline_entry_id: "mir.drop-order".to_string(),
            outcome: CompatibilityOutcome::FixedUpstream,
            observed: Some(
                "upstream changed drop elaboration for matching local behavior".to_string(),
            ),
            exception_id: None,
            upstream_fix_id: Some("fix.mir.drop-order".to_string()),
        },
    ];

    CompatibilityResultSummary {
        schema_version: SCHEMA_VERSION.to_string(),
        baseline_id: "baseline-2026-04-26".to_string(),
        generated_on: "2026-04-26".to_string(),
        run_id: Some("ci-42".to_string()),
        repo_head: None,
        repo_dirty: None,
        upstream_revision: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        architecture: None,
        runner: None,
        totals: ResultTotals::from_results(&results),
        results,
    }
}
