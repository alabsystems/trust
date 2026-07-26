use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;
use trust_upstream_compat::porting::{PortOptions, ProofMode, run_porting};
use trust_upstream_compat::{
    ExceptionStatus, TestException, TestExceptionKind, TestExceptionLedger, TestInventory,
    TestProofTotals, TestResultReport,
};

const PORTING_FIXTURE: &str =
    include_str!("../../../tests/upstream-rust/fixtures/porting-cli-rust.seed.toml");

#[test]
fn smoke_porting_imports_fixture_files_and_records_audit_and_missing_proof() {
    let seed = porting_seed();
    assert_eq!(
        seed.get("canonical_path").and_then(toml::Value::as_str),
        Some("targo trust domination upstream-tests")
    );

    let repo = TestRepo::new("smoke-audit");
    repo.write(
        "tests/rustdoc-html/description_default.rs",
        r#"//@ has foo/index.html '//head/title' 'foo - Rust'
//   'API documentation for the Rust `foo` crate.'
pub fn unchanged_rust_word() -> &'static str { "Rust" }
"#,
    );
    repo.write(
        "tests/run-make/print-request-help-stable-unstable/unstable-invalid-print-request-help.err",
        r#"error: unknown print request: `xxx`
  = help: for more information, see the rustc book: https://doc.rust-lang.org/rustc/command-line-arguments.html#--print-print-compiler-information
"#,
    );
    let current = repo.commit_all("seed upstream test fixtures");
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let patch_manifest = repo.write(
        "tests/upstream-rust/patches.toml",
        r#"
schema_version = "0.1.0"

[[patches]]
id = "trust.test.rustdoc-title"
status = "active"
owner = "@trust-release"
reason = "fixture Trust rustdoc title branding"
issue = "https://example.invalid/trust/rustdoc-title"
reviewed_on = "2026-05-07"
expires_on = "2026-08-05"
kind = "adapter-rule"
rule = "rustdoc_title_brand"

[[patches]]
id = "trust.test.rustdoc-description"
status = "active"
owner = "@trust-release"
reason = "fixture Trust rustdoc description branding"
issue = "https://example.invalid/trust/rustdoc-description"
reviewed_on = "2026-05-07"
expires_on = "2026-08-05"
kind = "adapter-rule"
rule = "rustdoc_description_brand"

[[patches]]
id = "trust.test.print-help"
status = "active"
owner = "@trust-release"
reason = "fixture Trust print help branding"
issue = "https://example.invalid/trust/print-help"
reviewed_on = "2026-05-07"
expires_on = "2026-08-05"
kind = "adapter-rule"
rule = "print_request_docs_help"
"#,
    );

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: Some(patch_manifest),
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/smoke"),
        execute: false,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: Some(10),
        release: false,
        proof_mode: ProofMode::Auto,
    })
    .expect("porting smoke run should complete");

    assert_eq!(report.exit_code, 0, "{}", report.render_terminal(&repo.root));
    assert_eq!(report.imported_files, 2);
    assert_eq!(report.upstream_test_files, 2);
    assert_eq!(report.audit_records, 6);

    let out_dir = repo.root.join("reports/smoke");
    let ported_rustdoc =
        fs::read_to_string(out_dir.join("ported/tests/rustdoc-html/description_default.rs"))
            .expect("ported rustdoc fixture should be readable");
    assert!(ported_rustdoc.contains("'foo - Trust'"));
    assert!(ported_rustdoc.contains("API documentation for the Trust `foo` crate"));
    assert!(ported_rustdoc.contains(r#"unchanged_rust_word() -> &'static str { "Rust" }"#));

    let audit_rules = read_jsonl_rules(&out_dir.join("adapter-audit.jsonl"));
    for expected in [
        "patch_manifest:trust.test.rustdoc-title:rustdoc_title_brand",
        "patch_manifest:trust.test.rustdoc-description:rustdoc_description_brand",
        "patch_manifest:trust.test.print-help:print_request_docs_help",
        "patch_manifest:trust.test.print-help:print_request_docs_help:file_digest",
    ] {
        assert!(audit_rules.contains(expected), "missing audit rule {expected}");
    }

    let scorecard = read_json(&out_dir.join("scorecard.json"));
    assert_eq!(scorecard["imported_files"].as_u64(), Some(2));
    assert_eq!(scorecard["upstream_test_files"].as_u64(), Some(2));
    assert_eq!(scorecard["ported_audit_records"].as_u64(), Some(6));
    assert_eq!(scorecard["patch_manifest_accounting"]["applied_patch_count"].as_u64(), Some(3));
    assert_eq!(scorecard["proof_mode"].as_str(), Some("smoke"));
    assert_eq!(scorecard["proof_required_for_exit"].as_bool(), Some(false));
    assert_eq!(scorecard["proof_accounting_status"].as_str(), Some("not_run"));
    assert_eq!(scorecard["proof_artifacts_complete"].as_bool(), Some(false));
    assert_eq!(
        string_array(&scorecard["missing_proof_artifacts"]),
        vec!["inventory.json", "results.json", "proof-summary.json"]
    );
    assert_eq!(
        scorecard["upstream_fix_accounting"]["applicable_fix_tracking_claim"].as_str(),
        Some("post-baseline upstream range is empty")
    );
    assert!(
        scorecard["validation_failures"].as_array().is_some_and(Vec::is_empty),
        "same-revision fixture should not produce validation failures"
    );

    assert_eq!(
        report.compatibility_summary_path.file_name().and_then(|name| name.to_str()),
        Some("compat-summary.json")
    );
    let summary = read_json(&report.compatibility_summary_path);
    assert_eq!(summary["baseline_id"].as_str(), Some("baseline-porting-engine"));
    assert_eq!(summary["runner"]["python_used"].as_bool(), Some(false));
    assert_eq!(summary["target_arch"].as_str(), Some(std::env::consts::ARCH));
    assert_eq!(summary["totals"]["unknown"].as_u64(), Some(1));
    assert_eq!(summary["results"][0]["outcome"].as_str(), Some("unknown"));
}

#[test]
fn bounded_apply_fails_closed_before_mutating_tests() {
    let repo = TestRepo::new("bounded-apply-fails-closed");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let current = repo.commit_all("bounded upstream fixture");
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let local_path = repo.root.join("tests/ui/proof.rs");
    let before = fs::read_to_string(&local_path).expect("local test should be readable");

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/bounded-apply"),
        execute: false,
        apply: true,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: Some(1),
        release: false,
        proof_mode: ProofMode::Smoke,
    })
    .expect_err("bounded apply should fail before import/apply");

    assert!(err.to_string().contains("--max-files"));
    assert!(err.to_string().contains("apply=true"));
    let after = fs::read_to_string(&local_path).expect("local test should still be readable");
    assert_eq!(after, before);
}

#[test]
fn bounded_full_proof_fails_closed_without_importing_subset() {
    let repo = TestRepo::new("bounded-full-proof-fails-closed");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let current = repo.commit_all("bounded upstream fixture");
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/bounded-full-proof"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: Some(1),
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect_err("bounded full proof must fail before subset evidence is created");

    assert!(err.to_string().contains("--max-files"));
    assert!(err.to_string().contains("proof_mode=full"));
    assert!(!repo.root.join("reports/bounded-full-proof/scorecard.json").exists());
}

#[test]
fn expired_supplied_test_exception_ledger_fails_closed_before_importing() {
    let repo = TestRepo::new("expired-ledger-fails-closed");
    let mut test_exceptions = test_exception_ledger(
        "test-exc.expired",
        "upstream.00000000.tests.ui.proof.rs",
        "tests/ui/proof.rs",
        "rust-lang/rust:feedface",
    );
    test_exceptions.exceptions[0].reviewed_on = "1999-01-01".to_string();
    test_exceptions.exceptions[0].expires_on = "2000-01-01".to_string();

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline: PathBuf::from("missing-baseline.toml"),
        upstream_fixes: PathBuf::from("missing-upstream-fixes.toml"),
        test_exceptions: Some(test_exceptions),
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: Some("2000-01-02".to_string()),
        upstream_revision: "rust-lang/rust:feedface".to_string(),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/expired-ledger"),
        execute: false,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: Some(1),
        release: false,
        proof_mode: ProofMode::Smoke,
    })
    .expect_err("expired active per-test exceptions must fail closed before import");

    assert!(err.to_string().contains("test exception ledger failed validation"));
    assert!(err.to_string().contains("expires_on"));
    assert!(!repo.root.join("reports/expired-ledger").exists());
}

#[test]
fn supplied_validation_date_controls_test_exception_expiry() {
    let repo = TestRepo::new("validation-date-controls-ledger");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let current = repo.commit_all("validation-date upstream fixture");
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let mut test_exceptions = test_exception_ledger(
        "test-exc.date-controlled",
        "upstream.00000000.tests.ui.proof.rs",
        "tests/ui/proof.rs",
        &current,
    );
    test_exceptions.exceptions[0].reviewed_on = "1999-01-01".to_string();
    test_exceptions.exceptions[0].expires_on = "2000-01-01".to_string();

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: Some(test_exceptions),
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: Some("1999-12-31".to_string()),
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/validation-date"),
        execute: false,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: Some(1),
        release: false,
        proof_mode: ProofMode::Smoke,
    })
    .expect("explicit validation date before expiry should allow the ledger");

    assert_eq!(report.exit_code, 0, "{}", report.render_terminal(&repo.root));
}

#[test]
fn scorecard_log_mode_reports_seeded_failures_and_reviewed_drift() {
    let seed = porting_seed();
    let scorecard_fixture =
        seed.get("scorecard_log_parse").expect("seed should contain scorecard fixture");
    let expected_failed_count =
        scorecard_fixture.get("expected_failed_count").and_then(toml::Value::as_integer).unwrap()
            as u64;
    let expected_failure_path =
        scorecard_fixture.get("expected_failure_path").and_then(toml::Value::as_str).unwrap();
    let expected_failure_suite =
        scorecard_fixture.get("expected_failure_suite").and_then(toml::Value::as_str).unwrap();
    let expected_failure_category =
        scorecard_fixture.get("expected_failure_category").and_then(toml::Value::as_str).unwrap();
    let expected_snippet_start = scorecard_fixture
        .get("expected_failure_snippet_start_line")
        .and_then(toml::Value::as_integer)
        .unwrap() as u64;
    let expected_snippet =
        scorecard_fixture.get("expected_snippet_contains").and_then(toml::Value::as_str).unwrap();

    let repo = TestRepo::new("scorecard-drift");
    repo.write("tests/ui/demo.rs", "fn demo() {}\n");
    let baseline_revision = repo.commit_all("baseline upstream fixture");
    repo.write("tests/ui/new-upstream.rs", "fn new_upstream() {}\n");
    let current_revision = repo.commit_all("current upstream fixture");
    let baseline = write_baseline(&repo, &baseline_revision);
    let upstream_fixes = write_reviewed_pending_upstream_fix(&repo, &current_revision);
    let log = scorecard_fixture.get("log").and_then(toml::Value::as_str).unwrap();
    let scorecard_log = repo.write("logs/scorecard.log", log);

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current_revision),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/scorecard"),
        execute: false,
        apply: false,
        fetch: false,
        scorecard_log: Some(scorecard_log),
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Smoke,
    })
    .expect("scorecard log parse run should complete");

    assert_eq!(report.exit_code, 1, "failed fixture log should fail the scorecard");
    assert_eq!(report.failed_tests, expected_failed_count);
    assert!(report.validation_failures.is_empty());

    let scorecard = read_json(&repo.root.join("reports/scorecard/scorecard.json"));
    let failures = scorecard["failed_tests"].as_array().expect("failed_tests should be an array");
    assert_eq!(failures.len() as u64, expected_failed_count);
    let failure = &failures[0];
    assert_eq!(failure["suite"].as_str(), Some(expected_failure_suite));
    assert_eq!(failure["path"].as_str(), Some(expected_failure_path));
    assert_eq!(failure["category"].as_str(), Some(expected_failure_category));
    assert_eq!(failure["detail_available"].as_bool(), Some(true));
    assert_eq!(failure["failure_snippet"]["start_line"].as_u64(), Some(expected_snippet_start));
    assert!(
        failure["failure_snippet"]["text"]
            .as_str()
            .is_some_and(|text| text.contains(expected_snippet))
    );
    assert_eq!(failure["actual_artifacts"][0]["kind"].as_str(), Some("stderr"));
    assert_eq!(failure["actual_artifacts"][0]["path"].as_str(), Some("/tmp/build/demo.stderr"));
    assert_eq!(failure["comparisons"][0]["actual"].as_str(), Some("stderr"));
    assert_eq!(failure["comparisons"][0]["expected"].as_str(), Some("stderr"));

    let tool_kinds = scorecard["tool_failures"]
        .as_array()
        .expect("tool_failures should be an array")
        .iter()
        .filter_map(|failure| failure["kind"].as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(tool_kinds, BTreeSet::from(["cargo-compile", "tidy"]));

    assert_eq!(scorecard["upstream_revision_drift"]["drifted_from_baseline"].as_bool(), Some(true));
    assert_eq!(
        scorecard["upstream_fix_accounting"]["reviewed_through_current_revision"].as_bool(),
        Some(true)
    );
    assert_eq!(
        scorecard["upstream_fix_accounting"]["unreviewed_revision_drift"].as_bool(),
        Some(false)
    );
    assert_eq!(
        scorecard["upstream_fix_accounting"]["pending_local_actions_count"].as_u64(),
        Some(1)
    );
    assert_eq!(
        scorecard["upstream_fix_accounting"]["applicable_fix_tracking_claim"].as_str(),
        Some("ledger reviewed through current upstream revision with pending local actions")
    );
}

#[cfg(unix)]
#[test]
fn full_proof_mode_accepts_complete_local_artifacts_from_fake_bootstrap() {
    use std::os::unix::fs::PermissionsExt;

    let repo = TestRepo::new("full-proof");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let current = repo.commit_all("proof upstream fixture");
    let _fake_targo = install_fake_targo(&repo, "trust added ok", 0);
    write_trust_added_manifest(
        &repo,
        "trust.added.full-proof-command",
        "targo trust domination trust-added --release quick",
        "trust.added.full-proof",
    );
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect("full proof run should complete through fake bootstrap");

    assert_eq!(report.exit_code, 0, "{}", report.render_terminal(&repo.root));

    let scorecard = read_json(&repo.root.join("reports/proof/scorecard.json"));
    assert_eq!(scorecard["executed"].as_bool(), Some(true));
    assert_eq!(scorecard["execution_exit_status"].as_i64(), Some(0));
    assert_eq!(scorecard["execution_telemetry"]["executor"].as_str(), Some("rust-bootstrap"));
    assert_eq!(scorecard["proof_mode"].as_str(), Some("full"));
    assert_eq!(scorecard["proof_required_for_exit"].as_bool(), Some(true));
    assert_eq!(scorecard["proof_accounting_status"].as_str(), Some("complete"));
    assert_eq!(scorecard["proof_artifacts_complete"].as_bool(), Some(true));
    assert!(scorecard["missing_proof_artifacts"].as_array().is_some_and(Vec::is_empty));
    assert!(scorecard["invalid_proof_artifacts"].as_array().is_some_and(Vec::is_empty));
    assert_eq!(scorecard["proof_artifact_validation"]["summary_totals"]["total"].as_u64(), Some(2));
    assert_eq!(
        scorecard["proof_artifact_validation"]["summary_totals"]["passed"].as_u64(),
        Some(2)
    );
    let expected_driver = repo.root.join("build/bootstrap/debug/bootstrap");
    let expected_driver = expected_driver.to_string_lossy();
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains(expected_driver.as_ref()))
    );
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains("test --src"))
    );
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains("--trust-vanilla"))
    );

    let markdown = fs::read_to_string(repo.root.join("reports/proof/scorecard.md"))
        .expect("proof scorecard markdown should be readable");
    assert!(markdown.contains("## Proof Accounting"));
    assert!(markdown.contains("- proof totals: total=2 passed=2 excepted=0 unaccounted=0"));

    let bootstrap = repo.root.join("build/bootstrap/debug/bootstrap");
    let mode = fs::metadata(&bootstrap).expect("fake bootstrap should exist").permissions().mode();
    assert_ne!(mode & 0o111, 0, "fake bootstrap must be executable for the engine path");

    let execution_log = fs::read_to_string(repo.root.join("reports/proof/execution.log"))
        .expect("execution log should be readable");
    assert!(execution_log.contains("executor=rust-bootstrap"));
    assert!(execution_log.contains("build/bootstrap/debug/bootstrap"));
    assert!(execution_log.contains("--trust-vanilla"));
    assert_no_legacy_execution_path(&execution_log);

    let capture = fs::read_to_string(fake_bootstrap_capture_path(&bootstrap))
        .expect("fake bootstrap capture should be readable");
    assert!(capture.contains("argv: <test>"));
    assert!(capture.contains("TRUST_UPSTREAM_RUST_EXECUTOR=rust-bootstrap"));
    assert!(capture.contains(&format!("TRUST_UPSTREAM_RUST_CURRENT_REVISION={current}")));
    assert!(capture.contains("TRUST_STRICT=1"));
    assert!(capture.contains("TRUST_RELEASE_GATE=0"));
    assert!(capture.contains("TRUST_UPSTREAM_RUST_PROOF_DIR="));
    assert!(capture.contains("TRUST_BOOTSTRAP_NO_VERIFY=\n"));
    assert!(capture.contains("TRUST_BOOTSTRAP_SHIM_NO_VERIFY=\n"));
    assert!(capture.contains("RUSTFLAGS_BOOTSTRAP=\n"));
    assert!(capture.contains("RUSTFLAGS_NOT_BOOTSTRAP=\n"));
    assert_no_legacy_execution_path(&capture);
}

#[cfg(unix)]
#[test]
fn executed_porting_passes_host_and_target_triples_to_bootstrap() {
    let repo = TestRepo::new("full-proof-target-triple");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let current = repo.commit_all("proof upstream fixture");
    let _fake_targo = install_fake_targo(&repo, "trust added ok", 0);
    write_trust_added_manifest(
        &repo,
        "trust.added.target-triple-command",
        "targo trust domination trust-added --release quick",
        "trust.added.target-triple-proof",
    );
    let bootstrap =
        install_fake_bootstrap_command(&repo.root.join("build/bootstrap/debug/bootstrap"));
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: Some("x86-release-shape".to_string()),
        target_arch: Some("x86_64".to_string()),
        target: Some("x86_64-unknown-linux-gnu".to_string()),
        target_triple: Some("x86_64-unknown-linux-gnu".to_string()),
        host: Some("x86_64-unknown-linux-gnu".to_string()),
        host_triple: Some("x86_64-unknown-linux-gnu".to_string()),
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&current),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-target-triple"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect("full proof run should complete through fake bootstrap");

    assert_eq!(report.exit_code, 0, "{}", report.render_terminal(&repo.root));

    let capture = fs::read_to_string(fake_bootstrap_capture_path(&bootstrap))
        .expect("fake bootstrap capture should be readable");
    assert!(
        capture.contains("argv: <test> <--src>")
            && capture.contains("<--host> <x86_64-unknown-linux-gnu>")
            && capture.contains("<--target> <x86_64-unknown-linux-gnu>"),
        "bootstrap invocation should bind execution to the declared x86_64 triples\n{capture}"
    );

    let scorecard = read_json(&repo.root.join("reports/proof-target-triple/scorecard.json"));
    let driver = scorecard["trust_cargo_driver"].as_str().expect("trust_cargo_driver");
    assert!(driver.contains("--host x86_64-unknown-linux-gnu"), "{driver}");
    assert!(driver.contains("--target x86_64-unknown-linux-gnu"), "{driver}");
}

#[cfg(unix)]
#[test]
fn full_proof_uses_supplied_test_exceptions_for_failed_artifacts() {
    let repo = TestRepo::new("full-proof-test-exceptions");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    let _fake_targo = install_fake_targo(&repo, "trust added ok", 0);
    write_trust_added_manifest(
        &repo,
        "trust.added.exception-proof-command",
        "targo trust domination trust-added --release quick",
        "trust.added.exception-proof",
    );
    install_failing_fake_bootstrap(&repo.root, 1);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let test_id = "upstream.00000000.tests.ui.proof.rs";

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: Some(test_exception_ledger(
            "test-exc.proof.expected-fail",
            test_id,
            "tests/ui/proof.rs",
            &upstream,
        )),
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-test-exceptions"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect("full proof run should score a failed bootstrap with supplied exceptions");

    assert_ne!(report.exit_code, 0, "nonzero suite execution still blocks the port proof path");

    let proof_dir = repo.root.join("reports/proof-test-exceptions/proof");
    let results = read_json(&proof_dir.join("results.json"));
    let summary = read_json(&proof_dir.join("proof-summary.json"));
    let result = json_array_object_with_str(&results["results"], "test_id", test_id);
    assert_eq!(result["outcome"].as_str(), Some("failed"));
    assert_eq!(result["exception_id"].as_str(), Some("test-exc.proof.expected-fail"));
    assert_eq!(summary["excepted"].as_u64(), Some(1));
    assert_eq!(summary["unaccounted"].as_u64(), Some(0));

    let scorecard = read_json(&repo.root.join("reports/proof-test-exceptions/scorecard.json"));
    assert_eq!(scorecard["proof_artifacts_complete"].as_bool(), Some(true));
    assert!(scorecard["invalid_proof_artifacts"].as_array().is_some_and(Vec::is_empty));
    assert_eq!(
        scorecard["proof_artifact_validation"]["summary_totals"]["excepted"].as_u64(),
        Some(1)
    );
}

#[cfg(unix)]
#[test]
fn full_proof_artifacts_include_trust_added_manifest_rows() {
    let repo = TestRepo::new("full-proof-trust-added");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    repo.write("tests/ui/trust-added.rs", "fn trust_added() {}\n");
    let fake_targo = install_fake_targo(&repo, "trust added ok", 0);
    write_trust_added_manifest(
        &repo,
        "trust.added.fixture-command",
        "targo trust domination trust-added --release quick",
        "trust.added.fixture",
    );
    repo.commit_all("local trust-added fixture");
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-trust-added"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect("full proof run with trust-added manifest should complete");

    assert_eq!(report.exit_code, 0, "{}", report.render_terminal(&repo.root));
    assert!(
        fake_targo_marker_path(&fake_targo).exists(),
        "Trust-added manifest command should be executed"
    );

    let proof_dir = repo.root.join("reports/proof-trust-added/proof");
    let inventory = read_json(&proof_dir.join("inventory.json"));
    let results = read_json(&proof_dir.join("results.json"));
    let summary = read_json(&proof_dir.join("proof-summary.json"));
    assert_port_proof_artifacts_are_schema_compatible(&inventory, &results, &summary);
    assert_eq!(summary["total"].as_u64(), Some(2));
    assert_eq!(summary["upstream"].as_u64(), Some(1));
    assert_eq!(summary["trust_added"].as_u64(), Some(1));
    assert_eq!(summary["passed"].as_u64(), Some(2));
    assert_eq!(summary["unaccounted"].as_u64(), Some(0));

    let trust_added_inventory =
        json_array_object_with_str(&inventory["tests"], "id", "trust.added.fixture");
    assert_eq!(trust_added_inventory["source"].as_str(), Some("trust_added"));
    assert_eq!(
        trust_added_inventory["path"].as_str(),
        Some("tests/trust-added/manifest.toml"),
        "Trust-added inventory path should stay repository-relative: {inventory:#}"
    );
    assert!(
        !trust_added_inventory["path"]
            .as_str()
            .unwrap_or_default()
            .contains(repo.root.to_string_lossy().as_ref()),
        "Trust-added inventory path must not be an absolute command path: {inventory:#}"
    );
    let trust_added_result =
        json_array_object_with_str(&results["results"], "test_id", "trust.added.fixture");
    assert_eq!(trust_added_result["outcome"].as_str(), Some("passed"));
    assert!(
        trust_added_result["observed"]
            .as_str()
            .is_some_and(|observed| observed.contains("trust.added.fixture-command"))
    );
    assert!(
        trust_added_result["artifact"]
            .as_str()
            .is_some_and(|artifact| artifact.contains("trust-added.log"))
    );
    assert!(
        results["command"]
            .as_str()
            .is_some_and(|command| command.contains("build/bootstrap/debug/bootstrap")),
        "result report command should include the exact bootstrap command: {results:#}"
    );
    assert!(
        results["command"].as_str().is_some_and(
            |command| command.contains("targo trust domination trust-added --release quick")
        ),
        "result report command should include executed Trust-added command: {results:#}"
    );

    let trust_added_log = fs::read_to_string(proof_dir.join("trust-added.log"))
        .expect("Trust-added execution log should be readable");
    assert!(trust_added_log.contains("# manifest=tests/trust-added/manifest.toml"));
    assert!(
        trust_added_log.contains("targo trust domination trust-added --release quick"),
        "Trust-added execution should use the temp repo manifest command: {trust_added_log}"
    );
    assert!(
        !trust_added_log.contains(workspace_root().to_string_lossy().as_ref()),
        "Trust-added execution must not run commands from the real workspace manifest: {trust_added_log}"
    );

    let scorecard = read_json(&repo.root.join("reports/proof-trust-added/scorecard.json"));
    assert_eq!(scorecard["proof_artifacts_complete"].as_bool(), Some(true));
    assert_eq!(scorecard["proof_artifact_validation"]["summary_totals"]["total"].as_u64(), Some(2));
    assert_eq!(
        scorecard["proof_artifact_validation"]["summary_totals"]["trust_added"].as_u64(),
        Some(1)
    );
    assert_eq!(
        scorecard["execution_telemetry"]["trust_added_manifest_executed"].as_bool(),
        Some(true)
    );
    assert_eq!(scorecard["execution_telemetry"]["trust_added_exit_status"].as_i64(), Some(0));
}

#[cfg(unix)]
#[test]
fn full_proof_rejects_python_trust_added_manifest_command_before_launch() {
    let repo = TestRepo::new("full-proof-trust-added-python-rejected");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    repo.write("tests/ui/trust-added.rs", "fn trust_added() {}\n");
    let python_script = repo.write(
        "bin/trust-added-python.py",
        "from pathlib import Path\nPath('python-manifest-ran.marker').write_text('ran')\n",
    );
    repo.write(
        "tests/trust-added/manifest.toml",
        &format!(
            r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.python-command"
command = "python3 {}"
covers = ["trust.added.python"]
required = true
"#,
            python_script.strip_prefix(&repo.root).unwrap().to_string_lossy()
        ),
    );
    repo.commit_all("local python trust-added fixture");
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-trust-added-python-rejected"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect_err("Python Trust-added proof commands must fail closed before launch");

    assert!(err.to_string().contains("Trust-added proof manifest"));
    assert!(
        !repo.root.join("python-manifest-ran.marker").exists(),
        "rejected Python manifest command must not be launched"
    );
}

#[cfg(unix)]
#[test]
fn full_proof_rejects_shell_trust_added_manifest_command_before_launch() {
    let repo = TestRepo::new("full-proof-trust-added-shell-rejected");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    repo.write("tests/ui/trust-added.rs", "fn trust_added() {}\n");
    repo.write(
        "tests/trust-added/manifest.toml",
        r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.shell-command"
command = "bash tests/run_trust_superset_suite.sh quick"
covers = ["trust.added.shell"]
required = true
"#,
    );
    repo.commit_all("local shell trust-added fixture");
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-trust-added-shell-rejected"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect_err("shell Trust-added proof commands must fail closed before launch");

    assert!(err.to_string().contains("Trust-added proof manifest"));
}

#[cfg(unix)]
#[test]
fn full_proof_rejects_shebang_trust_added_manifest_command_before_launch() {
    use std::os::unix::fs::PermissionsExt;

    let repo = TestRepo::new("full-proof-trust-added-shebang-rejected");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    repo.write("tests/ui/trust-added.rs", "fn trust_added() {}\n");
    let script = repo
        .write("bin/trust-added-script", "#!/bin/sh\nprintf ran > shebang-manifest-ran.marker\n");
    let mut permissions = fs::metadata(&script).expect("script metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&script, permissions).expect("script should be executable");
    write_trust_added_manifest(
        &repo,
        "trust.added.shebang-command",
        script.to_str().expect("script path should be UTF-8"),
        "trust.added.shebang",
    );
    repo.commit_all("local shebang trust-added fixture");
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let err = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-trust-added-shebang-rejected"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect_err("script Trust-added proof commands must fail closed before launch");

    assert!(err.to_string().contains("Trust-added proof manifest"));
    assert!(
        !repo.root.join("shebang-manifest-ran.marker").exists(),
        "rejected shebang manifest command must not be launched"
    );
}

#[cfg(unix)]
#[test]
fn full_proof_fails_closed_when_trust_added_manifest_command_fails() {
    let repo = TestRepo::new("full-proof-trust-added-fail");
    repo.write("tests/ui/proof.rs", "fn proof() {}\n");
    let upstream = repo.commit_all("upstream proof fixture");
    repo.write("tests/ui/trust-added.rs", "fn trust_added() {}\n");
    let fake_targo = install_fake_targo(&repo, "trust added failed", 42);
    write_trust_added_manifest(
        &repo,
        "trust.added.fixture-command",
        "targo trust domination trust-added --release quick",
        "trust.added.fixture",
    );
    repo.commit_all("local failing trust-added fixture");
    install_fake_bootstrap(&repo.root);
    let baseline = write_baseline(&repo, &upstream);
    let upstream_fixes = write_empty_upstream_fixes(&repo);

    let report = run_porting(PortOptions {
        repo_root: repo.root.clone(),
        baseline,
        upstream_fixes,
        test_exceptions: None,
        patch_manifest: None,
        llm_directives: None,
        summary_out: None,
        run_id: None,
        target_arch: None,
        target: None,
        target_triple: None,
        host: None,
        host_triple: None,
        test_exception_validation_date: None,
        upstream_revision: qualified_revision(&upstream),
        upstream_remote: "missing-upstream.invalid".to_string(),
        out_dir: PathBuf::from("reports/proof-trust-added-fail"),
        execute: true,
        apply: false,
        fetch: false,
        scorecard_log: None,
        bootstrap_args: String::new(),
        max_files: None,
        release: false,
        proof_mode: ProofMode::Full,
    })
    .expect("full proof run should score a trust-added command failure");

    assert!(
        fake_targo_marker_path(&fake_targo).exists(),
        "failing Trust-added manifest command should still be attempted"
    );
    assert_ne!(
        report.exit_code,
        0,
        "Trust-added command failure must fail closed\n{}",
        report.render_terminal(&repo.root)
    );

    let proof_dir = repo.root.join("reports/proof-trust-added-fail/proof");
    let results = read_json(&proof_dir.join("results.json"));
    let summary = read_json(&proof_dir.join("proof-summary.json"));
    assert_eq!(summary["total"].as_u64(), Some(2));
    assert_eq!(summary["upstream"].as_u64(), Some(1));
    assert_eq!(summary["trust_added"].as_u64(), Some(1));
    assert_eq!(summary["passed"].as_u64(), Some(1));
    assert_eq!(summary["unaccounted"].as_u64(), Some(1));
    let trust_added_result =
        json_array_object_with_str(&results["results"], "test_id", "trust.added.fixture");
    assert_eq!(trust_added_result["outcome"].as_str(), Some("failed"));

    let scorecard = read_json(&repo.root.join("reports/proof-trust-added-fail/scorecard.json"));
    assert_eq!(scorecard["proof_required_for_exit"].as_bool(), Some(true));
    assert_eq!(scorecard["execution_telemetry"]["trust_added_exit_status"].as_i64(), Some(42));
    assert!(string_array(&scorecard["invalid_proof_artifacts"]).contains(&"proof-summary.json"));
    assert!(
        scorecard["execution_exit_status"].as_i64().is_some_and(|status| status != 0)
            || !scorecard["validation_failures"].as_array().is_some_and(Vec::is_empty)
            || !scorecard["proof_artifacts_complete"].as_bool().unwrap_or(false),
        "scorecard must record a blocking Trust-added command failure: {scorecard:#}"
    );
}

#[cfg(unix)]
#[test]
fn port_cli_execute_uses_configured_fake_bootstrap_without_legacy_shell_path() {
    let repo = TestRepo::new("port-cli-proof");
    let workspace_root = workspace_root();
    let current =
        run_git(&workspace_root, ["rev-parse", "--verify", "HEAD^{commit}"]).trim().to_string();
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let patch_manifest = write_empty_patch_manifest(&repo);
    let fake_bootstrap = install_fake_bootstrap_command(&repo.root.join("bin/bootstrap"));
    let out_dir = repo.root.join("reports/cli-proof");
    let requested_revision = qualified_revision(&current);

    let output = Command::new(trust_upstream_compat_bin())
        .args([
            "port",
            "--baseline",
            baseline.to_str().expect("baseline path should be UTF-8"),
            "--upstream-fixes",
            upstream_fixes.to_str().expect("upstream fixes path should be UTF-8"),
            "--patch-manifest",
            patch_manifest.to_str().expect("patch manifest path should be UTF-8"),
            "--upstream-revision",
            requested_revision.as_str(),
            "--upstream-remote",
            "missing-upstream.invalid",
            "--out-dir",
            out_dir.to_str().expect("out dir path should be UTF-8"),
            "--execute",
            "--no-apply",
            "--no-fetch",
            "--max-files",
            "1",
            "--proof-mode",
            "smoke",
        ])
        .env("TRUST_UPSTREAM_RUST_BOOTSTRAP", &fake_bootstrap)
        .env_remove("TRUST_UPSTREAM_COMPAT_CARGO")
        .env_remove("TRUST_TARGO_BIN")
        .current_dir(&workspace_root)
        .output()
        .expect("trust-upstream-compat port should be runnable");

    assert!(
        output.status.success(),
        "port CLI failed: status={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let scorecard = read_json(&out_dir.join("scorecard.json"));
    assert_eq!(scorecard["executed"].as_bool(), Some(true));
    assert_eq!(scorecard["execution_exit_status"].as_i64(), Some(0));
    assert_eq!(scorecard["proof_mode"].as_str(), Some("smoke"));
    assert_eq!(scorecard["proof_required_for_exit"].as_bool(), Some(false));
    assert_eq!(scorecard["proof_accounting_status"].as_str(), Some("complete"));
    assert_eq!(scorecard["proof_artifacts_complete"].as_bool(), Some(true));
    assert_eq!(scorecard["proof_artifact_validation"]["summary_totals"]["total"].as_u64(), Some(1));
    let fake_bootstrap_display = fake_bootstrap.to_string_lossy();
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains(fake_bootstrap_display.as_ref()))
    );
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains("test --src"))
    );
    assert!(
        scorecard["trust_cargo_driver"]
            .as_str()
            .is_some_and(|driver| driver.contains("--trust-vanilla"))
    );
    assert_eq!(
        scorecard["requested_upstream_revision"].as_str(),
        Some(requested_revision.as_str())
    );
    assert_eq!(scorecard["resolved_upstream_revision"].as_str(), Some(current.as_str()));

    let execution_log = fs::read_to_string(out_dir.join("execution.log"))
        .expect("execution log should be readable");
    assert!(execution_log.contains("executor=rust-bootstrap"));
    assert!(execution_log.contains("--trust-vanilla"));
    assert_no_legacy_execution_path(&execution_log);

    let capture = fs::read_to_string(fake_bootstrap_capture_path(&fake_bootstrap))
        .expect("capture should exist");
    assert!(capture.contains("argv: <test>"));
    assert!(capture.contains("TRUST_UPSTREAM_RUST_EXECUTOR=rust-bootstrap"));
    assert!(capture.contains(&format!("TRUST_UPSTREAM_RUST_CURRENT_REVISION={current}")));
    assert!(capture.contains("TRUST_STRICT=1"));
    assert!(capture.contains("TRUST_RELEASE_GATE=0"));
    assert!(capture.contains("TRUST_UPSTREAM_RUST_PROOF_DIR="));
    assert!(capture.contains("TRUST_BOOTSTRAP_NO_VERIFY=\n"));
    assert!(capture.contains("TRUST_BOOTSTRAP_SHIM_NO_VERIFY=\n"));
    assert!(capture.contains("RUSTFLAGS_BOOTSTRAP=\n"));
    assert!(capture.contains("RUSTFLAGS_NOT_BOOTSTRAP=\n"));
    assert_no_legacy_execution_path(&capture);
}

#[test]
fn port_cli_summary_out_preserves_x86_64_and_aarch64_provenance_fail_closed() {
    struct SummaryCase {
        name: &'static str,
        run_id: &'static str,
        target_arch: &'static str,
        target: &'static str,
        target_triple: &'static str,
        host: &'static str,
        host_triple: &'static str,
        equals_form: bool,
    }

    let cases = [
        SummaryCase {
            name: "x86_64",
            run_id: "compat-x86_64-release-evidence",
            target_arch: "x86_64",
            target: "x86_64-unknown-linux-gnu",
            target_triple: "x86_64-unknown-linux-gnu",
            host: "x86_64-apple-darwin",
            host_triple: "x86_64-apple-darwin",
            equals_form: false,
        },
        SummaryCase {
            name: "aarch64",
            run_id: "compat-aarch64-release-evidence",
            target_arch: "aarch64",
            target: "aarch64-apple-darwin",
            target_triple: "aarch64-apple-darwin",
            host: "aarch64-apple-darwin",
            host_triple: "aarch64-apple-darwin",
            equals_form: true,
        },
    ];

    let repo = TestRepo::new("port-cli-summary-out-architectures");
    let workspace_root = workspace_root();
    let current =
        run_git(&workspace_root, ["rev-parse", "--verify", "HEAD^{commit}"]).trim().to_string();
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let patch_manifest = write_empty_patch_manifest(&repo);
    let requested_revision = qualified_revision(&current);

    for case in cases {
        let out_dir = repo.root.join(format!("reports/{}", case.name));
        let summary_out = repo.root.join(format!("summaries/{}-compat-summary.json", case.name));
        let mut args = vec!["port".to_string()];
        {
            let mut push_value = |flag: &str, value: String| {
                if case.equals_form {
                    args.push(format!("{flag}={value}"));
                } else {
                    args.push(flag.to_string());
                    args.push(value);
                }
            };
            push_value("--baseline", baseline.to_string_lossy().into_owned());
            push_value("--upstream-fixes", upstream_fixes.to_string_lossy().into_owned());
            push_value("--patch-manifest", patch_manifest.to_string_lossy().into_owned());
            push_value("--summary-out", summary_out.to_string_lossy().into_owned());
            push_value("--run-id", case.run_id.to_string());
            push_value("--target-arch", case.target_arch.to_string());
            push_value("--target", case.target.to_string());
            push_value("--target-triple", case.target_triple.to_string());
            push_value("--host", case.host.to_string());
            push_value("--host-triple", case.host_triple.to_string());
            push_value("--upstream-revision", requested_revision.clone());
            push_value("--upstream-remote", "missing-upstream.invalid".to_string());
            push_value("--out-dir", out_dir.to_string_lossy().into_owned());
            push_value("--max-files", "1".to_string());
            push_value("--proof-mode", "smoke".to_string());
        }
        args.extend(["--no-execute", "--no-apply", "--no-fetch"].into_iter().map(str::to_string));

        let output = Command::new(trust_upstream_compat_bin())
            .args(&args)
            .env_remove("TRUST_UPSTREAM_COMPAT_CARGO")
            .env_remove("TRUST_TARGO_BIN")
            .current_dir(&workspace_root)
            .output()
            .unwrap_or_else(|error| {
                panic!("trust-upstream-compat port should be runnable for {}: {error}", case.name)
            });

        assert!(
            output.status.success(),
            "{} summary port CLI failed: status={:?}\nstdout:\n{}\nstderr:\n{}",
            case.name,
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(summary_out.exists(), "{} summary-out path was not written", case.name);
        assert!(
            !out_dir.join("compat-summary.json").exists(),
            "{} run should honor --summary-out instead of writing the default summary path",
            case.name
        );

        let summary = read_json(&summary_out);
        assert_eq!(summary["baseline_id"].as_str(), Some("baseline-porting-engine"));
        assert_eq!(summary["run_id"].as_str(), Some(case.run_id));
        assert_eq!(summary["target_arch"].as_str(), Some(case.target_arch));
        assert_eq!(summary["target"].as_str(), Some(case.target));
        assert_eq!(summary["target_triple"].as_str(), Some(case.target_triple));
        assert_eq!(summary["host"].as_str(), Some(case.host));
        assert_eq!(summary["host_triple"].as_str(), Some(case.host_triple));
        assert_eq!(summary["architecture"].as_str(), Some(case.target_arch));
        let expected_upstream_revision = format!("missing-upstream.invalid:{current}");
        assert_eq!(
            summary["upstream_revision"].as_str(),
            Some(expected_upstream_revision.as_str())
        );
        assert_eq!(summary["runner"]["python_used"].as_bool(), Some(false));
        assert_eq!(summary["runner"]["implementation"].as_str(), Some("rust"));
        assert_eq!(
            summary["runner"]["entrypoint"].as_str(),
            Some("targo trust domination upstream-tests")
        );
        assert_eq!(summary["runner"]["command"].as_str(), Some("trust-upstream-compat port"));
        assert_eq!(summary["runner"]["run_id"].as_str(), Some(case.run_id));
        assert_eq!(summary["runner"]["target_arch"].as_str(), Some(case.target_arch));
        assert_eq!(summary["runner"]["target"].as_str(), Some(case.target));
        assert_eq!(summary["runner"]["target_triple"].as_str(), Some(case.target_triple));
        assert_eq!(summary["runner"]["host"].as_str(), Some(case.host));
        assert_eq!(summary["runner"]["host_triple"].as_str(), Some(case.host_triple));
        assert_eq!(summary["runner"]["execute"].as_bool(), Some(false));
        assert_eq!(summary["runner"]["release"].as_bool(), Some(false));
        assert_eq!(summary["runner"]["proof_mode"].as_str(), Some("smoke"));
        assert_eq!(summary["runner"]["proof_mode_requested"].as_str(), Some("smoke"));
        assert_eq!(summary["runner"]["proof_mode_resolved"].as_str(), Some("smoke"));
        let expected_summary_out = summary_out.to_string_lossy().replace('\\', "/");
        let expected_out_dir = out_dir.to_string_lossy().replace('\\', "/");
        assert_eq!(summary["runner"]["summary_out"].as_str(), Some(expected_summary_out.as_str()));
        assert_eq!(summary["runner"]["out_dir"].as_str(), Some(expected_out_dir.as_str()));
        let argv = string_array(&summary["runner"]["argv"]);
        assert_eq!(
            argv.iter().take(4).copied().collect::<Vec<_>>(),
            vec!["targo", "trust", "domination", "upstream-tests"]
        );
        assert!(!argv.contains(&"--release"));
        assert!(argv.contains(&"--no-execute"));
        assert_eq!(flag_value(&argv, "--proof-mode"), Some("smoke"));
        assert_eq!(flag_value(&argv, "--summary-out"), Some(expected_summary_out.as_str()));
        assert_eq!(flag_value(&argv, "--out-dir"), Some(expected_out_dir.as_str()));
        assert_eq!(flag_value(&argv, "--run-id"), Some(case.run_id));
        assert_eq!(flag_value(&argv, "--target-arch"), Some(case.target_arch));
        assert_eq!(flag_value(&argv, "--target-triple"), Some(case.target_triple));
        assert_eq!(
            summary["runner"]["release_evidence_contract"]["satisfied"].as_bool(),
            Some(false)
        );
        assert_eq!(
            summary["runner"]["release_evidence_contract"]["requires_proof_mode"].as_str(),
            Some("full")
        );
        assert_eq!(summary["totals"]["total"].as_u64(), Some(1));
        assert_eq!(summary["totals"]["compatible"].as_u64(), Some(0));
        assert_eq!(summary["totals"]["unknown"].as_u64(), Some(1));
        assert_eq!(summary["results"][0]["outcome"].as_str(), Some("unknown"));
        let observed = summary["results"][0]["observed"]
            .as_str()
            .expect("fail-closed summary should explain the observed status");
        assert!(observed.contains("not release-clean"), "{observed}");
        assert!(observed.contains("execute=false"), "{observed}");
        assert!(observed.contains("release=false"), "{observed}");
    }
}

#[test]
fn port_cli_rejects_expired_test_exception_ledger_before_porting() {
    let repo = TestRepo::new("port-cli-expired-test-exception");
    let test_exceptions = repo.write(
        "test-exceptions.toml",
        r#"
schema_version = "0.1.0"

[[exceptions]]
id = "test-exc.expired"
test_id = "upstream.ui.expired"
suite = "ui"
path = "tests/ui/expired.rs"
revision = "rust-lang/rust:feedface"
kind = "expected_fail"
status = "active"
owner = "@trust-release"
reason = "fixture expired active exception"
issue = "https://example.invalid/trust/expired"
reviewed_on = "2026-04-01"
expires_on = "2026-04-29"
allowed_patterns = ["fixture"]
"#,
    );
    let workspace_root = workspace_root();

    let output = Command::new(trust_upstream_compat_bin())
        .args([
            "port",
            "--test-exceptions",
            test_exceptions.to_str().expect("test exception path should be UTF-8"),
            "--no-execute",
            "--no-apply",
            "--no-fetch",
            "--max-files",
            "1",
        ])
        .env("TRUST_UPSTREAM_COMPAT_VALIDATION_DATE", "2026-04-29")
        .current_dir(&workspace_root)
        .output()
        .expect("trust-upstream-compat port should be runnable");

    assert!(!output.status.success(), "expired active exception should fail closed");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("test exceptions"), "{stderr}");
    assert!(stderr.contains("validation date '2026-04-29'"), "{stderr}");
}

#[cfg(unix)]
#[test]
fn port_cli_rejects_python_bootstrap_launcher_before_launch() {
    let repo = TestRepo::new("port-cli-python-bootstrap");
    let workspace_root = workspace_root();
    let current =
        run_git(&workspace_root, ["rev-parse", "--verify", "HEAD^{commit}"]).trim().to_string();
    let baseline = write_baseline(&repo, &current);
    let upstream_fixes = write_empty_upstream_fixes(&repo);
    let patch_manifest = write_empty_patch_manifest(&repo);
    let out_dir = repo.root.join("reports/python-bootstrap");
    let requested_revision = qualified_revision(&current);

    let output = Command::new(trust_upstream_compat_bin())
        .args([
            "port",
            "--baseline",
            baseline.to_str().expect("baseline path should be UTF-8"),
            "--upstream-fixes",
            upstream_fixes.to_str().expect("upstream fixes path should be UTF-8"),
            "--patch-manifest",
            patch_manifest.to_str().expect("patch manifest path should be UTF-8"),
            "--upstream-revision",
            requested_revision.as_str(),
            "--upstream-remote",
            "missing-upstream.invalid",
            "--out-dir",
            out_dir.to_str().expect("out dir path should be UTF-8"),
            "--execute",
            "--no-apply",
            "--no-fetch",
            "--max-files",
            "1",
            "--proof-mode",
            "smoke",
        ])
        .env("TRUST_UPSTREAM_RUST_BOOTSTRAP", "python x.py")
        .env_remove("TRUST_UPSTREAM_COMPAT_CARGO")
        .env_remove("TRUST_TARGO_BIN")
        .current_dir(&workspace_root)
        .output()
        .expect("trust-upstream-compat port should be runnable");

    assert!(!output.status.success(), "Python bootstrap launcher should fail closed");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("TRUST_UPSTREAM_RUST_BOOTSTRAP must name the Rust bootstrap binary"),
        "{stderr}"
    );
    assert!(!fake_bootstrap_capture_path(&repo.root.join("python")).exists());
}

fn porting_seed() -> toml::Value {
    toml::from_str(PORTING_FIXTURE).expect("porting seed fixture should parse as TOML")
}

fn qualified_revision(revision: &str) -> String {
    format!("rust-lang/rust:{revision}")
}

fn write_baseline(repo: &TestRepo, upstream_revision: &str) -> PathBuf {
    repo.write(
        "accounting/baseline.toml",
        &format!(
            r#"
schema_version = "0.1.0"
id = "baseline-porting-engine"

[upstream]
channel = "nightly"
revision = "{}"
snapshot_date = "2026-04-28"

[local]
revision = "trust:test"
branch = "main"

[[entries]]
id = "fixture.porting"
title = "porting fixture"
surface = "compiler_diagnostic"
upstream_artifact = "tests/ui/demo.rs"
local_artifact = "tests/ui/demo.rs"
status = "compatible"
labels = ["porting"]

[entries.expectation]
upstream_behavior = "upstream fixture is importable"
local_behavior = "ported fixture remains accounted"
compatibility_rule = "fixture import must be tracked in scorecard"
"#,
            qualified_revision(upstream_revision)
        ),
    )
}

fn write_empty_upstream_fixes(repo: &TestRepo) -> PathBuf {
    repo.write(
        "accounting/upstream-fixes.toml",
        r#"
schema_version = "0.1.0"
fixes = []
"#,
    )
}

fn write_empty_patch_manifest(repo: &TestRepo) -> PathBuf {
    repo.write(
        "accounting/patches.toml",
        r#"
schema_version = "0.1.0"
patches = []
"#,
    )
}

fn write_reviewed_pending_upstream_fix(repo: &TestRepo, current_revision: &str) -> PathBuf {
    repo.write(
        "accounting/upstream-fixes.toml",
        &format!(
            r#"
schema_version = "0.1.0"
tracked_until_revision = "{}"

[[fixes]]
id = "fix.compiletest.directive"
baseline_entry_id = "fixture.porting"
title = "compiletest directive drift"
upstream_reference = "https://github.com/rust-lang/rust/commit/{current_revision}"
status = "landed"
local_action = "port_fix"
landed_in_revision = "{}"
"#,
            qualified_revision(current_revision),
            qualified_revision(current_revision)
        ),
    )
}

#[cfg(unix)]
fn install_fake_bootstrap(root: &Path) {
    let bootstrap = root.join("build/bootstrap/debug/bootstrap");
    install_fake_bootstrap_command(&bootstrap);
}

#[cfg(unix)]
fn install_failing_fake_bootstrap(root: &Path, exit_code: i32) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;

    let bootstrap = root.join("build/bootstrap/debug/bootstrap");
    if let Some(parent) = bootstrap.parent() {
        fs::create_dir_all(parent).expect("fake bootstrap parent should be creatable");
    }
    fs::write(
        &bootstrap,
        format!(
            r#"#!/bin/sh
set -eu
printf '[ui] tests/ui/proof.rs ... ok\n'
exit {exit_code}
"#
        ),
    )
    .expect("failing fake bootstrap should be writable");
    let mut permissions =
        fs::metadata(&bootstrap).expect("failing fake bootstrap metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&bootstrap, permissions)
        .expect("failing fake bootstrap permissions should be set");
    bootstrap
}

#[cfg(unix)]
fn install_fake_bootstrap_command(bootstrap: &Path) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;

    if let Some(parent) = bootstrap.parent() {
        fs::create_dir_all(parent).expect("fake bootstrap parent should be creatable");
    }
    fs::write(
        bootstrap,
        r#"#!/bin/sh
set -eu
capture="$0.capture"
{
  printf 'argv:'
  for arg in "$@"; do
    printf ' <%s>' "$arg"
  done
  printf '\n'
  printf 'TRUST_UPSTREAM_RUST_EXECUTOR=%s\n' "${TRUST_UPSTREAM_RUST_EXECUTOR:-}"
  printf 'TRUST_UPSTREAM_RUST_CURRENT_REVISION=%s\n' "${TRUST_UPSTREAM_RUST_CURRENT_REVISION:-}"
  printf 'TRUST_STRICT=%s\n' "${TRUST_STRICT:-}"
  printf 'TRUST_RELEASE_GATE=%s\n' "${TRUST_RELEASE_GATE:-}"
  printf 'TRUST_UPSTREAM_RUST_PROOF_DIR=%s\n' "${TRUST_UPSTREAM_RUST_PROOF_DIR:-}"
  printf 'TRUST_BOOTSTRAP_NO_VERIFY=%s\n' "${TRUST_BOOTSTRAP_NO_VERIFY:-}"
  printf 'TRUST_BOOTSTRAP_SHIM_NO_VERIFY=%s\n' "${TRUST_BOOTSTRAP_SHIM_NO_VERIFY:-}"
  printf 'RUSTFLAGS_BOOTSTRAP=%s\n' "${RUSTFLAGS_BOOTSTRAP:-}"
  printf 'RUSTFLAGS_NOT_BOOTSTRAP=%s\n' "${RUSTFLAGS_NOT_BOOTSTRAP:-}"
} > "$capture"
case " $* " in
  *"x.py"*|*"run_trust_superset_suite.sh"*|*"python"*)
    echo "legacy upstream Rust execution path must not be invoked" >&2
    exit 97
    ;;
esac
printed=0
for arg in "$@"; do
  case "$arg" in
    tests/*)
      printf '[ui] %s ... ok\n' "$arg"
      printed=1
      ;;
  esac
done
if [ "$printed" = "0" ]; then
  printf '[ui] tests/ui/proof.rs ... ok\n'
fi
"#,
    )
    .expect("fake bootstrap should be writable");
    let mut permissions = fs::metadata(bootstrap).expect("fake bootstrap metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(bootstrap, permissions).expect("fake bootstrap permissions should be set");
    bootstrap.to_path_buf()
}

fn test_exception_ledger(
    exception_id: &str,
    test_id: &str,
    path: &str,
    revision: &str,
) -> TestExceptionLedger {
    TestExceptionLedger {
        schema_version: "0.1.0".to_string(),
        exceptions: vec![TestException {
            id: exception_id.to_string(),
            test_id: test_id.to_string(),
            suite: "ui".to_string(),
            path: path.to_string(),
            revision: Some(revision.to_string()),
            kind: TestExceptionKind::ExpectedFail,
            status: ExceptionStatus::Active,
            owner: "@trust-release".to_string(),
            reason: "fixture expected failure".to_string(),
            issue: "https://example.invalid/trust/1".to_string(),
            introduced_by: None,
            reviewed_on: "2026-04-29".to_string(),
            expires_on: "2026-07-28".to_string(),
            allowed_patterns: Vec::new(),
        }],
    }
}

#[cfg(unix)]
fn fake_bootstrap_capture_path(bootstrap: &Path) -> PathBuf {
    let file_name = bootstrap.file_name().expect("fake bootstrap should have a filename");
    bootstrap.with_file_name(format!("{}.capture", file_name.to_string_lossy()))
}

#[cfg(unix)]
fn install_fake_targo(repo: &TestRepo, message: &str, exit_code: i32) -> PathBuf {
    let command = repo.root.join("build/host/stage2/bin/targo");
    if let Some(parent) = command.parent() {
        fs::create_dir_all(parent).expect("Trust-added command parent should be creatable");
    }
    let source = command.with_extension("rs");
    fs::write(
        &source,
        format!(
            r#"
fn main() {{
    let program = std::env::args().next().expect("program path");
    std::fs::write(format!("{{program}}.marker"), {:?}).expect("write marker");
    std::process::exit({exit_code});
}}
"#,
            format!("{message}\n")
        ),
    )
    .expect("Trust-added native command source should be writable");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let status = Command::new(rustc)
        .args([
            "--edition=2021",
            source.to_str().expect("native command source path should be UTF-8"),
            "-o",
            command.to_str().expect("native command output path should be UTF-8"),
        ])
        .status()
        .expect("rustc should compile native Trust-added fixture command");
    assert!(status.success(), "rustc should compile native Trust-added fixture command");
    command
}

#[cfg(unix)]
fn write_trust_added_manifest(
    repo: &TestRepo,
    command_id: &str,
    command: &str,
    covered_test_id: &str,
) -> PathBuf {
    repo.write(
        "tests/trust-added/manifest.toml",
        &format!(
            r#"
schema_version = "0.1.0"

[[commands]]
id = "{command_id}"
command = "{command}"
covers = ["{covered_test_id}"]
required = true
"#,
        ),
    )
}

#[cfg(unix)]
fn fake_targo_marker_path(command: &Path) -> PathBuf {
    command.with_file_name(format!(
        "{}.marker",
        command.file_name().expect("command should have a filename").to_string_lossy()
    ))
}

fn read_json(path: &Path) -> Value {
    let text = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    serde_json::from_str(&text)
        .unwrap_or_else(|error| panic!("failed to parse {} as JSON: {error}", path.display()))
}

fn json_array_object_with_str<'a>(array: &'a Value, field: &str, value: &str) -> &'a Value {
    array
        .as_array()
        .expect("value should be an array")
        .iter()
        .find(|row| row.get(field).and_then(Value::as_str) == Some(value))
        .unwrap_or_else(|| panic!("missing JSON row with {field}={value} in {array:#}"))
}

fn assert_port_proof_artifacts_are_schema_compatible(
    inventory: &Value,
    results: &Value,
    summary: &Value,
) {
    for (name, artifact) in
        [("inventory.json", inventory), ("results.json", results), ("proof-summary.json", summary)]
    {
        assert!(
            artifact.as_object().is_some(),
            "{name} should remain a typed-schema-compatible JSON object"
        );
    }

    let typed_inventory = serde_json::from_value::<TestInventory>(inventory.clone())
        .expect("inventory should deserialize through the existing typed schema");
    let typed_results = serde_json::from_value::<TestResultReport>(results.clone())
        .expect("results should deserialize through the existing typed schema");
    let totals = serde_json::from_value::<TestProofTotals>(summary.clone())
        .expect("proof-summary totals should deserialize through the existing typed schema");
    assert_eq!(totals.total, typed_inventory.tests.len() as u64);
    assert_eq!(totals.total, typed_results.results.len() as u64);
}

fn read_jsonl_rules(path: &Path) -> BTreeSet<String> {
    fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).expect("audit row should be JSON"))
        .filter_map(|row| row["rule"].as_str().map(str::to_string))
        .collect()
}

fn string_array(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .expect("value should be an array")
        .iter()
        .map(|value| value.as_str().expect("array item should be a string"))
        .collect()
}

fn flag_value<'a>(argv: &'a [&str], flag: &str) -> Option<&'a str> {
    argv.windows(2).find_map(|window| (window[0] == flag).then_some(window[1]))
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("workspace root should be canonicalizable")
}

fn trust_upstream_compat_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-upstream-compat"))
}

fn assert_no_legacy_execution_path(text: &str) {
    let lower = text.to_ascii_lowercase();
    for forbidden in ["x.py", "run_trust_superset_suite.sh", "python"] {
        assert!(
            !lower.contains(forbidden),
            "legacy upstream Rust execution path marker `{forbidden}` found in:\n{text}"
        );
    }
}

struct TestRepo {
    root: PathBuf,
}

impl TestRepo {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after UNIX_EPOCH")
            .as_nanos();
        let root = std::env::temp_dir()
            .join(format!("trust-upstream-compat-{name}-{}-{nanos}-{id}", std::process::id()));
        fs::create_dir_all(&root).expect("temporary repo root should be creatable");
        run_git(&root, ["init", "-q"]);
        run_git(&root, ["config", "user.email", "trust-upstream-compat@example.invalid"]);
        run_git(&root, ["config", "user.name", "trust-upstream-compat tests"]);
        run_git(&root, ["config", "commit.gpgsign", "false"]);
        Self { root }
    }

    fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("parent directory should be creatable");
        }
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("failed to write {}: {error}", path.display()));
        path
    }

    fn commit_all(&self, message: &str) -> String {
        run_git(&self.root, ["add", "."]);
        run_git(&self.root, ["commit", "-q", "--no-gpg-sign", "-m", message]);
        run_git(&self.root, ["rev-parse", "--verify", "HEAD^{commit}"]).trim().to_string()
    }
}

impl Drop for TestRepo {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn run_git<const N: usize>(root: &Path, args: [&str; N]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .unwrap_or_else(|error| panic!("failed to run git in {}: {error}", root.display()));
    assert!(
        output.status.success(),
        "git command failed in {}: status={:?}\nstdout:\n{}\nstderr:\n{}",
        root.display(),
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("git stdout should be UTF-8")
}
