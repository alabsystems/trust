use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde_json::Value;

#[path = "support/publication_transport.rs"]
mod publication_transport;

#[test]
fn program_index_help_is_rust_owned() {
    let benchmark_output = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "--help"])
        .output()
        .expect("run benchmark help");
    let benchmark_stdout = String::from_utf8_lossy(&benchmark_output.stdout);
    let benchmark_stderr = String::from_utf8_lossy(&benchmark_output.stderr);
    assert_eq!(
        benchmark_output.status.code(),
        Some(0),
        "benchmark help should succeed\nstdout:\n{benchmark_stdout}\nstderr:\n{benchmark_stderr}"
    );
    assert!(benchmark_stdout.contains("program-index"));
    assert!(!benchmark_stdout.contains("program_index"));
    assert!(!benchmark_stdout.contains("programindex"));

    let output = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "program-index", "--help"])
        .output()
        .expect("run program-index help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust benchmark program-index"));
    assert!(stdout.contains("--compile-measurement cold-artifact|warm-incremental"));
    assert!(stdout.contains("--build-profile debug|release"));
    assert!(stdout.contains("--repetitions N"));
    assert!(stdout.contains("--trust-cg-mode report|enforce"));
    assert!(!stdout.contains("--trust_cg-mode"));
    assert!(stdout.contains("Python is not used"));
}

#[test]
fn program_index_rejects_zero_repetitions() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "program-index", "--repetitions", "0"])
        .output()
        .expect("run zero repetitions benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "zero repetitions should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--repetitions must be at least 1"),
        "stderr should explain the rejected repetition count\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
#[cfg(unix)]
fn program_index_rejects_deprecated_benchmark_command_aliases() {
    for deprecated in ["program_index", "programindex"] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "benchmark", deprecated, "--help"])
            .output()
            .expect("run deprecated command alias");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{deprecated} should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(&format!("unknown command `{deprecated}`")),
            "{deprecated} should be reported as unknown\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains("program-index"));
        assert!(!stderr.contains("program_index   Alias"));
    }
}

#[test]
#[cfg(unix)]
fn program_index_rejects_deprecated_trust_cg_cli_spellings() {
    let cases = [
        (vec!["--trust_cg-mode", "report"], "--trust_cg-mode"),
        (vec!["--trust_cg-mode=report"], "--trust_cg-mode"),
        (vec!["--slots", "trust_cg"], "deprecated slot spelling `trust_cg`"),
        (vec!["--slots=trust_cg"], "deprecated slot spelling `trust_cg`"),
        (vec!["--slot-bin", "trust_cg=/tmp/trustc"], "deprecated slot spelling `trust_cg`"),
        (vec!["--slot-bin=trust_cg=/tmp/trustc"], "deprecated slot spelling `trust_cg`"),
    ];

    for (args, expected_error) in cases {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "benchmark", "program-index"])
            .args(args)
            .output()
            .expect("run deprecated trust_cg spelling");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{expected_error} should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(expected_error),
            "stderr should report {expected_error}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("--trust-cg-mode") || stderr.contains("trust-cg"),
            "stderr should preserve the canonical spelling\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

#[test]
#[cfg(unix)]
fn program_index_report_contains_rust_owned_preflight_and_output_contracts() {
    let temp = TempDir::new("trust-program-index-report-contract");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("trustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "llvm",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--slot-bin",
            &format!("llvm={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run report contract benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");

    assert_eq!(report["runner"]["implementation"], "rust");
    assert!(report["target_arch"].as_str().is_some_and(|arch| !arch.is_empty()));
    assert!(report["host_arch"].as_str().is_some_and(|arch| !arch.is_empty()));
    assert_eq!(report["stage2_preflight"]["schema"], "trust.program-index.stage2-preflight.v1");
    assert_eq!(report["trust_unlock_path"]["schema"], "trust.program-index.unlock-path.v1");
    assert_eq!(report["trust_unlock_path"]["status"], "ready_for_trust_compile_evidence");
    assert_eq!(
        report["summary"]["codegen_output_evidence"]["schema"],
        "trust.compile-verify-program-index.codegen-output-evidence.v1"
    );
    assert_eq!(report["summary"]["known_good_compile_acceptance"]["status"], "passed");
    assert_eq!(report["summary"]["known_flawed_compile_acceptance"]["status"], "passed");
    assert_eq!(report["results"][0]["slot_diagnostics"]["canonical_binary"], "trustc");
    assert_eq!(report["results"][0]["resolved_binary_name"], "trustc");
}

#[test]
#[cfg(unix)]
fn program_index_default_report_emits_compile_resource_usage_evidence() {
    let temp = TempDir::new("trust-program-index-resource-usage");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--slot-bin",
            &format!("trust-noverify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run default compile resource usage benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "default compile resource usage benchmark should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["compile_measurement_mode"], "cold-artifact");
    assert_eq!(report["compile_measurement"]["default"], true);
    assert_eq!(report["summary"]["compile_resource_usage"]["rows_with_peak_rss"], 2);
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["modes"]["cold-artifact"],
        2
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["statuses"]["measured"],
        2
    );
    assert_eq!(report["summary"]["compile_resource_usage"]["sample_count_total"], 2);
    assert_eq!(report["summary"]["compile_resource_usage"]["rows_with_samples"], 2);

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 2);
    for row in rows {
        assert_eq!(row["program_id"], "sample.good");
        assert_compile_resource_usage_evidence(row);
        assert_sample_aggregation_evidence(row, 1);
    }
}

#[test]
#[cfg(unix)]
fn program_index_repetitions_aggregate_samples_without_duplicate_rows() {
    let temp = TempDir::new("trust-program-index-repetitions");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--slot-bin",
            &format!("trust-noverify={}", fake.display()),
            "--require-slots",
            "--repetitions",
            "3",
        ])
        .output()
        .expect("run repeated compile resource usage benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "repeated compile resource usage benchmark should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["repetitions"], 3);
    assert_eq!(report["summary"]["total_rows"], 2);
    assert_eq!(report["summary"]["compile_resource_usage"]["sample_count_total"], 6);
    assert_eq!(report["summary"]["compile_resource_usage"]["rows_with_samples"], 2);
    assert_eq!(
        report["summary"]["compile_resource_usage"]["by_slot"]["upstream-rustc"]["sample_count_total"],
        3
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["by_slot"]["trust-noverify"]["sample_count_total"],
        3
    );

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 2, "samples must not become duplicate result rows");
    let unique_row_keys = rows
        .iter()
        .map(|row| format!("{}:{}", row["program_id"], row["slot"]))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique_row_keys.len(), rows.len(), "program/slot rows should be unique");

    for row in rows {
        assert_eq!(row["program_id"], "sample.good");
        assert_compile_resource_usage_evidence(row);
        assert_sample_aggregation_evidence(row, 3);
        let sample_output_paths = row["samples"]
            .as_array()
            .expect("samples should be array")
            .iter()
            .map(|sample| sample["output_path"].as_str().expect("sample output path"))
            .collect::<Vec<_>>();
        let unique_sample_output_paths =
            sample_output_paths.iter().collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            unique_sample_output_paths.len(),
            sample_output_paths.len(),
            "each sample should keep distinct artifact evidence"
        );
        assert!(
            sample_output_paths.iter().all(|path| path.contains(".sample-")),
            "repeated samples should use suffixed artifact paths: {sample_output_paths:?}"
        );
    }
}

#[test]
#[cfg(unix)]
fn program_index_release_report_emits_strict_superiority_performance_schema() {
    let temp = TempDir::new("trust-program-index-strict-performance");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&fake);
    write_fake_compiler(&trustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "trust-verify",
            "--suite",
            "proof-design",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--slot-bin",
            &format!("trust-noverify={}", trustc.display()),
            "--slot-bin",
            &format!("trust-verify={}", trustc.display()),
            "--require-slots",
            "--build-profile",
            "release",
            "--runtime-parity",
            "--repetitions",
            "2",
        ])
        .output()
        .expect("run strict performance benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "strict performance report must not admit unbound proof evidence\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["build_profile"], "release");
    assert_eq!(report["build_profile_detail"]["release_like"], true);
    assert_eq!(
        report["strict_superiority_performance_evidence"]["schema"],
        "trust.strict-superiority.performance-evidence.v1"
    );
    assert_eq!(report["strict_superiority_performance_evidence"]["status"], "blocked");
    assert_eq!(
        report["strict_superiority_performance_evidence"]["candidate_rejection"]["rejected"],
        true
    );
    assert_eq!(report["strict_superiority_performance_evidence"]["repetitions"], 2);
    assert!(
        report["strict_superiority_performance_evidence"]["target_arch"]
            .as_str()
            .is_some_and(|value| !value.is_empty())
    );
    assert!(
        report["strict_superiority_performance_evidence"]["target_triple"]
            .as_str()
            .is_some_and(|value| !value.is_empty())
    );
    assert!(
        report["strict_superiority_performance_evidence"]["host"]["triple"]
            .as_str()
            .is_some_and(|value| !value.is_empty())
    );
    assert_eq!(report["performance_platform_identity"]["status"], "passed");
    assert_eq!(
        report["performance_platform_identity"]["schema"],
        "trust.strict-superiority.platform-identity.v1"
    );
    assert_eq!(
        report["performance_platform_identity"]["target_triple"],
        report["strict_superiority_performance_evidence"]["target_triple"]
    );
    assert_eq!(
        report["strict_superiority_performance_evidence"]["platform_identity"]["status"],
        "passed"
    );
    assert!(report["performance_platform_identity"]["slot_probes"].as_array().is_some_and(
        |probes| {
            probes.len() == 2
                && probes.iter().all(|probe| {
                    probe["probe"]["status"] == "available"
                        && probe["declared_host"]
                            == report["performance_platform_identity"]["target_triple"]
                })
        }
    ));

    let lanes = &report["strict_superiority_performance_evidence"]["lanes"];
    assert_eq!(lanes["clean_release_compile"]["status"], "blocked");
    assert!(
        lanes["clean_release_compile"]["blocked_reasons"]
            .as_array()
            .expect("blocked reasons")
            .iter()
            .any(|reason| reason == "candidate_data_rejected")
    );
    assert_eq!(lanes["clean_release_compile"]["required_build_profile"], "release");
    assert_eq!(lanes["clean_release_compile"]["rust"]["sample_count"], 4);
    assert_eq!(lanes["clean_release_compile"]["trust"]["trust-noverify"]["sample_count"], 4);
    assert!(lanes["clean_release_compile"]["rust"]["duration_seconds"]["p50"].as_f64().is_some());
    assert!(lanes["clean_release_compile"]["rust"]["duration_seconds"]["p95"].as_f64().is_some());
    assert!(
        lanes["clean_release_compile"]["rust"]["duration_seconds"]["geomean"].as_f64().is_some()
    );
    assert!(lanes["clean_release_compile"]["rust"]["size_bytes"]["max"].as_f64().is_some());
    assert_eq!(lanes["clean_release_compile"]["comparisons"][0]["trust_slot"], "trust-noverify");
    assert!(lanes["clean_release_compile"]["comparisons"][0]["ratio_vs_rust"].as_f64().is_some());
    assert_eq!(lanes["runtime_geomean"]["status"], "blocked");
    assert!(lanes["runtime_geomean"]["rust"]["duration_seconds"]["geomean"].is_null());
    assert_eq!(lanes["binary_size"]["status"], "blocked");
    assert!(lanes["binary_size"]["rust"]["size_bytes"]["geomean"].is_null());
    assert_eq!(lanes["incremental_debug_compile"]["status"], "blocked");
    assert!(
        lanes["incremental_debug_compile"]["blocked_reasons"]
            .as_array()
            .expect("blocked reasons should be array")
            .iter()
            .any(|reason| reason
                .as_str()
                .is_some_and(|reason| reason.contains("--build-profile debug")))
    );

    let rows = report["results"].as_array().expect("rows should be array");
    assert!(
        rows.iter().all(|row| row["measurement_profile"]["build_profile"] == "release"),
        "all compile rows should be marked as release profile"
    );
    assert!(
        rows.iter().all(|row| {
            row["command"]
                .as_array()
                .expect("command should be array")
                .iter()
                .any(|arg| arg == "opt-level=3")
        }),
        "release profile should pass -C opt-level=3"
    );
    assert_eq!(
        report["summary"]["strict_superiority_performance_evidence"]["lane_statuses"]["clean_release_compile"],
        "blocked"
    );
}

#[test]
#[cfg(unix)]
fn program_index_proof_design_suite_reports_non_candidate_rows_but_refuses_proof_admission() {
    let temp = TempDir::new("trust-program-index-proof-design");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&trustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--suite",
            "proof-design",
            "--compile-measurement",
            "warm-incremental",
            "--require-slots",
        ])
        .output()
        .expect("run proof-design suite benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "proof-design suite must remain inadmissible\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["program_index_evidence"]["model_source"], "builtin-proof-design-policy");
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(
        report["program_index_evidence"]["canonical_proof_design_status"],
        "source_tree_matches_head"
    );
    assert_eq!(
        report["program_index_evidence"]["source_execution_binding"],
        "candidate_primary_argv_unsealed_closure"
    );
    assert!(report["repo_head"].as_str().is_some_and(|head| head.len() == 40));
    assert_eq!(report["repo_head_matches_at_finish"], true);
    assert_eq!(report["program_index_evidence"]["selected_programs"], 2);
    assert_eq!(report["program_index_evidence"]["selected_pairs"], 1);
    assert_eq!(report["program_index_evidence"]["selected_candidate_rows"], 0);
    assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 2);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["admissible_for_domination"], false);
    assert_eq!(report["program_index_evidence"]["selected_suite_counts"]["proof-design"], 2);
    assert_eq!(
        report["summary"]["program_index_evidence"]["selected_suite_counts"]["proof-design"],
        2
    );
    assert_eq!(
        report["proof_design_verifier_evidence"]["schema"],
        "trust.compile-verify-program-index.proof-design-verifier-evidence.v1"
    );
    assert_eq!(report["proof_design_verifier_evidence"]["status"], "blocked");
    assert_eq!(report["proof_design_verifier_evidence"]["required"], true);
    assert_eq!(report["proof_design_verifier_evidence"]["admissible_for_domination"], false);
    assert_eq!(report["proof_design_verifier_evidence"]["selected_programs"], 2);
    assert_eq!(report["proof_design_verifier_evidence"]["verifier_rows"], 2);
    assert_eq!(report["proof_design_verifier_evidence"]["accepted_rows"], 0);
    assert_eq!(report["proof_design_verifier_evidence"]["stage2_binding"]["status"], "bound");
    assert_eq!(report["proof_design_verifier_evidence"]["stage2_binding"]["repo_stage2"], true);
    assert_eq!(
        report["proof_design_verifier_evidence"]["stage2_binding"]["canonical_binary"],
        "trustc"
    );
    assert_eq!(
        report["proof_design_verifier_evidence"]["transport_protocol"],
        "stderr-line-prefix"
    );
    assert_eq!(report["proof_design_verifier_evidence"]["transport_prefix"], "TRUST_JSON:");
    assert_eq!(report["summary"]["proof_design_verifier_evidence"]["status"], "blocked");
    assert!(
        report["proof_design_verifier_evidence"]["transport_sources"]
            .as_array()
            .expect("transport sources")
            .iter()
            .all(|source| source
                .as_str()
                .is_some_and(|path| path.starts_with("logs/trust-verify/")))
    );

    let suite = &report["program_index_evidence"]["selected_suites"]["proof-design"];
    assert_eq!(suite["candidate_rows"], 0);
    assert_eq!(suite["gating"], true);
    assert_eq!(suite["candidate_evidence"], false);
    assert_eq!(suite["admissible_for_domination"], false);
    assert_eq!(suite["evidence_class"], "blocked_gating_unsealed_source_execution");

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 2);
    for row in rows {
        assert_eq!(row["suite"], "proof-design");
        assert_eq!(row["slot"], "trust-verify");
        assert_eq!(row["source_execution"]["kind"], "candidate_primary_argv_unsealed_closure");
        assert_eq!(row["source_execution"]["authenticated_read"], false);
        assert_eq!(row["source_execution"]["transitive_source_closure"], "unresolved");
        assert_eq!(row["source_execution"]["source_copy_diagnostic"]["status"], "available");
        assert_eq!(
            row["source_execution"]["source_copy_diagnostic"]["selected_as_compiler_input"],
            true
        );
        assert_eq!(row["observed"], "source_input_blocked");
        assert_eq!(row["source_input_check"]["status"], "blocked_compiler_read");
        assert!(
            row["source_input_check"]["reason"]
                .as_str()
                .expect("census refusal")
                .contains("open compiler census")
        );
        assert_eq!(
            row["command"].as_array().and_then(|args| args.last()),
            Some(&row["source_execution"]["compiler_source_path"])
        );
        assert_eq!(
            row["incremental_warmup"]["command"].as_array().and_then(|args| args.last()),
            Some(&row["source_execution"]["compiler_source_path"])
        );
        assert!(
            Path::new(
                row["source_execution"]["source_copy_diagnostic"]["path"]
                    .as_str()
                    .expect("source copy path")
            )
            .is_file()
        );
        assert_eq!(
            row["source_execution"]["compiler_source_path"],
            row["source_execution"]["source_copy_diagnostic"]["path"]
        );
        assert_ne!(row["metadata"]["candidate"], true);
        assert!(
            !row["program_id"]
                .as_str()
                .expect("program id should be string")
                .starts_with("candidate_"),
            "proof-design row must not be a candidate row: {row:?}"
        );
    }
}

#[test]
#[cfg(unix)]
fn program_index_external_proof_design_index_remains_informational_without_proof_slot() {
    let temp = TempDir::new("trust-program-index-proof-design-informational");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&fake);
    let index = root.join("examples/bench/program_index/index.json");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--suite",
            "proof-design",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run informational proof-design benchmark");
    assert_eq!(
        output.status.code(),
        Some(0),
        "informational benchmark should run: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(report["proof_design_verifier_evidence"]["status"], "not_claimed");
    assert_eq!(report["proof_design_verifier_evidence"]["admissible_for_domination"], false);
    assert_eq!(report["results"].as_array().expect("results").len(), 2);
}

#[test]
#[cfg(unix)]
fn proof_design_primary_copy_is_compiler_argv_across_compile_paths_but_remains_unsealed() {
    let temp = TempDir::new("trust-proof-design-source-snapshot");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let compiler = temp.path().join("fake-rustc");
    let expected = temp.path().join("expected.rs");
    let seen = temp.path().join("seen-sources.txt");
    write_program_index_proof_design_fixture(&root);
    write_observing_compiler(&compiler);
    let live = root.join("examples/proof_good.rs");
    fs::copy(&live, &expected).expect("copy expected HEAD source");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "--program",
            "proof_gate.good",
            "--slot-bin",
            &format!("upstream-rustc={}", compiler.display()),
            "--slot-bin",
            &format!("trust-noverify={}", compiler.display()),
            "--compile-measurement",
            "warm-incremental",
            "--runtime-parity",
            "--require-slots",
        ])
        .env("TEST_LIVE_SOURCE", &live)
        .env("TEST_EXPECTED_SOURCE", &expected)
        .env("TEST_SEEN_SOURCES", &seen)
        .output()
        .expect("run snapshot benchmark");
    assert_eq!(
        output.status.code(),
        Some(1),
        "unsealed proof-design output must block runtime parity\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(fs::read(&live).expect("live source"), fs::read(&expected).expect("HEAD source"));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(
        report["program_index_evidence"]["canonical_proof_design_status"],
        "source_tree_matches_head"
    );
    assert_eq!(report["runtime_parity"]["status"], "not_applicable");
    assert_eq!(
        report["program_index_evidence"]["source_execution_binding"],
        "candidate_primary_argv_unsealed_closure"
    );
    let sources = fs::read_to_string(&seen).expect("compiler source log");
    let sources = sources.lines().collect::<Vec<_>>();
    assert_eq!(sources.len(), 6, "warmup, measured, and runtime builds for both slots");
    for observation in &sources {
        let (source, matched_head_after_edit) = observation.split_once('|').expect("observation");
        assert_ne!(Path::new(source), live, "compiler must not read the live primary path");
        assert_eq!(matched_head_after_edit, "1", "compiler argv must retain HEAD bytes");
    }
    for row in report["results"].as_array().expect("compile rows") {
        let source = row["source_execution"]["compiler_source_path"].as_str().expect("source path");
        assert_eq!(
            row["command"].as_array().and_then(|args| args.last()).and_then(Value::as_str),
            Some(source)
        );
        assert_eq!(
            row["incremental_warmup"]["command"]
                .as_array()
                .and_then(|args| args.last())
                .and_then(Value::as_str),
            Some(source)
        );
        assert_eq!(row["source_execution"]["source_copy_diagnostic"]["status"], "available");
        assert_eq!(row["source_input_check"]["status"], "matched_pre_post");
        assert_eq!(row["incremental_warmup"]["source_input_check"]["status"], "matched_pre_post");
        assert_eq!(
            row["source_execution"]["source_copy_diagnostic"]["path"],
            row["source_execution"]["compiler_source_path"]
        );
    }
    for row in report["runtime_parity"]["rows"].as_array().expect("runtime rows") {
        let source = row["source_execution"]["compiler_source_path"].as_str().expect("source path");
        assert_eq!(
            row["build_command"].as_array().and_then(|args| args.last()).and_then(Value::as_str),
            Some(source)
        );
        assert_eq!(row["source_input_check"]["status"], "matched_pre_post");
        assert_eq!(row["build_status"], "output_source_unsealed");
        assert_eq!(row["output_source_check"]["status"], "unsealed");
        assert_eq!(row["run_status"], "not_run");
        assert!(row["executable_sha256"].is_null());
    }
}

#[test]
#[cfg(unix)]
fn proof_design_unparsed_source_forms_remain_blocked_observations() {
    let cases = [
        ("comment_string", "fn main() { let _ = \"file\"; } // file\n"),
        ("include", "fn main() { let _ = include_str!(\"dep.txt\"); }\n"),
        ("module", "mod dep; fn main() {}\n"),
        ("absolute_path", "#[path = \"/tmp/dep.rs\"] mod dep; fn main() {}\n"),
    ];
    for (name, source) in cases {
        let temp = TempDir::new(&format!("trust-proof-design-observe-{name}"));
        let root = temp.path().join("repo");
        let report_dir = temp.path().join("report");
        let compiler = temp.path().join("compiler");
        write_program_index_proof_design_fixture(&root);
        write(root.join("examples/proof_good.rs"), source);
        write(root.join("examples/dep.txt"), "not declared\n");
        write(root.join("examples/dep.rs"), "pub fn dep() {}\n");
        commit_proof_design_fixture(&root);
        write_fake_compiler(&compiler);

        let output = Command::new(targo_trust_binary())
            .args([
                "trust",
                "benchmark",
                "program-index",
                "--repo-root",
                root.to_str().expect("root path"),
                "--index",
                root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
                "--report-dir",
                report_dir.to_str().expect("report path"),
                "--slots",
                "trust-noverify",
                "--program",
                "proof_gate.good",
                "--slot-bin",
                &format!("trust-noverify={}", compiler.display()),
                "--require-slots",
            ])
            .output()
            .expect("run observational benchmark");
        assert_eq!(
            output.status.code(),
            Some(0),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let report: Value = serde_json::from_slice(
            &fs::read(report_dir.join("report.json")).expect("observational report"),
        )
        .expect("parse report");
        assert_eq!(report["program_index_evidence"]["selected_programs"], 1, "{name}");
        assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 1, "{name}");
        assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
        assert_eq!(
            report["program_index_evidence"]["source_execution_binding"],
            "candidate_primary_argv_unsealed_closure"
        );
        let row = &report["results"][0];
        assert_eq!(row["outcome"], "passed", "{name}");
        assert_eq!(row["source_execution"]["source_copy_diagnostic"]["status"], "available");
        assert_eq!(row["source_execution"]["transitive_source_closure"], "unresolved");
        assert_eq!(
            row["command"].as_array().and_then(|args| args.last()),
            Some(&row["source_execution"]["compiler_source_path"])
        );
        assert_eq!(
            row["source_execution"]["source_copy_diagnostic"]["path"],
            row["source_execution"]["compiler_source_path"]
        );
    }
}

#[test]
#[cfg(unix)]
fn proof_design_missing_head_source_keeps_observational_rows() {
    let temp = TempDir::new("trust-proof-design-missing-head-source");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&trustc);
    let status = Command::new("git")
        .args(["rm", "--cached", "examples/proof_good.rs"])
        .current_dir(&root)
        .status()
        .expect("remove HEAD source only");
    assert!(status.success());
    let status = Command::new("git")
        .args([
            "-c",
            "user.name=Proof Design Test",
            "-c",
            "user.email=proof-design@example.invalid",
            "commit",
            "-qm",
            "omit canonical source",
        ])
        .current_dir(&root)
        .status()
        .expect("commit missing HEAD source");
    assert!(status.success());
    assert!(root.join("examples/proof_good.rs").is_file());

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "trust-verify",
            "--suite",
            "proof-design",
            "--require-slots",
        ])
        .output()
        .expect("run missing HEAD source benchmark");
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(report["program_index_evidence"]["selected_programs"], 2);
    assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 2);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["canonical_proof_design_status"], "blocked");
    assert_eq!(
        report["program_index_evidence"]["source_execution_binding"],
        "candidate_primary_argv_unsealed_closure"
    );
    assert_eq!(report["proof_design_verifier_evidence"]["status"], "blocked");
    assert_eq!(report["proof_design_verifier_evidence"]["verifier_rows"], 2);
    let rows = report["results"].as_array().expect("observational rows");
    assert_eq!(rows.len(), 2);
    for row in rows {
        assert_eq!(row["outcome"], "skipped");
        assert_eq!(row["source_execution"]["kind"], "candidate_primary_argv_unsealed_closure");
        assert_eq!(row["source_execution"]["source_copy_diagnostic"]["status"], "unavailable");
        assert!(
            row["source_execution"]["source_copy_diagnostic"]["reason"]
                .as_str()
                .is_some_and(|reason| reason.contains("canonical HEAD source copy unavailable"))
        );
        assert_eq!(row["command"], serde_json::json!([]));
        assert_eq!(row["source_execution"]["compiler_source_path"], Value::Null);
        assert_eq!(row["source_input_check"]["status"], "not_run");
    }
}

#[test]
#[cfg(unix)]
fn proof_design_missing_live_source_keeps_denominator() {
    let temp = TempDir::new("trust-proof-design-missing-live-source");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&trustc);
    fs::remove_file(root.join("examples/proof_good.rs")).expect("remove live source");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "trust-verify",
            "--suite",
            "proof-design",
            "--require-slots",
        ])
        .output()
        .expect("run missing live source benchmark");
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(report["program_index_evidence"]["selected_programs"], 2);
    assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 2);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["canonical_proof_design_status"], "blocked");
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(report["proof_design_verifier_evidence"]["status"], "blocked");
    assert_eq!(report["results"].as_array().map(Vec::len), Some(2));
    let missing = report["results"]
        .as_array()
        .expect("results")
        .iter()
        .find(|row| row["program_id"] == "proof_gate.good")
        .expect("missing-source row");
    assert_eq!(missing["outcome"], "skipped");
    assert_eq!(missing["observed"], "slot_skipped");
    assert_eq!(missing["source_sha256"], Value::Null);
    assert!(missing["skip_reason"].as_str().is_some_and(|reason| reason.contains("not readable")));
    assert_eq!(missing["source_execution"]["source_copy_diagnostic"]["status"], "unavailable");
}

#[test]
#[cfg(unix)]
fn proof_design_selection_does_not_read_missing_unselected_source() {
    let temp = TempDir::new("trust-proof-design-unselected-source");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&trustc);
    fs::remove_file(root.join("examples/candidate_good.rs")).expect("remove unselected source");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "trust-noverify",
            "--suite",
            "proof-design",
            "--require-slots",
        ])
        .output()
        .expect("run filtered proof-design benchmark");
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stderr));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(report["program_index_evidence"]["selected_programs"], 2);
    assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 2);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(
        report["program_index_evidence"]["canonical_proof_design_status"],
        "source_tree_matches_head"
    );
    assert_eq!(
        report["program_index_evidence"]["source_execution_binding"],
        "candidate_primary_argv_unsealed_closure"
    );
    assert_eq!(report["results"].as_array().map(Vec::len), Some(2));
}

#[test]
#[cfg(unix)]
fn proof_design_candidate_copy_change_blocks_observation_without_losing_row() {
    use std::os::unix::fs::PermissionsExt;

    let temp = TempDir::new("trust-proof-design-snapshot-tamper");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let compiler = temp.path().join("compiler");
    write_program_index_proof_design_fixture(&root);
    write(
        compiler.clone(),
        "#!/bin/sh\nout=''\nprev=''\nfor src do\n  if [ \"$prev\" = '-o' ]; then out=\"$src\"; fi\n  prev=\"$src\"\ndone\ncase \"$src\" in *.rs) ;; *) exit 0 ;; esac\nchmod u+w \"$src\"\nprintf 'tampered\\n' > \"$src\"\nmkdir -p \"$(dirname \"$out\")\"\nprintf 'fake object' > \"$out\"\n",
    );
    let mut permissions = fs::metadata(&compiler).expect("compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&compiler, permissions).expect("compiler permissions");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "trust-noverify",
            "--program",
            "proof_gate.good",
            "--slot-bin",
            &format!("trust-noverify={}", compiler.display()),
            "--repetitions",
            "2",
            "--require-slots",
        ])
        .output()
        .expect("run live-change benchmark");
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(report["program_index_evidence"]["selected_programs"], 1);
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(
        report["program_index_evidence"]["canonical_proof_design_status"],
        "source_tree_matches_head"
    );
    assert_eq!(
        report["program_index_evidence"]["source_execution_binding"],
        "candidate_primary_argv_unsealed_closure"
    );
    assert_eq!(report["results"][0]["outcome"], "failed");
    assert_eq!(report["results"][0]["observed"], "source_input_blocked");
    assert_eq!(report["results"][0]["source_input_check"]["status"], "blocked_post_read");
    assert_eq!(
        report["results"][0]["samples"][0]["source_input_check"]["status"],
        "blocked_post_read"
    );
    assert_eq!(
        report["results"][0]["samples"][1]["source_input_check"]["status"],
        "blocked_pre_read"
    );
    assert_eq!(report["results"][0]["samples"][1]["source_input_check"]["compiler_invoked"], false);
    assert_eq!(
        report["results"][0]["source_execution"]["source_copy_diagnostic"]["status"],
        "invalid"
    );
}

#[test]
#[cfg(unix)]
fn proof_design_edit_restore_stays_observational_despite_matching_edge_checks() {
    use std::os::unix::fs::PermissionsExt;

    let temp = TempDir::new("trust-proof-design-edit-restore");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let compiler = temp.path().join("compiler");
    write_program_index_proof_design_fixture(&root);
    write(
        compiler.clone(),
        "#!/bin/sh\nout=''\nprev=''\nfor src do\n  if [ \"$prev\" = '-o' ]; then out=\"$src\"; fi\n  prev=\"$src\"\ndone\ncase \"$src\" in *.rs) ;; *) exit 0 ;; esac\ncp \"$src\" \"$src.saved\"\nchmod u+w \"$src\"\nprintf 'fn main() { panic!(\"transient\"); }\\n' > \"$src\"\ncp \"$src.saved\" \"$src\"\nchmod a-w \"$src\"\nrm \"$src.saved\"\nmkdir -p \"$(dirname \"$out\")\"\nprintf 'fake object' > \"$out\"\n",
    );
    let mut permissions = fs::metadata(&compiler).expect("compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&compiler, permissions).expect("compiler permissions");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root path"),
            "--index",
            root.join("examples/bench/program_index/index.json").to_str().expect("index path"),
            "--report-dir",
            report_dir.to_str().expect("report path"),
            "--slots",
            "trust-noverify",
            "--program",
            "proof_gate.good",
            "--slot-bin",
            &format!("trust-noverify={}", compiler.display()),
            "--require-slots",
        ])
        .output()
        .expect("run edit/restore benchmark");
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stderr));
    let report: Value =
        serde_json::from_slice(&fs::read(report_dir.join("report.json")).expect("report"))
            .expect("parse report");
    assert_eq!(report["results"][0]["outcome"], "passed");
    assert_eq!(report["results"][0]["source_input_check"]["status"], "matched_pre_post");
    assert_eq!(report["results"][0]["source_execution"]["authenticated_read"], false);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
}

#[test]
#[cfg(unix)]
fn program_index_external_informational_index_cannot_admit_performance() {
    let temp = TempDir::new("trust-program-index-informational-performance");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);
    let index = temp.path().join("external-index.json");
    fs::copy(root.join("examples/bench/program_index/index.json"), &index)
        .expect("copy external index");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--slot-bin",
            &format!("trust-noverify={}", fake.display()),
            "--build-profile",
            "release",
            "--require-slots",
        ])
        .output()
        .expect("run external informational benchmark");
    assert_eq!(
        output.status.code(),
        Some(0),
        "informational benchmark should run: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["program_index_evidence"]["status"], "informational");
    assert_eq!(report["program_index_evidence"]["admissible_for_domination"], false);
    let performance = &report["strict_superiority_performance_evidence"];
    assert_eq!(performance["candidate_rejection"]["status"], "informational");
    assert_eq!(performance["candidate_rejection"]["rejected"], true);
    assert_eq!(performance["status"], "blocked");
    assert_eq!(performance["admissible_for_domination"], false);
    assert_eq!(performance["lanes"]["clean_release_compile"]["status"], "blocked");
    assert!(
        performance["lanes"]["clean_release_compile"]["blocked_reasons"]
            .as_array()
            .expect("blocked reasons")
            .iter()
            .any(|reason| reason == "candidate_data_rejected")
    );
    assert_eq!(report["results"].as_array().expect("results").len(), 4);
}

#[test]
#[cfg(unix)]
fn program_index_proof_design_suite_requires_repo_stage2_trust_verify_slot() {
    let temp = TempDir::new("trust-program-index-proof-design-external-verifier");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("external/bin/trustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--suite",
            "proof-design",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run proof-design suite with external fake verifier");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "external verifier must not be admissible proof-design evidence\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["program_index_evidence"]["status"], "blocked");
    assert_eq!(report["proof_design_verifier_evidence"]["required"], true);
    assert_eq!(report["proof_design_verifier_evidence"]["status"], "blocked");
    assert_eq!(
        report["proof_design_verifier_evidence"]["stage2_binding"]["status"],
        "non_repo_stage2"
    );
    assert_eq!(report["summary"]["proof_design_verifier_evidence"]["status"], "blocked");
    let blockers = report["proof_design_verifier_evidence"]["blocked_reasons"]
        .as_array()
        .expect("blocked reasons")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(
        blockers.iter().any(|reason| reason.contains("repo-local build/*/stage2/bin/trustc")),
        "blockers should explain the stage2 binding failure: {blockers:?}"
    );
}

#[test]
#[cfg(unix)]
fn program_index_proof_design_candidates_report_candidate_non_gating_evidence() {
    let temp = TempDir::new("trust-program-index-proof-design-candidates");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_proof_design_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--suite",
            "proof-design-candidates",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run proof-design-candidates suite benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "proof-design-candidates suite should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["program_index_evidence"]["status"], "candidate_non_gating");
    assert_eq!(report["program_index_evidence"]["selected_programs"], 2);
    assert_eq!(report["program_index_evidence"]["selected_pairs"], 1);
    assert_eq!(report["program_index_evidence"]["selected_candidate_rows"], 2);
    assert_eq!(report["program_index_evidence"]["selected_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["selected_admissible_gating_rows"], 0);
    assert_eq!(report["program_index_evidence"]["admissible_for_domination"], false);
    assert_eq!(
        report["program_index_evidence"]["selected_suite_counts"]["proof-design-candidates"],
        2
    );
    assert_eq!(report["summary"]["program_index_evidence"]["selected_candidate_rows"], 2);
    assert_eq!(
        report["strict_superiority_performance_evidence"]["candidate_rejection"]["rejected"],
        true
    );
    assert_eq!(
        report["strict_superiority_performance_evidence"]["candidate_rejection"]["selected_candidate_rows"],
        2
    );
    assert_eq!(
        report["summary"]["strict_superiority_performance_evidence"]["candidate_rejected"],
        true
    );
    let clean_compile_reasons = report["strict_superiority_performance_evidence"]["lanes"]
        ["clean_release_compile"]["blocked_reasons"]
        .as_array()
        .expect("blocked reasons should be array");
    assert!(
        clean_compile_reasons
            .iter()
            .any(|reason| reason.as_str() == Some("candidate_data_rejected")),
        "candidate performance data must be rejected fail-closed: {clean_compile_reasons:?}"
    );

    let suite = &report["program_index_evidence"]["selected_suites"]["proof-design-candidates"];
    assert_eq!(suite["candidate_rows"], 2);
    assert_eq!(suite["gating"], false);
    assert_eq!(suite["candidate_evidence"], true);
    assert_eq!(suite["non_gating"], true);
    assert_eq!(suite["admissible_for_domination"], false);
    assert_eq!(suite["evidence_class"], "candidate_non_gating");

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 2);
    for row in rows {
        assert_eq!(row["suite"], "proof-design-candidates");
        assert_eq!(row["metadata"]["candidate"], true);
        assert!(
            row["program_id"]
                .as_str()
                .expect("program id should be string")
                .starts_with("candidate_"),
            "candidate suite row should be visibly candidate evidence: {row:?}"
        );
    }
}

#[test]
#[cfg(unix)]
fn program_index_rust_cli_runs_fake_compile_verify_and_runtime_parity() {
    let temp = TempDir::new("trust-program-index-cli");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "trust-noverify",
            "trust-verify",
            "llvm",
            "trust-cg",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--slot-bin",
            &format!("trust-noverify={}", fake.display()),
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--slot-bin",
            &format!("llvm={}", fake.display()),
            "--slot-bin",
            &format!("trust-cg={}", fake.display()),
            "--require-slots",
            "--runtime-parity",
        ])
        .output()
        .expect("run Rust program-index CLI with fake compilers");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "program-index fake matrix should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("program-index report:"));
    assert!(stdout.contains("backward_pass=reported"));

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");

    assert_eq!(report["runner"]["implementation"], "rust");
    assert_eq!(report["runner"]["python_used"], false);
    assert_eq!(report["compile_measurement_mode"], "cold-artifact");
    assert_eq!(report["compile_measurement"]["requested_incremental"], false);
    assert_eq!(report["summary"]["passed"], 10);
    assert_eq!(report["summary"]["failed"], 0);
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "passed");
    let upstream_entries = report["summary"]["upstream_baseline"]["entries"]
        .as_array()
        .expect("upstream baseline entries should be array");
    let upstream_entry = upstream_entries
        .iter()
        .find(|entry| entry["slot"] == "upstream-rustc")
        .expect("upstream baseline entry should exist");
    assert_eq!(upstream_entry["status"], "passed");
    assert_eq!(upstream_entry["version_probe"]["status"], "available");
    assert_eq!(upstream_entry["sysroot_probe"]["status"], "available");
    assert_eq!(
        upstream_entry["blockers"].as_array().expect("baseline blockers should be array").len(),
        0
    );
    assert_eq!(report["summary"]["known_good_pass"]["status"], "passed");
    assert_eq!(report["summary"]["known_flawed_rejection"]["status"], "passed");
    assert_eq!(report["summary"]["backward_pass"]["status"], "reported");
    assert_eq!(report["summary"]["backward_pass"]["observed"]["no_repair_needed"], 1);
    assert_eq!(
        report["summary"]["backward_pass"]["observed"]["counterexample_or_repair_candidate"],
        1
    );
    assert_eq!(report["summary"]["runtime_parity"]["status"], "passed");
    assert_eq!(report["summary"]["runtime_parity"]["passed"], 8);
    assert_eq!(report["summary"]["runtime_parity"]["not_applicable"], 2);
    assert_eq!(report["summary"]["compile_resource_usage"]["rows_with_peak_rss"], 10);
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["incremental_rows"],
        0
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["measured_incremental_rows"],
        0
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["non_incremental_rows"],
        10
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["measured_non_incremental_rows"],
        10
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["modes"]["cold-artifact"],
        10
    );
    assert_eq!(
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["cache_states"]["cold_artifact"],
        10
    );

    let rows = report["results"].as_array().expect("rows should be array");
    assert!(rows.iter().all(|row| {
        row["measurement_profile"]["mode"] == "cold-artifact"
            && row["measurement_profile"]["requested_incremental"] == false
            && row["measurement_profile"]["incremental"] == false
            && row["measurement_profile"]["cache_state"] == "cold_artifact"
            && row["measurement_profile"]["runtime_measurements_separate"] == true
    }));
    let trust_verify_flawed = rows
        .iter()
        .find(|row| row["program_id"] == "sample.flawed" && row["slot"] == "trust-verify")
        .expect("flawed trust-verify row");
    assert_eq!(trust_verify_flawed["observed"], "verify_fail");
    assert_eq!(
        trust_verify_flawed["backward_pass"]["observed"],
        "counterexample_or_repair_candidate"
    );
    assert_eq!(trust_verify_flawed["transport"]["failed"], 1);
    assert_eq!(trust_verify_flawed["transport"]["counterexamples"], 1);

    let trust_cg_good = rows
        .iter()
        .find(|row| row["program_id"] == "sample.good" && row["slot"] == "trust-cg")
        .expect("trust_cg row");
    assert_eq!(trust_cg_good["observed"], "compile_pass");
    assert!(
        trust_cg_good["command"]
            .as_array()
            .expect("command array")
            .iter()
            .any(|arg| arg == "codegen-backend=trust_cg")
    );
}

#[test]
#[cfg(unix)]
fn program_index_dry_run_marks_warm_incremental_measurement_mode() {
    let temp = TempDir::new("trust-program-index-warm-incremental-dry-run");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--compile-measurement",
            "warm-incremental",
            "--dry-run",
        ])
        .output()
        .expect("run warm incremental dry-run");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "warm incremental dry-run should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");

    assert_eq!(report["compile_measurement_mode"], "warm-incremental");
    assert_eq!(report["compile_measurement"]["requested_incremental"], true);
    assert_eq!(
        report["compile_measurement"]["evidence_classification"],
        "warmup compile followed by measured rustc -C incremental compile"
    );
    assert_eq!(report["strict_superiority_performance_evidence"]["dry_run"], true);
    assert_eq!(report["strict_superiority_performance_evidence"]["status"], "blocked");
    let blockers = report["strict_superiority_performance_evidence"]["lanes"]
        ["incremental_debug_compile"]["blocked_reasons"]
        .as_array()
        .expect("blocked reasons should be array");
    assert!(
        blockers.iter().any(|reason| {
            reason.as_str().is_some_and(|reason| {
                reason.contains("dry-run report contains planned commands only")
            })
        }),
        "dry-run performance evidence should fail closed: {blockers:?}"
    );

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    assert_eq!(row["outcome"], "planned");
    assert_eq!(row["measurement_profile"]["mode"], "warm-incremental");
    assert_eq!(row["measurement_profile"]["cache_state"], "planned_warm_incremental");
    assert_eq!(row["measurement_profile"]["requested_incremental"], true);
    assert_eq!(row["measurement_profile"]["warmup_required"], true);
    assert_eq!(row["measurement_profile"]["incremental"], false);
    assert!(
        row["measurement_profile"]["rustc_incremental_arg"]
            .as_str()
            .expect("incremental arg")
            .starts_with("-C incremental=incremental/upstream-rustc/sample_good")
    );
    let command = row["command"].as_array().expect("command should be array");
    assert!(command.iter().any(|arg| arg == "-C"), "command should include -C: {command:?}");
    assert!(
        command
            .iter()
            .any(|arg| { arg.as_str().is_some_and(|arg| arg.starts_with("incremental=")) }),
        "command should include an incremental directory: {command:?}"
    );
}

#[test]
#[cfg(unix)]
fn program_index_warm_incremental_measurement_marks_incremental_evidence() {
    let temp = TempDir::new("trust-program-index-warm-incremental");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--require-slots",
            "--compile-measurement",
            "warm-incremental",
        ])
        .output()
        .expect("run warm incremental program-index CLI");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "warm incremental benchmark should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["compile_measurement_mode"], "warm-incremental");
    assert_eq!(report["compile_measurement"]["requested_incremental"], true);

    let profiles = &report["summary"]["compile_resource_usage"]["measurement_profiles"];
    assert_eq!(profiles["incremental_rows"], 1);
    assert_eq!(profiles["measured_incremental_rows"], 1);
    assert_eq!(profiles["non_incremental_rows"], 0);
    assert_eq!(profiles["requested_incremental_rows"], 1);
    assert_eq!(profiles["modes"]["warm-incremental"], 1);
    assert_eq!(profiles["cache_states"]["warm_incremental"], 1);
    assert_eq!(profiles["statuses"]["measured"], 1);

    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    assert_eq!(row["outcome"], "passed");
    assert!(command_contains_incremental_arg(&row["command"]));
    assert_eq!(row["incremental_warmup"]["status"], "passed");
    assert_eq!(row["incremental_warmup"]["valid_for_incremental_measurement"], true);
    assert!(command_contains_incremental_arg(&row["incremental_warmup"]["command"]));

    let profile = &row["measurement_profile"];
    assert_eq!(profile["mode"], "warm-incremental");
    assert_eq!(profile["requested_incremental"], true);
    assert_eq!(profile["incremental"], true);
    assert_eq!(profile["cache_state"], "warm_incremental");
    assert_eq!(profile["incremental_env"], "CARGO_INCREMENTAL=1");
    assert_eq!(profile["warmup_required"], true);
    assert_eq!(profile["warmup_valid"], true);
    assert!(
        profile["rustc_incremental_arg"]
            .as_str()
            .expect("incremental arg should be string")
            .contains("incremental/")
    );
}

#[test]
#[cfg(unix)]
fn runtime_parity_requires_non_baseline_comparison() {
    let temp = TempDir::new("trust-program-index-baseline-runtime");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", fake.display()),
            "--require-slots",
            "--runtime-parity",
        ])
        .output()
        .expect("run baseline-only runtime parity");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "baseline-only runtime parity should not be proof of parity\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["runtime_parity"]["status"], "baseline_only");
    assert_eq!(report["summary"]["runtime_parity"]["baseline_passed"], 2);
    assert_eq!(report["summary"]["runtime_parity"]["comparison_passed"], 0);
}

#[test]
#[cfg(unix)]
fn require_slots_reports_missing_slot_and_exits_2() {
    let temp = TempDir::new("trust-program-index-missing-required-slot");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let missing = temp.path().join("missing-trustc");
    write_program_index_fixture(&root);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--slot-bin",
            &format!("trust-verify={}", missing.display()),
            "--require-slots",
        ])
        .output()
        .expect("run with missing required slot");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "missing required slot should exit 2\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("program-index report:"));
    assert!(stdout.contains("program-index missing required slots: trust-verify"));
    assert!(stderr.contains("required slot binary not found for: trust-verify"));

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["required_slots"]["status"], "missing_required_slots");
    assert_eq!(report["required_slots"]["missing"][0], "trust-verify");
    assert_eq!(report["summary"]["required_slots"]["status"], "missing_required_slots");
    assert_eq!(report["summary"]["skipped"], 2);
    assert_eq!(report["summary"]["failed"], 0);
    assert_eq!(report["summary"]["unsupported_mir_gate"]["status"], "not_run");
    let rows = report["results"].as_array().expect("rows should be array");
    assert_eq!(rows.len(), 2);
    assert!(rows.iter().all(|row| row["slot"] == "trust-verify"));
    assert!(rows.iter().all(|row| row["outcome"] == "skipped"));
    assert!(rows.iter().all(|row| row["skip_reason"] == "required slot binary not found"));
}

#[test]
#[cfg(unix)]
fn program_index_trust_slots_ignore_path_trustc_fallback() {
    let temp = TempDir::new("trust-program-index-path-trustc");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let path_dir = temp.path().join("path-bin");
    let path_trustc = path_dir.join("trustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&path_trustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--require-slots",
        ])
        .env("PATH", &path_dir)
        .output()
        .expect("run with PATH-only trustc");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "PATH-only trustc must not satisfy Trust-owned evidence slots\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("required slot binary not found for: trust-verify"));

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["required_slots"]["status"], "missing_required_slots");
    assert_eq!(report["stage2_preflight"]["status"], "missing_slots");
    assert_eq!(report["trust_unlock_path"]["status"], "blocked_missing_slots");
    assert_eq!(report["slot_bindings"][0]["source"], "missing");
    assert_eq!(report["slot_bindings"][0]["binary"], Value::Null);
    let lookup_order = report["trust_unlock_path"]["lookup_order"]
        .as_array()
        .expect("lookup order should be array");
    assert!(
        lookup_order.iter().all(|entry| entry["kind"] != "path"),
        "Trust lookup order must not advertise PATH fallback: {lookup_order:?}"
    );
}

#[test]
#[cfg(unix)]
fn program_index_upstream_slot_is_the_pinned_oracle_never_path_rustc() {
    // STOCK-AS-ORACLE (docs/DECISION_QUEUE.md D16): an unoverridden
    // upstream-rustc slot binds rustup's pinned toolchain only. A PATH `rustc`
    // (on an aterm host, the reroute stub) must not bind it, the lookup must
    // never let rustup install the toolchain, and an absent oracle is an
    // explicit NOT RUN, never a pass.
    let temp = TempDir::new("trust-program-index-path-rustc");
    let root = temp.path().join("repo");
    write_program_index_fixture(&root);
    let index = root.join("examples/bench/program_index/index.json");
    let oracle = temp.path().join("oracle-bin/rustc");
    write_fake_compiler(&oracle);

    // (no rustup on PATH | rustup without the toolchain) x (--require-slots)
    for (rustup_has_oracle, require_slots) in
        [(None, false), (None, true), (Some(false), false), (Some(false), true)]
    {
        let case = format!("{rustup_has_oracle:?}-{require_slots}");
        let path_dir = temp.path().join(format!("path-{case}"));
        write_fake_compiler(&path_dir.join("rustc"));
        let rustup_log = temp.path().join(format!("rustup-{case}.log"));
        if let Some(has) = rustup_has_oracle {
            write_fake_rustup(
                &path_dir.join("rustup"),
                &rustup_log,
                has.then_some(oracle.as_path()),
            );
        }
        let report_dir = temp.path().join(format!("report-{case}"));
        let mut command = program_index_upstream_command(&root, &index, &report_dir, &path_dir);
        if require_slots {
            command.arg("--require-slots");
        }
        let output = command.output().expect("run with PATH-only rustc");
        let (report, stderr) = read_program_index_report(&output, &report_dir);
        assert_eq!(report["slot_bindings"][0]["source"], "oracle-not-installed", "{case}");
        assert_eq!(report["slot_bindings"][0]["binary"], Value::Null, "{case}");
        let rows = report["results"].as_array().expect("rows should be array");
        assert!(!rows.is_empty());
        assert!(rows.iter().all(|row| row["outcome"] == "skipped"), "{case}");
        if require_slots {
            assert_eq!(output.status.code(), Some(2), "{case} stderr:\n{stderr}");
            assert!(
                stderr.contains("upstream-rustc: NOT RUN: oracle 1.97.1 not installed"),
                "{case} stderr:\n{stderr}"
            );
        } else {
            assert!(
                rows.iter().all(|row| row["skip_reason"] == "NOT RUN: oracle 1.97.1 not installed"),
                "{case} rows: {rows:?}"
            );
        }
        if rustup_has_oracle.is_some() {
            assert_eq!(
                fs::read_to_string(&rustup_log).expect("rustup should have been asked"),
                "which --toolchain 1.97.1 rustc|RUSTUP_AUTO_INSTALL=0\n",
                "{case}"
            );
        }
    }

    // rustup with the toolchain: the slot binds what `rustup which` names.
    let path_dir = temp.path().join("path-installed");
    write_fake_compiler(&path_dir.join("rustc"));
    let rustup_log = temp.path().join("rustup-installed.log");
    write_fake_rustup(&path_dir.join("rustup"), &rustup_log, Some(&oracle));
    let report_dir = temp.path().join("report-installed");
    let output = program_index_upstream_command(&root, &index, &report_dir, &path_dir)
        .arg("--dry-run")
        .output()
        .expect("run with the pinned oracle installed");
    let (report, stderr) = read_program_index_report(&output, &report_dir);
    assert_eq!(output.status.code(), Some(0), "stderr:\n{stderr}");
    assert_eq!(report["slot_bindings"][0]["source"], "rustup:1.97.1");
    assert_eq!(report["slot_bindings"][0]["binary"], oracle.to_str().expect("oracle is utf-8"));
    assert_eq!(
        fs::read_to_string(&rustup_log).expect("rustup should have been asked"),
        "which --toolchain 1.97.1 rustc|RUSTUP_AUTO_INSTALL=0\n"
    );
}

#[cfg(unix)]
fn program_index_upstream_command(
    root: &Path,
    index: &Path,
    report_dir: &Path,
    path_dir: &Path,
) -> Command {
    let mut command = Command::new(targo_trust_binary());
    command
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
        ])
        .env("PATH", path_dir);
    command
}

#[cfg(unix)]
fn read_program_index_report(output: &std::process::Output, report_dir: &Path) -> (Value, String) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let report =
        serde_json::from_str(&fs::read_to_string(report_dir.join("report.json")).unwrap_or_else(
            |error| panic!("report should exist ({error})\nstdout:\n{stdout}\nstderr:\n{stderr}"),
        ))
        .expect("report should parse");
    (report, stderr)
}

/// A `rustup` that logs its arguments and `RUSTUP_AUTO_INSTALL`, then answers
/// `which` with `oracle` (exit 0) or, without one, as a missing toolchain.
#[cfg(unix)]
fn write_fake_rustup(path: &Path, log: &Path, oracle: Option<&Path>) {
    use std::os::unix::fs::PermissionsExt;

    let answer = match oracle {
        Some(oracle) => format!("printf '%s\\n' '{}'", oracle.display()),
        None => "echo \"error: toolchain '1.97.1' is not installed\" >&2; exit 1".to_string(),
    };
    write(
        path.to_path_buf(),
        &format!(
            "#!/bin/sh\nprintf '%s|RUSTUP_AUTO_INSTALL=%s\\n' \"$*\" \"${{RUSTUP_AUTO_INSTALL-unset}}\" >> '{}'\n{answer}\n",
            log.display()
        ),
    );
    let mut permissions = fs::metadata(path).expect("fake rustup metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake rustup permissions");
}

#[test]
#[cfg(unix)]
fn program_index_trust_slot_override_must_be_absolute() {
    let temp = TempDir::new("trust-program-index-relative-trustc");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let path_dir = temp.path().join("path-bin");
    let path_trustc = path_dir.join("trustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&path_trustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--slot-bin",
            "trust-verify=trustc",
            "--require-slots",
        ])
        .env("PATH", &path_dir)
        .output()
        .expect("run with relative Trust slot override");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "relative Trust slot override must not resolve through PATH\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["required_slots"]["missing"][0], "trust-verify");
    assert_eq!(report["slot_bindings"][0]["source"], "invalid-relative-override");
    assert_eq!(report["slot_bindings"][0]["binary"], Value::Null);
}

#[test]
#[cfg(unix)]
fn program_index_rejects_trust_binary_as_upstream_rustc_baseline() {
    let temp = TempDir::new("trust-program-index-upstream-trustc");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let trustc = root.join("build/host/stage2/bin/trustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&trustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", trustc.display()),
            "--program",
            "sample.good",
            "--require-slots",
            "--dry-run",
        ])
        .output()
        .expect("run with Trust compiler as upstream slot");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "Trust-owned upstream baseline should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "blocked");
    let blockers = report["summary"]["upstream_baseline"]["blockers"]
        .as_array()
        .expect("blockers should be array")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(blockers.iter().any(|blocker| blocker.contains("stage2")));
    assert!(blockers.iter().any(|blocker| blocker.contains("Trust-owned")));
}

#[test]
#[cfg(unix)]
fn program_index_rejects_failing_upstream_rustc_identity_probe() {
    let temp = TempDir::new("trust-program-index-upstream-failing-probe");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let rustc = temp.path().join("rustc");
    write_program_index_fixture(&root);
    write_fake_compiler_with_failing_identity_probe(&rustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", rustc.display()),
            "--program",
            "sample.good",
            "--require-slots",
            "--dry-run",
        ])
        .output()
        .expect("run with failing upstream identity probe");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "failing upstream baseline probe should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "blocked");
    let blockers = report["summary"]["upstream_baseline"]["blockers"]
        .as_array()
        .expect("blockers should be array")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(blockers.iter().any(|blocker| blocker.contains("-vV probe must succeed")));
    assert!(blockers.iter().any(|blocker| blocker.contains("--print sysroot probe must succeed")));
}

#[test]
#[cfg(unix)]
fn program_index_rejects_successful_non_rustc_upstream_identity_probe() {
    let temp = TempDir::new("trust-program-index-upstream-non-rustc-probe");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let rustc = temp.path().join("rustc");
    write_program_index_fixture(&root);
    write_fake_compiler_with_non_rustc_identity_probe(&rustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", rustc.display()),
            "--program",
            "sample.good",
            "--require-slots",
            "--dry-run",
        ])
        .output()
        .expect("run with non-rustc upstream identity probe");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "non-rustc upstream identity should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "blocked");
    let blockers = report["summary"]["upstream_baseline"]["blockers"]
        .as_array()
        .expect("blockers should be array")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(blockers.iter().any(|blocker| blocker.contains("binary: rustc")));
    assert!(blockers.iter().any(|blocker| blocker.contains("commit-hash")));
}

#[test]
#[cfg(unix)]
fn program_index_rejects_timing_out_upstream_rustc_identity_probe() {
    let temp = TempDir::new("trust-program-index-upstream-timeout-probe");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let rustc = temp.path().join("rustc");
    write_program_index_fixture(&root);
    write_fake_compiler_with_timing_out_identity_probe(&rustc);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", rustc.display()),
            "--program",
            "sample.good",
            "--require-slots",
            "--dry-run",
        ])
        .output()
        .expect("run with timing-out upstream identity probe");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "timing-out upstream baseline probe should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "blocked");
    let entry = report["summary"]["upstream_baseline"]["entries"][0].clone();
    assert_eq!(entry["version_probe"]["status"], "timeout");
    assert_eq!(entry["sysroot_probe"]["status"], "available");
    let blockers = entry["blockers"]
        .as_array()
        .expect("blockers should be array")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(blockers.iter().any(|blocker| blocker.contains("-vV probe must succeed")));
}

#[test]
#[cfg(unix)]
fn program_index_identity_probe_timeout_kills_process_group() {
    let temp = TempDir::new("trust-program-index-upstream-timeout-process-group");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let rustc = temp.path().join("rustc");
    write_program_index_fixture(&root);
    write_fake_compiler_with_persistent_identity_probe_child(&rustc);

    let index = root.join("examples/bench/program_index/index.json");
    let started = Instant::now();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "upstream-rustc",
            "--slot-bin",
            &format!("upstream-rustc={}", rustc.display()),
            "--program",
            "sample.good",
            "--require-slots",
            "--dry-run",
        ])
        .output()
        .expect("run with timing-out upstream identity probe child");
    let elapsed = started.elapsed();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "timing-out upstream baseline probe should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        elapsed < Duration::from_secs(15),
        "identity probe timeout should kill the process group promptly, took {elapsed:?}"
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["upstream_baseline"]["status"], "blocked");
    assert_eq!(
        report["summary"]["upstream_baseline"]["entries"][0]["version_probe"]["status"],
        "timeout"
    );
}

#[test]
#[cfg(unix)]
fn backward_pass_requires_counterexample_or_repair_payload() {
    let temp = TempDir::new("trust-program-index-backward-payload");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc-no-counterexample");
    write_program_index_fixture(&root);
    write_fake_compiler_without_counterexample(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run fake verifier without backward payload");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "missing backward payload should make backward_pass partial\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    let flawed = report["results"]
        .as_array()
        .expect("rows")
        .iter()
        .find(|row| row["program_id"] == "sample.flawed")
        .expect("flawed row");
    assert_eq!(flawed["observed"], "verify_fail");
    assert_eq!(flawed["backward_pass"]["observed"], "missing_backward_payload");
    assert_eq!(flawed["backward_pass"]["evidence"], "missing_or_mismatched");
    assert_eq!(report["summary"]["backward_pass"]["status"], "partial");
}

#[test]
#[cfg(unix)]
fn transport_is_parsed_after_large_stderr_prefix() {
    let temp = TempDir::new("trust-program-index-tail-transport");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc-tail-transport");
    write_program_index_fixture(&root);
    write_fake_compiler_with_tail_transport(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.flawed",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run tail transport fake verifier");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "tail transport should be parsed beyond capture head\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    let row = &report["results"][0];
    assert_eq!(row["observed"], "verify_fail");
    assert_eq!(row["transport"]["failed"], 1);
    assert_eq!(row["transport"]["counterexamples"], 1);
    assert!(row["stderr_tail_excerpt"].as_str().expect("tail excerpt").contains("TRUST_JSON:"));
}

#[test]
#[cfg(unix)]
fn unsupported_mir_without_explicit_gap_fails_trust_verify_row() {
    let temp = TempDir::new("trust-program-index-unsupported-mir-fail");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc-unsupported-mir");
    write_program_index_fixture(&root);
    write_fake_verifier_with_unsupported_mir_verify_pass(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run unsupported MIR fake verifier");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "unsupported MIR should fail without an explicit expected gap\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("unsupported_mir=failed"));
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    let row = &report["results"][0];
    assert_eq!(row["observed"], "verify_pass");
    assert_eq!(row["outcome"], "failed");
    assert_eq!(row["classification"], "regression");
    assert_eq!(
        row["classification_reason"],
        "trust-verify emitted unsupported MIR for a supported program-index row"
    );
    assert_eq!(row["unsupported_mir_gate_status"], "failed");
    assert_eq!(
        report["summary"]["unsupported_mir_gate"]["schema"],
        "trust.program-index.unsupported-mir-gate.v1"
    );
    assert_eq!(report["summary"]["unsupported_mir_gate"]["status"], "failed");
    assert_eq!(report["summary"]["unsupported_mir_gate"]["unsupported_rows"], 1);
    assert_eq!(report["summary"]["unsupported_mir_gate"]["failed"], 1);
    assert_eq!(
        report["summary"]["unsupported_mir_gate"]["failed_rows"][0]["program_id"],
        "sample.good"
    );
}

#[test]
#[cfg(unix)]
fn unsupported_mir_is_allowed_only_by_explicit_expected_gap_signature() {
    let temp = TempDir::new("trust-program-index-unsupported-mir-gap");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc-unsupported-mir-no-transport");
    write_program_index_fixture_with_expected_known_gap(
        &root,
        "unsupported-mir-good",
        r#"{
      "id": "unsupported-mir-good",
      "slot": "trust-verify",
      "program_id": "sample.good",
      "observed": ["verify_no_transport"],
      "stderr_contains_any": ["unsupported MIR"],
      "reason": "known unsupported MIR coverage gap"
    }"#,
    );
    write_fake_verifier_with_unsupported_mir_no_transport(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.good",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run expected unsupported MIR fake verifier");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "explicit unsupported MIR expected gap should be allowed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    let row = &report["results"][0];
    assert_eq!(row["observed"], "verify_no_transport");
    assert_eq!(row["outcome"], "excepted");
    assert_eq!(row["classification"], "expected-known-gap");
    assert_eq!(row["expected_known_gap_id"], "unsupported-mir-good");
    assert_eq!(row["unsupported_mir_gate_status"], "allowed_expected_gap");
    assert_eq!(report["summary"]["unsupported_mir_gate"]["status"], "passed_with_expected_gaps");
    assert_eq!(
        report["summary"]["unsupported_mir_gate"]["allowed_rows"][0]["program_id"],
        "sample.good"
    );
}

#[test]
#[cfg(unix)]
fn expected_known_gap_only_applies_to_hooked_programs() {
    let temp = TempDir::new("trust-program-index-gap-hooks");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc-unsupported-mir-no-transport");
    write_program_index_fixture_with_expected_known_gap(
        &root,
        "generic-unsupported-mir-gap",
        r#"{
      "id": "generic-unsupported-mir-gap",
      "slot": "trust-verify",
      "observed": ["verify_no_transport"],
      "stderr_contains_any": ["unsupported MIR"],
      "reason": "known unsupported MIR coverage gap for the hooked good row only"
    }"#,
    );
    write_fake_verifier_with_unsupported_mir_no_transport(&fake);

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.flawed",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run unhooked expected gap row");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "unhooked expected gap must not except sample.flawed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    let row = &report["results"][0];
    assert_eq!(row["program_id"], "sample.flawed");
    assert_eq!(row["outcome"], "failed");
    assert_eq!(row["classification"], "regression");
    assert!(row.get("expected_known_gap_id").is_none());
}

#[test]
#[cfg(unix)]
fn expected_known_gap_rejects_verify_pass_observed_value() {
    let temp = TempDir::new("trust-program-index-gap-verify-pass");
    let root = temp.path().join("repo");
    write_program_index_fixture_with_expected_known_gap(
        &root,
        "bad-verify-pass-gap",
        r#"{
      "id": "bad-verify-pass-gap",
      "slot": "trust-verify",
      "program_id": "sample.good",
      "observed": ["verify_pass"],
      "stderr_contains_any": ["UnsupportedMir"],
      "reason": "invalid expected gap"
    }"#,
    );

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--slots",
            "trust-verify",
            "--list",
        ])
        .output()
        .expect("run invalid expected gap index");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "verify_pass expected gap should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("verify_pass must remain a regression"));
}

#[test]
#[cfg(unix)]
fn repair_evidence_report_is_validated() {
    let temp = TempDir::new("trust-program-index-repair-validation");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);
    write_valid_repair_report(&report_dir.join("repair-e2e/repair-proof-improvement.json"));

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.flawed",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run with valid repair report");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["repair_evidence"]["status"], "real_e2e_report_validated");
    assert_eq!(
        report["summary"]["repair_evidence"]["validation_errors"]
            .as_array()
            .expect("validation errors")
            .len(),
        0
    );
}

#[test]
#[cfg(unix)]
fn repair_evidence_report_rejects_unvalidated_artifact() {
    let temp = TempDir::new("trust-program-index-repair-invalid");
    let root = temp.path().join("repo");
    let report_dir = temp.path().join("report");
    let fake = temp.path().join("fake-rustc");
    write_program_index_fixture(&root);
    write_fake_compiler(&fake);
    write(
        report_dir.join("repair-e2e/repair-proof-improvement.json"),
        r#"{"schema":"trust.repair-e2e.proof-improvement.v1","improvement":{"improved":false}}"#,
    );

    let index = root.join("examples/bench/program_index/index.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "benchmark",
            "program-index",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--index",
            index.to_str().expect("index should be utf-8"),
            "--report-dir",
            report_dir.to_str().expect("report dir should be utf-8"),
            "--slots",
            "trust-verify",
            "--program",
            "sample.flawed",
            "--slot-bin",
            &format!("trust-verify={}", fake.display()),
            "--require-slots",
        ])
        .output()
        .expect("run with invalid repair report");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let report: Value = serde_json::from_str(
        &fs::read_to_string(report_dir.join("report.json")).expect("report should exist"),
    )
    .expect("report should parse");
    assert_eq!(report["summary"]["repair_evidence"]["status"], "artifact_present_unvalidated");
    assert!(
        !report["summary"]["repair_evidence"]["validation_errors"]
            .as_array()
            .expect("validation errors")
            .is_empty()
    );
}

fn command_contains_incremental_arg(command: &Value) -> bool {
    let args: Vec<&str> = command
        .as_array()
        .expect("command should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("command args should be strings"))
        .collect();
    args.contains(&"-C") && args.iter().any(|arg| arg.starts_with("incremental="))
}

fn assert_compile_resource_usage_evidence(row: &Value) {
    let label = format!(
        "{}:{}",
        row["program_id"].as_str().unwrap_or("unknown-program"),
        row["slot"].as_str().unwrap_or("unknown-slot")
    );
    let duration_seconds = row["duration_seconds"]
        .as_f64()
        .unwrap_or_else(|| panic!("{label}: duration_seconds must be numeric"));
    assert!(
        duration_seconds > 0.0,
        "{label}: duration_seconds must be positive, got {duration_seconds}"
    );

    let usage = row["resource_usage"]
        .as_object()
        .unwrap_or_else(|| panic!("{label}: resource_usage must be an object"));
    assert_eq!(
        usage.get("source").and_then(Value::as_str),
        Some("os.wait4"),
        "{label}: resource_usage should come from wait4 on unix"
    );
    let elapsed_seconds = usage
        .get("elapsed_seconds")
        .and_then(Value::as_f64)
        .unwrap_or_else(|| panic!("{label}: resource_usage.elapsed_seconds must be numeric"));
    assert!(
        elapsed_seconds > 0.0,
        "{label}: resource_usage.elapsed_seconds must be positive, got {elapsed_seconds}"
    );
    assert!(
        (duration_seconds - elapsed_seconds).abs() <= f64::EPSILON,
        "{label}: duration_seconds {duration_seconds} must match resource_usage.elapsed_seconds {elapsed_seconds}"
    );

    let peak_rss_bytes = row["peak_rss_bytes"]
        .as_i64()
        .unwrap_or_else(|| panic!("{label}: peak_rss_bytes must be an integer"));
    assert!(peak_rss_bytes > 0, "{label}: peak_rss_bytes must be positive, got {peak_rss_bytes}");
    let resource_peak_rss_bytes = usage
        .get("peak_rss_bytes")
        .and_then(Value::as_i64)
        .unwrap_or_else(|| panic!("{label}: resource_usage.peak_rss_bytes must be an integer"));
    assert!(
        resource_peak_rss_bytes > 0,
        "{label}: resource_usage.peak_rss_bytes must be positive, got {resource_peak_rss_bytes}"
    );
    assert_eq!(
        peak_rss_bytes, resource_peak_rss_bytes,
        "{label}: peak_rss_bytes must match resource_usage.peak_rss_bytes"
    );
}

fn assert_sample_aggregation_evidence(row: &Value, expected_count: u64) {
    let label = format!(
        "{}:{}",
        row["program_id"].as_str().unwrap_or("unknown-program"),
        row["slot"].as_str().unwrap_or("unknown-slot")
    );
    assert_eq!(
        row["requested_repetitions"].as_u64(),
        Some(expected_count),
        "{label}: requested_repetitions should match"
    );
    assert_eq!(
        row["sample_count"].as_u64(),
        Some(expected_count),
        "{label}: sample_count should match"
    );
    let samples =
        row["samples"].as_array().unwrap_or_else(|| panic!("{label}: samples must be an array"));
    assert_eq!(samples.len() as u64, expected_count, "{label}: samples length should match");
    for (index, sample) in samples.iter().enumerate() {
        assert_eq!(sample["sample_index"].as_u64(), Some((index + 1) as u64));
        assert_eq!(sample["outcome"], "passed", "{label}: sample should pass");
        assert!(
            sample["duration_seconds"].as_f64().is_some_and(|value| value > 0.0),
            "{label}: sample duration should be positive"
        );
        assert!(
            sample["resource_usage"]["elapsed_seconds"].as_f64().is_some_and(|value| value > 0.0),
            "{label}: sample resource elapsed time should be positive"
        );
        assert_eq!(
            sample["peak_rss_bytes"], sample["resource_usage"]["peak_rss_bytes"],
            "{label}: sample peak RSS should match sample resource usage"
        );
    }

    let aggregation = &row["sample_aggregation"];
    assert_eq!(aggregation["status"], "aggregated", "{label}: sample aggregation status");
    assert_eq!(
        aggregation["sample_count"].as_u64(),
        Some(expected_count),
        "{label}: aggregation sample_count"
    );
    assert!(
        aggregation["representative_sample_index"]
            .as_u64()
            .is_some_and(|value| (1..=expected_count).contains(&value)),
        "{label}: representative_sample_index should point at a collected sample"
    );
    assert_eq!(
        aggregation["aggregate_field_policy"]["duration_seconds"].as_str(),
        Some("median"),
        "{label}: duration aggregation policy should be median"
    );
    assert_eq!(
        aggregation["aggregate_field_policy"]["peak_rss_bytes"].as_str(),
        Some("max"),
        "{label}: peak RSS aggregation policy should be max"
    );
    assert_eq!(
        aggregation["duration_seconds"]["count"].as_u64(),
        Some(expected_count),
        "{label}: duration stats count"
    );
    for key in ["median", "p50", "min", "max", "stdev"] {
        assert!(
            aggregation["duration_seconds"][key].as_f64().is_some(),
            "{label}: duration stats should include {key}"
        );
    }
    assert_eq!(
        aggregation["peak_rss_bytes"]["count"].as_u64(),
        Some(expected_count),
        "{label}: RSS stats count"
    );
    for key in ["median", "p50", "min", "max", "stdev"] {
        assert!(
            aggregation["peak_rss_bytes"][key].as_f64().is_some()
                || aggregation["peak_rss_bytes"][key].as_i64().is_some(),
            "{label}: RSS stats should include {key}"
        );
    }
    assert_eq!(
        row["resource_usage"]["aggregation"]["sample_count"].as_u64(),
        Some(expected_count),
        "{label}: resource_usage aggregation sample_count"
    );
}

fn write_program_index_proof_design_fixture(root: &Path) {
    write(root.join("examples/proof_good.rs"), "fn main() { println!(\"same output\"); }\n");
    write(root.join("examples/proof_flawed.rs"), "fn main() { println!(\"same output\"); }\n");
    write(root.join("examples/candidate_good.rs"), "fn main() { println!(\"same output\"); }\n");
    write(root.join("examples/candidate_flawed.rs"), "fn main() { println!(\"same output\"); }\n");
    write(
        root.join("examples/bench/program_index/index.json"),
        r#"{
  "schema": "trust.compile-verify-program-index.v1",
  "version": 1,
  "suite_evidence_model": {
    "schema": "trust.compile-verify-program-index.suite-evidence.v1",
    "gating_suites": ["proof-design"],
    "candidate_suites": ["proof-design-candidates"]
  },
  "expectation_model": {
    "default_by_variant": {
      "good": {"backward_pass": {"expected": "no_repair_needed"}},
      "flawed": {"backward_pass": {"expected": "counterexample_or_repair_candidate"}}
    }
  },
  "programs": [
    {
      "id": "proof_gate.good",
      "pair_id": "proof_gate",
      "variant": "good",
      "path": "examples/proof_good.rs",
      "obligations": ["division_by_zero"],
      "suite": "proof-design",
      "metadata": {
        "proof_design": true,
        "formatter_free": true
      }
    },
    {
      "id": "proof_gate.flawed",
      "pair_id": "proof_gate",
      "variant": "flawed",
      "path": "examples/proof_flawed.rs",
      "obligations": ["division_by_zero"],
      "suite": "proof-design",
      "metadata": {
        "proof_design": true,
        "formatter_free": true
      }
    },
    {
      "id": "candidate_gate.good",
      "pair_id": "candidate_gate",
      "variant": "good",
      "path": "examples/candidate_good.rs",
      "obligations": ["adt_control_flow"],
      "suite": "proof-design-candidates",
      "metadata": {
        "proof_design": true,
        "candidate": true,
        "formatter_free": true
      }
    },
    {
      "id": "candidate_gate.flawed",
      "pair_id": "candidate_gate",
      "variant": "flawed",
      "path": "examples/candidate_flawed.rs",
      "obligations": ["adt_control_flow"],
      "suite": "proof-design-candidates",
      "metadata": {
        "proof_design": true,
        "candidate": true,
        "formatter_free": true
      }
    }
  ],
  "expected_known_gaps": []
}
"#,
    );
    commit_proof_design_fixture(root);
}

fn commit_proof_design_fixture(root: &Path) {
    let status =
        Command::new("git").args(["init", "-q"]).current_dir(root).status().expect("git init");
    assert!(status.success(), "git init failed");
    let status =
        Command::new("git").args(["add", "examples"]).current_dir(root).status().expect("git add");
    assert!(status.success(), "git add failed");
    let status = Command::new("git")
        .args([
            "-c",
            "user.name=Proof Design Test",
            "-c",
            "user.email=proof-design@example.invalid",
            "commit",
            "-qm",
            "fixture",
        ])
        .current_dir(root)
        .status()
        .expect("git commit");
    assert!(status.success(), "git commit failed");
}

fn write_program_index_fixture(root: &Path) {
    write(root.join("examples/good.rs"), "fn main() { println!(\"same output\"); }\n");
    write(root.join("examples/flawed.rs"), "fn main() { println!(\"same output\"); }\n");
    write(
        root.join("examples/bench/program_index/index.json"),
        r#"{
  "schema": "trust.compile-verify-program-index.v1",
  "version": 1,
  "expectation_model": {
    "default_by_variant": {
      "good": {"backward_pass": {"expected": "no_repair_needed"}},
      "flawed": {"backward_pass": {"expected": "counterexample_or_repair_candidate"}}
    }
  },
  "programs": [
    {
      "id": "sample.good",
      "pair_id": "sample",
      "variant": "good",
      "path": "examples/good.rs",
      "obligations": ["division_by_zero"],
      "suite": "unit"
    },
    {
      "id": "sample.flawed",
      "pair_id": "sample",
      "variant": "flawed",
      "path": "examples/flawed.rs",
      "obligations": ["division_by_zero"],
      "suite": "unit"
    }
  ],
  "expected_known_gaps": []
}
"#,
    );
}

fn write_program_index_fixture_with_expected_known_gap(root: &Path, hook_id: &str, gap: &str) {
    write(root.join("examples/good.rs"), "fn main() { println!(\"same output\"); }\n");
    write(root.join("examples/flawed.rs"), "fn main() { println!(\"same output\"); }\n");
    let index = r#"{
  "schema": "trust.compile-verify-program-index.v1",
  "version": 1,
  "expectation_model": {
    "default_by_variant": {
      "good": {"backward_pass": {"expected": "no_repair_needed"}},
      "flawed": {"backward_pass": {"expected": "counterexample_or_repair_candidate"}}
    },
    "program_exception_hooks": {
      "sample.good": ["__HOOK_ID__"]
    }
  },
  "programs": [
    {
      "id": "sample.good",
      "pair_id": "sample",
      "variant": "good",
      "path": "examples/good.rs",
      "obligations": ["division_by_zero"],
      "suite": "unit"
    },
    {
      "id": "sample.flawed",
      "pair_id": "sample",
      "variant": "flawed",
      "path": "examples/flawed.rs",
      "obligations": ["division_by_zero"],
      "suite": "unit"
    }
  ],
  "expected_known_gaps": [
    __GAP__
  ]
}
"#
    .replace("__HOOK_ID__", hook_id)
    .replace("__GAP__", gap);
    write(root.join("examples/bench/program_index/index.json"), &index);
}

#[cfg(unix)]
fn write_fake_compiler(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    let proved_result = publication_transport::proved_result(
        trust_types::VcKind::DivisionByZero,
        "fixture::main",
        "program-index-request",
        "program-index-proof",
    );
    let failed_result = publication_transport::failed_result(
        "division_by_zero",
        "fixture",
        "fixture::main",
        "program-index-request",
        "program-index-failure",
        "den = 0",
    );
    let proved_result = serde_json::to_string(&proved_result).expect("serialize proved transport");
    let failed_result = serde_json::to_string(&failed_result).expect("serialize failed transport");
    assert!(!proved_result.contains('\'') && !failed_result.contains('\''));
    let script = r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    printf 'rustc 1.95.0 (fake)\nbinary: rustc\ncommit-hash: 59807616e1fa2540724bfbac14d7976d7e4a3860\nhost: aarch64-apple-darwin\nrelease: 1.95.0\n'
    exit 0
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf '/opt/upstream-rust/sysroot\n'
      exit 0
    fi
    ;;
esac
out=""
prev=""
src=""
is_verify=0
is_link=0
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then
    out="$arg"
  fi
  case "$arg" in
    *trust-verify-output=json*) is_verify=1 ;;
    --emit=link) is_link=1 ;;
  esac
  prev="$arg"
  src="$arg"
done
mkdir -p "$(dirname "$out")"
if [ "$is_link" = "1" ]; then
  printf '#!/bin/sh\nprintf "same output\\n"\n' > "$out"
  chmod +x "$out"
else
  printf 'fake object' > "$out"
fi
if [ "$is_verify" = "1" ]; then
  case "$src" in
    *flawed*) proved=0; failed=1; outcome=failed ;;
    *) proved=1; failed=0; outcome=proved ;;
  esac
  if [ "$failed" = "1" ]; then
    printf 'TRUST_JSON:{"type":"function_result","function":"fixture::main","results":[__FAILED_RESULT__],"proved":0,"failed":1,"unknown":0,"runtime_checked":0,"total":1}\n' >&2
  else
    printf 'TRUST_JSON:{"type":"function_result","function":"fixture::main","results":[__PROVED_RESULT__],"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"total":1}\n' >&2
  fi
fi
"#
    .replace("__PROVED_RESULT__", &proved_result)
    .replace("__FAILED_RESULT__", &failed_result);
    write(path.to_path_buf(), &script);
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_observing_compiler(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    printf 'rustc 1.95.0 (fake)\nbinary: rustc\ncommit-hash: 59807616e1fa2540724bfbac14d7976d7e4a3860\nhost: aarch64-apple-darwin\nrelease: 1.95.0\n'
    exit 0
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf '/opt/upstream-rust/sysroot\n'
      exit 0
    fi
    ;;
esac
out=""
src=""
prev=""
link=0
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then out="$arg"; fi
  if [ "$arg" = "--emit=link" ]; then link=1; fi
  prev="$arg"
  src="$arg"
done
printf 'mid-run edit\n' > "$TEST_LIVE_SOURCE"
if cmp -s "$src" "$TEST_EXPECTED_SOURCE"; then
  matched=1
else
  matched=0
fi
cp "$TEST_EXPECTED_SOURCE" "$TEST_LIVE_SOURCE"
printf '%s|%s\n' "$src" "$matched" >> "$TEST_SEEN_SOURCES"
mkdir -p "$(dirname "$out")"
if [ "$link" = 1 ]; then
  printf '#!/bin/sh\nprintf "same output\\n"\n' > "$out"
  chmod +x "$out"
else
  printf 'fake object' > "$out"
fi
"#,
    );
    let mut permissions = fs::metadata(path).expect("observing compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("observing compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_with_failing_identity_probe(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    printf 'broken version probe\n' >&2
    exit 42
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf 'broken sysroot probe\n' >&2
      exit 43
    fi
    ;;
esac
printf 'fake object\n'
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_with_non_rustc_identity_probe(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    printf 'trustc 1.95.0 (fake)\nbinary: trustc\ncommit-hash: short\nhost: aarch64-apple-darwin\nrelease: 1.95.0\n'
    exit 0
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf '/opt/upstream-rust/sysroot\n'
      exit 0
    fi
    ;;
esac
printf 'fake object\n'
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_with_timing_out_identity_probe(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    sleep 30
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf '/opt/upstream-rust/sysroot\n'
      exit 0
    fi
    ;;
esac
printf 'fake object\n'
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_with_persistent_identity_probe_child(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
case "${1:-}" in
  -vV)
    sleep 30 &
    wait
    ;;
  --print)
    if [ "${2:-}" = "sysroot" ]; then
      printf '/opt/upstream-rust/sysroot\n'
      exit 0
    fi
    ;;
esac
printf 'fake object\n'
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_verifier_with_unsupported_mir_verify_pass(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
out=""
prev=""
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then
    out="$arg"
  fi
  prev="$arg"
done
mkdir -p "$(dirname "$out")"
printf 'fake object' > "$out"
printf 'error: UnsupportedMir in fake verifier path\n' >&2
printf 'TRUST_JSON:{"type":"function_result","function":"fixture::main","results":[{"kind":"division_by_zero","description":"fixture","outcome":"proved","solver":"fake","time_ms":1}],"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"total":1}\n' >&2
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_verifier_with_unsupported_mir_no_transport(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
out=""
prev=""
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then
    out="$arg"
  fi
  prev="$arg"
done
mkdir -p "$(dirname "$out")"
printf 'fake object' > "$out"
printf 'error: unsupported MIR in fake verifier path\n' >&2
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_without_counterexample(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
out=""
prev=""
src=""
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then
    out="$arg"
  fi
  prev="$arg"
  src="$arg"
done
mkdir -p "$(dirname "$out")"
printf 'fake object' > "$out"
case "$src" in
  *flawed*) printf 'TRUST_JSON:{"type":"function_result","function":"fixture::main","results":[{"kind":"division_by_zero","description":"fixture","outcome":"failed","solver":"fake","time_ms":1}],"proved":0,"failed":1,"unknown":0,"runtime_checked":0,"total":1}\n' >&2 ;;
  *) printf 'TRUST_JSON:{"type":"function_result","function":"fixture::main","results":[{"kind":"division_by_zero","description":"fixture","outcome":"proved","solver":"fake","time_ms":1}],"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"total":1}\n' >&2 ;;
esac
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

#[cfg(unix)]
fn write_fake_compiler_with_tail_transport(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    write(
        path.to_path_buf(),
        r#"#!/bin/sh
set -eu
out=""
prev=""
for arg in "$@"; do
  if [ "$prev" = "-o" ]; then
    out="$arg"
  fi
  prev="$arg"
done
mkdir -p "$(dirname "$out")"
printf 'fake object' > "$out"
head -c 2100000 /dev/zero | tr '\0' 'x' >&2
printf '\nTRUST_JSON:{"type":"function_result","function":"fixture::main","results":[{"kind":"division_by_zero","description":"fixture","outcome":"failed","solver":"fake","time_ms":1,"counterexample":"den = 0"}],"proved":0,"failed":1,"unknown":0,"runtime_checked":0,"total":1}\n' >&2
"#,
    );
    let mut permissions = fs::metadata(path).expect("fake compiler metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("fake compiler permissions");
}

fn write_valid_repair_report(path: &Path) {
    write(
        path.to_path_buf(),
        r#"{
  "schema": "trust.repair-e2e.proof-improvement.v1",
  "before": {
    "divzero_counterexamples": ["fixture::main: den = 0"]
  },
  "improvement": {
    "proved_delta": 1,
    "failed_delta": -1,
    "divzero_proved_delta": 1,
    "divzero_failed_delta": -1,
    "improved": true
  }
}
"#,
    );
}

fn write(path: PathBuf, text: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("parent should be creatable");
    }
    fs::write(path, text).expect("file should be writable");
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }

    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
        fs::create_dir_all(&path).expect("temporary directory should be creatable");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
