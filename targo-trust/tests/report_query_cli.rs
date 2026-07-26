use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};

#[test]
fn report_query_cli_exposes_timeout_in_json_and_terminal_output() {
    let temp = TempDir::new("targo-trust-report-query-timeout");
    let report_path = temp.path().join("report.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&timeout_report()).expect("serialize timeout report"),
    )
    .expect("write timeout report fixture");

    let json_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "slow", "--json"])
        .output()
        .expect("run report-query --json");
    let stdout = String::from_utf8_lossy(&json_output.stdout);
    let stderr = String::from_utf8_lossy(&json_output.stderr);
    assert_eq!(
        json_output.status.code(),
        Some(1),
        "timeout obligations must fail --require proved\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let value: Value =
        serde_json::from_slice(&json_output.stdout).expect("report-query stdout should be JSON");
    assert_eq!(value["crate_name"], "report-query-timeout-fixture");
    assert_eq!(value["query"]["function"], "slow");
    assert_eq!(value["matches"], 1);
    assert_eq!(value["focused_exit_code"], 1);
    assert_eq!(value["focused_summary"]["total_obligations"], 2);
    assert_eq!(value["focused_summary"]["unknown"], 1);
    assert_eq!(value["focused_summary"]["timed_out"], 1);
    assert_eq!(value["functions"][0]["obligations"][0]["outcome"]["status"], "timeout");
    assert_eq!(value["functions"][0]["obligations"][0]["outcome"]["timeout_ms"], 42_000);
    assert_eq!(value["functions"][0]["obligations"][1]["outcome"]["status"], "unknown");

    let terminal_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "slow"])
        .output()
        .expect("run report-query terminal output");
    let terminal_stdout = String::from_utf8_lossy(&terminal_output.stdout);
    let terminal_stderr = String::from_utf8_lossy(&terminal_output.stderr);
    assert_eq!(
        terminal_output.status.code(),
        Some(1),
        "terminal report-query should preserve timeout failure semantics\nstdout:\n{terminal_stdout}\nstderr:\n{terminal_stderr}"
    );
    assert!(
        terminal_stdout.contains(
            "summary: 0 proved, 0 failed, 0 runtime-checked, 1 unknown, 1 timeout (2 obligations)"
        ),
        "terminal summary should distinguish unknown from timeout\nstdout:\n{terminal_stdout}"
    );
    assert!(
        terminal_stdout.contains(
            "[timeout] arithmetic_overflow: solver timed out before proving bound (ay, 42000ms)"
        ),
        "terminal obligation rows should label timeout obligations\nstdout:\n{terminal_stdout}"
    );
}

#[test]
fn report_query_cli_preserves_summary_timeouts_when_rows_are_missing_or_partial() {
    let temp = TempDir::new("targo-trust-report-query-summary-timeout");
    let report_path = temp.path().join("report.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&summary_timeout_report())
            .expect("serialize summary timeout report"),
    )
    .expect("write summary timeout report fixture");

    let cases = [("summary_only", 2, 1, 1), ("partial", 3, 1, 2)];
    for (function, total_obligations, unknown, timeout) in cases {
        let json_output = Command::new(targo_trust_binary())
            .args(["trust", "report-query", "--report"])
            .arg(&report_path)
            .args(["--function", function, "--json"])
            .output()
            .expect("run report-query --json");
        let stdout = String::from_utf8_lossy(&json_output.stdout);
        let stderr = String::from_utf8_lossy(&json_output.stderr);
        assert_eq!(
            json_output.status.code(),
            Some(1),
            "summary timeout fixtures must fail --require proved for {function}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );

        let value: Value = serde_json::from_slice(&json_output.stdout)
            .expect("report-query stdout should be JSON");
        assert_eq!(value["focused_summary"]["total_obligations"], total_obligations);
        assert_eq!(value["focused_summary"]["unknown"], unknown);
        assert_eq!(value["focused_summary"]["timed_out"], timeout);
    }

    let terminal_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "partial"])
        .output()
        .expect("run report-query terminal output");
    let terminal_stdout = String::from_utf8_lossy(&terminal_output.stdout);
    let terminal_stderr = String::from_utf8_lossy(&terminal_output.stderr);
    assert_eq!(
        terminal_output.status.code(),
        Some(1),
        "partial summary timeout fixture must fail --require proved\nstdout:\n{terminal_stdout}\nstderr:\n{terminal_stderr}"
    );
    assert!(
        terminal_stdout.contains(
            "summary: 0 proved, 0 failed, 0 runtime-checked, 1 unknown, 2 timeouts (3 obligations)"
        ),
        "terminal summary should reconcile summary timeouts with partial rows\nstdout:\n{terminal_stdout}"
    );
}

#[test]
fn report_query_cli_preserves_skipped_and_runtime_checked_splits() {
    let temp = TempDir::new("targo-trust-report-query-skipped-runtime");
    let report_path = temp.path().join("report.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&skipped_runtime_report())
            .expect("serialize skipped/runtime report"),
    )
    .expect("write skipped/runtime report fixture");

    let skipped_json = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "resource_limited", "--json"])
        .output()
        .expect("run report-query skipped --json");
    let stdout = String::from_utf8_lossy(&skipped_json.stdout);
    let stderr = String::from_utf8_lossy(&skipped_json.stderr);
    assert_eq!(
        skipped_json.status.code(),
        Some(1),
        "skipped obligations must fail --require proved\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let value: Value =
        serde_json::from_slice(&skipped_json.stdout).expect("report-query stdout should be JSON");
    assert_eq!(value["focused_summary"]["unknown"], 1);
    assert_eq!(value["focused_summary"]["timed_out"], 1);
    assert_eq!(value["focused_summary"]["skipped"], 1);

    let runtime_json = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "dynamic_guard", "--json"])
        .output()
        .expect("run report-query runtime --json");
    let stdout = String::from_utf8_lossy(&runtime_json.stdout);
    let stderr = String::from_utf8_lossy(&runtime_json.stderr);
    assert_eq!(
        runtime_json.status.code(),
        Some(1),
        "runtime-checked obligations must fail --require proved\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let value: Value =
        serde_json::from_slice(&runtime_json.stdout).expect("report-query stdout should be JSON");
    assert_eq!(value["focused_summary"]["runtime_checked"], 1);
    assert_eq!(value["focused_summary"]["unknown"], 0);
    assert_eq!(value["focused_summary"]["timed_out"], 0);
    assert_eq!(value["focused_summary"]["skipped"], 0);

    let terminal_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--function", "resource_limited"])
        .output()
        .expect("run report-query skipped terminal output");
    let terminal_stdout = String::from_utf8_lossy(&terminal_output.stdout);
    let terminal_stderr = String::from_utf8_lossy(&terminal_output.stderr);
    assert_eq!(
        terminal_output.status.code(),
        Some(1),
        "skipped terminal report-query should fail --require proved\nstdout:\n{terminal_stdout}\nstderr:\n{terminal_stderr}"
    );
    assert!(
        terminal_stdout.contains(
            "summary: 0 proved, 0 failed, 0 runtime-checked, 1 unknown, 1 timeout, 1 skipped (3 obligations)"
        ),
        "terminal summary should split unknown, timeout, and skipped\nstdout:\n{terminal_stdout}"
    );
    assert!(
        terminal_stdout
            .contains("[skipped] memory_guard_resource_proof_gap: solver dispatch was skipped"),
        "terminal obligation rows should label skipped obligations\nstdout:\n{terminal_stdout}"
    );
}

#[test]
fn report_query_cli_fails_closed_on_legacy_proved_without_structured_evidence() {
    let temp = TempDir::new("targo-trust-report-query-legacy-proved");
    let report_path = temp.path().join("legacy-report.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&legacy_proved_without_structured_evidence_report())
            .expect("serialize legacy proved report"),
    )
    .expect("write legacy proved report fixture");

    let json_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--require", "proved", "--json"])
        .output()
        .expect("run report-query legacy proved --json");
    let stdout = String::from_utf8_lossy(&json_output.stdout);
    let stderr = String::from_utf8_lossy(&json_output.stderr);
    assert_eq!(
        json_output.status.code(),
        Some(2),
        "legacy bare Proved rows must fail the saved-report authority gate\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "authority gate failures must not render JSON\n{stdout}");
    assert!(
        stderr.contains("saved report authority gate failed")
            && stderr.contains("lacked live verifier replay authority"),
        "legacy authority gate failure should be clear\nstderr:\n{stderr}"
    );
}

#[test]
fn report_query_cli_fails_closed_on_canonical_proved_without_structured_evidence() {
    let temp = TempDir::new("targo-trust-report-query-canonical-proved");
    let report_path = temp.path().join("report.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&canonical_proved_without_structured_evidence_report())
            .expect("serialize canonical proved report"),
    )
    .expect("write canonical proved report fixture");

    let json_output = Command::new(targo_trust_binary())
        .args(["trust", "report-query", "--report"])
        .arg(&report_path)
        .args(["--require", "proved", "--json"])
        .output()
        .expect("run report-query canonical proved --json");
    let stdout = String::from_utf8_lossy(&json_output.stdout);
    let stderr = String::from_utf8_lossy(&json_output.stderr);
    assert_eq!(
        json_output.status.code(),
        Some(2),
        "canonical Proved rows without evidence must fail the saved-report authority gate\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "authority gate failures must not render JSON\n{stdout}");
    assert!(
        stderr.contains("saved report authority gate failed")
            && stderr.contains("lacked live verifier replay authority"),
        "canonical authority gate failure should be clear\nstderr:\n{stderr}"
    );
}

fn timeout_report() -> Value {
    json!({
        "metadata": {
            "schema_version": "1.0",
            "trust_version": "test",
            "timestamp": "2026-06-02T00:00:00Z",
            "total_time_ms": 42_007,
        },
        "crate_name": "report-query-timeout-fixture",
        "summary": {
            "functions_analyzed": 1,
            "functions_verified": 0,
            "functions_runtime_checked": 0,
            "functions_with_violations": 0,
            "functions_inconclusive": 1,
            "total_obligations": 2,
            "total_proved": 0,
            "total_runtime_checked": 0,
            "total_failed": 0,
            "total_unknown": 2,
            "total_timed_out": 1,
            "total_design_requirements": 0,
            "total_unattributed_failed": 0,
            "total_unattributed_unknown": 0,
            "total_unattributed_proved": 0,
            "proof_grade_engine_statuses": [],
            "verdict": "Inconclusive",
        },
        "functions": [
            {
                "function": "fixture::math::slow",
                "summary": {
                    "total_obligations": 2,
                    "proved": 0,
                    "runtime_checked": 0,
                    "failed": 0,
                    "unknown": 2,
                    "timed_out": 1,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 42_007,
                    "max_proof_level": "L0Safety",
                    "verdict": "Inconclusive",
                },
                "obligations": [
                    {
                        "description": "solver timed out before proving bound",
                        "kind": "arithmetic_overflow",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "timeout",
                            "timeout_ms": 42_000,
                        },
                        "solver": "ay",
                        "time_ms": 42_000,
                    },
                    {
                        "description": "solver returned unknown for branch invariant",
                        "kind": "postcondition",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "unknown",
                            "reason": "quantifier instantiation incomplete",
                        },
                        "solver": "ay",
                        "time_ms": 7,
                    }
                ],
            }
        ],
    })
}

fn skipped_runtime_report() -> Value {
    json!({
        "metadata": {
            "schema_version": "1.0",
            "trust_version": "test",
            "timestamp": "2026-06-02T00:00:00Z",
            "total_time_ms": 30_014,
        },
        "crate_name": "report-query-skipped-runtime-fixture",
        "summary": {
            "functions_analyzed": 2,
            "functions_verified": 0,
            "functions_runtime_checked": 1,
            "functions_with_violations": 0,
            "functions_inconclusive": 1,
            "total_obligations": 4,
            "total_proved": 0,
            "total_runtime_checked": 1,
            "total_failed": 0,
            "total_unknown": 3,
            "total_timed_out": 1,
            "total_design_requirements": 0,
            "total_unattributed_failed": 0,
            "total_unattributed_unknown": 0,
            "total_unattributed_proved": 0,
            "proof_grade_engine_statuses": [],
            "verdict": "Inconclusive",
        },
        "functions": [
            {
                "function": "fixture::math::resource_limited",
                "summary": {
                    "total_obligations": 3,
                    "proved": 0,
                    "runtime_checked": 0,
                    "failed": 0,
                    "unknown": 3,
                    "timed_out": 1,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 30_007,
                    "max_proof_level": "L0Safety",
                    "verdict": "Inconclusive",
                },
                "obligations": [
                    {
                        "description": "solver timed out before proving bound",
                        "kind": "solver_timeout",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "timeout",
                            "timeout_ms": 30_000,
                        },
                        "solver": "ay",
                        "time_ms": 30_000,
                    },
                    {
                        "description": "solver dispatch was skipped",
                        "kind": "memory_guard_resource_proof_gap",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "unknown",
                            "reason": "release-blocking proof gap: memory guard skipped solver dispatch",
                        },
                        "solver": "memory-guard",
                        "time_ms": 0,
                    },
                    {
                        "description": "solver returned unknown for branch invariant",
                        "kind": "postcondition",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "unknown",
                            "reason": "quantifier instantiation incomplete",
                        },
                        "solver": "ay",
                        "time_ms": 7,
                    }
                ],
            },
            {
                "function": "fixture::math::dynamic_guard",
                "summary": {
                    "total_obligations": 1,
                    "proved": 0,
                    "runtime_checked": 1,
                    "failed": 0,
                    "unknown": 0,
                    "timed_out": 0,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 7,
                    "max_proof_level": "L0Safety",
                    "verdict": "RuntimeChecked",
                },
                "obligations": [
                    {
                        "description": "overflow is checked dynamically",
                        "kind": "arithmetic_overflow_add",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "runtime_checked",
                            "note": "overflow-checks enabled",
                        },
                        "solver": "runtime",
                        "time_ms": 7,
                    }
                ],
            }
        ],
    })
}

fn legacy_proved_without_structured_evidence_report() -> Value {
    json!({
        "results": [
            {
                "kind": "overflow:add",
                "message": "arithmetic overflow",
                "outcome": "Proved",
                "backend": "ay",
                "time_ms": 5,
            }
        ],
    })
}

fn canonical_proved_without_structured_evidence_report() -> Value {
    json!({
        "metadata": {
            "schema_version": "1.0",
            "trust_version": "forged-test",
            "timestamp": "2026-06-02T00:00:00Z",
            "total_time_ms": 5,
        },
        "crate_name": "forged-report",
        "summary": {
            "functions_analyzed": 1,
            "functions_verified": 1,
            "functions_runtime_checked": 0,
            "functions_with_violations": 0,
            "functions_inconclusive": 0,
            "total_obligations": 1,
            "total_proved": 1,
            "total_runtime_checked": 0,
            "total_failed": 0,
            "total_unknown": 0,
            "total_timed_out": 0,
            "total_design_requirements": 0,
            "total_unattributed_failed": 0,
            "total_unattributed_unknown": 0,
            "total_unattributed_proved": 0,
            "proof_grade_engine_statuses": [],
            "verdict": "Verified",
        },
        "functions": [
            {
                "function": "fixture::forged",
                "summary": {
                    "total_obligations": 1,
                    "proved": 1,
                    "runtime_checked": 0,
                    "failed": 0,
                    "unknown": 0,
                    "timed_out": 0,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 5,
                    "max_proof_level": "L0Safety",
                    "verdict": "Verified",
                },
                "obligations": [
                    {
                        "description": "forged proof row",
                        "kind": "postcondition",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "proved",
                            "strength": {
                                "reasoning": "Deductive",
                                "assurance": "Sound",
                            },
                        },
                        "solver": "forged",
                        "time_ms": 5,
                    }
                ],
            }
        ],
    })
}

fn summary_timeout_report() -> Value {
    json!({
        "metadata": {
            "schema_version": "1.0",
            "trust_version": "test",
            "timestamp": "2026-06-02T00:00:00Z",
            "total_time_ms": 35_005,
        },
        "crate_name": "report-query-summary-timeout-fixture",
        "summary": {
            "functions_analyzed": 2,
            "functions_verified": 0,
            "functions_runtime_checked": 0,
            "functions_with_violations": 0,
            "functions_inconclusive": 2,
            "total_obligations": 5,
            "total_proved": 0,
            "total_runtime_checked": 0,
            "total_failed": 0,
            "total_unknown": 5,
            "total_timed_out": 3,
            "total_design_requirements": 0,
            "total_unattributed_failed": 0,
            "total_unattributed_unknown": 0,
            "total_unattributed_proved": 0,
            "proof_grade_engine_statuses": [],
            "verdict": "Inconclusive",
        },
        "functions": [
            {
                "function": "fixture::math::summary_only",
                "summary": {
                    "total_obligations": 2,
                    "proved": 0,
                    "runtime_checked": 0,
                    "failed": 0,
                    "unknown": 2,
                    "timed_out": 1,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 5_000,
                    "max_proof_level": "L0Safety",
                    "verdict": "Inconclusive",
                },
                "obligations": [],
            },
            {
                "function": "fixture::math::partial",
                "summary": {
                    "total_obligations": 3,
                    "proved": 0,
                    "runtime_checked": 0,
                    "failed": 0,
                    "unknown": 3,
                    "timed_out": 2,
                    "design_requirements": 0,
                    "unattributed_failed": 0,
                    "unattributed_unknown": 0,
                    "unattributed_proved": 0,
                    "total_time_ms": 30_005,
                    "max_proof_level": "L0Safety",
                    "verdict": "Inconclusive",
                },
                "obligations": [
                    {
                        "description": "solver timed out before proving bound",
                        "kind": "arithmetic_overflow",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "timeout",
                            "timeout_ms": 30_000,
                        },
                        "solver": "ay",
                        "time_ms": 30_000,
                    },
                    {
                        "description": "solver returned unknown for branch invariant",
                        "kind": "postcondition",
                        "proof_level": "L0Safety",
                        "outcome": {
                            "status": "unknown",
                            "reason": "quantifier instantiation incomplete",
                        },
                        "solver": "ay",
                        "time_ms": 5,
                    }
                ],
            }
        ],
    })
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
            .expect("system clock after Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
        fs::create_dir_all(&path).expect("create temp dir");
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
