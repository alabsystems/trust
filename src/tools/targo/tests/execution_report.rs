// Trust: actual cold, warm and failed compilations must retain whole-graph outcomes.
#![cfg(unix)]

use std::fs;
use std::os::unix::process::CommandExt as _;
use std::path::Path;
use std::process::{Command, Output};

use serde_json::Value;

fn command(root: &Path, home: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_targo"));
    cmd.arg0("targo")
        .current_dir(root)
        .arg("-Zbuild-analysis")
        .env("CARGO_HOME", home)
        .env("CARGO_TARGET_DIR", root.join("target.noindex"));
    for name in [
        "CARGO_LOG",
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
    ] {
        cmd.env_remove(name);
    }
    cmd
}

fn build_and_report(root: &Path, home: &Path, succeeds: bool) -> Value {
    let build = command(root, home)
        .args([
            "-Zmem-stats",
            "--unverified",
            "--config",
            "build.analysis.enabled=true",
            "build",
            "--offline",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    assert_eq!(
        build.status.success(),
        succeeds,
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let rows: Vec<Value> = String::from_utf8_lossy(&build.stdout)
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let sessions: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    assert_eq!(sessions.len(), 1, "{rows:?}");
    let id = sessions[0]["run_id"].as_str().unwrap();
    let output: Output = command(root, home)
        .args(["report", "execution", "--id", id, "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["run_id"], id);
    assert_eq!(report["schema"], "targo-execution-report-v1");
    report
}

#[test]
fn actual_cold_warm_and_failed_builds_have_distinct_native_outcomes() {
    let world = tempfile::tempdir().unwrap();
    let root = world.path().join("workspace");
    let home = world.path().join("home");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir(&home).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='execution-sample'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn value() -> u32 { 7 }\n").unwrap();
    fs::write(
        root.join("src/main.rs"),
        "fn main() { assert_eq!(execution_sample::value(), 7); }\n",
    )
    .unwrap();

    let cold = build_and_report(&root, &home, true);
    assert_eq!(cold["availability"], "complete");
    assert_eq!(cold["graph_outcome"], "succeeded");
    assert_eq!(cold["registered_units"], 2);
    assert_eq!(cold["execution"]["scheduled_dirty"], 2);
    assert_eq!(cold["execution"]["succeeded"], 2);
    assert_eq!(cold["compiler_activity"]["availability"], "complete");
    assert_eq!(cold["compiler_activity"]["successful_primary_processes"], 2);
    assert_eq!(cold["compiler_activity"]["unmeasured_starts"], 0);
    assert_eq!(
        cold["shared_dependency_frontier"]["availability"],
        "disabled"
    );
    assert!(cold["shared_dependency_frontier"]["eligible_units"].is_null());
    for unit in cold["units"].as_array().unwrap() {
        assert!(unit["process"]["owning_wait_cpu"].is_object());
        assert!(unit["process"]["peak_rss_bytes"].is_u64());
    }

    let warm = build_and_report(&root, &home, true);
    assert_eq!(warm["availability"], "complete");
    assert_eq!(warm["execution"]["scheduled_fresh"], 2);
    assert_eq!(warm["execution"]["scheduled_dirty"], 0);
    assert_eq!(warm["execution"]["succeeded"], 2);
    assert_eq!(warm["compiler_activity"]["successful_primary_processes"], 0);
    assert_eq!(warm["compiler_activity"]["completed_without_start"], 2);

    fs::write(
        root.join("src/lib.rs"),
        "compile_error!(\"intentional failed prerequisite\");\n",
    )
    .unwrap();
    let failed = build_and_report(&root, &home, false);
    assert_eq!(failed["availability"], "complete");
    assert_eq!(failed["graph_outcome"], "failed");
    assert_eq!(failed["registered_units"], 2);
    assert_eq!(failed["execution"]["failed"], 1);
    assert_eq!(failed["execution"]["not_executed"], 1);
    assert_eq!(failed["execution"]["succeeded"], 0);
    assert_eq!(failed["compiler_activity"]["availability"], "incomplete");
    assert!(failed["compiler_activity"]["successful_primary_processes"].is_null());
}
