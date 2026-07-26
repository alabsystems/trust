use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

#[test]
fn proof_concurrency_producer_audit_fails_closed_with_missing_producer_contract() {
    let repo = clean_git_repo("proof-concurrency-producer-missing");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency-producer",
            "audit",
            "--format",
            "json",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency producer audit");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "producer helper must fail closed until real artifacts are generated\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.trim().is_empty(), "JSON blocked report should keep stderr empty");

    let report: Value = serde_json::from_slice(&output.stdout).expect("blocked JSON should parse");
    assert_eq!(report["schema"], "trust.proof-concurrency.producer-audit.v1");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["producer"]["expected_solver"], "trust-concurrency-prover-release-v1");
    assert_eq!(report["producer"]["implemented"], false);
    assert_eq!(report["producer"]["blocker_code"], "missing_trust_concurrency_release_producer");
    assert_eq!(report["artifact_dir"], "reports/proof/concurrency-artifacts");
    assert!(
        report["next_required_interface"]["materializer_command"]
            .as_str()
            .expect("materializer command should be a string")
            .contains("proof-concurrency --materialize-input-manifest")
    );

    let artifacts = report["required_artifacts"].as_array().expect("artifact list should exist");
    assert_eq!(artifacts.len(), 3);
    let ids: Vec<&str> = artifacts
        .iter()
        .map(|artifact| artifact["id"].as_str().expect("id should be a string"))
        .collect();
    assert_eq!(
        ids,
        vec!["race_free_arc_mutex", "atomic_release_acquire", "channel_happens_before"]
    );
    for artifact in artifacts {
        let files = artifact["files"].as_array().expect("files should be an array");
        assert_eq!(files.len(), 4);
        for file in files {
            assert_eq!(file["status"], "missing");
        }
    }
    assert!(
        !repo.join("reports").join("proof").join("concurrency-artifacts").exists(),
        "blocked producer audit must not synthesize artifact files"
    );

    let _ = fs::remove_dir_all(&repo);
}

fn clean_git_repo(label: &str) -> PathBuf {
    let repo = temp_test_dir(label);
    fs::create_dir_all(&repo).expect("create temp repo");
    run_git(&repo, &["init"]);
    run_git(&repo, &["config", "user.email", "trust-tests@example.invalid"]);
    run_git(&repo, &["config", "user.name", "Trust Tests"]);
    fs::write(repo.join("README.md"), "proof concurrency producer fixture\n")
        .expect("write fixture");
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "fixture"]);
    repo
}

fn run_git(repo: &Path, args: &[&str]) {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("run git {}: {error}", args.join(" ")));
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("targo-trust-{label}-{}-{unique}", std::process::id()))
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
