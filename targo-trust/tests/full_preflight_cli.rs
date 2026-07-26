use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn verify_full_preflight_help_rejects_removed_command() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "full-preflight", "--help"])
        .output()
        .expect("run targo trust verify full-preflight help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "full-preflight help should reject the removed command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed command help should not print usage");
    assert!(stderr.contains("removed shell/Python-era release alias"));
    assert!(stderr.contains("targo trust release check"));
    assert!(
        !stderr.contains("full_verify_preflight.py"),
        "removed-command stderr must not expose the backend script filename\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("x.py"),
        "removed-command stderr must not expose bootstrap x.py naming\nstderr:\n{stderr}"
    );
}

#[test]
fn verify_full_preflight_rejects_default_release_backend_before_python() {
    let root = temp_test_dir("targo-trust-full-preflight-release-reject");
    let scripts = root.join("scripts");
    fs::create_dir_all(&scripts).expect("create scripts dir");
    let marker = root.join("backend-ran");
    fs::write(
        scripts.join("full_verify_preflight.py"),
        format!(
            r#"#!/usr/bin/env python3
from pathlib import Path
Path({marker:?}).write_text("backend ran\n", encoding="utf-8")
"#,
            marker = marker.display().to_string()
        ),
    )
    .expect("write fake full preflight backend");

    let report = root.join("reports").join("preflight.json");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "full-preflight",
            "--repo-root",
            root.to_str().expect("utf-8 temp path"),
            "--json-output",
            "reports/preflight.json",
        ])
        .env("TRUST_REPO_ROOT", &root)
        .env("TRUST_SCRIPT_PYTHON", "python3")
        .output()
        .expect("run targo trust verify full-preflight");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "default release preflight should reject deprecated backend\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("removed shell/Python-era release alias"),
        "stderr should explain the removed alias\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("targo trust verify cargo-cache"),
        "stderr should identify Rust-native replacement gates\nstderr:\n{stderr}"
    );
    assert!(!marker.exists(), "rejected preflight must not invoke Python backend");
    assert!(!report.exists(), "rejected preflight must not leave a backend report");

    let _ = fs::remove_dir_all(&root);
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique =
        SystemTime::now().duration_since(UNIX_EPOCH).expect("clock after epoch").as_nanos();
    std::env::temp_dir().join(format!("{label}-{}-{unique}", std::process::id()))
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
