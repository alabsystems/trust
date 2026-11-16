//! Actual frontend refusal controls; no fixture creates a managed root or
//! execution/proof eligibility. The real host/SDK qualification is separate.
#![cfg(any(target_os = "linux", target_os = "macos"))]
use std::io::Write as _;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn invoke(args: &[&str], input: &[u8]) -> Output {
    let project = tempfile::tempdir().unwrap();
    std::fs::create_dir(project.path().join(".cargo")).unwrap();
    std::fs::write(
        project.path().join("Cargo.toml"),
        b"this is not a manifest {",
    )
    .unwrap();
    std::fs::write(
        project.path().join(".cargo/config.toml"),
        b"this is not config {",
    )
    .unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_targo"))
        .args(args)
        .env_clear()
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .env("PATH", "/usr/bin:/bin")
        .env("CARGO_HOME", project.path().join("cargo-home"))
        .current_dir(project.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    let until = Instant::now() + Duration::from_secs(60);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() >= until {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!("actual private entry did not refuse within its bound: {output:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(!project.path().join("target").exists());
    assert!(!project.path().join("cargo-home").exists());
    output
}

#[test]
fn private_workload_entry_refuses_bad_frame_before_project_or_lane_work() {
    let output = invoke(&["--resource-workload-v1"], &[0, 0, 0, 0]);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("service frame exceeds its original finite bound"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("UNVERIFIED:"),
        "lane started before original custody: {stderr}"
    );
    assert!(
        !stderr.contains("config.toml"),
        "project config was read: {stderr}"
    );
}

#[test]
fn private_workload_entry_refuses_extra_arguments_before_reading_input() {
    let output = invoke(&["--resource-workload-v1", "--no-deps"], &[]);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("accepts only its exact private argument"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("config.toml"),
        "project config was read: {stderr}"
    );
}

#[test]
fn ordinary_frontend_still_reports_its_genuine_targo_version_without_a_workload() {
    let output = invoke(&["--unverified", "--version"], &[]);
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).starts_with("targo "),
        "{output:?}"
    );
}
