//! Trust: colliding native invocations retain independently readable reports.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates
#![cfg(unix)]

use std::fs;
use std::os::unix::process::CommandExt as _;
use std::path::Path;
use std::process::{Command, Output};

use cargo_test_support::prelude::*;
use cargo_test_support::project;
use serde_json::Value;

fn command(root: &Path, home: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .arg0("targo")
        .current_dir(root)
        .arg("-Zbuild-analysis")
        .env("CARGO_HOME", home)
        .env("CARGO_TARGET_DIR", root.join("target.noindex"));
    for name in [
        "__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS",
        "CARGO_LOG",
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
    ] {
        command.env_remove(name);
    }
    command
}

// Trust: the maintained native fixture and every actual command stream remain
// under cargo-test-support's retained project, including on failed assertions.
fn recorded_output(command: &mut Command, evidence: &Path) -> Output {
    fs::create_dir_all(evidence.parent().unwrap()).unwrap();
    fs::create_dir(evidence).unwrap();
    let output = command.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    output
}

fn native_build(root: &Path, home: &Path, evidence: &Path) -> String {
    let output = recorded_output(
        command(root, home)
            .args([
                "-Zmem-stats",
                "--unverified",
                "--config",
                "build.analysis.enabled=true",
                "build",
                "--offline",
                "--message-format=json",
            ])
            // Trust: exercise the existing test-only timestamp override to make
            // the collision deterministic. The product never adjusts its clock.
            .env("__CARGO_TEST_INVOCATION_TIME", "2026-11-08T01:02:03Z"),
        evidence,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let sessions = output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<Value>(line).ok())
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect::<Vec<_>>();
    assert_eq!(
        sessions.len(),
        1,
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    sessions[0]["run_id"].as_str().unwrap().to_owned()
}

fn execution_report(root: &Path, home: &Path, id: &str, evidence: &Path) -> Value {
    let output = recorded_output(
        command(root, home).args(["report", "execution", "--id", id, "--json"]),
        evidence,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["run_id"], id);
    assert_eq!(report["availability"], "complete");
    assert_eq!(report["graph_outcome"], "succeeded");
    assert_eq!(report["compiler_activity"]["availability"], "complete");
    report
}

#[cargo_test]
fn native_same_timestamp_invocations_preserve_every_exact_report() {
    let project = project()
        .at("workspace")
        .file(
            "Cargo.toml",
            concat!(
                "[package]\nname='log-identity-sample'\nversion='0.1.0'\nedition='2024'\n",
                "[workspace]\n[profile.dev]\ndebug=0\nstrip='none'\n",
            ),
        )
        .file("src/lib.rs", "pub fn value() -> u32 { 7 }\n")
        .build();
    let root = project.root();
    // Trust: retain diagnostics beside the package so writing reports cannot
    // itself change the package's source input set between warm invocations.
    let fixture = root.parent().unwrap();
    let home = fixture.join("analysis-home");
    let evidence = fixture.join("native-evidence");
    fs::create_dir(&home).unwrap();

    let mut retained = Vec::new();
    for invocation in 0..3 {
        let id = native_build(&root, &home, &evidence.join(format!("build-{invocation}")));
        if invocation == 0 {
            assert!(
                !id.contains('~'),
                "first session must retain legacy spelling"
            );
        }
        assert!(retained.iter().all(|(prior, _)| prior != &id));
        let path = home.join("log").join(format!("{id}.jsonl"));
        let bytes = fs::read(path).unwrap();
        fs::write(
            evidence.join(format!("retained-{invocation}.jsonl")),
            &bytes,
        )
        .unwrap();
        retained.push((id, bytes));
        // The first unsuffixed legacy-format session and every collision
        // remain byte-exact and pass the SAME strict native report reader.
        for (index, (id, bytes)) in retained.iter().enumerate() {
            assert_eq!(
                fs::read(home.join("log").join(format!("{id}.jsonl"))).unwrap(),
                *bytes
            );
            let report = execution_report(
                &root,
                &home,
                id,
                &evidence.join(format!("report-{invocation}-{index}")),
            );
            assert_eq!(
                report["compiler_activity"]["successful_primary_processes"],
                if index == 0 { 1 } else { 0 }
            );
            assert_eq!(report["compiler_activity"]["unmeasured_starts"], 0);
        }
        assert_eq!(retained.len(), invocation + 1);
    }

    let sessions = recorded_output(
        command(&root, &home).args(["report", "sessions"]),
        &evidence.join("sessions"),
    );
    assert!(
        sessions.status.success(),
        "{}",
        String::from_utf8_lossy(&sessions.stderr)
    );
    let listed = String::from_utf8(sessions.stderr).unwrap();
    let listed_ids = listed
        .lines()
        .filter_map(|line| line.trim().strip_prefix("- "))
        .collect::<Vec<_>>();
    let expected_ids = retained
        .iter()
        .rev()
        .map(|(id, _)| id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(listed_ids, expected_ids, "{listed}");
}
