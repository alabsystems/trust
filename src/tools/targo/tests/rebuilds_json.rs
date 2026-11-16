//! Native rebuild reports preserve every observed compilation unit.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

use serde_json::{Value, json};

const OWNER: &str = "rebuild_report_owner";
const DEP: &str = "rebuild_report_dep";

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture explicitly selects its original CLI/compiler tools and PATH before project configuration exists"
)]
fn command(project: &Path, world: &Path) -> Command {
    let executable = std::env::var_os("TARGO_REBUILD_REPORT_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(project)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching original rustdoc"),
        )
        .env("CARGO_BUILD_ANALYSIS_ENABLED", "true")
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

fn recorded(command: &mut Command, evidence: &Path) -> Output {
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&json!({
            "program": command.get_program().to_string_lossy(),
            "args": command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd": command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
    let output = command.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    fs::write(
        evidence.join("status.json"),
        serde_json::to_vec_pretty(&json!({
            "success": output.status.success(), "code": output.status.code(),
            "display": output.status.to_string(),
        }))
        .unwrap(),
    )
    .unwrap();
    output
}

fn success(output: &Output, world: &Path) {
    assert!(
        output.status.success(),
        "world={} status={}\nstdout={}\nstderr={}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

struct Build {
    run_id: String,
    artifacts: Vec<Value>,
}

fn build(project: &Path, world: &Path, label: &str) -> Build {
    let evidence = world.join(label);
    let output = recorded(
        command(project, world).args([
            "--unverified",
            "build",
            "-Zbuild-analysis",
            "--offline",
            "--lib",
            "--bin",
            OWNER,
            "--message-format=json",
            "-vv",
            "-j1",
            "-Zmem-stats",
        ]),
        &evidence,
    );
    success(&output, world);
    let rows = output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .map(|line| serde_json::from_slice::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    let artifacts = rows
        .iter()
        .filter(|row| row["reason"] == "compiler-artifact")
        .cloned()
        .collect::<Vec<_>>();
    let sessions = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect::<Vec<_>>();
    fs::write(
        evidence.join("rows.json"),
        serde_json::to_vec_pretty(&rows).unwrap(),
    )
    .unwrap();
    fs::write(
        evidence.join("artifacts.json"),
        serde_json::to_vec_pretty(&artifacts).unwrap(),
    )
    .unwrap();
    fs::write(
        evidence.join("sessions.json"),
        serde_json::to_vec_pretty(&sessions).unwrap(),
    )
    .unwrap();
    assert_eq!(sessions.len(), 1, "world={} rows={rows:?}", world.display());
    let run_id = sessions[0]["run_id"].as_str().unwrap().to_owned();
    fs::write(evidence.join("run_id"), &run_id).unwrap();
    let log = fs::read(world.join("home/log").join(format!("{run_id}.jsonl"))).unwrap();
    fs::write(evidence.join("analysis.jsonl"), log).unwrap();
    Build { run_id, artifacts }
}

fn execute(build: &Build, world: &Path, label: &str) -> Output {
    let binaries = build
        .artifacts
        .iter()
        .filter(|row| row["target"]["kind"] == json!(["bin"]))
        .collect::<Vec<_>>();
    assert_eq!(binaries.len(), 1, "{:?}", build.artifacts);
    recorded(
        &mut Command::new(binaries[0]["executable"].as_str().unwrap()),
        &world.join(label),
    )
}

fn report(project: &Path, world: &Path, build: &Build, label: &str) -> Output {
    recorded(
        command(project, world).args([
            "report",
            "rebuilds",
            "-Zbuild-analysis",
            "--id",
            &build.run_id,
            "--json",
        ]),
        &world.join(label),
    )
}

fn target<'a>(units: &'a [Value], name: &str, kind: &str) -> &'a Value {
    let found = units
        .iter()
        .filter(|unit| unit["target"]["name"] == name && unit["target"]["kind"] == kind)
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "{units:?}");
    found[0]
}

fn assert_report(report: &Value, build: &Build, cached: u64, dirty: u64, new: u64) {
    assert_eq!(report["schema"], "targo-rebuilds-v1");
    assert_eq!(report["run_id"], build.run_id);
    assert_eq!(report["scope"], "observed-fingerprint-classifications");
    assert_eq!(report["stream_completeness"], "complete");
    assert_eq!(report["input_accounting"], "finalized");
    assert_eq!(report["registered_units"], 3);
    assert_eq!(report["classified_units"], 3);
    assert_eq!(report["unclassified_units"], 0);
    assert_eq!(
        report["observed_counts"],
        json!({"cached":cached,"dirty":dirty,"new":new})
    );
    let units = report["units"].as_array().unwrap();
    assert_eq!(units.len(), 3);
    assert_eq!(
        units
            .iter()
            .filter(|unit| unit["fingerprint"]["status"] == "fresh")
            .count() as u64,
        cached
    );
    assert_eq!(
        units
            .iter()
            .filter(|unit| unit["fingerprint"]["status"] == "dirty")
            .count() as u64,
        dirty
    );
    assert_eq!(
        units
            .iter()
            .filter(|unit| unit["fingerprint"]["status"] == "new")
            .count() as u64,
        new
    );
    assert!(
        units
            .windows(2)
            .all(|pair| pair[0]["index"].as_u64().unwrap() < pair[1]["index"].as_u64().unwrap())
    );
    assert_eq!(build.artifacts.len(), 3, "{:?}", build.artifacts);
    for unit in units {
        assert_eq!(unit["mode"], "build");
        assert!(!unit["platform"].as_str().unwrap().is_empty());
        assert_eq!(unit["features"], json!([]));
        assert!(unit["requested"].is_boolean());
        let dependencies = unit["dependencies"].as_array().unwrap();
        assert!(
            dependencies
                .windows(2)
                .all(|pair| pair[0].as_u64().unwrap() < pair[1].as_u64().unwrap())
        );
        assert!(
            dependencies
                .iter()
                .all(|index| units.iter().any(|candidate| candidate["index"] == *index))
        );
        let artifact = build
            .artifacts
            .iter()
            .find(|row| {
                row["package_id"] == unit["package_id"]
                    && row["target"]["name"] == unit["target"]["name"]
                    && row["target"]["kind"]
                        .as_array()
                        .unwrap()
                        .contains(&unit["target"]["kind"])
            })
            .unwrap_or_else(|| panic!("unit={unit} artifacts={:?}", build.artifacts));
        let fingerprint = &unit["fingerprint"];
        assert!(fingerprint["rechecked"].is_boolean());
        let status = fingerprint["status"].as_str().unwrap();
        assert!(matches!(status, "fresh" | "dirty" | "new"));
        assert_eq!(
            artifact["fresh"],
            status == "fresh",
            "unit={unit} artifact={artifact}"
        );
        if status == "dirty" {
            let category = fingerprint["reason"]
                .as_str()
                .expect("typed dirty reason category");
            assert!(
                !category.is_empty()
                    && category
                        .bytes()
                        .all(|b| b.is_ascii_lowercase() || b == b'-')
            );
        } else {
            assert!(fingerprint["reason"].is_null());
        }
    }
    let library = target(units, OWNER, "lib");
    let binary = target(units, OWNER, "bin");
    let dependency = target(units, DEP, "lib");
    assert_eq!(library["package_id"], binary["package_id"]);
    assert_ne!(library["index"], binary["index"]);
    assert_ne!(library["package_id"], dependency["package_id"]);
    assert_eq!(dependency["requested"], false);
    assert_eq!(library["requested"], true);
    assert_eq!(binary["requested"], true);
    assert!(
        library["dependencies"]
            .as_array()
            .unwrap()
            .contains(&dependency["index"])
    );
    assert!(
        binary["dependencies"]
            .as_array()
            .unwrap()
            .contains(&library["index"])
    );
    // These are graph frontiers for New as well as Dirty observations, not
    // attribution of compiler time or a proof of a causal rebuild chain.
    let frontiers = report["non_cached_dependency_frontier_roots"]
        .as_array()
        .unwrap();
    assert!(
        frontiers
            .windows(2)
            .all(|pair| pair[0].as_u64().unwrap() < pair[1].as_u64().unwrap())
    );
    for frontier in frontiers {
        assert!(
            units
                .iter()
                .any(|unit| unit["index"] == *frontier && unit["fingerprint"]["status"] != "fresh")
        );
    }
    if cached == 3 {
        assert!(frontiers.is_empty());
    }
    if dirty == 2 {
        assert_eq!(library["fingerprint"]["status"], "dirty");
        assert_eq!(binary["fingerprint"]["status"], "dirty");
        assert_eq!(dependency["fingerprint"]["status"], "fresh");
        assert!(frontiers.contains(&library["index"]));
    }
}

#[test]
fn native_rebuilds_json_preserves_cold_warm_and_same_package_units() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-rebuilds-json.noindex");
    fs::create_dir_all(&base).unwrap();
    // Retain the world before selecting tools or checking any compilation/report.
    let world = tempfile::Builder::new()
        .prefix("report")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let project = world.join("project");
    let dependency = world.join("dependency");
    for path in [
        project.join("src"),
        dependency.join("src"),
        world.join("home"),
        world.join("target"),
    ] {
        fs::create_dir_all(path).unwrap();
    }
    for label in [
        "cold",
        "warm",
        "dirty",
        "cold-binary",
        "dirty-binary",
        "cold-report",
        "warm-report",
        "dirty-report",
    ] {
        fs::create_dir(world.join(label)).unwrap();
    }
    fs::write(world.join("owner-lib-after.rs"), []).unwrap();
    fs::write(world.join("observed.json"), []).unwrap();
    fs::write(project.join("Cargo.toml"), "[package]\nname='rebuild_report_owner'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\nrebuild_report_dep={path='../dependency'}\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(
        dependency.join("Cargo.toml"),
        "[package]\nname='rebuild_report_dep'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        dependency.join("src/lib.rs"),
        "pub fn value() -> u32 { 1 }\n",
    )
    .unwrap();
    fs::write(
        project.join("src/lib.rs"),
        "pub fn value() -> u32 { rebuild_report_dep::value() + 1 }\n",
    )
    .unwrap();
    fs::write(
        world.join("owner-lib-before.rs"),
        fs::read(project.join("src/lib.rs")).unwrap(),
    )
    .unwrap();
    fs::write(
        project.join("src/main.rs"),
        "fn main() { println!(\"{}\", rebuild_report_owner::value()); }\n",
    )
    .unwrap();
    let cold = build(&project, &world, "cold");
    let cold_binary = execute(&cold, &world, "cold-binary");
    let warm = build(&project, &world, "warm");
    fs::write(
        project.join("src/lib.rs"),
        "pub fn value() -> u32 { rebuild_report_dep::value() + 2 }\n",
    )
    .unwrap();
    fs::write(
        world.join("owner-lib-after.rs"),
        fs::read(project.join("src/lib.rs")).unwrap(),
    )
    .unwrap();
    let dirty = build(&project, &world, "dirty");
    let dirty_binary = execute(&dirty, &world, "dirty-binary");
    // Execute all real phases first, so an unsupported --json on the baseline
    // cannot hide successful compilation, warm reuse, or the changed binary.
    let cold_report = report(&project, &world, &cold, "cold-report");
    let warm_report = report(&project, &world, &warm, "warm-report");
    let dirty_report = report(&project, &world, &dirty, "dirty-report");
    fs::write(world.join("observed.json"), serde_json::to_vec_pretty(&json!({
        "cold_run":cold.run_id,"warm_run":warm.run_id,"dirty_run":dirty.run_id,
        "cold_artifacts":cold.artifacts,"warm_artifacts":warm.artifacts,"dirty_artifacts":dirty.artifacts,
        "cold_binary_stdout":cold_binary.stdout,"dirty_binary_stdout":dirty_binary.stdout,
        "report_success":[cold_report.status.success(),warm_report.status.success(),dirty_report.status.success()],
    })).unwrap()).unwrap();
    success(&cold_binary, &world);
    success(&dirty_binary, &world);
    assert_eq!(cold_binary.stdout, b"2\n");
    assert_eq!(dirty_binary.stdout, b"3\n");
    assert_eq!(cold.artifacts.len(), 3);
    assert!(cold.artifacts.iter().all(|row| row["fresh"] == false));
    assert_eq!(warm.artifacts.len(), 3);
    assert!(warm.artifacts.iter().all(|row| row["fresh"] == true));
    assert_eq!(dirty.artifacts.len(), 3);
    assert!(
        dirty
            .artifacts
            .iter()
            .all(|row| row["fresh"] == (row["target"]["name"] == DEP))
    );
    for output in [&cold_report, &warm_report, &dirty_report] {
        success(output, &world);
    }
    assert_report(
        &serde_json::from_slice::<Value>(&cold_report.stdout).unwrap(),
        &cold,
        0,
        0,
        3,
    );
    assert_report(
        &serde_json::from_slice::<Value>(&warm_report.stdout).unwrap(),
        &warm,
        3,
        0,
        0,
    );
    assert_report(
        &serde_json::from_slice::<Value>(&dirty_report.stdout).unwrap(),
        &dirty,
        1,
        2,
        0,
    );
}
