//! Actual ordinary native lint routing, using the selected SDK's real driver.
#![cfg(target_os = "macos")]

use std::path::Path;
use std::process::{Command, Output};

use cargo_test_support::{cargo_test, project, registry::Package};
use serde_json::Value;

struct Observed {
    execution: Value,
    artifacts: Vec<Value>,
}

fn command(root: &Path) -> Command {
    let current = std::env::var_os("TARGO_NATIVE_LINT_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(current);
    command
        .current_dir(root)
        .args([
            "--config",
            &format!(
                "build.build-dir='{}'",
                root.join("lint-build.noindex").display()
            ),
        ])
        .env("CARGO_BUILD_ANALYSIS_ENABLED", "true")
        // The ambient recursive selector must not switch the authenticated
        // current planner back to the selected SDK's older sibling.
        .env("CARGO", "/untrusted/ambient/targo")
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

fn observe(root: &Path, lint: bool) -> Observed {
    let mut compile = command(root);
    if lint {
        compile.arg("tippy");
    } else {
        compile.args(["--unverified", "test"]);
    }
    compile.args([
        "--offline",
        "--lib",
        "--message-format=json",
        "-Zbuild-analysis",
        "-Zmem-stats",
        "-j1",
    ]);
    if lint {
        compile.args(["--", "-D", "warnings"]);
    } else {
        compile.arg("--no-run");
    }
    let output = compile.output().unwrap();
    assert_success(&output);
    let rows: Vec<Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect();
    let sessions: Vec<_> = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect();
    assert_eq!(sessions.len(), 1, "{rows:?}");
    let outputs: Vec<_> = rows
        .iter()
        .filter(|row| {
            row["reason"] == "compiler-artifact" && row["target"]["name"] == "native_lint_owner"
        })
        .flat_map(|row| row["filenames"].as_array().unwrap())
        .collect();
    assert!(!outputs.is_empty(), "{rows:?}");
    assert!(outputs.iter().all(|path| {
        Path::new(path.as_str().unwrap()).starts_with(root.join("lint-build.noindex"))
    }));
    let id = sessions[0]["run_id"].as_str().unwrap();
    let report = command(root)
        .args([
            "-Zbuild-analysis",
            "report",
            "execution",
            "--id",
            id,
            "--json",
        ])
        .output()
        .unwrap();
    assert_success(&report);
    let report: Value = serde_json::from_slice(&report.stdout).unwrap();
    assert_eq!(report["run_id"], id);
    assert_eq!(report["availability"], "complete");
    assert_eq!(report["graph_outcome"], "succeeded");
    assert_eq!(report["compiler_activity"]["availability"], "complete");
    Observed {
        execution: report,
        artifacts: rows
            .into_iter()
            .filter(|row| row["reason"] == "compiler-artifact")
            .collect(),
    }
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cargo_test]
fn ordinary_tippy_keeps_test_products_and_external_build_dependencies() {
    Package::new("native_lint_shared", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 1 }\n")
        .publish();
    // A build-only dependency has the same resolved host profile in test and
    // check. Sharing A between normal and build edges instead legitimately
    // changes its deferred debuginfo: test can share the linked normal unit,
    // while check's normal edge emits metadata and the host build defaults to
    // no debug information. Keep A to exercise that distinct normal edge, and
    // require exact reuse of independently requested B.
    Package::new("native_lint_build", "1.0.0")
        .local(true)
        .file("src/lib.rs", "pub fn value() -> u32 { 1 }\n")
        .publish();
    let p = project()
        .file(
            ".cargo/config.toml",
            &format!(
                "[source.crates-io]\nreplace-with='local'\n[source.local]\nlocal-registry={:?}\n",
                cargo_test_support::registry::registry_path()
            ),
        )
        .file("Cargo.toml", "[package]\nname='native_lint_owner'\nversion='0.0.0'\nedition='2021'\n[dependencies]\nnative_lint_shared='1.0.0'\n[build-dependencies]\nnative_lint_build='1.0.0'\n")
        .file("build.rs", "fn main() { assert_eq!(native_lint_build::value(), 1); println!(\"cargo:rerun-if-changed=build.rs\"); }\n")
        .file("src/lib.rs", "pub fn value() -> u32 { native_lint_shared::value() }\n").build();
    let cold = observe(&p.root(), false);
    assert!(
        cold.execution["compiler_activity"]["successful_primary_processes"]
            .as_u64()
            .unwrap()
            > 0
    );
    let lint = observe(&p.root(), true);
    let external_builds: Vec<_> = lint.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["target"]["name"] == "native_lint_build" && unit["mode"] == "build")
        .collect();
    assert_eq!(external_builds.len(), 1, "{}", lint.execution);
    assert!(
        external_builds
            .iter()
            .all(|unit| unit["scheduled_fresh"] == true
                && unit["process"]["command_started_seconds"].is_null()),
        "{}",
        lint.execution
    );
    let build_artifact = |observed: &Observed| {
        let artifacts: Vec<_> = observed
            .artifacts
            .iter()
            .filter(|artifact| artifact["target"]["name"] == "native_lint_build")
            .collect();
        assert_eq!(artifacts.len(), 1, "{:?}", observed.artifacts);
        (
            artifacts[0]["profile"].clone(),
            artifacts[0]["features"].clone(),
            artifacts[0]["filenames"].clone(),
        )
    };
    let cold_builds: Vec<_> = cold.execution["units"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["target"]["name"] == "native_lint_build" && unit["mode"] == "build")
        .collect();
    assert_eq!(cold_builds.len(), 1, "{}", cold.execution);
    assert_eq!(cold_builds[0]["scheduled_fresh"], false);
    assert!(
        cold_builds[0]["process"]["command_started_seconds"]
            .as_f64()
            .is_some(),
        "{}",
        cold.execution
    );
    assert_eq!(
        build_artifact(&cold),
        build_artifact(&lint),
        "the requested build artifact must actually match"
    );
    let after = observe(&p.root(), false);
    assert_eq!(
        after.execution["compiler_activity"]["successful_primary_processes"],
        0
    );
    assert_eq!(after.execution["execution"]["scheduled_dirty"], 0);
    assert_eq!(
        cold.execution["registered_units"],
        after.execution["registered_units"]
    );
    assert_eq!(build_artifact(&cold), build_artifact(&after));
}

#[cargo_test]
fn ordinary_native_lint_reaches_the_selected_real_driver() {
    let p = project()
        .file(
            "src/lib.rs",
            "pub fn equal(value: u32) -> bool { value == value }\n",
        )
        .build();
    let output = command(&p.root())
        .args([
            "clippy",
            "--offline",
            "--lib",
            "--message-format=json",
            "--",
            "-D",
            "clippy::eq_op",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .any(|row| row["reason"] == "compiler-message"
                && row["message"]["code"]["code"] == "clippy::eq_op"),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cargo_test]
fn legacy_argument_validation_happens_before_the_planner() {
    let p = project()
        .file("Cargo.toml", "not a valid manifest\n")
        .build();
    let output = command(&p.root())
        .args(["tippy", "--", "--not-a-compiler-option", "--no-deps"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("not-a-compiler-option"), "{error}");
    assert!(!error.contains("failed to parse manifest"), "{error}");
}

#[cargo_test]
fn legacy_version_preflight_cannot_emit_an_object_from_forwarded_inputs() {
    let p = project()
        .file("Cargo.toml", "not a valid manifest\n")
        .file("input.rs", "fn main() {}\n")
        .build();
    let canary = p.root().join("unexpected-preflight.o");
    let source = p.root().join("input.rs");
    let output = command(&p.root())
        .args(["tippy", "--", "--no-deps", "--emit=obj", "-o"])
        .arg(&canary)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("manifest"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!canary.exists(), "a version-only preflight emitted bytes");
}
