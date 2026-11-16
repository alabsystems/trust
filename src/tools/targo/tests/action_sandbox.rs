#![cfg(target_os = "macos")]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn build(root: &Path, confined: bool) -> Output {
    build_with_environment(root, confined, None)
}

fn build_with_environment(root: &Path, confined: bool, value: Option<&str>) -> Output {
    let executable = std::env::var_os("TARGO_ENVIRONMENT_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", std::env::var_os("RUSTC").unwrap())
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly")
        .args([
            "--unverified",
            "build",
            "--offline",
            "--lib",
            "-Zbuild-dir-new-layout",
            "--message-format=json",
        ]);
    if confined {
        command.args(["--config", "build.action-sandbox=true"]);
    }
    if let Some(value) = value {
        command.env("UNUSED_ACTION_INPUT", value);
    }
    command.env("UNDECLARED_ACTION_INPUT", value.unwrap_or("ambient"));
    command.output().unwrap()
}

fn fresh(output: &Output) -> bool {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<serde_json::Value> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .filter(|row: &serde_json::Value| row["reason"] == "compiler-artifact")
        .collect();
    assert_eq!(rows.len(), 1);
    rows[0]["fresh"] == true
}

#[test]
fn native_compilation_is_confined_and_cannot_reuse_unconfined_outputs() {
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let workspace = temp.path().join("project");
    let root = workspace.join("member");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        workspace.join("Cargo.toml"),
        "[workspace]\nmembers=['member']\nresolver='2'\n",
    )
    .unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='confined_action'\nversion='0.0.0'\nedition='2021'\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn value() -> u32 { 42 }\n").unwrap();
    assert!(!fresh(&build(&root, false)));
    assert!(
        !fresh(&build(&root, true)),
        "unconfined output cannot satisfy a confined action"
    );
    assert!(fresh(&build(&root, true)));
    let private = workspace.join("secret.txt");
    fs::write(&private, b"outside source inputs").unwrap();
    fs::write(
        root.join("src/lib.rs"),
        format!("pub const SECRET: &str = include_str!({private:?});\n"),
    )
    .unwrap();
    let denied = build(&root, true);
    assert!(!denied.status.success(), "undeclared reads must fail");
    assert!(
        !fresh(&build(&root, false)),
        "ordinary compilation remains available"
    );
    // A failed confined action must not publish the unconfined fallback.
    assert!(!build(&root, true).status.success());
    fs::write(root.join("src/lib.rs"), "pub fn value() -> u32 { 42 }\n").unwrap();
    fs::write(
        root.join("build.rs"),
        "fn main() { panic!(\"must not execute\"); }\n",
    )
    .unwrap();
    let refused = build(&root, true);
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("without build scripts or proc macros")
    );
    assert!(!String::from_utf8_lossy(&refused.stderr).contains("must not execute"));
}

#[test]
fn confined_reuse_binds_inherited_environment_even_without_env_dep_info() {
    let root = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    fs::create_dir(root.path().join("src")).unwrap();
    fs::create_dir(root.path().join(".cargo")).unwrap();
    fs::write(
        root.path().join(".cargo/config.toml"),
        "[env]\nUNUSED_ACTION_INPUT = { value = 'fallback', force = false }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='environment_input'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.path().join("src/lib.rs"),
        "pub fn value() -> u32 { 42 }\n",
    )
    .unwrap();
    assert!(!fresh(&build_with_environment(
        root.path(),
        true,
        Some("first")
    )));
    assert!(fresh(&build_with_environment(
        root.path(),
        true,
        Some("first")
    )));
    assert!(
        !fresh(&build_with_environment(root.path(), true, Some("second"))),
        "a different inherited environment cannot replay the earlier action"
    );
    assert!(fresh(&build_with_environment(
        root.path(),
        true,
        Some("second")
    )));
    assert!(!fresh(&build_with_environment(root.path(), true, None)));
}

#[test]
fn undeclared_ambient_values_neither_reach_the_compiler_nor_invalidate_reuse() {
    let root = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    fs::create_dir(root.path().join("src")).unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='undeclared_environment'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.path().join("src/lib.rs"),
        "const _: () = assert!(option_env!(\"UNDECLARED_ACTION_INPUT\").is_none());\n",
    )
    .unwrap();
    assert!(!fresh(&build_with_environment(
        root.path(),
        true,
        Some("first")
    )));
    assert!(fresh(&build_with_environment(
        root.path(),
        true,
        Some("second")
    )));
}

#[test]
fn source_observing_scheduler_transport_revalidates_its_actual_value() {
    for variable in [
        "CARGO_JOBSERVER_HANDOFF",
        "TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT",
    ] {
        let root = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
        fs::create_dir(root.path().join("src")).unwrap();
        fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='scheduler_environment'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
        fs::write(
            root.path().join("src/lib.rs"),
            format!("pub const TRANSPORT: &str = env!({variable:?});\n"),
        )
        .unwrap();
        assert!(!fresh(&build(root.path(), true)));
        assert!(
            !fresh(&build(root.path(), true)),
            "a new scheduler endpoint cannot replay an artifact that embedded the old endpoint"
        );
    }
}
