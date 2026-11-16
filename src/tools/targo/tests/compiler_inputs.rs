#![cfg(target_os = "macos")]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn build(root: &Path, state: &Path, confined: bool) -> Output {
    let executable = std::env::var_os("TARGO_COMPILER_INPUT_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", state)
        .env("CARGO_HOME", state.join("home"))
        .env("CARGO_TARGET_DIR", state.join("target"))
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
    command.output().unwrap()
}

#[test]
fn a_confined_compiler_cannot_read_an_unhashed_sibling_tool() {
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temp.path().join("source");
    let state = temp.path().join("state");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir(&state).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='compiler_inputs'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    let other_tool = std::env::var_os("RUSTDOC").expect("matching SDK rustdoc");
    let other_tool = Path::new(&other_tool).canonicalize().unwrap();
    fs::write(
        root.join("src/lib.rs"),
        format!("pub const LENGTH: usize = include_bytes!({other_tool:?}).len();\n"),
    )
    .unwrap();
    let ordinary = build(&root, &state, false);
    assert!(
        ordinary.status.success(),
        "{}",
        String::from_utf8_lossy(&ordinary.stderr)
    );
    let confined = build(&root, &state, true);
    assert!(
        !confined.status.success(),
        "unhashed SDK contents were readable: {}",
        String::from_utf8_lossy(&confined.stdout)
    );
    assert!(
        String::from_utf8_lossy(&confined.stdout).contains("Operation not permitted"),
        "{}\n{}",
        String::from_utf8_lossy(&confined.stdout),
        String::from_utf8_lossy(&confined.stderr)
    );
}
