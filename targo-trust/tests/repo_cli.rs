use std::path::PathBuf;
use std::process::Command;

#[test]
fn repo_help_lists_submodule_reachability_gate() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "--help"])
        .output()
        .expect("run repo help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "repo help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("submodule-reachability"));
    assert!(stdout.contains("targo trust repo submodule-reachability --json"));
    assert!(
        !stdout.contains(".py"),
        "repo help must not expose Python script names or bootstrap x.py naming\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.lines().any(|line| line.trim_start().starts_with("cargo trust ")),
        "repo help must not advertise deprecated cargo trust spelling\nstdout:\n{stdout}"
    );
}

#[test]
fn repo_check_help_uses_repo_command_name() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "check", "--help"])
        .output()
        .expect("run repo check help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "repo check help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust repo check"));
    assert!(
        !stdout.contains("targo trust gate check-all"),
        "repo check help should not relabel itself as the gate command\nstdout:\n{stdout}"
    );
}

#[test]
fn repo_verify_examples_command_remains_compatible() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "verify-examples", "--help"])
        .output()
        .expect("run repo verify-examples help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "repo verify-examples should remain compatible\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust verify examples"));
}

#[test]
fn repo_check_all_alias_is_removed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "check-all", "--help"])
        .output()
        .expect("run removed repo check-all alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "repo check-all alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("removed alias; use `targo trust repo check`"),
        "repo check-all alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn repo_script_syntax_alias_is_removed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "script-syntax", "--help"])
        .output()
        .expect("run removed repo script-syntax alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "repo script-syntax alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("removed alias; use `targo trust repo scripts`"),
        "repo script-syntax alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn repo_examples_alias_is_removed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "examples", "--help"])
        .output()
        .expect("run removed repo examples alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "repo examples alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("removed alias; use `targo trust repo verify-examples`"),
        "repo examples alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn repo_submodule_reachability_dispatches_to_script() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "repo", "submodule-reachability", "--help"])
        .env("TRUST_REPO_ROOT", workspace_root())
        .output()
        .expect("run repo submodule reachability help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "submodule reachability script help should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("Fail closed when parent-pinned submodule commits are not contained")
            && stdout.contains("--self-check"),
        "repo command should dispatch to scripts/check_submodule_remote_reachability.py help\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("usage: targo trust repo submodule-reachability"),
        "repo command help should expose the targo command name\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("deprecated Python-backed adapter"),
        "repo command should mark script-backed adapter as deprecated\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("check_submodule_remote_reachability.py"),
        "repo command help should not expose the Python script filename\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
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

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust manifest should live under workspace root")
        .to_path_buf()
}
