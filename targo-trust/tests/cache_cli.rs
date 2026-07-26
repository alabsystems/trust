use std::path::PathBuf;
use std::process::Command;

#[test]
fn cache_help_lists_build_cache_subcommands() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "cache", "--help"])
        .output()
        .expect("run cache help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "cache help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust cache"));
    for expected in ["stats", "gc [--max-size BYTES]", "clear --yes", "info <key-hex>"] {
        assert!(stdout.contains(expected), "missing `{expected}` in {stdout}");
    }
}

#[test]
fn verify_cargo_cache_help_lists_release_materializer() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "cargo-cache", "--help"])
        .output()
        .expect("run verify cargo-cache help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "verify cargo-cache help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust verify cargo-cache"));
    assert!(stdout.contains("--cargo-home <path>"));
    assert!(stdout.contains("registry-only Cargo seed cache"));
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
