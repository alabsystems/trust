use std::path::PathBuf;
use std::process::Command;

#[test]
fn top_level_help_names_targo_as_canonical_frontend() {
    let help = Command::new(targo_trust_binary())
        .args(["trust", "--help"])
        .output()
        .expect("run trust help");

    let stdout = String::from_utf8_lossy(&help.stdout);
    let stderr = String::from_utf8_lossy(&help.stderr);
    assert_eq!(
        help.status.code(),
        Some(0),
        "top-level help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("Canonical frontend: targo is the Trust Cargo replacement"),
        "top-level help should teach the canonical Trust Cargo replacement\nstdout:\n{stdout}"
    );
    assert!(stdout.contains("targo trust check [file]"));
    assert!(stdout.contains("targo trust verify cargo-cache"));
    assert!(!stdout.contains("targo trust verify full-preflight"));
    assert!(!stdout.contains("Removed Python full-preflight backend"));
    assert!(!stdout.contains("Confirm removed backend rejection"));
    assert!(
        !stdout.lines().any(|line| line.trim_start().starts_with("cargo trust ")),
        "top-level help must not advertise deprecated cargo trust spelling\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.contains(".py"),
        "top-level help must not expose Python script implementation names\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("x.py"),
        "top-level help must not expose bootstrap x.py naming\nstdout:\n{stdout}"
    );
}

#[test]
fn verify_help_advertises_cargo_cache_and_release_verify_commands() {
    let help = Command::new(targo_trust_binary())
        .args(["trust", "verify", "--help"])
        .output()
        .expect("run verify help");

    let stdout = String::from_utf8_lossy(&help.stdout);
    let stderr = String::from_utf8_lossy(&help.stderr);
    assert_eq!(
        help.status.code(),
        Some(0),
        "verify help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("cargo-cache"),
        "verify help should advertise routed cargo-cache command\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("targo trust verify cargo-cache"),
        "verify help examples should include the cargo-cache command\nstdout:\n{stdout}"
    );
    assert!(stdout.contains("repo-gate"));
    assert!(stdout.contains("solvers"));
    assert!(stdout.contains("self"));
    assert!(!stdout.contains("full-preflight"));
    assert!(!stdout.contains("native-solver-sample"));
    assert!(!stdout.contains("compiler verifier readiness adapter"));
    assert!(
        !stdout.contains(".py"),
        "verify help must keep transitional script names out of the public surface\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("x.py"),
        "verify help must keep bootstrap runner names out of the public surface\nstdout:\n{stdout}"
    );

    let cargo_cache = Command::new(targo_trust_binary())
        .args(["trust", "verify", "cargo-cache", "--help"])
        .output()
        .expect("run verify cargo-cache help");
    let stdout = String::from_utf8_lossy(&cargo_cache.stdout);
    let stderr = String::from_utf8_lossy(&cargo_cache.stderr);
    assert_eq!(
        cargo_cache.status.code(),
        Some(0),
        "verify cargo-cache help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("Usage: targo trust verify cargo-cache"));
    assert!(stdout.contains("--repo-root <path>"));
    assert!(stdout.contains("--cargo-home <path>"));
    assert!(stdout.contains("--json-output <path>"));
}

#[test]
fn removed_verify_aliases_point_to_canonical_commands() {
    for (alias, replacement) in [
        ("example-corpus", "targo trust verify examples"),
        ("verify-examples", "targo trust verify examples"),
        ("cache-materialize", "targo trust verify cargo-cache"),
        ("cache-materialization", "targo trust verify cargo-cache"),
        ("solver-check", "targo trust verify solvers"),
        ("gate", "targo trust verify repo-gate"),
        ("check-all", "targo trust verify repo-gate"),
        ("compiler", "targo trust verify self --full-verifier"),
        ("compiler-verifier", "targo trust verify self --full-verifier"),
        ("native-solver-sample", "targo trust verify solvers"),
    ] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "verify", alias, "--help"])
            .output()
            .unwrap_or_else(|error| panic!("run verify {alias} help: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed verify alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stdout.trim().is_empty(), "removed aliases should not print old help");
        assert!(
            stderr.contains("removed alias") && stderr.contains(replacement),
            "removed alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    let preflight = Command::new(targo_trust_binary())
        .args(["trust", "verify", "preflight", "--help"])
        .output()
        .expect("run verify preflight help");
    let stdout = String::from_utf8_lossy(&preflight.stdout);
    let stderr = String::from_utf8_lossy(&preflight.stderr);
    assert_eq!(
        preflight.status.code(),
        Some(2),
        "removed release preflight alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed release alias should not print old help");
    assert!(stderr.contains("removed shell/Python-era release alias"), "{stderr}");
    assert!(stderr.contains("targo trust verify cargo-cache"), "{stderr}");
    assert!(stderr.contains("targo trust release check"), "{stderr}");
    assert!(!stderr.contains("targo trust verify full-preflight"), "{stderr}");
}

#[test]
fn examples_verify_alias_points_to_canonical_verify_examples() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "examples", "verify", "--help"])
        .output()
        .expect("run removed examples verify alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "examples verify alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not print old help");
    assert!(
        stderr.contains("removed alias; use `targo trust verify examples`"),
        "examples verify alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
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
