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

/// The removed `deps` aliases must NAME their replacement on stderr instead of
/// falling through to the generic `unknown command` usage dump.
///
/// Nothing in this repository calls these arms — their only callers are users
/// and scripts typing the pre-rename spelling — so a dead-code sweep reads them
/// as dead and deletes them, which is exactly what fc5a9655a0 did. The absence
/// of a test is what let that regression stay invisible; this is that test.
#[test]
fn removed_deps_aliases_point_to_canonical_commands() {
    for (alias, replacement) in [
        (&["report"][..], "targo trust deps status"),
        (&["verify"][..], "targo trust deps validate"),
        (&["alignment"][..], "targo trust deps status"),
        (&["alignment", "status"][..], "targo trust deps status"),
        (&["inventory"][..], "targo trust deps upstream-test-inventory"),
    ] {
        let spelling = alias.join(" ");
        let mut args = vec!["trust", "deps"];
        args.extend_from_slice(alias);
        args.push("--help");

        let output = Command::new(targo_trust_binary())
            .args(&args)
            .output()
            .unwrap_or_else(|error| panic!("run deps {spelling} help: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed deps alias `{spelling}` should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "removed alias should not print old help\nstdout:\n{stdout}"
        );
        assert!(
            stderr.contains(&format!(
                "targo trust deps {spelling}: removed alias; use `{replacement}`"
            )),
            "removed deps alias `{spelling}` should name the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

/// The removed `bootstrap` aliases carry the same contract as the `repo`,
/// `verify` and `gate` arms: exit `2`, nothing on stdout, and the canonical
/// spelling named on stderr.
#[test]
fn removed_bootstrap_aliases_point_to_canonical_commands() {
    for (alias, replacement) in [
        ("create-genesis", "targo trust bootstrap create-local-genesis"),
        ("discover-stage0-seed", "targo trust bootstrap discover-stage0"),
    ] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "bootstrap", alias, "--help"])
            .output()
            .unwrap_or_else(|error| panic!("run bootstrap {alias} help: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed bootstrap alias `{alias}` should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
        assert!(
            stderr.contains(&format!(
                "targo trust bootstrap {alias}: removed alias; use `{replacement}`"
            )),
            "removed bootstrap alias `{alias}` should name the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

/// `bootstrap script-syntax` is NOT a removed alias and must never grow one.
///
/// `script-syntax` only ever existed under `repo` (-> `repo scripts`) and
/// `gate` (-> `gate scripts`); both are restored and covered in repo_cli.rs and
/// gate_cli.rs. A name `bootstrap` never carried deserves the honest
/// `unknown command` answer plus the bootstrap usage listing, not an invented
/// redirect — this pins that distinction against a future restoration pass.
#[test]
fn bootstrap_script_syntax_is_an_unknown_command_not_a_removed_alias() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "bootstrap", "script-syntax", "--help"])
        .output()
        .expect("run bootstrap script-syntax help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "an unrecognized bootstrap leaf must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "unknown command should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains("targo trust bootstrap: unknown command `script-syntax`"),
        "unknown bootstrap command should say so\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("Usage: targo trust bootstrap <command>"),
        "unknown bootstrap command should print the bootstrap usage\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("removed alias"),
        "bootstrap never carried `script-syntax`, so no replacement may be invented\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// `targo trust kani` was deleted OUTRIGHT (R2 deletion D-A), not renamed, so
/// its guidance names no replacement subcommand — it says where the surface
/// went. It must also not repeat the pre-sweep claim that a `kani` dependency
/// stays fail-closed in `targo trust build`: the 2026-07-26 amendment
/// (two-language design v5 §3.2) replaced that rejection with a disclosure, so
/// restoring the old sentence verbatim would have shipped a lie about the gate.
#[test]
fn removed_top_level_kani_subcommand_explains_its_deletion() {
    for args in [&["trust", "kani"][..], &["trust", "kani", "--help"][..]] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("run removed kani subcommand {args:?}: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed kani subcommand should be rejected for {args:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "removed subcommand should print nothing on stdout\nstdout:\n{stdout}"
        );
        assert!(
            stderr.contains("`kani` has been removed (R2 deletion D-A)")
                && stderr.contains("no replacement subcommand"),
            "kani guidance should state the deletion and that nothing replaces it\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("#[kani::harness]")
                && stderr.contains("targo trust build")
                && stderr.contains("targo trust check"),
            "kani guidance should route to the native harness lane and the live commands\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            !stderr.to_lowercase().contains("fail-closed"),
            "a kani dependency now DISCLOSES rather than failing the build; the guidance must not re-assert the retired rejection\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("unknown subcommand"),
            "the removed spelling must be answered by name, not by the generic usage dump\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
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
