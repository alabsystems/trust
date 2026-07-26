use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn rust_vs_trust_cli_domination_upstream_tests_is_first_class_targo_trust_command() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "upstream-tests", "--help"])
        .output()
        .expect("run targo trust domination upstream-tests --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "upstream-tests help should dispatch successfully\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust domination upstream-tests"));
    assert!(!stdout.contains("targo trust rust-vs-trust"));
    assert!(stdout.contains("Rust `trust-upstream-compat port` command"));
    assert!(stdout.contains("--test-exceptions <path>"));
    assert!(stdout.contains("--proof-mode auto|smoke|full"));
    assert!(stdout.contains("Python is not used."));
    assert!(!stdout.contains("upstream-rust-tests"));
}

#[test]
fn rust_vs_trust_cli_alias_is_rejected_with_domination_migration() {
    for args in [
        &["trust", "rust-vs-trust", "--help"][..],
        &["trust", "rust-vs-trust", "upstream-tests", "--help"][..],
    ] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .expect("run removed targo trust rust-vs-trust alias");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "rust-vs-trust alias should be rejected for {args:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("`rust-vs-trust` has been removed")
                && stderr.contains("targo trust domination"),
            "alias rejection should name the canonical domination command\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(!stdout.contains("targo trust rust-vs-trust"));
    }
}

#[test]
fn rust_vs_trust_cli_domination_upstream_rust_tests_alias_is_rejected() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "upstream-rust-tests", "--help"])
        .output()
        .expect("run removed targo trust domination upstream-rust-tests alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "upstream-rust-tests alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("`upstream-rust-tests` has been removed")
            && stderr.contains("targo trust domination upstream-tests"),
        "alias rejection should name the canonical upstream-tests command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!stdout.contains("targo trust domination upstream-tests"));
    assert_no_legacy_execution_path(&stdout);
    assert_no_legacy_execution_path(&stderr);
}

#[test]
fn rust_vs_trust_cli_domination_trust_added_is_manifest_facing_rust_command() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "trust-added", "--help"])
        .env_remove("TRUST_RELEASE_GATE")
        .output()
        .expect("run targo trust domination trust-added --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "trust-added help should dispatch successfully\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust domination trust-added"));
    assert!(stdout.contains("trust-added-compiletest"));
    assert!(stdout.contains("stage0-lineage"));
    assert!(stdout.contains("Diagnostic smoke modes (never canonical release evidence)"));
    assert!(stdout.contains("Rust-native local diagnostics"));
    assert!(stdout.contains("Every canonical release mode remains blocked"));
    assert!(stdout.contains("Smoke aliases cannot cover"));
    assert!(stdout.contains("those canonical inventory IDs"));
    assert_no_legacy_execution_path(&stdout);
    assert_no_legacy_execution_path(&stderr);
}

#[test]
fn rust_vs_trust_cli_domination_trust_added_help_rejects_every_mixed_invocation() {
    for (label, args, release_environment) in [
        ("mode", &["trust", "domination", "trust-added", "quick", "--help"][..], false),
        ("strict", &["trust", "domination", "trust-added", "--strict", "-h"][..], false),
        (
            "explicit release",
            &["trust", "domination", "trust-added", "--help", "--release", "quick"][..],
            false,
        ),
        ("release environment", &["trust", "domination", "trust-added", "--help"][..], true),
    ] {
        let mut command = Command::new(targo_trust_binary());
        command.args(args).env_remove("TRUST_RELEASE_GATE");
        if release_environment {
            command.env("TRUST_RELEASE_GATE", "1");
        }
        let output = command
            .output()
            .unwrap_or_else(|error| panic!("run mixed trust-added help case {label}: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "mixed trust-added help case {label} must fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(if label.contains("release") {
                "`--help` cannot be combined with a release request"
            } else {
                "`--help` must be used by itself"
            }),
            "mixed trust-added help case {label} should explain the usage boundary\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            !stdout.contains("Trust-added proof inventory"),
            "a rejected mixed invocation must not report successful help dispatch"
        );
    }
}

#[test]
fn rust_vs_trust_cli_domination_outer_and_upstream_help_reject_mixed_invocations() {
    for (label, args, expected) in [
        (
            "outer long help",
            &["trust", "domination", "--help", "trust-added", "--release", "quick"][..],
            "targo trust domination: `--help` must be used by itself",
        ),
        (
            "outer short help",
            &["trust", "domination", "-h", "added-tests", "--release", "quick"][..],
            "targo trust domination: `--help` must be used by itself",
        ),
        (
            "upstream release help",
            &["trust", "domination", "upstream-tests", "--release", "--help"][..],
            "targo trust domination upstream-tests: `--help` must be used by itself",
        ),
    ] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("run mixed dispatcher help case {label}: {error}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "mixed dispatcher help case {label} must fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains(expected), "unexpected error for {label}: {stderr}");
        assert!(!stdout.contains("Trust-added proof inventory"));
        assert!(!stdout.contains("Rust-owned upstream test porting"));
    }
}

#[test]
#[cfg(unix)]
fn rust_vs_trust_cli_domination_trust_added_release_help_never_executes_a_sentinel() {
    let temp = TempDir::new("trust-added-release-help-no-exec");
    for (label, args, release_environment) in [
        (
            "explicit",
            &["trust", "domination", "trust-added", "--release", "quick", "--help"][..],
            false,
        ),
        ("environment", &["trust", "domination", "trust-added", "--help"][..], true),
    ] {
        let fake_targo = install_fake_tool(temp.path().join(label).join("targo"), 0);
        let capture = fake_targo.with_extension("argv");
        let mut command = Command::new(targo_trust_binary());
        command.args(args).env("TRUST_TARGO_BIN", &fake_targo).env_remove("TRUST_RELEASE_GATE");
        if release_environment {
            command.env("TRUST_RELEASE_GATE", "1");
        }
        let output = command
            .output()
            .unwrap_or_else(|error| panic!("run release/help sentinel case {label}: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "release/help sentinel case {label} must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains("`--help` cannot be combined with a release request"));
        assert!(
            !capture.exists(),
            "release/help refusal must happen before the configured executable is launched"
        );
    }
}

#[test]
fn rust_vs_trust_cli_domination_native_release_modes_fail_before_execution() {
    for mode in [
        "quick",
        "trust-added-compiletest",
        "trustc-native",
        "native-contracts-pipeline-v2",
        "binary-decompilation-golden",
        "launch",
        "local-stage2-surface-smoke",
        "trust-extra-smoke",
        "public-distribution-cull-smoke",
        "prepublish-local-surface-smoke",
        "stage0-metadata-coherence-smoke",
    ] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "domination", "trust-added", "--release", mode])
            .env("TRUST_TARGO_BIN", "/definitely/not/an/authority/targo")
            .output()
            .unwrap_or_else(|error| panic!("run blocked native release mode {mode}: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{mode} release evidence must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains(&format!("release mode `{mode}` is blocked")));
        assert!(stderr.contains("independently authenticated, isolated environment"));
        assert!(stderr.contains("can never satisfy"));
        assert_no_legacy_execution_path(&stdout);
        assert_no_legacy_execution_path(&stderr);
    }
}

#[test]
fn rust_vs_trust_cli_domination_release_environment_cannot_bypass_the_block() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "trust-added", "quick"])
        .env("TRUST_RELEASE_GATE", "1")
        .output()
        .expect("run native mode with engine-facing release policy");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stderr.contains("release mode `quick` is blocked"));
    assert!(!stdout.contains("LOCAL DIAGNOSTIC PASS"));
}

#[test]
#[cfg(unix)]
fn rust_vs_trust_cli_domination_release_block_never_executes_a_tool_shaped_sentinel() {
    let temp = TempDir::new("trust-added-release-no-exec");
    let fake_targo = install_fake_tool(temp.path().join("build/fake-host/stage2/bin/targo"), 0);
    let capture = fake_targo.with_extension("argv");
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "trust-added", "--release", "quick"])
        .env("TRUST_TARGO_BIN", &fake_targo)
        .output()
        .expect("run blocked release mode with an executable-shaped sentinel");

    assert_eq!(output.status.code(), Some(2));
    assert!(
        !capture.exists(),
        "release refusal must happen before any configured executable is launched"
    );
}

#[test]
fn rust_vs_trust_cli_domination_native_mode_ignores_upstream_repo_redirects() {
    let foreign = TempDir::new("trust-added-foreign-root");
    let output = Command::new(targo_trust_binary())
        .args(["trust", "domination", "trust-added", "stage0-metadata-coherence-smoke"])
        .env("TRUST_UPSTREAM_COMPAT_REPO_ROOT", foreign.path())
        .current_dir(foreign.path())
        .output()
        .expect("run native diagnostic from a redirected foreign checkout");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "trust-added must bind to its compiled checkout, not an upstream-test override or cwd\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("LOCAL DIAGNOSTIC PASS"));
    assert!(stdout.contains("Parsed src/stage0"));
    assert!(!stdout.contains(foreign.path().to_string_lossy().as_ref()));
}

#[test]
fn rust_vs_trust_cli_domination_trust_added_fails_closed_instead_of_shell_dispatch() {
    for (canonical, diagnostic) in [
        ("installed", "local-stage2-surface-smoke"),
        ("installed-default", "local-stage2-surface-smoke"),
        ("trust-extra", "trust-extra-smoke"),
        ("public-distribution", "public-distribution-cull-smoke"),
        ("prepublish", "prepublish-local-surface-smoke"),
        ("stage0-lineage", "stage0-metadata-coherence-smoke"),
    ] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "domination", "trust-added", "--release", canonical])
            .output()
            .unwrap_or_else(|error| panic!("run blocked trust-added mode {canonical}: {error}"));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{canonical} should fail closed until authenticated native execution exists\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains(&format!("canonical mode `{canonical}` is blocked")));
        assert!(stderr.contains(&format!("weaker `{diagnostic}` mode is runnable")));
        assert!(stderr.contains(&format!("can never satisfy `{canonical}` release evidence")));
        assert!(stderr.contains("tests/trust-added/manifest.toml"));
        assert_no_legacy_execution_path(&stdout);
        assert_no_legacy_execution_path(&stderr);
    }
}

#[test]
#[cfg(unix)]
fn rust_vs_trust_cli_domination_upstream_tests_dispatches_to_rust_porting_front_door() {
    let temp = TempDir::new("trust-upstream-tests-dispatch");
    let fake_targo = install_fake_tool(temp.path().join("targo"), 0);
    let capture = fake_targo.with_extension("argv");
    let upstream_args = [
        "upstream-tests",
        "--no-execute",
        "--no-apply",
        "--no-fetch",
        "--max-files",
        "1",
        "--test-exceptions",
        "tests/upstream-rust/test-exceptions.toml",
        "--proof-mode",
        "smoke",
    ];
    let expected_manifest = workspace_root().join("crates/trust-upstream-compat/Cargo.toml");
    let expected_args = vec![
        "run",
        "--manifest-path",
        expected_manifest.to_str().expect("manifest path should be utf-8"),
        "--locked",
        "--",
        "port",
        "--no-execute",
        "--no-apply",
        "--no-fetch",
        "--max-files",
        "1",
        "--test-exceptions",
        "tests/upstream-rust/test-exceptions.toml",
        "--proof-mode",
        "smoke",
    ];

    {
        let args: Vec<&str> =
            ["trust", "domination"].iter().chain(upstream_args.iter()).copied().collect();
        let output = Command::new(targo_trust_binary())
            .args(&args)
            .env("TRUST_UPSTREAM_COMPAT_CARGO", &fake_targo)
            .output()
            .expect("run targo trust upstream-tests through fake targo");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(0),
            "upstream-tests dispatch should use fake targo successfully for {args:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(
                "targo trust domination upstream-tests: dispatching Rust upstream porting CLI"
            ),
            "dispatch should identify the canonical upstream-tests front door for {args:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );

        let captured = fs::read_to_string(&capture).expect("fake targo should capture argv");
        let captured_args: Vec<&str> = captured.lines().collect();
        assert_eq!(
            captured_args, expected_args,
            "canonical command should forward to Rust porting CLI for {args:?}"
        );
        assert_no_legacy_execution_path(&captured);
        assert_no_legacy_execution_path(&stdout);
        assert_no_legacy_execution_path(&stderr);
    }
}

#[test]
#[cfg(unix)]
fn rust_vs_trust_cli_domination_upstream_tests_release_rejects_configured_ambient_cargo() {
    let temp = TempDir::new("trust-upstream-tests-release-guard");
    let fake_cargo = install_fake_tool(temp.path().join("cargo"), 0);
    let capture = fake_cargo.with_extension("argv");
    let args = [
        "trust",
        "domination",
        "upstream-tests",
        "--release",
        "--no-execute",
        "--no-apply",
        "--no-fetch",
        "--max-files",
        "1",
    ];

    let output = Command::new(targo_trust_binary())
        .args(args)
        .env("TRUST_UPSTREAM_COMPAT_CARGO", &fake_cargo)
        .output()
        .expect("run targo trust domination upstream-tests --release with fake cargo");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "release upstream-tests should reject configured ambient upstream cargo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("upstream porting requires Trust targo"),
        "release rejection should explain the Trust targo requirement\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("TRUST_UPSTREAM_COMPAT_CARGO"),
        "release rejection should name the configured source\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!capture.exists(), "rejected ambient upstream cargo must not be executed");
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
        .join("..")
        .canonicalize()
        .expect("workspace root should be canonicalizable")
}

#[cfg(unix)]
fn install_fake_tool(path: PathBuf, exit_code: i32) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("fake tool parent should be creatable");
    }
    fs::write(
        &path,
        format!(
            r#"#!/bin/sh
set -eu
capture="$0.argv"
: > "$capture"
for arg in "$@"; do
  printf '%s\n' "$arg" >> "$capture"
done
exit {exit_code}
"#
        ),
    )
    .expect("fake tool should be writable");
    let mut permissions = fs::metadata(&path).expect("fake tool metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("fake tool permissions should be set");
    path
}

fn assert_no_legacy_execution_path(text: &str) {
    let lower = text.to_ascii_lowercase();
    for forbidden in
        ["python", "x.py", "bash ", ".sh", "run_trust_superset_suite", "run_trust_robust_suite"]
    {
        assert!(
            !lower.contains(forbidden),
            "legacy upstream Rust execution path marker `{forbidden}` found in:\n{text}"
        );
    }
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
        fs::create_dir_all(&path).expect("temporary test directory should be creatable");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
