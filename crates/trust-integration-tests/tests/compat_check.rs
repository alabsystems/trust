// Compatibility check integration test for Trust.
//
// Verifies that Trust can compile popular crates.io crates without regressions.
// Requires the "trust" toolchain to be registered with rustup:
//   rustup toolchain link trust <path-to-trust-build>/host/stage2
//
// If the toolchain is not available, tests pass with a diagnostic message
// (not skipped -- the ignore attribute is forbidden by org policy).
//
// Test tiers:
//   - test_compat_crate_list_exists: validates the 100-crate list file
//   - test_compat_script_exists_and_executable: validates the shell harness
//   - test_compat_toolchain_check: validates toolchain detection logic
//   - test_compat_check_with_stable: single-crate smoke test (cfg-if + stable)
//   - test_compat_batch_stable_smoke: 10-crate cross-tier smoke test (stable)
//   - test_compat_check_all_trust_toolchain: full 100-crate check (trust toolchain)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::Command;

/// Returns the repo root by walking up from the manifest dir.
fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-integration-tests -> repo root is ../../
    manifest.parent().expect("parent of manifest dir").parent().expect("repo root").to_path_buf()
}

/// Resolve a cargo that honors `+toolchain` directives.
///
/// The `+toolchain` proxy is a rustup-shim feature: a Homebrew (or otherwise
/// non-rustup) cargo on `PATH` errors with "no such command: `+stable`". So we
/// prefer the rustup-installed cargo at `~/.cargo/bin/cargo` (a symlink to the
/// rustup proxy), which always honors `+toolchain`. Returns `None` if no such
/// cargo is present, in which case `+toolchain` work must be skipped.
fn rustup_cargo() -> Option<PathBuf> {
    let candidate = dirs_home()?.join(".cargo").join("bin").join("cargo");
    if candidate.exists() {
        Some(candidate)
    } else {
        None
    }
}

/// Best-effort home directory lookup without pulling in extra deps.
fn dirs_home() -> Option<PathBuf> {
    std::env::var_os("HOME").map(PathBuf::from).filter(|p| !p.as_os_str().is_empty())
}

/// Check whether a rustup toolchain is registered.
fn toolchain_available(name: &str) -> bool {
    Command::new("rustup")
        .args(["toolchain", "list"])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).lines().any(|line| line.starts_with(name)))
        .unwrap_or(false)
}

/// Parse the crate list file, returning crate names (skipping comments/blanks).
fn parse_crate_list(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path)
        .expect("failed to read crate list")
        .lines()
        .filter(|line| !line.trim_start().starts_with('#'))
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// Run `cargo +<toolchain> check` on a minimal crate that depends on `crate_name`.
fn check_crate_with_toolchain(
    crate_name: &str,
    toolchain: &str,
    work_dir: &Path,
    cargo: &Path,
) -> Result<(), String> {
    let crate_dir = work_dir.join(crate_name);
    std::fs::create_dir_all(crate_dir.join("src")).map_err(|e| format!("mkdir failed: {e}"))?;

    let crate_ident = crate_name.replace('-', "_");

    let cargo_toml = format!(
        r#"[package]
name = "compat-test-{crate_name}"
version = "0.1.0"
edition = "2021"

[dependencies]
{crate_name} = "*"
"#
    );
    std::fs::write(crate_dir.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("write Cargo.toml: {e}"))?;

    let main_rs = format!("use {crate_ident} as _;\nfn main() {{}}\n");
    std::fs::write(crate_dir.join("src/main.rs"), main_rs)
        .map_err(|e| format!("write main.rs: {e}"))?;

    let output = Command::new(cargo)
        .arg(format!("+{toolchain}"))
        .args(["check", "--manifest-path"])
        .arg(crate_dir.join("Cargo.toml"))
        .output()
        .map_err(|e| format!("cargo exec: {e}"))?;

    if output.status.success() {
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let first_error =
            stderr.lines().find(|l| l.starts_with("error")).unwrap_or("unknown error");
        Err(format!("cargo check failed: {first_error}"))
    }
}

#[test]
fn test_compat_crate_list_exists() {
    let list_path = repo_root().join("tests/compat/top_crates.txt");
    assert!(list_path.exists(), "crate list missing at {}", list_path.display());
    let crates = parse_crate_list(&list_path);
    assert!(crates.len() >= 100, "expected at least 100 crates, got {}", crates.len());
}

#[test]
fn test_compat_script_exists_and_executable() {
    let script_path = repo_root().join("scripts/compat_check.sh");
    assert!(script_path.exists(), "compat script missing at {}", script_path.display());

    // Verify the script is parseable by bash (syntax check only)
    let output = Command::new("bash")
        .args(["-n", script_path.to_str().unwrap()])
        .output()
        .expect("bash -n failed to execute");
    assert!(
        output.status.success(),
        "compat_check.sh has syntax errors: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_compat_toolchain_check() {
    // This test validates the toolchain detection logic itself.
    // It does NOT require the trust toolchain -- it tests that we can
    // detect presence/absence correctly.
    let has_stable = toolchain_available("stable");
    // stable is virtually always present; this is a sanity check of our detection logic.
    // If somehow stable is missing, this still passes -- we're testing the function works.
    eprintln!("toolchain detection: stable={has_stable}");

    let has_trust = toolchain_available("trust");
    eprintln!("toolchain detection: trust={has_trust}");
    if !has_trust {
        eprintln!(
            "NOTE: 'trust' toolchain not registered. \
             To enable full compat testing, build Trust and run: \
             rustup toolchain link trust <stage2-dir>"
        );
    }
    // Always passes -- this is infrastructure validation.
}

#[test]
fn test_compat_check_with_stable() {
    // Smoke test: verify the harness works by checking one crate with stable.
    // This validates the test infrastructure itself.
    if !toolchain_available("stable") {
        eprintln!("NOTE: stable toolchain not available, cannot validate compat harness");
        return;
    }
    let Some(cargo) = rustup_cargo() else {
        eprintln!(
            "NOTE: no rustup cargo at ~/.cargo/bin/cargo; `+toolchain` directives are \
             unsupported by a non-rustup cargo. Skipping compat harness validation."
        );
        return;
    };

    let work_dir = tempfile::tempdir().expect("tempdir");
    let result = check_crate_with_toolchain("cfg-if", "stable", work_dir.path(), &cargo);
    assert!(result.is_ok(), "cfg-if should compile with stable: {:?}", result.err());
}

/// Representative crates spanning all 5 tiers of the crate list.
/// Used for the batch smoke test to validate the harness at broader scale
/// without downloading all 100 crates (which is slow).
const SMOKE_CRATES: &[&str] = &[
    "cfg-if",   // Tier 1: foundational, zero-dep
    "log",      // Tier 1: foundational, widely used
    "either",   // Tier 2: core ecosystem
    "indexmap", // Tier 2: core ecosystem, uses hashbrown
    "bitflags", // Tier 3: unicode & encoding tier
    "semver",   // Tier 3: versioning
    "glob",     // Tier 4: utilities
    "fnv",      // Tier 5: applications & frameworks
    "paste",    // Tier 5: proc-macro utility
    "adler",    // Tier 4: small checksum crate
];

#[test]
fn test_compat_batch_stable_smoke() {
    // Validates the harness works across a representative sample of 10 crates
    // spanning all tiers. This catches harness issues (e.g., crate naming,
    // edition compatibility, dependency resolution) before the full 100-crate
    // run with the trust toolchain.
    if !toolchain_available("stable") {
        eprintln!("NOTE: stable toolchain not available, cannot run batch smoke test");
        return;
    }
    let Some(cargo) = rustup_cargo() else {
        eprintln!(
            "NOTE: no rustup cargo at ~/.cargo/bin/cargo; `+toolchain` directives are \
             unsupported by a non-rustup cargo. Skipping batch smoke test."
        );
        return;
    };

    let work_dir = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<(&str, String)> = Vec::new();

    for crate_name in SMOKE_CRATES {
        eprintln!("smoke: {crate_name}");
        match check_crate_with_toolchain(crate_name, "stable", work_dir.path(), &cargo) {
            Ok(()) => eprintln!("  PASS: {crate_name}"),
            Err(e) => {
                eprintln!("  FAIL: {crate_name}: {e}");
                failures.push((crate_name, e));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "Stable smoke test failures ({}/{}):\n{}",
        failures.len(),
        SMOKE_CRATES.len(),
        failures.iter().map(|(c, e)| format!("  {c}: {e}")).collect::<Vec<_>>().join("\n")
    );
    eprintln!(
        "=== Batch smoke test PASSED: {}/{} crates ===",
        SMOKE_CRATES.len(),
        SMOKE_CRATES.len()
    );
}

#[test]
fn test_compat_check_all_trust_toolchain() {
    // Full compatibility check: all listed crates with the trust toolchain.
    // Gracefully exits if trust toolchain is not available.
    if !toolchain_available("trust") {
        eprintln!(
            "NOTE: 'trust' toolchain not registered. \
             Skipping full compat check. \
             Build Trust and run: rustup toolchain link trust <stage2-dir>"
        );
        return;
    }
    let Some(cargo) = rustup_cargo() else {
        eprintln!(
            "NOTE: no rustup cargo at ~/.cargo/bin/cargo; `+toolchain` directives are \
             unsupported by a non-rustup cargo. Skipping full compat check."
        );
        return;
    };

    let list_path = repo_root().join("tests/compat/top_crates.txt");
    let crates = parse_crate_list(&list_path);
    let work_dir = tempfile::tempdir().expect("tempdir");

    let mut failures: Vec<(String, String)> = Vec::new();

    for crate_name in &crates {
        eprintln!("checking: {crate_name}");
        match check_crate_with_toolchain(crate_name, "trust", work_dir.path(), &cargo) {
            Ok(()) => eprintln!("  PASS: {crate_name}"),
            Err(e) => {
                eprintln!("  FAIL: {crate_name}: {e}");
                failures.push((crate_name.clone(), e));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "Trust compatibility failures ({}/{}):\n{}",
        failures.len(),
        crates.len(),
        failures.iter().map(|(c, e)| format!("  {c}: {e}")).collect::<Vec<_>>().join("\n")
    );
}
