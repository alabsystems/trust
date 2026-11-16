// Compatibility check integration test for Trust.
//
// Verifies that Trust can compile popular crates.io crates without regressions.
//
// This is a drop-in COMPILE compatibility check ("all valid Rust compiles
// identically"), not a verification census. Every compile runs through the
// Trust build tool in its explicit unverified lane, `targo --unverified check`:
// the proof pipeline is off for every unit and no proof claim is made, which is
// the vanilla-comparison posture of docs/TOOLCHAIN_POSTURE.md §4.3 with the
// lane owned by targo instead of hand-set `-Ztrust-verify=off` flags.
// `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` are cleared so an inherited flag cannot
// change the lane. A crate that fails here failed to COMPILE under Trust.
//
// The build tool is `$CARGO` (targo sets it to itself for test processes),
// else `targo`, and it must accept `--unverified --version` — the only
// discriminator between targo and upstream cargo under the same name
// (CLAUDE.md). Anything else FAILS these tests loudly. Until 2026-09-28 they
// drove rustup `cargo +stable`/`cargo +trust` proxies and returned early with a
// NOTE when `~/.cargo/bin/cargo` was absent, so on an aterm machine (no rustup
// proxies) every tier "passed" having compiled nothing (all ALab systems
// build with Trust; the stock `+stable` tiers are gone).
//
// Test tiers:
//   - test_compat_crate_list_exists: validates the crate list file
//   - test_compat_script_exists_and_executable: validates the shell harness
//   - test_compat_toolchain_check: the build tool is really targo
//   - test_compat_lane_is_the_explicit_unverified_lane: the compile argv/env
//   - test_compat_check_smoke: single-crate smoke test (cfg-if)
//   - test_compat_batch_smoke: 10-crate cross-tier smoke test
//   - test_compat_check_all_trust_toolchain: the full crate list, #[ignore]d
//     here (see below)
//   - test_compat_verified_posture_scopes_only_first_party: `targo trust check`
//     on a serde fixture analyzes only the first-party unit and preserves the
//     PM-1 authority refusal for its in-process derive macro
//   - test_verified_posture_classifier_refutes_mutants: its classifier refutes
//     a blanket off-switch, a re-verified dependency and a silent graph, and
//     its exit check refuses every exit but an advisory pass, measured or not
//
// WHERE THE FULL LIST RUNS. The 123-crate list tier took 1129 s on its own
// (measured 2026-09-28, --test-threads=4): more than every other test of a
// typical push together, paid by every push that touches this crate, since
// `scoped.crates-tests` runs every touched member's tests. (Until 2026-10-28
// that lane also had a flat 1200 s budget, which this tier alone would have
// used up; CRATES-TIME-1 replaced it with a stall bound.) The same list
// (tests/compat/top_crates.txt) is the release row
// `release.crates-io-native-compat` (scripts/compat_check.sh), which compiles
// it through `targo --unverified` and writes a receipt. So the tier is
// #[ignore]d here, visibly — it reports `ignored`, never a pass — and a
// developer can still run it: `targo --unverified test -p
// trust-integration-tests --test compat_check -- --ignored`. The fast tiers
// (lane, toolchain identity, cfg-if smoke, the 10-crate batch, the live
// posture test, the classifier mutants) stay in the push lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// Returns the repo root by walking up from the manifest dir.
fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-integration-tests -> repo root is ../../
    manifest.parent().expect("parent of manifest dir").parent().expect("repo root").to_path_buf()
}

/// The Trust build tool: `$CARGO` if set (targo sets it to itself for test
/// processes), else `targo`. Panics unless it accepts `--unverified --version`:
/// upstream cargo rejects that flag, so a stock Cargo can never stand in here.
fn trust_targo() -> PathBuf {
    let targo =
        std::env::var_os("CARGO").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("targo"));
    let output = Command::new(&targo)
        .args(["--unverified", "--version"])
        .output()
        .unwrap_or_else(|e| panic!("cannot run `{} --unverified --version`: {e}", targo.display()));
    assert!(
        output.status.success(),
        "`{} --unverified --version` failed: this is not the Trust build tool (upstream cargo \
         rejects the flag). Run this suite with `targo --unverified test`.\n{}",
        targo.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    targo
}

/// A scratch directory under Cargo's per-target tmp dir. `targo trust` refuses a
/// target directory under a world-writable directory such as `/tmp`, so the
/// fixtures never live in the system temp dir.
fn scratch_dir() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("compat-check-")
        .tempdir_in(env!("CARGO_TARGET_TMPDIR"))
        .expect("tempdir under CARGO_TARGET_TMPDIR")
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

/// The compile-compatibility command: `targo --unverified check` on one
/// manifest, into `target_dir`, with every inherited channel that could change
/// the lane or swap the compiler cleared.
fn compat_check_command(targo: &Path, manifest: &Path, target_dir: &Path) -> Command {
    let mut command = Command::new(targo);
    command
        .args(["--unverified", "check", "--manifest-path"])
        .arg(manifest)
        .env("CARGO_TARGET_DIR", target_dir)
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .env_remove("RUSTC")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER");
    command
}

/// Write a minimal binary crate at `crate_dir` with one `[dependencies]` line.
fn write_fixture_crate(
    crate_dir: &Path,
    package_name: &str,
    dependency_line: &str,
    main_rs: &str,
) -> Result<(), String> {
    std::fs::create_dir_all(crate_dir.join("src")).map_err(|e| format!("mkdir failed: {e}"))?;
    // `[workspace]`: the fixture lives under the repository's target dir, and
    // must not be taken for a member of the enclosing workspace.
    let cargo_toml = format!(
        r#"[package]
name = "{package_name}"
version = "0.1.0"
edition = "2021"

[dependencies]
{dependency_line}

[workspace]
"#
    );
    std::fs::write(crate_dir.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("write Cargo.toml: {e}"))?;
    std::fs::write(crate_dir.join("src/main.rs"), main_rs)
        .map_err(|e| format!("write main.rs: {e}"))
}

/// Run `targo --unverified check` on a minimal crate that depends on `crate_name`.
fn check_crate_unverified(crate_name: &str, work_dir: &Path, targo: &Path) -> Result<(), String> {
    let crate_dir = work_dir.join(crate_name);
    let crate_ident = crate_name.replace('-', "_");
    write_fixture_crate(
        &crate_dir,
        &format!("compat-test-{crate_name}"),
        &format!("{crate_name} = \"*\""),
        &format!("use {crate_ident} as _;\nfn main() {{}}\n"),
    )?;

    let output =
        compat_check_command(targo, &crate_dir.join("Cargo.toml"), &work_dir.join("target"))
            .output()
            .map_err(|e| format!("targo exec: {e}"))?;

    if output.status.success() {
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let first_error =
            stderr.lines().find(|l| l.starts_with("error")).unwrap_or("unknown error");
        Err(format!("targo --unverified check failed: {first_error}"))
    }
}

/// Check every crate in `crates`, returning the failures.
fn check_crates(crates: &[&str], targo: &Path) -> Vec<(String, String)> {
    let work_dir = scratch_dir();
    let mut failures = Vec::new();
    for crate_name in crates {
        eprintln!("checking: {crate_name}");
        match check_crate_unverified(crate_name, work_dir.path(), targo) {
            Ok(()) => eprintln!("  PASS: {crate_name}"),
            Err(e) => {
                eprintln!("  FAIL: {crate_name}: {e}");
                failures.push((crate_name.to_string(), e));
            }
        }
    }
    failures
}

fn render_failures(failures: &[(String, String)]) -> String {
    failures.iter().map(|(c, e)| format!("  {c}: {e}")).collect::<Vec<_>>().join("\n")
}

#[test]
fn test_compat_lane_is_the_explicit_unverified_lane() {
    use std::ffi::OsStr;

    let command = compat_check_command(
        Path::new("/pkg/bin/targo"),
        Path::new("/fixture/Cargo.toml"),
        Path::new("/fixture/target"),
    );
    let args: Vec<&OsStr> = command.get_args().collect();
    assert_eq!(
        args,
        ["--unverified", "check", "--manifest-path", "/fixture/Cargo.toml"].map(OsStr::new),
        "the lane flag must precede the verb: a lane-less `targo check` is refused"
    );
    let envs: Vec<(&OsStr, Option<&OsStr>)> = command.get_envs().collect();
    for cleared in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTFLAGS", "RUSTC"] {
        assert!(
            envs.contains(&(OsStr::new(cleared), None)),
            "{cleared} must be cleared so it cannot change the lane: {envs:?}"
        );
    }
    assert!(
        !envs.iter().any(|(_, value)| value.is_some_and(|v| v.to_string_lossy().contains("-Z"))),
        "the lane belongs to targo; no -Z flag is hand-set: {envs:?}"
    );
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
    // The build tool this suite drives is the Trust targo, and it names its
    // own toolchain. This replaces the old rustup `toolchain list` probe,
    // which "always passed" whatever it found.
    let targo = trust_targo();
    let version = Command::new(&targo)
        .args(["--unverified", "--version"])
        .output()
        .expect("targo --unverified --version");
    let text = String::from_utf8_lossy(&version.stdout);
    eprintln!("compat build tool: {} -> {}", targo.display(), text.trim());
    assert!(text.starts_with("targo "), "unexpected targo identity: {text}");
}

#[test]
fn test_compat_check_smoke() {
    // Smoke test: the harness compiles one crate under the Trust toolchain.
    let targo = trust_targo();
    let failures = check_crates(&["cfg-if"], &targo);
    assert!(
        failures.is_empty(),
        "cfg-if must compile under Trust:\n{}",
        render_failures(&failures)
    );
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
fn test_compat_batch_smoke() {
    // Validates the harness across a representative sample of 10 crates
    // spanning all tiers, under the Trust toolchain. This catches harness
    // issues (crate naming, edition compatibility, dependency resolution)
    // before the full-list run.
    let targo = trust_targo();
    let failures = check_crates(SMOKE_CRATES, &targo);
    assert!(
        failures.is_empty(),
        "Trust smoke test failures ({}/{}):\n{}",
        failures.len(),
        SMOKE_CRATES.len(),
        render_failures(&failures)
    );
    eprintln!(
        "=== Batch smoke test PASSED: {}/{} crates ===",
        SMOKE_CRATES.len(),
        SMOKE_CRATES.len()
    );
}

#[test]
#[ignore = "full list runs as release.crates-io-native-compat (scripts/compat_check.sh); \
            at 1129 s alone it is too heavy for every push of this crate (file header)"]
fn test_compat_check_all_trust_toolchain() {
    // Full compatibility check: every listed crate under the Trust toolchain,
    // in the explicit unverified lane (see the file header).
    let targo = trust_targo();
    let list_path = repo_root().join("tests/compat/top_crates.txt");
    let crates = parse_crate_list(&list_path);
    let names: Vec<&str> = crates.iter().map(String::as_str).collect();
    let failures = check_crates(&names, &targo);
    assert!(
        failures.is_empty(),
        "Trust compatibility failures ({}/{}):\n{}",
        failures.len(),
        crates.len(),
        render_failures(&failures)
    );
}

// ---------------------------------------------------------------------------
// The verified posture a user gets.
//
// The compile lane above turns verification off for every unit, so it cannot
// notice a regression in the posture a real consumer runs: `targo trust check`
// verifies the first-party unit and excludes every host unit (build scripts,
// proc-macros) and third-party dependency unit from the proof frontier, per
// unit, with no hand-written flags. (Until 2026-09-28 this test wrote the
// docs/TOOLCHAIN_POSTURE.md §4.2.1 `.cargo/config.toml` three-lane off-switch
// config and ran `cargo +trust`; the verified Targo lane owns that scoping now
// and refuses such off-switch tables — CLAUDE.md "Consuming repos".) The check
// reads targo's own per-unit proof inventory from `--json`.
// ---------------------------------------------------------------------------

const ROOT_PACKAGE: &str = "compat-posture-serde";

/// The `package_id` a verified function row belongs to: rows are named
/// `cargo-target(package_id="…",…)::path`.
fn function_package_id(function: &str) -> Option<&str> {
    function.strip_prefix("cargo-target(package_id=\"")?.split('"').next()
}

fn units<'a>(inventory: &'a Value, bucket: &str, role: &str) -> &'a [Value] {
    inventory[bucket][role].as_array().map(Vec::as_slice).unwrap_or_default()
}

/// Every way the report contradicts the posture: the root unit is verified and
/// covered, and nothing else is. Empty means the posture holds.
fn posture_violations(report: &Value) -> Vec<String> {
    let inventory = &report["cargo_proof_inventory"];
    let is_root = |unit: &Value| {
        unit["package_name"] == ROOT_PACKAGE
            && unit["package_id"].as_str().is_some_and(|id| id.starts_with("path+"))
    };
    let mut violations = Vec::new();

    let covered_roots = units(inventory, "covered", "primary_roots");
    let root_ids: Vec<&str> = covered_roots
        .iter()
        .filter(|u| is_root(u))
        .filter_map(|u| u["package_id"].as_str())
        .collect();
    if root_ids.is_empty() {
        violations.push("no root unit in the covered proof frontier".to_string());
    }
    for unit in covered_roots.iter().filter(|u| !is_root(u)) {
        violations.push(format!("non-root unit covered as a primary root: {}", unit["package_id"]));
    }
    let excluded =
        inventory["excluded_active_units"].as_array().map(Vec::as_slice).unwrap_or_default();
    for unit in excluded.iter().filter(|u| is_root(u)) {
        violations
            .push(format!("root unit was excluded from verification: {}", unit["target_name"]));
    }
    for bucket in ["declared", "completed", "covered"] {
        for unit in units(inventory, bucket, "dependency_units") {
            violations
                .push(format!("dependency unit was verified ({bucket}): {}", unit["package_id"]));
        }
    }
    let functions = report["functions"].as_array().map(Vec::as_slice).unwrap_or_default();
    if functions.is_empty()
        || report["verification_gate"]["coverage"]["processed"].as_u64() == Some(0)
    {
        violations.push("root unit reported no verification results".to_string());
    }
    for function in functions {
        let name = function["function"].as_str().unwrap_or_default();
        match function_package_id(name) {
            Some(id) if root_ids.contains(&id) => {}
            _ => violations.push(format!("a function outside the root unit was verified: {name}")),
        }
    }
    violations
}

/// Every host/dependency lane must actually be exercised by the fixture's
/// graph — a build script, a proc-macro and a registry library unit — and
/// excluded. Returns the lanes that no excluded unit covered.
fn uncovered_lanes(report: &Value) -> Vec<&'static str> {
    let excluded = report["cargo_proof_inventory"]["excluded_active_units"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default();
    let has_kind = |kind: &str| {
        excluded
            .iter()
            .any(|u| u["target_kinds"].as_array().is_some_and(|k| k.iter().any(|v| v == kind)))
    };
    let mut missing = Vec::new();
    if !has_kind("custom-build") {
        missing.push("host build-script unit");
    }
    if !has_kind("proc-macro") {
        missing.push("host proc-macro unit");
    }
    let serde_lib = excluded.iter().any(|u| {
        u["package_id"].as_str().is_some_and(|id| id.starts_with("registry+"))
            && u["target_name"] == "serde"
            && u["target_kinds"].as_array().is_some_and(|k| k.iter().any(|v| v == "lib"))
    });
    if !serde_lib {
        missing.push("third-party target library unit (serde)");
    }
    missing
}

/// A proc-macro can forge its compiler's proof transport. The fixture must keep
/// the advisory results observational and return the PM-1 could-not-run status.
fn proc_macro_authority_violations(
    report: &Value,
    exit_code: Option<i32>,
    stderr: &str,
) -> Vec<&'static str> {
    let mut violations = Vec::new();
    if exit_code != Some(3) {
        violations.push("proc-macro fixture did not exit could-not-run (3)");
    }
    if report["authority"] != "untrusted_observational_only_no_proof_credit" {
        violations
            .push("proc-macro results were not explicitly observational without proof credit");
    }
    let gate = &report["verification_gate"];
    if gate["lane"] != "advisory" || gate["decision"] != "could-not-run" || gate["exit_code"] != 3 {
        violations.push("JSON gate did not retain the advisory could-not-run refusal");
    }
    if !stderr.contains("forfeits proof authority") || !stderr.contains("PM-1") {
        violations.push("proc-macro authority loss was not disclosed");
    }
    violations
}

/// Every way the run's exit contradicts a judgeable advisory run. Empty means
/// the run is one whose posture the inventory states.
///
/// `targo trust check --allow-l0-gaps` passes on unproved rows (exit 0), and
/// since T7b (254d721283 and its review 81f353f45d, DECISION_QUEUE T7b-EXIT-1,
/// taken 2026-10-11 with this capability cost named: "advisory runs that
/// exited 0 now exit 3") the same pass exits 3, COULD NOT RUN, when its rows
/// are no measurement. A row with no stated stop is `unclassified`, so the
/// outcome is `not-reproducible`; the serde fixture's derived `serialize`
/// carries two (measured 2026-10-21 on the installed 0.11.0, `20565c325`:
/// a hardened twin withheld for want of attachable evidence and a
/// runtime-checked drop-glue row). Reproducibility is about the verdicts, not
/// about which units were verified, so that exit is judged too, but only in the
/// shape T7b gives it: T7b-EXIT-1's rule 5 (`RunExit::decide`) exits 3 only
/// when those rows alone failed the run (no refuted row, the compiler
/// concluded, neither the hardened proof-evidence gate nor the Cargo-exclusion
/// gate failed). Rule 5 does not read the run gate, so it also exits 3 for a run
/// that published no obligation row at all when one backstop-ledger stop makes
/// it not reproducible; before T7b that run exited 1 (inconclusive), so exit 3
/// is judged only with rows. A run whose rows could not run (a refused
/// admission, a keyless row), a run with no rows, an incomplete coverage, a
/// refutation, a setup error, or an exit the gate did not publish is not judged.
fn exit_violations(code: Option<i32>, report: &Value) -> Vec<String> {
    let gate = &report["verification_gate"];
    let decision = gate["decision"].as_str().unwrap_or_default();
    let published = gate["exit_code"].as_i64();
    let mut violations = Vec::new();
    if code.map(i64::from) != published {
        violations
            .push(format!("process exit {code:?} is not the gate's published exit {published:?}"));
    }
    match code {
        Some(0) if matches!(decision, "pass" | "conditional-pass") => {}
        Some(3) if decision == "could-not-run" => {
            let outcome = gate["determinism"]["outcome"].as_str().unwrap_or_default();
            if outcome != "not-reproducible" {
                violations.push(format!(
                    "exit 3 with determinism outcome {outcome:?}: the rows could not run (a \
                     refused admission, a keyless row), which this test does not judge"
                ));
            }
            if gate["counts"]["failed"].as_u64() != Some(0) {
                violations.push(format!(
                    "exit 3 with refuted rows ({}): a refutation exits 1",
                    gate["counts"]["failed"]
                ));
            }
            if gate["coverage"]["coverage_complete"].as_bool() != Some(true) {
                violations.push("exit 3 with incomplete coverage".to_string());
            }
            if gate["counts"]["total"].as_u64().is_none_or(|total| total == 0) {
                violations.push(format!(
                    "exit 3 with no obligation rows ({}): the advisory lane would not have \
                     passed",
                    gate["counts"]["total"]
                ));
            }
        }
        _ => violations.push(format!(
            "exit {code:?} with gate decision {decision:?}: neither an advisory pass nor a pass \
             whose rows alone are no measurement"
        )),
    }
    violations
}

#[test]
fn test_compat_verified_posture_scopes_only_first_party() {
    let targo = trust_targo();
    let work_dir = scratch_dir();
    let crate_dir = work_dir.path().join("posture-serde");
    write_fixture_crate(
        &crate_dir,
        ROOT_PACKAGE,
        r#"serde = { version = "1", features = ["derive"] }"#,
        "#[derive(serde::Serialize)]\n\
         struct Point {\n    x: i32,\n    y: i32,\n}\n\n\
         fn main() {\n    let _ = Point { x: 1, y: 2 };\n}\n",
    )
    .expect("write fixture crate");
    std::fs::write(
        crate_dir.join("Cargo.lock"),
        include_str!("fixtures/compat-posture-serde.lock"),
    )
    .expect("write locked posture fixture graph");

    // Advisory mode retains per-unit observations, but the in-process derive
    // macro forfeits proof authority (PM-1). Keep that refusal and the complete
    // host/dependency graph while checking WHICH units were analyzed.
    // This named authority refusal is distinct from the ordinary advisory
    // measurement classifier `exit_violations`, whose controls remain below.
    let output = Command::new(&targo)
        .current_dir(&crate_dir)
        .args(["trust", "check", "--locked", "--allow-l0-gaps", "--json"])
        .env("CARGO_TARGET_DIR", crate_dir.join("target"))
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .env_remove("CARGO_BUILD_TARGET")
        .env_remove("RUSTC")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .output()
        .expect("run targo trust check");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let report: Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("targo trust check --json did not print JSON ({e}):\n{stderr}"));

    let authority = proc_macro_authority_violations(&report, output.status.code(), &stderr);
    assert!(authority.is_empty(), "PM-1 authority posture regressed: {authority:?}\n{stderr}");

    let missing = uncovered_lanes(&report);
    assert!(missing.is_empty(), "fixture graph did not exercise: {missing:?}\n{stderr}");
    let violations = posture_violations(&report);
    assert!(
        violations.is_empty(),
        "verified posture regressed:\n  {}\nstderr:\n{stderr}",
        violations.join("\n  ")
    );
}

#[test]
fn test_proc_macro_authority_classifier_refutes_success_and_proof_credit() {
    use serde_json::json;

    let report = json!({
        "authority": "untrusted_observational_only_no_proof_credit",
        "verification_gate": { "lane": "advisory", "decision": "could-not-run", "exit_code": 3 },
    });
    let disclosure = "this unit forfeits proof authority: in-process proc-macro (PM-1)";
    assert!(proc_macro_authority_violations(&report, Some(3), disclosure).is_empty());
    for exit_code in [Some(0), Some(1), None] {
        assert!(!proc_macro_authority_violations(&report, exit_code, disclosure).is_empty());
    }
    for (pointer, value) in [
        ("/authority", json!("evidence-grade")),
        ("/authority", json!(null)),
        ("/verification_gate/lane", json!("strict")),
        ("/verification_gate/decision", json!("pass")),
        ("/verification_gate/exit_code", json!(0)),
    ] {
        let mut mutant = report.clone();
        *mutant.pointer_mut(pointer).unwrap() = value;
        assert!(
            !proc_macro_authority_violations(&mutant, Some(3), disclosure).is_empty(),
            "{mutant}"
        );
    }
    for missing_disclosure in ["", "forfeits proof authority", "PM-1"] {
        assert!(!proc_macro_authority_violations(&report, Some(3), missing_disclosure).is_empty());
    }
}

/// The classifier must refute the silent failures, or the live test above
/// could pass on a blanket off-switch or a re-verified dependency graph.
#[test]
fn test_verified_posture_classifier_refutes_mutants() {
    use serde_json::json;

    const ROOT: &str = "path+file:///fx#compat-posture-serde@0.1.0";
    const SERDE: &str = "registry+https://github.com/rust-lang/crates.io-index#serde@1.0.0";
    const DERIVE: &str = "registry+https://github.com/rust-lang/crates.io-index#serde_derive@1.0.0";
    let unit = |id: &str, package: &str, target: &str, kind: &str| {
        json!({ "package_id": id, "package_name": package, "target_name": target,
                "target_kinds": [kind] })
    };
    let root = unit(ROOT, ROOT_PACKAGE, ROOT_PACKAGE, "bin");
    let serde_lib = unit(SERDE, "serde", "serde", "lib");
    let serde_build = unit(SERDE, "serde", "build-script-build", "custom-build");
    let derive = unit(DERIVE, "serde_derive", "serde_derive", "proc-macro");
    let function = |id: &str, path: &str| json!({ "function": format!("cargo-target(package_id=\"{id}\",package=\"x\")::{path}") });
    let report = |covered_roots: Vec<Value>,
                  covered_deps: Vec<Value>,
                  excluded: Vec<Value>,
                  functions: Vec<Value>| {
        json!({
            "cargo_proof_inventory": {
                "declared": { "primary_roots": covered_roots.clone(), "dependency_units": covered_deps.clone() },
                "completed": { "primary_roots": covered_roots.clone(), "dependency_units": covered_deps.clone() },
                "covered": { "primary_roots": covered_roots, "dependency_units": covered_deps },
                "excluded_active_units": excluded,
            },
            "verification_gate": { "coverage": { "processed": functions.len() } },
            "functions": functions,
        })
    };

    // The measured good shape.
    let good = report(
        vec![root.clone()],
        vec![],
        vec![serde_lib.clone(), serde_build.clone(), derive.clone()],
        vec![function(ROOT, "compat_posture_serde::main")],
    );
    assert_eq!(posture_violations(&good), Vec::<String>::new());
    assert_eq!(uncovered_lanes(&good), Vec::<&str>::new());

    // Mutant 1: blanket off-switch — the root is excluded and nothing verified.
    let blanket_off = report(vec![], vec![], vec![root.clone(), serde_lib.clone()], vec![]);
    let v = posture_violations(&blanket_off);
    assert!(v.iter().any(|m| m.contains("no root unit in the covered proof frontier")), "{v:?}");
    assert!(v.iter().any(|m| m.contains("root unit was excluded")), "{v:?}");
    assert!(v.iter().any(|m| m.contains("reported no verification results")), "{v:?}");

    // Mutant 2: the dependency graph is verified again.
    let reverified = report(
        vec![root.clone()],
        vec![serde_lib.clone()],
        vec![serde_build.clone(), derive.clone()],
        vec![function(ROOT, "compat_posture_serde::main"), function(SERDE, "serde::ser::f")],
    );
    let v = posture_violations(&reverified);
    assert!(v.iter().any(|m| m.contains("dependency unit was verified")), "{v:?}");
    assert!(v.iter().any(|m| m.contains("a function outside the root unit was verified")), "{v:?}");
    assert!(uncovered_lanes(&reverified).contains(&"third-party target library unit (serde)"));

    // Mutant 3: a dependency covered as if it were a primary root.
    let smuggled =
        report(vec![root.clone(), serde_lib.clone()], vec![], vec![], vec![function(ROOT, "m")]);
    let v = posture_violations(&smuggled);
    assert!(v.iter().any(|m| m.contains("non-root unit covered as a primary root")), "{v:?}");

    // Lane coverage refutes a graph without host units.
    let no_host = report(vec![root], vec![], vec![serde_lib], vec![function(ROOT, "m")]);
    let missing = uncovered_lanes(&no_host);
    assert!(missing.contains(&"host build-script unit"), "{missing:?}");
    assert!(missing.contains(&"host proc-macro unit"), "{missing:?}");
    assert!(!missing.contains(&"third-party target library unit (serde)"), "{missing:?}");

    // The exit: the two judgeable shapes, then each way out of them.
    let gate_rows = |decision: &str, exit: u8, outcome: &str, failed: u64, total: u64| {
        json!({ "verification_gate": {
            "decision": decision, "exit_code": exit,
            "counts": { "failed": failed, "total": total },
            "coverage": { "coverage_complete": true },
            "determinism": { "outcome": outcome },
        } })
    };
    let gate = |decision: &str, exit: u8, outcome: &str, failed: u64, complete: bool| {
        json!({ "verification_gate": {
            "decision": decision, "exit_code": exit,
            "counts": { "failed": failed, "total": 11 },
            "coverage": { "coverage_complete": complete },
            "determinism": { "outcome": outcome },
        } })
    };
    let exit_holds = |code: i32, report: &Value| exit_violations(Some(code), report).is_empty();
    let refuted = |code: i32, report: &Value, needle: &str| {
        let v = exit_violations(Some(code), report);
        assert!(v.iter().any(|m| m.contains(needle)), "exit {code} {report}: {v:?}");
    };
    // The measured shapes: an advisory pass, and the same pass whose rows are
    // not reproducible (the installed 0.11.0 on the serde fixture).
    assert!(exit_holds(0, &gate("conditional-pass", 0, "measured", 0, true)));
    assert!(exit_holds(0, &gate("pass", 0, "measured", 0, true)));
    assert!(exit_holds(3, &gate("could-not-run", 3, "not-reproducible", 0, true)));
    // Rows that could not run (a refused admission, a keyless row).
    refuted(3, &gate("could-not-run", 3, "could-not-run", 0, true), "the rows could not run");
    // A refutation or a coverage shortfall under exit 3.
    refuted(3, &gate("could-not-run", 3, "not-reproducible", 1, true), "refuted rows");
    refuted(3, &gate("could-not-run", 3, "not-reproducible", 0, false), "incomplete coverage");
    // A not-reproducible exit 3 with no rows at all (a backstop-ledger stop alone):
    // before T7b it exited 1, inconclusive, so it is no advisory pass.
    assert!(exit_holds(3, &gate_rows("could-not-run", 3, "not-reproducible", 0, 1)));
    refuted(3, &gate_rows("could-not-run", 3, "not-reproducible", 0, 0), "no obligation rows");
    let mut no_count = gate_rows("could-not-run", 3, "not-reproducible", 0, 1);
    no_count["verification_gate"]["counts"].as_object_mut().expect("counts").remove("total");
    refuted(3, &no_count, "no obligation rows");
    // An exit the gate did not publish, either way.
    refuted(3, &gate("conditional-pass", 0, "not-reproducible", 0, true), "published exit");
    refuted(0, &gate("could-not-run", 3, "not-reproducible", 0, true), "published exit");
    // A failed or inconclusive gate, and a setup error with no gate at all.
    refuted(1, &gate("fail", 1, "measured", 1, true), "neither an advisory pass");
    refuted(1, &gate("inconclusive", 1, "measured", 0, true), "neither an advisory pass");
    refuted(2, &json!({}), "neither an advisory pass");
}

// Trust: retain the incoming branch's independent authority mutant table.
#[test]
fn test_posture_authority_classifier_refutes_mutants() {
    use serde_json::json;
    let disclosure = "this unit forfeits proof authority: in-process proc-macro (PM-1)";
    let good = json!({
        "authority": "untrusted_observational_only_no_proof_credit",
        "verification_gate": { "lane": "advisory", "decision": "could-not-run", "exit_code": 3 },
    });
    assert!(proc_macro_authority_violations(&good, Some(3), disclosure).is_empty());
    for code in [None, Some(0), Some(1), Some(2)] {
        assert!(!proc_macro_authority_violations(&good, code, disclosure).is_empty());
    }
    for (pointer, value) in [
        ("/authority", json!("proof")),
        ("/authority", Value::Null),
        ("/verification_gate/lane", json!("strict")),
        ("/verification_gate/decision", json!("verified")),
        ("/verification_gate/exit_code", json!(0)),
    ] {
        let mut mutant = good.clone();
        *mutant.pointer_mut(pointer).expect("mutated field exists") = value;
        assert!(
            !proc_macro_authority_violations(&mutant, Some(3), disclosure).is_empty(),
            "{pointer}"
        );
    }
}
