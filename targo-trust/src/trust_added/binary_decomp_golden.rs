//! `binary-decompilation-golden` — the binary decompilation golden-JSON gate,
//! Rust-native.
//!
//! Faithful port of `tests/e2e_binary_decompilation_golden_json.sh` (the
//! 1076-line contract). Shell-backed execution stays banned: every step here
//! is a direct process spawn of a Trust-owned binary (stage2 targo, the built
//! `targo-trust` binary) plus in-Rust file inspection and JSON assertions
//! (serde_json replaces the Python JSON checks).
//!
//! Steps, in the shell gate's order:
//! 1. Checked-certificate manifest release-gate coverage: inspect the CLI
//!    surface (`--checked-cert-manifest` / `checked_certificate_manifests` /
//!    `verify-binary`) and dispatch the appropriate focused manifest test.
//! 2. Focused binary gate inventory: ask libtest for its runtime inventory,
//!    uniquely resolve, and execute every pinned focused test exactly across
//!    the `targo-trust` binary and `trust-ir-bridge` library targets. Runtime
//!    inventory avoids coupling evidence to a particular source-module layout.
//! 3. Build the `targo-trust` binary and drive it over the checked-in hex ELF
//!    fixtures plus synthetic bad-format / RISC-V / PE / i386 inputs, asserting
//!    the stable JSON contract (proof-evidence with a rejected proof-grade
//!    gate, rejected conversion gates, non-`Undef` preserved symbolic formulas,
//!    fail-closed rejections).
//!
//! Fidelity notes:
//! - Cargo test/build steps use the shared bounded process runner. Every pinned
//!   unit test must have a positive `test <exact-name> ... ok` transcript;
//!   successful zero-test or ignored-test filters are rejected.
//! - The CLI smoke runs ARE captured; `capture()` already fails closed on an
//!   unexpected `SKIP:` marker, which subsumes the shell's `skip_gate` default
//!   (the `TRUST_ALLOW_REVIEW_GATE_SKIPS=1` escape hatch is intentionally not
//!   ported — a release gate never accepts a skip).
//! - The build profile is driven by `policy.release` (the shell's
//!   `TRUST_CARGO_TRUST_BUILD_PROFILE` env is not honored).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};
use serde_json::Value;

use crate::stage2_tools::host_executable_name;

use super::trustc_native::{Captured, capture};
use super::{
    GatePolicy, pin_targo_sibling_toolchain, read_bounded_exact_file_under, resolve_gate_targo,
    scrub_gate_process_environment, section,
};

const X86_64_ENTRY: &str = "0x400000";

const X86_64_FIXTURE_HEX: &str = "tests/fixtures/binary_decomp/x86_64-load-elf.hex";
const X86_64_FIXTURE_SHA256: &str =
    "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000";
const AARCH64_FIXTURE_HEX: &str = "tests/fixtures/binary_decomp/aarch64-ret-elf.hex";
const AARCH64_FIXTURE_SHA256: &str =
    "76e21c45581b19d655f08eb1564e33b389c80a739b49296f8f339e27597a3e02";
const AARCH64_UNSUPPORTED_FIXTURE_HEX: &str =
    "tests/fixtures/binary_decomp/aarch64-ret-and-unsupported-mrs-elf.hex";
const AARCH64_UNSUPPORTED_FIXTURE_SHA256: &str =
    "8879be4512a39c96d0effd56f2a8ad018cc58f2bdb25cb91fbe55805d1686774";

const MAX_FIXTURE_HEX_BYTES: u64 = 4 * 1024 * 1024;

/// The 20 focused `targo-trust` tests the shell inventory pins.
const TARGO_TRUST_FOCUSED_TESTS: &[&str] = &[
    "test_failed_x86_64_solver_result_replays_exact_instruction_bytes",
    "test_failed_x86_64_replay_with_mismatched_instruction_size_fails_closed",
    "test_exact_replay_sat_candidate_matches_checked_in_golden",
    "test_confirmed_replay_without_exact_original_bytes_fails_closed",
    "test_verify_binary_proof_grade_gate_rejects_missing_evidence_in_terminal_and_json",
    "test_verify_binary_raw_solver_proof_bytes_do_not_satisfy_proof_grade_gate",
    "test_decompile_output_kind_routes_derived_targets_to_text_outputs",
    "test_parse_convert_target_accepts_binary_conversion_targets",
    "test_convert_partial_derived_output_fails_without_proof_grade_claim",
    "test_convert_rejects_proof_grade_label_until_all_binary_release_gate_conditions_hold",
    "test_verify_binary_report_surfaces_checked_certificate_import_json_and_terminal",
    "test_x86_64_empty_ledger_release_evidence_matches_golden_and_blocks_release",
    "test_verify_binary_imports_produced_checked_certificate_and_matches_refutation_golden",
    "test_convert_report_surfaces_symbolic_formula_metadata_in_json_and_terminal",
    "test_exploit_find_report_captures_phase_diagnostics_without_claiming_exploit",
    "test_exploit_find_raw_solver_failure_requires_replay_before_confirmation",
    "test_exploit_find_checked_unsat_certificate_without_claim_does_not_satisfy_refutation",
    "test_exploit_find_sat_candidate_requires_exact_replay_even_with_checked_unsat_evidence",
    "test_exploit_find_replayed_sat_candidate_without_checked_refutation_stays_blocked",
    "test_exploit_find_fails_even_when_binary_vcs_are_proved",
];

/// The 3 focused `targo-trust` rewrite-loop tests (moved to `rewrite_loop/tests.rs`).
const REWRITE_LOOP_FOCUSED_TESTS: &[&str] = &[
    "test_strengthen_failures_rejects_binary_source_without_exact_provenance",
    "test_runtime_strengthen_wrapper_keeps_binary_source_closed",
    "test_binary_source_backpropagation_blockers_require_exact_runtime_provenance",
];

/// Focused `trust-ir-bridge` symbolic-lowering and native guard-contract tests.
const IR_BRIDGE_FOCUSED_TESTS: &[&str] = &[
    "test_symbolic_operand_lowers_to_formula_dialect_not_undef",
    "test_symbolic_aggregate_lowers_without_undef_seed",
    "test_symbolic_array_repeat_lowers_without_undef_seed",
    "native_inferred_contract_model_binds_guard_to_tag",
];

const MAX_GATE_SOURCE_BYTES: u64 = 8 * 1024 * 1024;

pub(crate) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("Binary decompilation golden JSON");
    println!(
        "Scope: builds the targo-trust binary, materializes checked-in x86_64/AArch64 ELF fixtures, and pins the stable JSON contract for Rust skeleton, TrustIr, derived conversions, and verify-binary proof-evidence summaries."
    );

    let targo = resolve_gate_targo(root, policy.strict)?;
    println!("Targo: {}", targo.display());

    let targo_manifest = manifest_str(root, "targo-trust/Cargo.toml")?;
    let crates_manifest = manifest_str(root, "crates/Cargo.toml")?;
    let cargo_target = tempfile::Builder::new()
        .prefix("trust-binary-gate-target-")
        .tempdir()
        .context("failed to create isolated binary-gate Cargo target directory")?;

    run_checked_certificate_manifest_gate(
        root,
        &targo,
        &targo_manifest,
        &crates_manifest,
        cargo_target.path(),
    )?;
    run_binary_release_unit_gates(
        root,
        &targo,
        &targo_manifest,
        &crates_manifest,
        cargo_target.path(),
    )?;
    run_binary_cli_contract(root, &targo, &targo_manifest, cargo_target.path(), policy)?;

    println!();
    println!("=== binary decompilation golden JSON: PASS ===");
    Ok(())
}

fn manifest_str(root: &Path, rel: &str) -> Result<String> {
    root.join(rel)
        .to_str()
        .map(ToOwned::to_owned)
        .with_context(|| format!("manifest path {rel} is not valid UTF-8"))
}

// ---------------------------------------------------------------------------
// Streamed explicit-unverified Targo test/build steps (shell `set -e` semantics)
// ---------------------------------------------------------------------------

fn run_test_step(targo: &Path, args: &[&str], cwd: &Path, target_dir: &Path) -> Result<()> {
    capture_test_step(targo, args, cwd, target_dir).map(|_| ())
}

fn capture_test_step(
    targo: &Path,
    args: &[&str],
    cwd: &Path,
    target_dir: &Path,
) -> Result<Captured> {
    println!();
    println!(">>> {} {}", targo.display(), args.join(" "));
    let mut command = Command::new(targo);
    command.arg("--unverified").args(args).current_dir(cwd);
    scrub_gate_process_environment(&mut command);
    pin_targo_sibling_toolchain(&mut command, targo)?;
    command.env("CARGO_TARGET_DIR", target_dir).env("CARGO_NET_OFFLINE", "true");
    let captured = capture(command)?;
    print!("{}", captured.stdout);
    eprint!("{}", captured.stderr);
    if !captured.exited_with(0) {
        bail!("`targo {}` exited with {}", args.join(" "), captured.exit);
    }
    Ok(captured)
}

/// Resolve a source-pinned base test name to one and only one libtest name,
/// then run that exact test and prove that it was neither filtered nor ignored.
fn run_exact_test(
    targo: &Path,
    cargo_args: &[&str],
    expected_base_name: &str,
    cwd: &Path,
    target_dir: &Path,
) -> Result<()> {
    let inventory = list_test_names(targo, cargo_args, cwd, target_dir)?;
    let exact_name = resolve_exact_test_name(&inventory, expected_base_name)?;
    run_exact_test_name(targo, cargo_args, &exact_name, cwd, target_dir)
}

fn list_test_names(
    targo: &Path,
    cargo_args: &[&str],
    cwd: &Path,
    target_dir: &Path,
) -> Result<Vec<String>> {
    let mut list_args = cargo_args.to_vec();
    list_args.extend(["--", "--list", "--format", "terse"]);
    println!();
    println!(">>> {} {}", targo.display(), list_args.join(" "));
    let mut command = Command::new(targo);
    command.arg("--unverified").args(&list_args).current_dir(cwd);
    scrub_gate_process_environment(&mut command);
    pin_targo_sibling_toolchain(&mut command, targo)?;
    command.env("CARGO_TARGET_DIR", target_dir).env("CARGO_NET_OFFLINE", "true");
    let listed = capture(command)?;
    if !listed.exited_with(0) {
        print!("{}", listed.stdout);
        eprint!("{}", listed.stderr);
        bail!("`targo {}` exited with {}", list_args.join(" "), listed.exit);
    }
    let inventory = listed
        .stdout
        .lines()
        .filter_map(|line| line.strip_suffix(": test"))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if inventory.is_empty() {
        bail!("test target listed zero tests; a vacuous target is not gate evidence");
    }
    println!("  listed {} non-vacuous tests", inventory.len());
    Ok(inventory)
}

fn resolve_exact_test_name(inventory: &[String], expected_base_name: &str) -> Result<String> {
    let matches = inventory
        .iter()
        .map(String::as_str)
        .filter(|name| {
            *name == expected_base_name
                || name
                    .strip_suffix(expected_base_name)
                    .is_some_and(|prefix| prefix.ends_with("::"))
        })
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let [exact_name] = matches.as_slice() else {
        bail!(
            "expected exactly one listed test named {expected_base_name}, found {}: {matches:?}",
            matches.len()
        );
    };
    Ok(exact_name.clone())
}

fn run_exact_test_name(
    targo: &Path,
    cargo_args: &[&str],
    exact_name: &str,
    cwd: &Path,
    target_dir: &Path,
) -> Result<()> {
    let mut run_args = cargo_args.to_vec();
    run_args.push(exact_name);
    run_args.extend(["--", "--exact"]);
    let ran = capture_test_step(targo, &run_args, cwd, target_dir)?;
    let expected_pass = format!("test {exact_name} ... ok");
    if !ran.stdout.lines().any(|line| line.trim() == expected_pass) {
        bail!(
            "exact test {exact_name} exited successfully without a positive libtest execution record; zero-test and ignored-test transcripts are not release evidence"
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 1: checked certificate manifest release gate coverage
// ---------------------------------------------------------------------------

enum ManifestGate {
    TargoTrust(String),
    ProofCert(String),
}

fn run_checked_certificate_manifest_gate(
    root: &Path,
    targo: &Path,
    targo_manifest: &str,
    crates_manifest: &str,
    target_dir: &Path,
) -> Result<()> {
    println!();
    println!("--- checked certificate manifest release gate coverage");
    match select_manifest_gate(root)? {
        ManifestGate::TargoTrust(test) => {
            println!("selected targo-trust manifest coverage: {test}");
            run_exact_test(
                targo,
                &["test", "--manifest-path", targo_manifest, "--bin", "targo-trust"],
                &test,
                root,
                target_dir,
            )
        }
        ManifestGate::ProofCert(test) => {
            println!("selected trust-proof-cert manifest coverage: {test}");
            run_exact_test(
                targo,
                &[
                    "test",
                    "--manifest-path",
                    crates_manifest,
                    "-p",
                    "trust-proof-cert",
                    "--test",
                    "checked_binary_certificate",
                ],
                &test,
                root,
                target_dir,
            )
        }
    }
}

fn select_manifest_gate(root: &Path) -> Result<ManifestGate> {
    let read = |rel: &str| -> Result<String> {
        let bytes = read_bounded_exact_file_under(root, Path::new(rel), MAX_GATE_SOURCE_BYTES)
            .with_context(|| format!("failed to read manifest-gate source {rel}"))?;
        String::from_utf8(bytes)
            .with_context(|| format!("manifest-gate source {rel} is not valid UTF-8"))
    };
    let cargo_cli = read("targo-trust/src/cli.rs")?;
    let cargo_main = read("targo-trust/src/main.rs")?;
    let cargo_tests = read("targo-trust/src/tests.rs")?;
    let checked_src = read("crates/trust-proof-cert/src/checked_binary_certificate.rs")?
        + &read("crates/trust-proof-cert/src/lib.rs")?;
    let checked_tests = read("crates/trust-proof-cert/tests/checked_binary_certificate.rs")?;

    let cargo_manifest_test =
        scan_fn_names(&cargo_tests).into_iter().find(|name| is_targo_manifest_test(name));

    let verify_binary_manifest_import_visible = cargo_cli.contains("--checked-cert-manifest")
        && cargo_main.contains("--checked-cert-manifest")
        && (cargo_cli.contains("checked_certificate_manifests")
            || cargo_main.contains("checked_certificate_manifests"))
        && cargo_main.contains("verify-binary")
        && cargo_manifest_test.is_some();

    if verify_binary_manifest_import_visible {
        return Ok(ManifestGate::TargoTrust(cargo_manifest_test.expect("checked")));
    }

    let rejection_test =
        scan_fn_names(&checked_tests).into_iter().find(|name| is_proof_cert_rejection_test(name));
    let checked_manifest_rejection_visible =
        checked_src.contains("CheckedBinaryCertificateManifest") && rejection_test.is_some();
    if checked_manifest_rejection_visible {
        return Ok(ManifestGate::ProofCert(rejection_test.expect("checked")));
    }

    bail!(
        "binary decompilation release gate is missing checked-certificate manifest coverage: expected either targo trust verify-binary --checked-cert-manifest visibility with a focused targo-trust test, or CheckedBinaryCertificateManifest rejection coverage in trust-proof-cert"
    );
}

/// `test_[A-Za-z0-9_]*checked_(?:certificate|cert)_manifest[A-Za-z0-9_]*`.
fn is_targo_manifest_test(name: &str) -> bool {
    name.starts_with("test_")
        && (name.contains("checked_certificate_manifest") || name.contains("checked_cert_manifest"))
}

/// `checked_binary_certificate_manifest[A-Za-z0-9_]*reject[A-Za-z0-9_]*`.
fn is_proof_cert_rejection_test(name: &str) -> bool {
    name.starts_with("checked_binary_certificate_manifest") && name.contains("reject")
}

// ---------------------------------------------------------------------------
/// Extract, in source order, every identifier that appears as `fn <ident>`
/// followed by optional whitespace and `(` — the Rust analogue of the shell
/// gate's `fn\s+NAME\s*\(` regex.
fn scan_fn_names(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut names = Vec::new();
    let mut search = 0;
    while let Some(offset) = text[search..].find("fn") {
        let start = search + offset;
        search = start + 2;
        let before_ok = start == 0 || !is_ident_byte(bytes[start - 1]);
        let after = start + 2;
        if !before_ok || after >= bytes.len() || !bytes[after].is_ascii_whitespace() {
            continue;
        }
        let mut cursor = after;
        while cursor < bytes.len() && bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
        }
        let id_start = cursor;
        while cursor < bytes.len() && is_ident_byte(bytes[cursor]) {
            cursor += 1;
        }
        if cursor == id_start {
            continue;
        }
        let id_end = cursor;
        while cursor < bytes.len() && bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
        }
        if cursor < bytes.len() && bytes[cursor] == b'(' {
            names.push(text[id_start..id_end].to_string());
        }
    }
    names
}

fn is_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

// ---------------------------------------------------------------------------
// Step 2: focused runtime-inventoried exact unit gates
// ---------------------------------------------------------------------------

fn run_binary_release_unit_gates(
    root: &Path,
    targo: &Path,
    targo_manifest: &str,
    crates_manifest: &str,
    target_dir: &Path,
) -> Result<()> {
    println!();
    println!("--- exact targo-trust binary release unit gates");
    let targo_test_args = ["test", "--manifest-path", targo_manifest, "--bin", "targo-trust"];
    let targo_inventory = list_test_names(targo, &targo_test_args, root, target_dir)?;
    for test in TARGO_TRUST_FOCUSED_TESTS.iter().chain(REWRITE_LOOP_FOCUSED_TESTS) {
        let exact = resolve_exact_test_name(&targo_inventory, test)?;
        run_exact_test_name(targo, &targo_test_args, &exact, root, target_dir)?;
    }

    println!();
    println!("--- exact symbolic formula TrustIr lowering unit gates");
    let bridge_test_args =
        ["test", "--manifest-path", crates_manifest, "-p", "trust-ir-bridge", "--lib"];
    let bridge_inventory = list_test_names(targo, &bridge_test_args, root, target_dir)?;
    for test in IR_BRIDGE_FOCUSED_TESTS {
        let exact = resolve_exact_test_name(&bridge_inventory, test)?;
        run_exact_test_name(targo, &bridge_test_args, &exact, root, target_dir)?;
    }

    println!();
    println!("--- trust-proof-cert checked binary certificate gates");
    for integration_test in ["checked_binary_certificate", "binary_decomp_certificate_gate"] {
        let run = capture_test_step(
            targo,
            &[
                "test",
                "--manifest-path",
                crates_manifest,
                "-p",
                "trust-proof-cert",
                "--test",
                integration_test,
            ],
            root,
            target_dir,
        )?;
        if !run
            .stdout
            .lines()
            .any(|line| line.trim().starts_with("test ") && line.trim().ends_with(" ... ok"))
        {
            bail!(
                "integration test target {integration_test} exited successfully without running a non-ignored test"
            );
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 3: build targo-trust and drive the binary CLI JSON contract
// ---------------------------------------------------------------------------

fn run_binary_cli_contract(
    root: &Path,
    targo: &Path,
    targo_manifest: &str,
    target_dir: &Path,
    policy: GatePolicy,
) -> Result<()> {
    let profile = if policy.release { "release" } else { "debug" };
    println!();
    println!("--- build targo-trust ({profile})");
    let target_dir_text =
        target_dir.to_str().context("binary gate target directory is not valid UTF-8")?;
    let mut build_args: Vec<&str> = vec![
        "build",
        "--manifest-path",
        targo_manifest,
        "--bin",
        "targo-trust",
        "--target-dir",
        target_dir_text,
    ];
    if policy.release {
        build_args.push("--release");
    }
    run_test_step(targo, &build_args, root, target_dir)?;

    let cargo_trust = target_dir.join(profile).join(host_executable_name("targo-trust"));
    if !is_exact_executable_file(&cargo_trust) {
        bail!("built targo-trust binary is missing or not executable: {}", cargo_trust.display());
    }
    println!("Using targo-trust binary: {}", cargo_trust.display());

    let scratch = tempfile::Builder::new()
        .prefix("trust-binary-decomp-")
        .tempdir()
        .context("failed to create binary-decomp scratch dir")?;
    let tmp = scratch.path();

    // Materialize the checked-in x86_64 ELF fixture.
    println!();
    println!("--- materialize checked-in x86_64 ELF fixture");
    let input_bin = tmp.join("x86_64-load.elf");
    materialize_hex_fixture(root, X86_64_FIXTURE_HEX, &input_bin, X86_64_FIXTURE_SHA256)?;
    let input = input_bin.to_str().context("x86_64 fixture path is not valid UTF-8")?;

    // strict decompile must fail closed on unsupported coverage.
    println!("--- targo trust decompile --to trust_ir --strict --json");
    let strict = run_cli(
        &cargo_trust,
        &["decompile", input, "--to", "trust_ir", "--entry", X86_64_ENTRY, "--strict", "--json"],
    )?;
    if strict.exited_with(0) {
        bail!(
            "targo trust decompile --to trust_ir --strict --json unexpectedly succeeded; strict mode must fail closed on unsupported coverage"
        );
    }

    println!("--- targo trust decompile --to rust --json");
    let rust = run_cli(
        &cargo_trust,
        &[
            "decompile",
            input,
            "--to",
            "rust",
            "--entry",
            X86_64_ENTRY,
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_exit_zero(&rust, "targo trust decompile --to rust --json")?;

    println!("--- targo trust decompile --to trust_ir --json");
    let trust_ir = run_cli(
        &cargo_trust,
        &[
            "decompile",
            input,
            "--to",
            "trust_ir",
            "--entry",
            X86_64_ENTRY,
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_exit_zero(&trust_ir, "targo trust decompile --to trust_ir --json")?;

    println!("--- targo trust convert --to trust-cg --json");
    let trust_cg = run_cli(
        &cargo_trust,
        &[
            "convert",
            input,
            "--to",
            "trust-cg",
            "--entry",
            X86_64_ENTRY,
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_rejected_conversion(&trust_cg, "trust-cg")?;

    println!("--- targo trust convert --to wasm --json");
    let wasm = run_cli(
        &cargo_trust,
        &[
            "convert",
            input,
            "--to",
            "wasm",
            "--entry",
            X86_64_ENTRY,
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_rejected_conversion(&wasm, "wasm")?;

    println!("--- targo trust verify-binary exposes proof evidence JSON");
    let verify_binary = run_cli(
        &cargo_trust,
        &["verify-binary", input, "--entry", X86_64_ENTRY, "--allow-unsupported", "--json"],
    )?;
    require_not_setup_failure(&verify_binary, "targo trust verify-binary --json")?;

    println!("--- targo trust verify-binary exposes proof evidence terminal summary");
    let verify_binary_terminal = run_cli(
        &cargo_trust,
        &["verify-binary", input, "--entry", X86_64_ENTRY, "--allow-unsupported"],
    )?;
    require_not_setup_failure(&verify_binary_terminal, "targo trust verify-binary terminal")?;

    // Synthetic fail-closed inputs.
    let bad_format_bin = tmp.join("not-an-object.bin");
    fs::write(&bad_format_bin, b"not an object file")
        .context("failed to write bad-format fixture")?;
    let bad_target_bin = tmp.join("unsupported-target.o");
    write_riscv_elf(&bad_target_bin)?;
    let pe_bin = tmp.join("minimal-pe.bin");
    fs::write(&pe_bin, b"MZ\x00\x00").context("failed to write PE fixture")?;
    let i386_bin = tmp.join("minimal-i386.o");
    write_i386_elf(&i386_bin)?;

    println!("--- targo trust decompile rejects unsupported format");
    let bad_format = decompile_strict(&cargo_trust, &bad_format_bin)?;
    require_nonzero(&bad_format, "targo trust decompile accepted unsupported non-object input")?;

    println!("--- targo trust decompile rejects unsupported target");
    let bad_target = decompile_strict(&cargo_trust, &bad_target_bin)?;
    require_nonzero(&bad_target, "targo trust decompile accepted unsupported ELF target")?;

    println!("--- targo trust decompile rejects PE/COFF fail-closed");
    let pe = decompile_strict(&cargo_trust, &pe_bin)?;
    require_nonzero(&pe, "targo trust decompile accepted unsupported PE/COFF input")?;

    println!("--- targo trust decompile rejects ELF i386 fail-closed");
    let i386 = decompile_strict(&cargo_trust, &i386_bin)?;
    require_nonzero(&i386, "targo trust decompile accepted unsupported ELF i386 input")?;

    println!("--- materialize checked-in AArch64 ELF fixture");
    let aarch64_bin = tmp.join("aarch64-ret.elf");
    materialize_hex_fixture(root, AARCH64_FIXTURE_HEX, &aarch64_bin, AARCH64_FIXTURE_SHA256)?;
    let aarch64_path = aarch64_bin.to_str().context("aarch64 fixture path is not valid UTF-8")?;

    println!("--- targo trust decompile reports checked-in AArch64 ELF fixture");
    let aarch64 = run_cli(
        &cargo_trust,
        &[
            "decompile",
            aarch64_path,
            "--to",
            "trust_ir",
            "--entry",
            "0x400000",
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_exit_zero(&aarch64, "targo trust decompile checked-in AArch64 fixture --json")?;

    println!("--- materialize checked-in AArch64 unsupported-ledger fixture");
    let aarch64_unsupported_bin = tmp.join("aarch64-ret-and-unsupported-mrs.elf");
    materialize_hex_fixture(
        root,
        AARCH64_UNSUPPORTED_FIXTURE_HEX,
        &aarch64_unsupported_bin,
        AARCH64_UNSUPPORTED_FIXTURE_SHA256,
    )?;
    let aarch64_unsupported_path =
        aarch64_unsupported_bin.to_str().context("aarch64 unsupported fixture path not UTF-8")?;

    println!("--- targo trust decompile preserves checked-in AArch64 unsupported ledger");
    let aarch64_unsupported = run_cli(
        &cargo_trust,
        &[
            "decompile",
            aarch64_unsupported_path,
            "--to",
            "trust_ir",
            "--all",
            "--allow-unsupported",
            "--json",
        ],
    )?;
    require_exit_zero(
        &aarch64_unsupported,
        "targo trust decompile checked-in AArch64 unsupported-ledger fixture --json",
    )?;

    // ---- JSON contract assertions (ported from the Python block) ----
    let rust_report = parse_report(&rust, "rust")?;
    let trust_ir_report = parse_report(&trust_ir, "trust_ir")?;
    let trust_cg_report = parse_report(&trust_cg, "trust-cg")?;
    let wasm_report = parse_report(&wasm, "wasm")?;
    let verify_binary_report = parse_report(&verify_binary, "verify-binary")?;
    let strict_report = parse_report(&strict, "strict")?;
    let bad_format_report = parse_report(&bad_format, "bad format")?;
    let bad_target_report = parse_report(&bad_target, "bad target")?;
    let pe_report = parse_report(&pe, "PE")?;
    let i386_report = parse_report(&i386, "i386")?;
    let aarch64_report = parse_report(&aarch64, "aarch64")?;
    let aarch64_unsupported_report =
        parse_report(&aarch64_unsupported, "aarch64 unsupported-ledger")?;

    assert_common(&rust_report, "rust", &input_bin)?;
    assert_common(&trust_ir_report, "trust_ir", &input_bin)?;
    assert_common(&trust_cg_report, "trust-cg", &input_bin)?;
    assert_common(&wasm_report, "wasm", &input_bin)?;

    assert_verify_binary(&verify_binary_report, &input_bin)?;
    assert_verify_binary_terminal(&verify_binary_terminal.stdout)?;
    assert_strict(&strict_report)?;
    assert_bad_format(&bad_format_report)?;
    assert_bad_target(&bad_target_report)?;
    assert_pe(&pe_report)?;
    assert_i386(&i386_report)?;
    assert_rust_output(&rust_report)?;

    let trust_ir_symbolic_keys = assert_trust_ir_output(&trust_ir_report)?;

    assert_derived_output(&trust_cg_report, "trust-cg", "trust_cg_text")?;
    assert_derived_output(&wasm_report, "wasm", "wasm_text")?;
    assert_convert_symbolic_formula_json_contract(
        &trust_cg_report,
        "trust-cg",
        "TrustCg",
        &trust_ir_symbolic_keys,
    )?;
    assert_convert_symbolic_formula_json_contract(
        &wasm_report,
        "wasm",
        "Wasm",
        &trust_ir_symbolic_keys,
    )?;

    assert_aarch64(&aarch64_report, &aarch64_bin)?;
    assert_aarch64_unsupported(&aarch64_unsupported_report, &aarch64_unsupported_bin)?;

    println!();
    println!("  PASS: binary decompilation golden JSON contract holds");
    Ok(())
}

fn is_exact_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::symlink_metadata(path) else { return false };
    if !metadata.file_type().is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn decompile_strict(bin: &Path, input: &Path) -> Result<Captured> {
    let input = input.to_str().context("synthetic fixture path is not valid UTF-8")?;
    run_cli(bin, &["decompile", input, "--to", "trust_ir", "--strict", "--json"])
}

fn run_cli(bin: &Path, args: &[&str]) -> Result<Captured> {
    let mut command = Command::new(bin);
    command.args(args);
    scrub_gate_process_environment(&mut command);
    capture(command)
}

/// The `--allow-unsupported` decompiles must exit 0.
fn require_exit_zero(run: &Captured, what: &str) -> Result<()> {
    if !run.exited_with(0) {
        bail!("{what} exited {}\nstdout:\n{}\nstderr:\n{}", run.exit, run.stdout, run.stderr);
    }
    Ok(())
}

/// convert lanes must fail closed with exactly exit 1 (0 = wrongly accepted,
/// >1 = setup/internal failure).
fn require_rejected_conversion(run: &Captured, target: &str) -> Result<()> {
    if run.exited_with(0) {
        bail!(
            "targo trust convert --to {target} --json unexpectedly accepted a non-proof-grade conversion"
        );
    }
    if !run.exited_with(1) {
        bail!(
            "targo trust convert --to {target} --json exited setup/internal status {}\nstderr:\n{}",
            run.exit,
            run.stderr
        );
    }
    Ok(())
}

/// verify-binary may exit 0 or 1; >1 (or a signal) is a setup/internal failure.
fn require_not_setup_failure(run: &Captured, what: &str) -> Result<()> {
    if !run.exited_with_one_of(&[0, 1]) {
        bail!("{what} exited setup/internal status {}\nstderr:\n{}", run.exit, run.stderr);
    }
    Ok(())
}

/// Synthetic fail-closed inputs: any non-zero exit passes; exit 0 fails.
fn require_nonzero(run: &Captured, message: &str) -> Result<()> {
    if run.exited_with(0) {
        bail!("{message}");
    }
    Ok(())
}

fn parse_report(run: &Captured, label: &str) -> Result<Value> {
    serde_json::from_str(&run.stdout).with_context(|| {
        format!(
            "{label}: CLI output should be a JSON report\nstdout:\n{}\nstderr:\n{}",
            run.stdout, run.stderr
        )
    })
}

// ---------------------------------------------------------------------------
// Fixtures: hex materialization + synthetic ELF/PE writers
// ---------------------------------------------------------------------------

fn materialize_hex_fixture(
    root: &Path,
    rel: &str,
    out_path: &Path,
    expected_sha256: &str,
) -> Result<()> {
    let bytes = read_bounded_exact_file_under(root, Path::new(rel), MAX_FIXTURE_HEX_BYTES)
        .with_context(|| format!("failed to read fixture hex {rel}"))?;
    let text =
        std::str::from_utf8(&bytes).with_context(|| format!("fixture hex {rel} not ASCII"))?;
    let compact: String = text.chars().filter(|ch| !ch.is_whitespace()).collect();
    if compact.is_empty() {
        bail!("empty fixture hex: {rel}");
    }
    if !compact.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("fixture contains non-hex bytes: {rel}");
    }
    let data = decode_hex(&compact).with_context(|| format!("invalid fixture hex {rel}"))?;
    let actual_sha256 = trust_types::digest::stable_sha256_hex(&data);
    if actual_sha256 != expected_sha256 {
        bail!(
            "fixture SHA-256 mismatch for {rel}: expected {expected_sha256}, got {actual_sha256}"
        );
    }
    if data.is_empty() {
        bail!("checked-in fixture {rel} materialized to an empty binary");
    }
    fs::write(out_path, &data)
        .with_context(|| format!("failed to materialize fixture to {}", out_path.display()))?;
    println!("fixture {rel}: {} bytes, sha256={actual_sha256}", data.len());
    Ok(())
}

fn decode_hex(compact: &str) -> Result<Vec<u8>> {
    if compact.len() % 2 != 0 {
        bail!("odd number of hex digits");
    }
    let bytes = compact.as_bytes();
    let mut out = Vec::with_capacity(compact.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push((hex_value(pair[0])? << 4) | hex_value(pair[1])?);
    }
    Ok(out)
}

fn hex_value(byte: u8) -> Result<u8> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => bail!("non-hex byte"),
    }
}


/// 64-byte ET_REL header with e_machine EM_RISCV (243), unsupported by the
/// lifter. Mirrors the shell's `struct.pack_into("<HHIQQQIHHHHHH", ...)`.
fn write_riscv_elf(path: &Path) -> Result<()> {
    let mut elf = vec![0u8; 64];
    elf[0..4].copy_from_slice(&[0x7f, b'E', b'L', b'F']);
    elf[4] = 2; // ELFCLASS64
    elf[5] = 1; // ELFDATA2LSB
    elf[6] = 1; // EV_CURRENT
    elf[16..18].copy_from_slice(&1u16.to_le_bytes()); // e_type = ET_REL
    elf[18..20].copy_from_slice(&243u16.to_le_bytes()); // e_machine = EM_RISCV
    elf[20..24].copy_from_slice(&1u32.to_le_bytes()); // e_version
    elf[52..54].copy_from_slice(&64u16.to_le_bytes()); // e_ehsize
    fs::write(path, &elf).with_context(|| format!("failed to write {}", path.display()))
}

/// 52-byte ELFCLASS32 header with e_machine EM_386 (3). Mirrors the shell's
/// `struct.pack_into("<HHIIIIIHHHHHH", ...)`.
fn write_i386_elf(path: &Path) -> Result<()> {
    let mut elf = vec![0u8; 52];
    elf[0..4].copy_from_slice(&[0x7f, b'E', b'L', b'F']);
    elf[4] = 1; // ELFCLASS32
    elf[5] = 1; // ELFDATA2LSB
    elf[6] = 1; // EV_CURRENT
    elf[16..18].copy_from_slice(&1u16.to_le_bytes()); // e_type = ET_REL
    elf[18..20].copy_from_slice(&3u16.to_le_bytes()); // e_machine = EM_386
    elf[20..24].copy_from_slice(&1u32.to_le_bytes()); // e_version
    elf[40..42].copy_from_slice(&52u16.to_le_bytes()); // e_ehsize
    fs::write(path, &elf).with_context(|| format!("failed to write {}", path.display()))
}

// ---------------------------------------------------------------------------
// JSON contract helpers
// ---------------------------------------------------------------------------

fn sfield<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("")
}

fn ifield(value: &Value, key: &str) -> Option<i64> {
    value.get(key).and_then(Value::as_i64)
}

fn ifield_or(value: &Value, key: &str, default: i64) -> i64 {
    value.get(key).and_then(Value::as_i64).unwrap_or(default)
}

fn bfield(value: &Value, key: &str) -> Option<bool> {
    value.get(key).and_then(Value::as_bool)
}

fn afield<'a>(value: &'a Value, key: &str) -> Option<&'a Vec<Value>> {
    value.get(key).and_then(Value::as_array)
}

fn objf<'a>(value: &'a Value, key: &str) -> Option<&'a Value> {
    value.get(key).filter(|inner| inner.is_object())
}

fn nonempty_array(value: &Value, key: &str) -> bool {
    afield(value, key).is_some_and(|items| !items.is_empty())
}

fn binary_matches(report: &Value, expected: &Path) -> bool {
    let reported = sfield(report, "binary");
    let reported_real = fs::canonicalize(reported).unwrap_or_else(|_| PathBuf::from(reported));
    let expected_real = fs::canonicalize(expected).unwrap_or_else(|_| expected.to_path_buf());
    reported_real == expected_real
}

fn any_item_contains(value: &Value, key: &str, needle: &str) -> bool {
    afield(value, key).is_some_and(|items| {
        items.iter().any(|item| item.as_str().is_some_and(|text| text.contains(needle)))
    })
}

fn any_str_contains(items: &[Value], needle: &str) -> bool {
    items.iter().any(|item| item.as_str().is_some_and(|text| text.contains(needle)))
}

fn sum_obj_values(value: &Value, key: &str) -> Option<i64> {
    let object = value.get(key)?.as_object()?;
    let mut sum: i64 = 0;
    for entry in object.values() {
        sum = sum.checked_add(entry.as_i64()?)?;
    }
    Some(sum)
}

fn assert_common(report: &Value, target: &str, expected_binary: &Path) -> Result<()> {
    if !binary_matches(report, expected_binary) {
        bail!("{target}: binary path mismatch");
    }
    if sfield(report, "target") != target {
        bail!("{target}: target mismatch: {:?}", report.get("target"));
    }
    if !["ok", "incomplete"].contains(&sfield(report, "status")) {
        bail!("{target}: expected status ok/incomplete, got {:?}", report.get("status"));
    }
    if sfield(report, "selection") != "address" {
        bail!("{target}: expected address selection");
    }
    if sfield(report, "entry") != X86_64_ENTRY {
        bail!("{target}: expected selected entry {X86_64_ENTRY}");
    }
    if bfield(report, "strict") != Some(false) {
        bail!("{target}: allow-unsupported should set strict false");
    }
    if ifield_or(report, "functions_decompiled", 0) < 1 {
        bail!("{target}: expected at least one decompiled function");
    }
    if ifield_or(report, "blocks", 0) < 1 {
        bail!("{target}: expected lifted blocks");
    }
    if ifield_or(report, "statements", 0) < 1 {
        bail!("{target}: expected lifted statements");
    }
    if ifield(report, "failures") != Some(0) {
        bail!("{target}: unexpected failures: {:?}", report.get("failure_items"));
    }
    if !nonempty_array(report, "functions") {
        bail!("{target}: missing function summaries");
    }
    if sfield(report, "format") != "ELF" {
        bail!("{target}: expected ELF format");
    }
    if sfield(report, "architecture") != "x86-64" {
        bail!("{target}: expected x86-64 architecture");
    }
    if afield(report, "unsupported_items").is_none() {
        bail!("{target}: unsupported_items should be a stable list");
    }
    Ok(())
}

fn assert_verify_binary(report: &Value, expected_binary: &Path) -> Result<()> {
    if !binary_matches(report, expected_binary) {
        bail!("verify-binary: binary path mismatch");
    }
    if sfield(report, "format") != "ELF" {
        bail!("verify-binary: expected ELF format");
    }
    if sfield(report, "architecture") != "x86-64" {
        bail!("verify-binary: expected x86-64 architecture");
    }
    if sfield(report, "entry") != X86_64_ENTRY {
        bail!("verify-binary: expected selected entry {X86_64_ENTRY}");
    }
    if bfield(report, "strict") != Some(false) {
        bail!("verify-binary: allow-unsupported should set strict false");
    }
    if ifield_or(report, "functions_analyzed", 0) < 1 {
        bail!("verify-binary: expected at least one analyzed function");
    }
    if ifield_or(report, "vcs", 0) < 1 {
        bail!("verify-binary: expected generated binary VCs for proof-evidence coverage");
    }
    if sfield(report, "trust_level") == "proof_grade" {
        bail!("verify-binary: proof evidence must not upgrade this fixture to proof-grade");
    }

    let Some(proof_evidence) = objf(report, "proof_evidence") else {
        bail!("verify-binary: missing proof_evidence JSON object");
    };
    let Some(proof_gate) = objf(report, "proof_grade_gate") else {
        bail!("verify-binary: missing top-level proof_grade_gate JSON object");
    };
    if bfield(proof_gate, "accepted") != Some(false) || sfield(proof_gate, "status") != "rejected" {
        bail!("verify-binary: top-level proof_grade_gate must reject this fixture");
    }
    if bfield(proof_gate, "raw_solver_proof_bytes_sufficient") != Some(false) {
        bail!("verify-binary: raw solver proof bytes must not be sufficient");
    }
    if !nonempty_array(proof_gate, "rejections") {
        bail!("verify-binary: rejected proof-grade gate should explain blockers");
    }

    let Some(shared_gate) = objf(proof_evidence, "proof_grade_gate") else {
        bail!("verify-binary: proof_evidence should include shared proof_grade_gate");
    };
    if bfield(shared_gate, "accepted") != Some(false) {
        bail!("verify-binary: shared proof evidence gate must reject this fixture");
    }
    if ifield(proof_evidence, "total_vcs") != ifield(report, "vcs") {
        bail!("verify-binary: proof_evidence total_vcs should match generated VCs");
    }
    if ifield(proof_evidence, "total_vcs") != ifield(proof_gate, "required_vcs") {
        bail!("verify-binary: proof gate required_vcs should match proof evidence");
    }
    if ifield(proof_evidence, "solver_dispatches") != ifield(proof_gate, "solver_dispatches") {
        bail!("verify-binary: solver dispatch accounting mismatch");
    }
    let dispatches = ifield(proof_evidence, "solver_dispatches");
    if sum_obj_values(proof_evidence, "solver_dispatch_status_counts") != dispatches
        || dispatches.is_none()
    {
        bail!("verify-binary: solver dispatch counts should cover every dispatch");
    }
    if sum_obj_values(proof_evidence, "replay_status_counts") != dispatches {
        bail!("verify-binary: replay counts should cover every dispatch");
    }
    let Some(coverage) = objf(proof_evidence, "checked_certificate_coverage") else {
        bail!("verify-binary: missing checked_certificate_coverage");
    };
    if ifield(coverage, "required_vcs") != ifield(proof_evidence, "total_vcs") {
        bail!("verify-binary: certificate coverage required_vcs mismatch");
    }
    if bfield(coverage, "raw_solver_proof_bytes_satisfy_coverage") != Some(false) {
        bail!("verify-binary: raw solver proof bytes must not satisfy certificate coverage");
    }
    Ok(())
}

fn assert_verify_binary_terminal(text: &str) -> Result<()> {
    for expected in [
        "targo trust verify-binary report",
        "proof-grade gate: rejected",
        "proof evidence: total_vcs=",
        "proof evidence solver dispatch counts:",
        "proof evidence replay counts:",
        "proof evidence certificate coverage:",
        "shared_proof_grade_gate=rejected",
    ] {
        if !text.contains(expected) {
            bail!("verify-binary terminal: missing {expected:?}");
        }
    }
    if text.contains("proof-grade gate: accepted") {
        bail!("verify-binary terminal: proof-grade gate must not be accepted");
    }
    Ok(())
}

fn assert_strict(report: &Value) -> Result<()> {
    if sfield(report, "format") != "ELF" {
        bail!("strict: expected accepted x86-64 input format ELF");
    }
    if sfield(report, "architecture") != "x86-64" {
        bail!("strict: expected accepted x86-64 architecture report");
    }
    if bfield(report, "strict") != Some(true) {
        bail!("strict: expected strict true");
    }
    if sfield(report, "target") != "trust_ir" {
        bail!("strict: expected trust_ir target");
    }
    if ifield_or(report, "functions_decompiled", 0) < 1 {
        bail!(
            "strict: expected x86-64 ELF to lift at least one function before fail-closed coverage checks"
        );
    }
    if ifield_or(report, "unsupported", 0) < 1 {
        bail!("strict: expected unsupported coverage to be recorded");
    }
    if !nonempty_array(report, "unsupported_items") {
        bail!("strict: expected unsupported_items to explain fail-closed strict rejection");
    }
    Ok(())
}

fn assert_bad_format(report: &Value) -> Result<()> {
    if sfield(report, "status") != "failed" {
        bail!("bad format: expected failed, got {:?}", report.get("status"));
    }
    if sfield(report, "output_trust_level") != "rejected" {
        bail!("bad format: expected rejected output trust");
    }
    if ifield_or(report, "failures", 0) < 1 {
        bail!("bad format: expected failure item");
    }
    if ifield(report, "functions_decompiled") != Some(0) {
        bail!("bad format: unsupported input should decompile zero functions");
    }
    Ok(())
}

fn assert_bad_target(report: &Value) -> Result<()> {
    if sfield(report, "status") != "incomplete" {
        bail!("bad target: expected incomplete unsupported report, got {:?}", report.get("status"));
    }
    if sfield(report, "output_trust_level") != "rejected" {
        bail!("bad target: expected rejected output trust");
    }
    if ifield_or(report, "unsupported", 0) < 1 {
        bail!("bad target: expected unsupported target item");
    }
    if !any_item_contains(report, "unsupported_items", "unsupported ELF machine type") {
        bail!(
            "bad target: expected unsupported machine diagnostic, got {:?}",
            report.get("unsupported_items")
        );
    }
    if ifield(report, "functions_decompiled") != Some(0) {
        bail!("bad target: unsupported target should decompile zero functions");
    }
    Ok(())
}

fn assert_pe(report: &Value) -> Result<()> {
    if sfield(report, "status") != "incomplete" {
        bail!("PE: expected incomplete unsupported report, got {:?}", report.get("status"));
    }
    if sfield(report, "output_trust_level") != "rejected" {
        bail!("PE: expected rejected output trust");
    }
    if ifield(report, "functions_decompiled") != Some(0) {
        bail!("PE: unsupported target should decompile zero functions");
    }
    let has_pe_diagnostic = afield(report, "unsupported_items").is_some_and(|items| {
        items.iter().any(|item| {
            item.as_str()
                .is_some_and(|text| text.contains("PE/COFF") && text.contains("not implemented"))
        })
    });
    if !has_pe_diagnostic {
        bail!("PE: expected fail-closed PE diagnostic, got {:?}", report.get("unsupported_items"));
    }
    Ok(())
}

fn assert_i386(report: &Value) -> Result<()> {
    if sfield(report, "status") != "incomplete" {
        bail!("i386: expected incomplete unsupported report, got {:?}", report.get("status"));
    }
    if sfield(report, "output_trust_level") != "rejected" {
        bail!("i386: expected rejected output trust");
    }
    if ifield(report, "functions_decompiled") != Some(0) {
        bail!("i386: unsupported target should decompile zero functions");
    }
    if !any_item_contains(
        report,
        "unsupported_items",
        "32-bit x86/i386 lifting is not implemented yet",
    ) {
        bail!(
            "i386: expected fail-closed i386 diagnostic, got {:?}",
            report.get("unsupported_items")
        );
    }
    Ok(())
}

fn assert_rust_output(report: &Value) -> Result<()> {
    if sfield(report, "output_kind") != "rust_skeleton" {
        bail!("rust: output_kind should be rust_skeleton");
    }
    if sfield(report, "output_trust_level") != "exploratory" {
        bail!("rust: output should be marked exploratory");
    }
    if sfield(report, "output_validation") != "exploratory_not_validated" {
        bail!("rust: output should be marked exploratory_not_validated");
    }
    if !sfield(report, "validation_note").contains("exploratory") {
        bail!("rust: validation note should label exploratory output");
    }
    if !sfield(report, "output_content").contains("fn ") {
        bail!("rust: expected Rust skeleton output");
    }
    Ok(())
}

/// Assert the TrustIr decompile output and return its symbolic-formula keys.
fn assert_trust_ir_output(report: &Value) -> Result<BTreeSet<(String, String, String)>> {
    if sfield(report, "output_kind") != "trust_ir_json" {
        bail!("trust_ir: output_kind should be trust_ir_json");
    }
    if sfield(report, "output_trust_level") != "partial" {
        bail!("trust_ir: output should be marked partial");
    }
    if sfield(report, "output_validation") != "lifted_trust_ir_partial" {
        bail!("trust_ir: output should be marked lifted_trust_ir_partial");
    }
    if !sfield(report, "validation_note").contains("partial") {
        bail!("trust_ir: validation note should label partial output");
    }
    let artifact: Value = serde_json::from_str(sfield(report, "output_content"))
        .context("trust_ir: output_content should be a JSON artifact")?;
    if sfield(&artifact, "trust_level") != "Partial" {
        bail!("trust_ir: artifact trust level should remain Partial");
    }
    if !nonempty_array(&artifact, "functions") {
        bail!("trust_ir: artifact should include lifted function records");
    }

    let Some(formulas) = afield(report, "preserved_symbolic_formulas") else {
        bail!(
            "trust_ir: binary decompile output should expose preserved symbolic machine formulas"
        );
    };
    if formulas.is_empty() {
        bail!(
            "trust_ir: binary decompile output should expose preserved symbolic machine formulas"
        );
    }
    let mut keys = BTreeSet::new();
    for formula in formulas {
        keys.insert(symbolic_key(formula));
        if sfield(formula, "target") != "TrustIr" {
            bail!("trust_ir: symbolic formula target mismatch: {formula:?}");
        }
        assert_inspectable_formula(formula, "trust_ir")?;
    }
    Ok(keys)
}

fn assert_derived_output(report: &Value, target: &str, output_kind: &str) -> Result<()> {
    if sfield(report, "output_kind") != output_kind {
        bail!("{target}: expected output_kind {output_kind}");
    }
    if !["partial", "rejected"].contains(&sfield(report, "output_trust_level")) {
        bail!("{target}: derived output should be partial or fail-closed rejected");
    }
    if !["validated_partial", "translation_rejected", "inspectable_rejected"]
        .contains(&sfield(report, "output_validation"))
    {
        bail!(
            "{target}: expected validated_partial, translation_rejected, or inspectable_rejected, got {:?}",
            report.get("output_validation")
        );
    }
    if !sfield(report, "validation_note").contains("proof-grade") {
        bail!("{target}: validation note should preserve non-proof-grade claim");
    }
    let Some(gate) = objf(report, "conversion_gate") else {
        bail!("{target}: missing conversion_gate");
    };
    if bfield(gate, "accepted") != Some(false) || sfield(gate, "status") != "rejected" {
        bail!("{target}: conversion gate should reject non-proof-grade output");
    }
    if sfield(gate, "target") != target {
        bail!("{target}: conversion gate target mismatch");
    }
    if bfield(gate, "proof_grade_artifact") != Some(false) {
        bail!("{target}: conversion gate must not mark non-proof-grade output proof-grade");
    }
    if !nonempty_array(gate, "blockers") {
        bail!("{target}: rejected conversion gate should explain blockers");
    }
    let Some(target_blockers) = afield(report, "target_validation_blockers") else {
        bail!("{target}: target_validation_blockers should be a stable JSON list");
    };
    if !target_blockers.iter().any(|blocker| {
        blocker.get("feature").and_then(Value::as_str) == Some("missing-target-semantic-validation")
    }) {
        bail!("{target}: release gate must exercise missing-target-semantic-validation blocker");
    }
    let Some(validation_blockers) = afield(gate, "validation_blockers") else {
        bail!("{target}: conversion gate should expose validation_blockers");
    };
    if !any_str_contains(validation_blockers, "missing-target-semantic-validation") {
        bail!("{target}: conversion gate should surface missing-target-semantic-validation");
    }
    Ok(())
}

fn assert_convert_symbolic_formula_json_contract(
    report: &Value,
    target: &str,
    symbolic_target: &str,
    trust_ir_keys: &BTreeSet<(String, String, String)>,
) -> Result<()> {
    let Some(formulas) = afield(report, "preserved_symbolic_formulas") else {
        bail!(
            "{target}: convert --to {target} --json after binary decompile should expose preserved symbolic formulas"
        );
    };
    if formulas.is_empty() {
        bail!(
            "{target}: convert --to {target} --json after binary decompile should expose preserved symbolic formulas"
        );
    }
    if sfield(report, "output_trust_level") != "rejected" {
        bail!("{target}: symbolic binary conversion must remain fail-closed rejected");
    }
    if !["inspectable_rejected", "translation_rejected"]
        .contains(&sfield(report, "output_validation"))
    {
        bail!(
            "{target}: symbolic binary conversion should be inspectable or translation rejected, got {:?}",
            report.get("output_validation")
        );
    }
    let symbolic_keys: BTreeSet<(String, String, String)> =
        formulas.iter().map(symbolic_key).collect();
    if trust_ir_keys.is_disjoint(&symbolic_keys) {
        bail!(
            "{target}: preserved symbolic formulas should correspond to the preceding TrustIr decompile output"
        );
    }
    let Some(target_blockers) = afield(report, "target_validation_blockers") else {
        bail!("{target}: target_validation_blockers should be a stable JSON list");
    };
    let Some(gate) = objf(report, "conversion_gate") else {
        bail!("{target}: conversion gate should expose validation_blockers");
    };
    let Some(validation_blockers) = afield(gate, "validation_blockers") else {
        bail!("{target}: conversion gate should expose validation_blockers");
    };
    for formula in formulas {
        if sfield(formula, "target") != symbolic_target {
            bail!("{target}: symbolic formula target mismatch: {formula:?}");
        }
        assert_inspectable_formula(formula, target)?;
        let formula_json = serde_json::to_string(formula.get("formula").unwrap_or(&Value::Null))
            .unwrap_or_default();
        if !["Var", "Select", "BvAdd", "BvOr"].iter().any(|op| formula_json.contains(op)) {
            bail!("{target}: expected structured symbolic formula JSON, got {formula:?}");
        }
    }
    if !target_blockers.iter().any(|blocker| {
        blocker.get("feature").and_then(Value::as_str) == Some("symbolic-formula-proof-semantics")
            && blocker.get("target").and_then(Value::as_str) == Some(symbolic_target)
    }) {
        bail!("{target}: symbolic formulas must have an inspectable proof-semantics blocker");
    }
    if bfield(gate, "accepted") != Some(false) || sfield(gate, "status") != "rejected" {
        bail!("{target}: conversion gate must remain rejected for symbolic formulas");
    }
    if !any_str_contains(validation_blockers, "symbolic-formula-proof-semantics") {
        bail!("{target}: conversion gate should surface symbolic-formula proof-semantics blockers");
    }
    Ok(())
}

/// A symbolic formula's `formula` field must be present, not the string
/// "Undef", and must not lower to `Undef` anywhere in its JSON.
fn assert_inspectable_formula(formula: &Value, label: &str) -> Result<()> {
    let value = formula.get("formula");
    if value.is_none() || value == Some(&Value::String("Undef".to_string())) {
        bail!("{label}: symbolic formula must be inspectable, got {formula:?}");
    }
    let json = serde_json::to_string(value.expect("checked")).unwrap_or_default();
    if json.contains("Undef") {
        bail!("{label}: symbolic formula must not be lowered to Undef: {formula:?}");
    }
    Ok(())
}

fn symbolic_key(formula: &Value) -> (String, String, String) {
    let component = |key: &str| {
        serde_json::to_string(formula.get(key).unwrap_or(&Value::Null)).unwrap_or_default()
    };
    (component("function"), component("block"), component("statement_index"))
}

fn assert_aarch64(report: &Value, expected_binary: &Path) -> Result<()> {
    if !binary_matches(report, expected_binary) {
        bail!("aarch64: binary path mismatch");
    }
    if sfield(report, "target") != "trust_ir" {
        bail!("aarch64: expected trust_ir target, got {:?}", report.get("target"));
    }
    if sfield(report, "entry") != "0x400000" {
        bail!("aarch64: expected selected entry 0x400000, got {:?}", report.get("entry"));
    }
    if sfield(report, "format") != "ELF" {
        bail!("aarch64: expected ELF format");
    }
    if sfield(report, "architecture") != "AArch64" {
        bail!("aarch64: expected AArch64 architecture, got {:?}", report.get("architecture"));
    }
    if bfield(report, "strict") != Some(false) {
        bail!("aarch64: allow-unsupported should set strict false");
    }
    if !["ok", "incomplete"].contains(&sfield(report, "status")) {
        bail!("aarch64: expected status ok/incomplete, got {:?}", report.get("status"));
    }
    if ifield_or(report, "functions_decompiled", 0) < 1 {
        bail!("aarch64: expected at least one decompiled function");
    }
    if ifield_or(report, "blocks", 0) < 1 {
        bail!("aarch64: expected lifted blocks");
    }
    if ifield_or(report, "statements", 0) < 1 {
        bail!("aarch64: expected lifted statements");
    }
    if sfield(report, "output_kind") != "trust_ir_json" {
        bail!("aarch64: output_kind should be trust_ir_json");
    }
    if sfield(report, "output_trust_level") != "partial" {
        bail!("aarch64: output should be marked partial until proof-grade evidence exists");
    }
    if afield(report, "unsupported_items").is_none() {
        bail!("aarch64: unsupported_items should be a stable list");
    }
    Ok(())
}

fn assert_aarch64_unsupported(report: &Value, expected_binary: &Path) -> Result<()> {
    if !binary_matches(report, expected_binary) {
        bail!("aarch64 unsupported-ledger: binary path mismatch");
    }
    if sfield(report, "target") != "trust_ir" {
        bail!(
            "aarch64 unsupported-ledger: expected trust_ir target, got {:?}",
            report.get("target")
        );
    }
    if sfield(report, "selection") != "all" {
        bail!("aarch64 unsupported-ledger: expected all-functions selection");
    }
    if sfield(report, "format") != "ELF" {
        bail!("aarch64 unsupported-ledger: expected ELF format");
    }
    if sfield(report, "architecture") != "AArch64" {
        bail!(
            "aarch64 unsupported-ledger: expected AArch64 architecture, got {:?}",
            report.get("architecture")
        );
    }
    if bfield(report, "strict") != Some(false) {
        bail!("aarch64 unsupported-ledger: allow-unsupported should set strict false");
    }
    if sfield(report, "status") != "incomplete" {
        bail!(
            "aarch64 unsupported-ledger: expected incomplete status with a non-empty ledger, got {:?}",
            report.get("status")
        );
    }
    if ifield(report, "functions_decompiled") != Some(2) {
        bail!(
            "aarch64 unsupported-ledger: expected exactly two successfully decompiled functions, got {:?}",
            report.get("functions_decompiled")
        );
    }
    if ifield_or(report, "blocks", 0) < 1 {
        bail!("aarch64 unsupported-ledger: expected lifted blocks from supported function");
    }
    if ifield_or(report, "statements", 0) < 1 {
        bail!("aarch64 unsupported-ledger: expected lifted statements from supported function");
    }
    if ifield_or(report, "unsupported", 0) < 1 {
        bail!("aarch64 unsupported-ledger: expected unsupported ledger entries");
    }
    let Some(unsupported_items) = afield(report, "unsupported_items") else {
        bail!("aarch64 unsupported-ledger: unsupported_items should be a non-empty stable list");
    };
    if unsupported_items.is_empty() {
        bail!("aarch64 unsupported-ledger: unsupported_items should be a non-empty stable list");
    }
    if !any_str_contains(unsupported_items, "trust_fixture_unsupported_mrs") {
        bail!(
            "aarch64 unsupported-ledger: expected unsupported symbol name in ledger, got {unsupported_items:?}"
        );
    }
    if any_str_contains(unsupported_items, "trust_fixture_supported_prfm") {
        bail!(
            "aarch64 unsupported-ledger: supported PRFM fixture function should not be a ledger item, got {unsupported_items:?}"
        );
    }
    if unsupported_items.iter().any(|item| {
        item.as_str().is_some_and(|text| {
            text.to_uppercase().contains("PRFM") || text.contains("opcode Prfm")
        })
    }) {
        bail!(
            "aarch64 unsupported-ledger: supported PRFM instruction should stay out of unsupported_items, got {unsupported_items:?}"
        );
    }
    if !any_str_contains(unsupported_items, "unsupported instruction semantics") {
        bail!(
            "aarch64 unsupported-ledger: expected semantic-lift unsupported diagnostic, got {unsupported_items:?}"
        );
    }
    if sfield(report, "output_kind") != "trust_ir_json" {
        bail!("aarch64 unsupported-ledger: output_kind should be trust_ir_json");
    }
    if sfield(report, "output_trust_level") != "partial" {
        bail!("aarch64 unsupported-ledger: output should remain partial, not proof-grade");
    }
    let artifact: Value = serde_json::from_str(sfield(report, "output_content"))
        .context("aarch64 unsupported-ledger: output_content should be a JSON artifact")?;
    let Some(records) = artifact
        .get("unsupported")
        .and_then(|inner| inner.get("records"))
        .and_then(Value::as_array)
    else {
        bail!("aarch64 unsupported-ledger: artifact should carry an unsupported records ledger");
    };
    if Some(records.len() as i64) != ifield(report, "unsupported") {
        bail!("aarch64 unsupported-ledger: report count should match artifact ledger");
    }
    if !records
        .iter()
        .any(|record| record.get("stage").and_then(Value::as_str) == Some("trust-lift"))
    {
        bail!(
            "aarch64 unsupported-ledger: expected trust-lift stage in artifact unsupported ledger"
        );
    }
    if records.iter().any(|record| {
        serde_json::to_string(record).unwrap_or_default().to_uppercase().contains("PRFM")
    }) {
        bail!(
            "aarch64 unsupported-ledger: artifact unsupported ledger should not mention supported PRFM"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scan_fn_names_matches_regex_semantics() {
        let source = "#[test]\nfn test_alpha() {}\npub fn beta (x: u32) {}\nfn gamma<T>() {}\nprefixfn delta() {}\n";
        let names = scan_fn_names(source);
        assert!(names.contains(&"test_alpha".to_string()));
        assert!(names.contains(&"beta".to_string()));
        // Generic `fn gamma<T>()` has `<` before `(`, so it is not matched
        // (the shell regex `fn\s+NAME\s*\(` would not match either).
        assert!(!names.contains(&"gamma".to_string()));
        // `prefixfn` has no word boundary before `fn`.
        assert!(!names.contains(&"delta".to_string()));
    }

    #[test]
    fn manifest_test_matcher_mirrors_regex() {
        assert!(is_targo_manifest_test(
            "test_parse_args_checked_certificate_manifests_do_not_passthrough"
        ));
        assert!(is_targo_manifest_test("test_checked_cert_manifest_import"));
        assert!(!is_targo_manifest_test("test_unrelated_binary_gate"));
        assert!(!is_targo_manifest_test("checked_certificate_manifest_helper"));
    }

    #[test]
    fn proof_cert_rejection_matcher_mirrors_regex() {
        assert!(is_proof_cert_rejection_test(
            "checked_binary_certificate_manifest_rejects_missing_certificate_files"
        ));
        assert!(!is_proof_cert_rejection_test(
            "checked_binary_certificate_manifest_from_artifact_refs_is_stable"
        ));
        assert!(!is_proof_cert_rejection_test("some_other_reject_test"));
    }

    #[test]
    fn hex_decode_round_trips_and_rejects_bad_input() {
        assert_eq!(decode_hex("7f454c46").expect("hex"), vec![0x7f, 0x45, 0x4c, 0x46]);
        assert!(decode_hex("abc").is_err()); // odd length
        assert!(hex_value(b'z').is_err());
    }

    #[test]
    fn riscv_and_i386_headers_have_expected_machine_bytes() {
        let dir = tempfile::tempdir().expect("tmp");
        let riscv = dir.path().join("riscv.o");
        write_riscv_elf(&riscv).expect("riscv");
        let riscv_bytes = fs::read(&riscv).expect("read riscv");
        assert_eq!(riscv_bytes.len(), 64);
        assert_eq!(&riscv_bytes[0..4], b"\x7fELF");
        assert_eq!(u16::from_le_bytes([riscv_bytes[18], riscv_bytes[19]]), 243);

        let i386 = dir.path().join("i386.o");
        write_i386_elf(&i386).expect("i386");
        let i386_bytes = fs::read(&i386).expect("read i386");
        assert_eq!(i386_bytes.len(), 52);
        assert_eq!(u16::from_le_bytes([i386_bytes[18], i386_bytes[19]]), 3);
    }

    #[test]
    fn symbolic_key_uses_all_three_fields() {
        let a = serde_json::json!({"function": "f", "block": 1, "statement_index": 0});
        let b = serde_json::json!({"function": "f", "block": 1, "statement_index": 1});
        assert_ne!(symbolic_key(&a), symbolic_key(&b));
    }

    #[test]
    fn inspectable_formula_rejects_undef() {
        let good = serde_json::json!({"formula": {"Var": "x"}});
        assert!(assert_inspectable_formula(&good, "t").is_ok());
        let undef_string = serde_json::json!({"formula": "Undef"});
        assert!(assert_inspectable_formula(&undef_string, "t").is_err());
        let undef_nested = serde_json::json!({"formula": {"BvOr": ["Undef", "x"]}});
        assert!(assert_inspectable_formula(&undef_nested, "t").is_err());
        let missing = serde_json::json!({});
        assert!(assert_inspectable_formula(&missing, "t").is_err());
    }
}
