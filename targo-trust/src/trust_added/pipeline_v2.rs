//! `native-contracts-pipeline-v2` — the first #1049 runner hook, Rust-native.
//!
//! Faithful port of the superset suite's mode: focused native transport, the
//! basic contract corpus, and Formula-family owner checks. It does not claim
//! full Pipeline v2 release validation.
//!
//! Steps, in the shell gate's order:
//! 1. Same-run typed trust-vc / trust-wp / trust-mc ownership evidence.
//! 2. MIR-compatibility contract source-recovery fail-closed behavioral
//!    tests. This is an adapter lane, not frontend authority; Rust and Lean
//!    frontends produce TrustIR directly.
//! 3. VC-generation guard-contract soundness/consumer tests feeding the
//!    TrustIR native spine, including multi-parameter and one-way implication
//!    summaries.
//! 4. The three trustc-native sub-gates (compiler transport, public CLI,
//!    root resolution) — shared with the `trustc-native` mode.
//! 5. The basic contracts proof-corpus smoke (`examples/contracts/
//!    basic-contracts`, materialized as a hermetic scratch copy): the
//!    explicit `targo --unverified check` lane type-checks clean, raw trustc verification
//!    (`targo trust check --format json`) fails closed on exactly the pinned
//!    deliberately-unproved set, and the standalone compatibility inventory.
//! 6. `targo --unverified test -p trust-router --test formula_compat_gate` through the
//!    resolved Trust targo.
//!
//! The shell gate's `require_subcheck` steps only asserted that the *shell
//! scripts* existed before dispatching them; the sub-gates are Rust functions
//! here, so those vestigial file-existence checks are dropped.

use std::collections::BTreeSet;
use std::path::Path;

use anyhow::{Context, Result, bail};
use serde_json::Value;
use trust_types::{
    JsonProofReport, ObligationOutcome, ProofStrength, SavedReportSanitization,
    UntrustedSavedOutcomeClaim, UntrustedSavedReportClaims, VcKind,
};
use trust_verifier_api::{
    EvidenceDisposition, EvidenceStatus, VerificationRunManifest, VerificationRunStatus,
    VerificationRunSummary,
};

use super::trustc_native::{
    Captured, capture, compiler_verify, contains, field_str, json_object, public_cli,
    public_cli_command, root_resolution, standalone_targo,
};
use super::{
    GatePolicy, pin_targo_sibling_toolchain, read_bounded_exact_file_under,
    scrub_gate_process_environment, section,
};
use crate::stage2_tools::{
    revalidate_exact_executable, revalidate_repo_stage2_tool, snapshot_exact_executable,
    snapshot_repo_stage2_tool,
};

const MAX_THREE_SUITE_MANIFEST_BYTES: u64 = 8 * 1024 * 1024;
const THREE_SUITE_SAMPLE_FILTER: &str = "sample_bundle_records_trust_vc_memory_bridge_debt";
const TRUST_MC_SAMPLE_OBLIGATION: &str = "sample::trust-mc-arithmetic-safety";
const TRUST_VC_SAMPLE_OBLIGATION: &str = "sample::trust-vc-ownership";
const TRUST_WP_SAMPLE_OBLIGATION: &str = "sample::trust-wp-postcondition";

const CONTRACT_CORPUS_FUNCTIONS: [&str; 5] =
    ["divide_exact", "abs_total", "get_at", "running_total", "midpoint_checked"];
const AUTHORED_ENSURES_FUNCTIONS: [&str; 3] = ["divide_exact", "abs_total", "get_at"];
const CONTRACT_CORPUS_CRATE: &str = "basic_contracts";
const CONTRACT_CORPUS_SYNTHETIC_ROW: &str = "<crate:basic_contracts>";

fn canonical_contract_corpus_function<'a>(
    function: &'a str,
    report_subject: &str,
) -> Option<&'a str> {
    let function = function.strip_prefix(report_subject)?.strip_prefix("::")?;
    if function == CONTRACT_CORPUS_SYNTHETIC_ROW {
        return Some(CONTRACT_CORPUS_SYNTHETIC_ROW);
    }
    let short = function.strip_prefix("basic_contracts::")?;
    CONTRACT_CORPUS_FUNCTIONS.contains(&short).then_some(short)
}

fn exact_contract_clause_location(
    location: Option<&trust_types::SourceSpan>,
    function: &str,
) -> bool {
    let expected_line = match function {
        "divide_exact" => 7,
        "abs_total" => 13,
        "get_at" => 26,
        _ => return false,
    };
    location.is_some_and(|span| {
        Path::new(&span.file).ends_with(Path::new("src/lib.rs"))
            && span.line_start == expected_line
            && span.line_end >= span.line_start
            && (span.line_end > span.line_start || span.col_end >= span.col_start)
    })
}

fn validate_contract_cargo_identity(report: &JsonProofReport) -> Result<()> {
    let inventory = report
        .cargo_proof_inventory
        .as_ref()
        .context("native contract report is missing its Cargo proof-unit inventory")?;
    if inventory.schema != trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2 {
        bail!("native contract report uses an unsupported Cargo proof inventory schema");
    }
    if inventory.include_dependencies
        || inventory.declared != inventory.completed
        || inventory.declared != inventory.covered
    {
        bail!(
            "native contract report did not declare, complete, and cover one exact Cargo proof frontier"
        );
    }
    if !inventory.declared.test_execution_units.is_empty()
        || !inventory.declared.dependency_units.is_empty()
        || !inventory.excluded_active_units.is_empty()
        || inventory.declared.primary_roots.len() != 1
    {
        bail!("native contract report Cargo frontier is not the single pinned library unit");
    }
    let unit = &inventory.declared.primary_roots[0];
    if unit.package_name != "basic-contracts"
        || unit.target_name != CONTRACT_CORPUS_CRATE
        || unit.target_kinds != ["lib"]
        || unit.proof_unit_role != "primary"
        || unit.graph_role != "primary"
        || unit.exclusion_reason.is_some()
        || unit.compile_target.trim().is_empty()
        || unit.compile_target_spec_sha256.is_some()
        // `targo trust check` runs the proof frontier in BUILD mode, not check
        // mode: TrustVerify runs over optimized MIR, which `cargo check` can
        // stop short of, so `Subcommand::Check` maps to build-mode targo (see
        // pipeline::run's cargo_cmd selection). The proof unit therefore
        // reports `proof_unit_mode = "build"`, and so does `compile_mode`.
        || unit.proof_unit_mode != "build"
        || !unit.package_id.starts_with("path+file://")
        || !unit.package_id.ends_with("/basic-contracts#0.1.0")
    {
        bail!("native contract report Cargo unit does not identify basic-contracts 0.1.0 exactly");
    }
    let semantics = unit
        .semantics
        .as_ref()
        .context("native contract report Cargo unit omits its closed semantic descriptor")?;
    crate::pipeline::transport::validate_cargo_unit_semantics(
        semantics,
        "native contract report Cargo unit",
    )
    .map_err(anyhow::Error::msg)?;
    let semantic_digest = crate::pipeline::transport::cargo_unit_semantics_sha256(semantics)
        .map_err(anyhow::Error::msg)?;
    if unit.semantics_sha256.as_deref() != Some(semantic_digest.as_str())
        || semantics.target_edition != "2024"
        || semantics.target_crate_types != ["lib"]
        || semantics.cfg_test
        // A plain `[lib]` target carries the default `harness = true` (a static
        // target-config property, independent of build mode — `cfg_test` above
        // already pins that no test harness is compiled). The corpus lib sets no
        // `harness = false`, so its unit reports `target_harness = true`; pin
        // that exact value rather than reject the library default.
        || !semantics.target_harness
        || semantics.target_proc_macro
        || semantics.compiler.frontend != "rustc"
        || semantics.compiler.codegen_backend != "llvm"
    {
        bail!("native contract report Cargo unit semantic identity is inconsistent");
    }

    // Cargo-mode reports scope every function under this exact single-target
    // subject. Bind every inventory field that survives in the observational
    // DTO back to that subject instead of accepting a short crate-name alias.
    if !report.crate_name.starts_with("cargo-target(") || !report.crate_name.ends_with(')') {
        bail!("native contract report subject is not one exact Cargo target identity");
    }
    let quoted_subject_field = |field: &str| {
        let prefix = format!("{field}=\"");
        report
            .crate_name
            .split_once(&prefix)
            .and_then(|(_, suffix)| suffix.split_once('"').map(|(value, _)| value))
    };
    let unit_identity = quoted_subject_field("unit_identity_sha256");
    let compile_kind = quoted_subject_field("compile_kind");
    let Some(unit_identity) = unit_identity.filter(|digest| {
        digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    }) else {
        bail!("native contract report subject contains a malformed hidden Cargo identity field");
    };
    // A host build (the smoke corpus is compiled for the host with no
    // `--target`) serializes `compile_kind = "host"`; only a cross-compile uses
    // `target(<triple>)`. The proof unit is always the host library unit.
    if compile_kind != Some("host") {
        bail!("native contract report subject contains a malformed hidden Cargo identity field");
    }
    let expected_subject = format!(
        "cargo-target(package_id={:?},package={:?},kind={:?},target={:?},compile_target={:?},compile_mode={:?},compile_kind={:?},unit_identity_sha256={:?},compile_target_spec_sha256={:?},proof_unit_index={},proof_unit_mode={:?},proof_unit_role={:?},semantics_sha256={:?})",
        unit.package_id,
        unit.package_name,
        unit.target_kinds,
        unit.target_name,
        unit.compile_target,
        unit.proof_unit_mode,
        "host",
        unit_identity,
        unit.compile_target_spec_sha256,
        unit.proof_unit_index,
        unit.proof_unit_mode,
        unit.proof_unit_role,
        semantic_digest,
    );
    if report.crate_name != expected_subject {
        bail!(
            "native contract report subject does not exactly match its Cargo proof-unit inventory"
        );
    }
    Ok(())
}

fn exact_authored_postcondition(obligation: &trust_types::ObligationReport) -> bool {
    let Some(typed_kind) =
        obligation.transport_evidence.as_ref().and_then(|evidence| evidence.typed_kind.as_deref())
    else {
        return false;
    };
    matches!(typed_kind, VcKind::Postcondition)
        && obligation.kind == "postcondition"
        && obligation.description == typed_kind.description()
}

fn exact_fail_closed_unparseable_ensures(obligation: &trust_types::ObligationReport) -> bool {
    let Some(typed_kind) =
        obligation.transport_evidence.as_ref().and_then(|evidence| evidence.typed_kind.as_deref())
    else {
        return false;
    };
    matches!(
        typed_kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "SpecEnsuresUnparseable"
    ) && obligation.kind == "unsupported_mir"
        && obligation.description == typed_kind.description()
}

pub(super) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("Native Trust contract Pipeline v2 hook");
    println!(
        "Scope: first #1049 runner hook only. This dispatches focused native transport, basic contract corpus, and Formula-family owner checks; it does not claim full Pipeline v2 release validation."
    );

    // Resolve once and retain endpoint identities across the complete gate.
    // Subchecks resolve the same unique sibling pair independently; the final
    // recheck detects any persistent tool replacement during those launches.
    let (initial_targo, initial_trustc) = standalone_targo(root)?;
    let targo_identity =
        snapshot_repo_stage2_tool(root, &initial_targo, "native-contracts-pipeline-v2", "targo")
            .map_err(anyhow::Error::msg)?;
    let trustc_identity =
        snapshot_repo_stage2_tool(root, &initial_trustc, "native-contracts-pipeline-v2", "trustc")
            .map_err(anyhow::Error::msg)?;

    let run_result = (|| -> Result<()> {
        section("Same-run native proof-engine artifact manifest");
        run_three_suite_artifact_gate(root)?;

        run_contract_source_recovery_tests(root, policy)?;
        run_vcgen_guard_contract_tests(root)?;

        compiler_verify(root, policy)?;
        public_cli(root, policy)?;
        root_resolution(root, policy)?;
        basic_contracts_smoke(root, policy)?;

        section("Formula compatibility gate test");
        let (targo, _trustc) = standalone_targo(root)?;
        let manifest = root.join("crates/Cargo.toml");
        let mut command = std::process::Command::new(&targo);
        let target = tempfile::Builder::new()
            .prefix("trust-formula-compat-target-")
            .tempdir()
            .context("failed to create formula compatibility target directory")?;
        scrub_gate_process_environment(&mut command);
        pin_targo_sibling_toolchain(&mut command, &targo)?;
        command
            .arg("--unverified")
            .arg("test")
            .arg("--manifest-path")
            .arg(&manifest)
            .args(["--locked", "-p", "trust-router", "--test", "formula_compat_gate"])
            .current_dir(root)
            .env("CARGO_TARGET_DIR", target.path())
            .env("CARGO_NET_OFFLINE", "true");
        let run =
            capture(command).with_context(|| format!("failed to launch {}", targo.display()))?;
        if !run.exited_with(0) {
            bail!(
                "trust-router formula_compat_gate test failed with status {}\nstdout:\n{}\nstderr:\n{}",
                run.exit,
                run.stdout,
                run.stderr
            );
        }
        if !run
            .stdout
            .lines()
            .any(|line| line.trim().starts_with("test ") && line.trim().ends_with(" ... ok"))
        {
            bail!(
                "formula compatibility target exited successfully without running a non-ignored test"
            );
        }
        Ok(())
    })();

    let targo_stability = revalidate_repo_stage2_tool(
        &targo_identity,
        "native-contracts-pipeline-v2 after-use check",
        "targo",
    )
    .map_err(anyhow::Error::msg);
    let trustc_stability = revalidate_repo_stage2_tool(
        &trustc_identity,
        "native-contracts-pipeline-v2 after-use check",
        "trustc",
    )
    .map_err(anyhow::Error::msg);
    run_result?;
    targo_stability?;
    trustc_stability
}

pub(super) fn run_three_suite_artifact_gate(root: &Path) -> Result<()> {
    let (targo, _) = standalone_targo(root)?;
    let scratch = tempfile::Builder::new()
        .prefix("trust-three-suite-artifacts-")
        .tempdir()
        .context("failed to create three-suite artifact directory")?;
    let manifest_path = scratch.path().join("verification-run-manifest.json");
    let target = scratch.path().join("target");
    // The manifest-writer test. Its result is intentionally Inconclusive: only
    // trust-wp supplies same-run native proof in this synthetic sample; trust-mc
    // and trust-vc are both native-authority debt (the b62 hardening refuses the
    // sample's serialized trust-mc verdict, and the trust-vc obligation carries
    // no replay-authorized TrustVc request), so a passing Rust test must not be
    // confused with a fully-proved run.
    let test = THREE_SUITE_SAMPLE_FILTER;
    let mut command = std::process::Command::new(&targo);
    scrub_gate_process_environment(&mut command);
    pin_targo_sibling_toolchain(&mut command, &targo)?;
    command
        .arg("--unverified")
        .args(["test", "--manifest-path"])
        .arg(root.join("crates/Cargo.toml"))
        .args([
            "--locked",
            "-p",
            "trust-router",
            "--features",
            "trust-build",
            "--test",
            "full_verifier_three_suite_sample",
            test,
            "--",
            "--exact",
        ])
        .current_dir(root)
        .env("CARGO_TARGET_DIR", &target)
        .env("CARGO_NET_OFFLINE", "true")
        .env("TRUST_FULL_VERIFIER_THREE_SUITE_MODE", "required-native-suites")
        .env("TRUST_THREE_SUITE_MANIFEST_OUT", &manifest_path);
    let run = capture(command)?;
    if !run.exited_with(0) {
        bail!(
            "native three-suite artifact test failed with status {}\nstdout:\n{}\nstderr:\n{}",
            run.exit,
            run.stdout,
            run.stderr
        );
    }
    let expected_positive = format!("test {test} ... ok");
    if !run.stdout.lines().any(|line| line.trim() == expected_positive) {
        bail!("three-suite positive filter did not execute the exact named test");
    }

    let bytes = read_bounded_exact_file_under(
        scratch.path(),
        Path::new("verification-run-manifest.json"),
        MAX_THREE_SUITE_MANIFEST_BYTES,
    )
    .context("native three-suite test did not materialize a bounded exact verifier manifest")?;
    if bytes.is_empty() {
        bail!("native three-suite verifier manifest is empty");
    }
    let manifest: VerificationRunManifest = serde_json::from_slice(&bytes)
        .context("native three-suite test emitted an invalid typed verifier manifest")?;
    manifest
        .validate_derived_state()
        .map_err(anyhow::Error::msg)
        .context("native three-suite verifier manifest failed derived-state validation")?;
    validate_three_suite_manifest(&manifest)?;
    let digest = trust_types::digest::stable_sha256_hex(&bytes);
    println!(
        "Validated one typed fail-closed three-suite manifest: trust-wp accepted (same-run native deductive proof), trust-mc and trust-vc rejected pending live native-bundle CHC/PDR (trust-mc) and kernel-replayed TrustVc (trust-vc) authority (sha256:{digest})"
    );

    // A positive-only fixture could conceal dispatch fallback. Exercise the
    // paired negative row with one required suite removed and require its
    // fail-closed assertions to pass as well.
    let negative = "sample_bundle_required_suite_mode_rejects_missing_native_suite";
    let mut command = std::process::Command::new(&targo);
    scrub_gate_process_environment(&mut command);
    pin_targo_sibling_toolchain(&mut command, &targo)?;
    command
        .arg("--unverified")
        .args(["test", "--manifest-path"])
        .arg(root.join("crates/Cargo.toml"))
        .args([
            "--locked",
            "-p",
            "trust-router",
            "--features",
            "trust-build",
            "--test",
            "full_verifier_three_suite_sample",
            negative,
            "--",
            "--exact",
        ])
        .current_dir(root)
        .env("CARGO_TARGET_DIR", &target)
        .env("CARGO_NET_OFFLINE", "true")
        .env("TRUST_FULL_VERIFIER_THREE_SUITE_MODE", "required-native-suites");
    let run = capture(command)?;
    if !run.exited_with(0) {
        bail!(
            "native three-suite missing-engine fail-closed test failed with status {}\nstdout:\n{}\nstderr:\n{}",
            run.exit,
            run.stdout,
            run.stderr
        );
    }
    let expected_negative = format!("test {negative} ... ok");
    if !run.stdout.lines().any(|line| line.trim() == expected_negative) {
        bail!("three-suite negative filter did not execute the exact named test");
    }
    Ok(())
}

/// Validate the current three-suite integration contract without converting a
/// passing test process into a counterfeit proof claim.
///
/// After the ratified b62 "reject unreplayed native proof authority" hardening,
/// only TrustWp supplies same-run, materialized native proof evidence for this
/// synthetic sample. TrustMc's proof-grade admission now requires a live opaque
/// native-bundle CHC/PDR authority (the sample carries only a serialized
/// `FullVerificationVerdict` plus a trivial native formula, which is
/// diagnostic-only), and TrustVc request planning still refuses to manufacture
/// evidence without a replay-authorized TrustVc request. The only sound
/// aggregate is therefore `Inconclusive` with exactly one accepted proof
/// (trust-wp) and both the trust-mc and trust-vc rows rejected. This is a
/// weaker-but-honest claim than the former 2/3 shape; do not restore proved=2
/// without genuine live native trust-mc authority.
fn validate_three_suite_manifest(manifest: &VerificationRunManifest) -> Result<()> {
    let expected_summary = VerificationRunSummary {
        requested_obligations: 3,
        evidence_count: 3,
        proved: 1,
        unsupported: 2,
        ..VerificationRunSummary::default()
    };
    if manifest.status != VerificationRunStatus::Inconclusive
        || manifest.summary != expected_summary
        || manifest.accepted_evidence.len() != 1
        || manifest.rejected_evidence.len() != 2
        || !manifest.skipped.is_empty()
    {
        bail!(
            "native three-suite verifier manifest must be fail-closed: Inconclusive with exactly 1 accepted proof (trust-wp) and 2 unsupported rejections (trust-mc/trust-vc); summary={:?}, accepted={}, rejected={}, skipped={}",
            manifest.summary,
            manifest.accepted_evidence.len(),
            manifest.rejected_evidence.len(),
            manifest.skipped.len(),
        );
    }
    if manifest.is_release_actionable() {
        bail!("inconclusive native three-suite manifest must never be release-actionable");
    }

    // trust-wp is the only same-run materialized native proof in this synthetic
    // sample.
    let Some(trust_wp) = manifest
        .accepted_evidence
        .iter()
        .find(|decision| decision.obligation_id == TRUST_WP_SAMPLE_OBLIGATION)
    else {
        bail!("native three-suite manifest omitted accepted trust-wp evidence");
    };
    if trust_wp.engine.name != "trust-full-verifier"
        || trust_wp.status != EvidenceStatus::Proved
        || trust_wp.disposition != EvidenceDisposition::AcceptedProof
        || trust_wp.artifacts.is_empty()
        || !trust_wp.artifacts.iter().any(|artifact| artifact.materialization.is_some())
        || !trust_wp.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("primary owner trust-wp@")
                && diagnostic.contains("accepted evidence")
        })
    {
        bail!(
            "native three-suite trust-wp row is not same-run accepted materialized proof evidence"
        );
    }

    // trust-mc and trust-vc are both native-authority debt: rejected as
    // unsupported and artifact-free until a live opaque native-bundle CHC/PDR
    // authority (trust-mc) and a replay-authorized TrustVc request (trust-vc)
    // are supplied.
    let expected_rejected =
        [(TRUST_MC_SAMPLE_OBLIGATION, "trust-mc"), (TRUST_VC_SAMPLE_OBLIGATION, "trust-vc")];
    for (obligation_id, suite) in expected_rejected {
        let Some(decision) = manifest
            .rejected_evidence
            .iter()
            .find(|decision| decision.obligation_id == obligation_id)
        else {
            bail!("native three-suite manifest omitted rejected {suite} evidence");
        };
        if decision.engine.name != "trust-full-verifier"
            || decision.status != EvidenceStatus::Unsupported
            || decision.disposition != EvidenceDisposition::RejectedStatus
            || decision.proof_strength.is_some()
            || !decision.artifacts.is_empty()
            || !decision.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(&format!("primary owner {suite}@"))
                    && diagnostic.contains("rejected evidence")
            })
        {
            bail!(
                "native three-suite {suite} row must remain unsupported and artifact-free until native proof authority is available"
            );
        }
    }

    // The trust-vc rejection additionally records the specific missing-request
    // cause; keep pinning it so a silent dispatch fallback cannot masquerade as
    // this fail-closed shape.
    let trust_vc = manifest
        .rejected_evidence
        .iter()
        .find(|decision| decision.obligation_id == TRUST_VC_SAMPLE_OBLIGATION)
        .context("native three-suite manifest omitted rejected trust-vc evidence")?;
    if !trust_vc
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.contains("contains no TrustVc requests"))
    {
        bail!(
            "native three-suite trust-vc row must record the no-TrustVc-request cause until kernel-replayed proof authority is available"
        );
    }

    Ok(())
}


fn require_bootstrap_execution_policy(policy: GatePolicy) -> Result<()> {
    if policy.release {
        bail!(
            "release native-contracts-pipeline-v2 refuses the mutable repository-local build/bootstrap executable: its exact-file digest can be checked before and after use, but no independently authenticated source/build provenance binds those bytes; run this adapter test only as a non-release diagnostic until an external attestation or execution-isolated build handle is available"
        );
    }
    Ok(())
}

fn run_contract_source_recovery_tests(root: &Path, policy: GatePolicy) -> Result<()> {
    section("MIR-compatibility contract source-recovery behavioral tests");
    // `trust-mir-extract` requires rustc_private, so it is deliberately
    // EXCLUDED from the crates/ dev workspace (crates/Cargo.toml `exclude`)
    // and is a member of the ROOT compiler workspace instead. A targo
    // invocation against crates/Cargo.toml can never resolve it ("package ID
    // specification did not match any packages"), and a direct manifest build
    // fails on cross-workspace path deps. Route the behavioral tests through
    // the Rust bootstrap binary's crate-test lane
    // (`bootstrap test crates/trust-mir-extract`) — the same no-Python
    // bootstrap resolution the trust-added compiletest gate uses — which
    // builds against the cached stage2 compiler artifacts.
    // `compat_source_recovery_must_be_explicitly_selected` was deleted with the
    // legacy compat/debug source-scraping contract lane it guarded
    // (R-U §1.2-5, d6cda3055b1) — the surface no longer exists, so the four
    // surviving behavioral tests are the complete set.
    require_bootstrap_execution_policy(policy)?;
    const SOURCE_RECOVERY_TESTS: [&str; 4] = [
        "convert_trust_contract_bundle_maps_supported_requires_ensures_payloads",
        "convert_trust_contract_bundle_accepts_empty_bundle",
        "convert_trust_contract_bundle_preserves_unsupported_predicates_fail_closed",
        "native_no_contract_bundle_fails_closed_without_source_scraping",
    ];
    let bootstrap = super::rust_bootstrap_binary(root)?;
    let bootstrap_identity = snapshot_exact_executable(
        &bootstrap,
        "native-contracts-pipeline-v2",
        "repository bootstrap executable",
    )
    .map_err(anyhow::Error::msg)?;
    let mut command = std::process::Command::new(&bootstrap);
    command
        .arg("test")
        .arg("--src")
        .arg(root)
        .args(["--stage", "2", "--force-rerun", "--set", "build.submodules=false"])
        .arg("crates/trust-mir-extract")
        .current_dir(root);
    for test in SOURCE_RECOVERY_TESTS {
        command.arg("--test-args").arg(format!("tests::{test}"));
    }
    command.arg("--test-args").arg("--exact");
    // `rust_bootstrap_binary` constrains the path shape, but path shape does
    // not scrub compiler wrappers, loader injection, or forwarded authority.
    // Apply the native gate's compiler/loader override blacklist immediately
    // before bounded capture. This reduces ambient authority for a local
    // diagnostic but is not an isolated/allowlisted release environment.
    scrub_gate_process_environment(&mut command);
    let run_result = capture(command)
        .with_context(|| format!("failed to launch {} for trust-mir-extract", bootstrap.display()));
    let identity_result = revalidate_exact_executable(
        &bootstrap_identity,
        "native-contracts-pipeline-v2",
        "repository bootstrap executable",
    )
    .map_err(anyhow::Error::msg);
    let run = run_result?;
    identity_result?;
    if !run.exited_with(0) {
        bail!(
            "trust-mir-extract behavioral source-recovery tests failed with status {}\nstdout:\n{}\nstderr:\n{}",
            run.exit,
            run.stdout,
            run.stderr
        );
    }
    // The bootstrap crate-test lane runs libtest in terse mode (`--format
    // terse`): it emits `running N tests`, a run of `.` per pass, and a
    // `test result: ok. N passed; …` summary — it never prints the per-test
    // `test tests::<name> ... ok` lines. We therefore verify execution from
    // the terse summary, which is airtight here: we pass exactly
    // SOURCE_RECOVERY_TESTS.len() distinct `tests::<name>` filters with
    // `--exact`, so `running {len} tests` proves every named test was
    // selected (a misspelled or deleted name would lower the count), and
    // `test result: ok. {len} passed; 0 failed` proves each one passed.
    let n = SOURCE_RECOVERY_TESTS.len();
    let selected_exact_count =
        run.stdout.lines().any(|line| line.trim() == format!("running {n} tests"));
    if !selected_exact_count {
        bail!(
            "trust-mir-extract bootstrap crate-test lane did not select the {n} exact source-recovery tests (no `running {n} tests` line)\nstdout:\n{}",
            run.stdout
        );
    }
    let all_passed = run.stdout.lines().any(|line| {
        let line = line.trim();
        line.starts_with(&format!("test result: ok. {n} passed;")) && line.contains("0 failed;")
    });
    if !all_passed {
        bail!(
            "trust-mir-extract bootstrap crate-test lane did not report `test result: ok. {n} passed; 0 failed` for the source-recovery tests\nstdout:\n{}",
            run.stdout
        );
    }
    if run.stdout.contains("test result: FAILED") || run.stderr.contains("test result: FAILED") {
        bail!(
            "trust-mir-extract bootstrap crate-test lane reported a FAILED test result\nstdout:\n{}\nstderr:\n{}",
            run.stdout,
            run.stderr
        );
    }
    Ok(())
}

fn run_vcgen_guard_contract_tests(root: &Path) -> Result<()> {
    section("TrustIR-native-spine VCgen inferred guard-contract gates");
    let (targo, _) = standalone_targo(root)?;
    let target = tempfile::Builder::new()
        .prefix("trust-vcgen-guard-contract-target-")
        .tempdir()
        .context("failed to create VCgen guard-contract target directory")?;
    for base in [
        "multi_arm_probe_body_records_nothing",
        "infers_bool_pred_multi_param",
        "infers_bool_pred_enum_not_first",
        "infers_implies_true_from_payload_guard",
        "implies_true_emits_one_directional_fact",
        "infers_implies_true_from_probe_and",
        "multi_param_consumer_connects_only_at_exact_arity",
    ] {
        let exact = format!("generate::unwrap_panic_freedom_tests::{base}");
        let mut command = std::process::Command::new(&targo);
        scrub_gate_process_environment(&mut command);
        pin_targo_sibling_toolchain(&mut command, &targo)?;
        command
            .arg("--unverified")
            .args(["test", "--manifest-path"])
            .arg(root.join("crates/Cargo.toml"))
            .args(["--locked", "-p", "trust-vcgen", "--lib"])
            .arg(&exact)
            .args(["--", "--exact"])
            .current_dir(root)
            .env("CARGO_TARGET_DIR", target.path())
            .env("CARGO_NET_OFFLINE", "true");
        let run = capture(command)
            .with_context(|| format!("failed to launch VCgen guard-contract test {exact}"))?;
        if !run.exited_with(0) {
            bail!(
                "VCgen guard-contract test `{exact}` failed with status {}\nstdout:\n{}\nstderr:\n{}",
                run.exit,
                run.stdout,
                run.stderr
            );
        }
        let expected = format!("test {exact} ... ok");
        if !run.stdout.lines().any(|line| line.trim() == expected) {
            bail!(
                "VCgen guard-contract filter exited successfully without executing exact test `{exact}`"
            );
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Basic contracts proof-corpus smoke (e2e_basic_contracts_smoke.sh)
// ---------------------------------------------------------------------------

fn basic_contracts_smoke(root: &Path, _policy: GatePolicy) -> Result<()> {
    println!();
    println!("=== tRust E2E Test: basic contracts proof corpus smoke ===");
    println!();

    let crate_dir = root.join("examples/contracts/basic-contracts");
    if !crate_dir.join("Cargo.toml").is_file() {
        bail!(
            "ERROR (setup): example crate manifest not found: {}",
            crate_dir.join("Cargo.toml").display()
        );
    }
    let (targo, trustc) = standalone_targo(root)?;
    println!("Using targo:       {}", targo.display());
    println!("Using trustc:       {}", trustc.display());
    println!("Crate:             {}", crate_dir.display());
    println!();

    let scratch = tempfile::Builder::new()
        .prefix("basic_contracts_smoke_")
        .tempdir()
        .context("failed to create scratch dir")?;
    // Canonicalize the scratch root before deriving the corpus copy or the
    // Cargo target dir. On macOS `tempfile` yields a `/var/folders/…` path, but
    // `/var` is a symlink to `/private/var`, so a `CARGO_TARGET_DIR` under it is
    // a NON-canonical runtime-library path that the dev-launcher's verified
    // pathname-authority check rejects ("forbids aliases and redirection") —
    // verification then never runs, the transport is empty, and this gate reads
    // the fail-closed refutation as a missing-JSON setup failure. `scratch`
    // still owns the same directory (same inode) for drop cleanup.
    let scratch_root = scratch
        .path()
        .canonicalize()
        .context("failed to canonicalize scratch dir")?;
    // The corpus is exercised from a hermetic scratch copy: cargo resolves and
    // writes a fresh lock there, so the gate neither trips over a stale
    // committed Cargo.lock (the exec-c30dc44143 failure: trust-spec 0.1.0 was
    // still pinned after the 0.1.1 bump) nor mutates the working tree.
    let work_dir = materialize_contracts_corpus(&crate_dir, &scratch_root)?;
    let target_dir = scratch_root.join("target");

    // Explicit `targo --unverified check` is the product's compile-only lane: the targo
    // frontend runs the native build with the verifier disabled per invocation
    // (fast-lint). This pins the original intent of the step — "the example
    // crate type-checks" — which MUST hold even though the corpus deliberately
    // fail-closes under verification: an exit != 0 here means either the crate
    // stopped being valid Rust or the unverified lane started verifying.
    println!("--- standalone targo --unverified check (compile-only lane)");
    let mut check = std::process::Command::new(&targo);
    scrub_gate_process_environment(&mut check);
    pin_targo_sibling_toolchain(&mut check, &targo)?;
    check
        .args(["--unverified", "check", "--offline"])
        .current_dir(&work_dir)
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("CARGO_NET_OFFLINE", "true");
    let check_run = capture(check)?;
    if !check_run.exited_with(0) {
        bail!(
            "basic-contracts targo check exited with status {} — the deliberately-refutable corpus must still type-check clean on the explicit `targo --unverified check` lane\nstdout:\n{}\nstderr:\n{}",
            check_run.exit,
            check_run.stdout,
            check_run.stderr
        );
    }
    println!("  PASS: basic-contracts type-checks clean on the unverified native lane");
    println!();

    // Default verification is fail-closed: this corpus DELIBERATELY carries
    // unprovable contracts (divide_exact's `ensures` is mathematically false
    // for inexact division), so `targo trust check` must refuse the build —
    // in the exact pinned way, under every gate policy. A 0 here would mean
    // the refutation lane silently broke.
    println!("--- targo trust check --format json (default verification must fail closed)");
    let mut trust_check = public_cli_command(&targo, &work_dir, &["check", "--format", "json"])?;
    trust_check.env("CARGO_TARGET_DIR", &target_dir).env("CARGO_NET_OFFLINE", "true");
    let trust_run = capture(trust_check)?;
    if contains(&trust_run.stdout, "TRUST_JSON:") || contains(&trust_run.stderr, "TRUST_JSON:") {
        bail!("targo trust check leaked raw TRUST_JSON transport");
    }
    if contains(&trust_run.stderr, "falling back to standalone source analysis") {
        bail!(
            "ERROR (setup): standalone Trust toolchain is visible, but targo trust fell back to source inventory\nstderr:\n{}",
            trust_run.stderr
        );
    }
    if !contains(&trust_run.stderr, "using native compiler") {
        bail!(
            "ERROR (setup): standalone Trust toolchain is visible, but targo trust did not report native compiler verification\nstderr:\n{}",
            trust_run.stderr
        );
    }
    assert_contracts_check_report(&trust_run).with_context(|| {
        format!(
            "targo trust JSON report did not match the pinned fail-closed proof-corpus shape\nstdout:\n{}\nstderr:\n{}",
            trust_run.stdout, trust_run.stderr
        )
    })?;
    // The human-readable refusal must name the permanent refutation and tie
    // the nonzero exit to the verification refusal, not some other build
    // error. The exact diagnostic phrasing is the compiler's to evolve, so
    // only the attribution to divide_exact is pinned.
    if !contains(&trust_run.stderr, "divide_exact") {
        bail!(
            "targo trust check stderr did not attribute the refusal to divide_exact\nstderr:\n{}",
            trust_run.stderr
        );
    }
    if !contains(&trust_run.stderr, "could not compile `basic-contracts`") {
        bail!(
            "targo trust check stderr did not tie the failure to the verification build refusal\nstderr:\n{}",
            trust_run.stderr
        );
    }
    println!(
        "  PASS: default verification fail-closes on exactly the pinned deliberately-unproved set"
    );
    println!("  PASS: targo trust JSON report includes expected basic contract functions");
    println!();

    // The standalone inventory is itself fail-closed: the corpus deliberately
    // leaves running_total/midpoint_checked unspecified, so this exact
    // one-file inventory reports two unknown rows and exits 1.
    println!("--- targo trust check --standalone --format json");
    let mut standalone =
        public_cli_command(&targo, &work_dir, &["check", "--standalone", "--format", "json"])?;
    standalone.env("CARGO_TARGET_DIR", &target_dir).env("CARGO_NET_OFFLINE", "true");
    let standalone_run = capture(standalone)?;
    assert_contracts_standalone_report(&standalone_run).with_context(|| {
        format!(
            "targo trust standalone JSON did not preserve the authored contract clauses\nstdout:\n{}\nstderr:\n{}",
            standalone_run.stdout, standalone_run.stderr
        )
    })?;
    println!(
        "  PASS: standalone compatibility inventory preserves authored clauses and stays fail-closed on unspecified public APIs"
    );
    println!();
    println!("=== basic contracts proof corpus smoke: PASS ===");
    Ok(())
}

/// Materialize a hermetic copy of the basic-contracts corpus under `scratch`:
/// sources are copied verbatim — the manifest carries the `[trust]` policy
/// table with them — and the committed `Cargo.lock`
/// is deliberately NOT copied — the corpus is self-contained (first-class
/// signature clauses, no path dependencies), so offline resolution in the copy
/// is deterministic and never mutates the working tree. A relative `path = `
/// dependency, if the corpus ever regrows one, is a setup error: it would
/// dangle from the scratch copy.
fn materialize_contracts_corpus(crate_dir: &Path, scratch: &Path) -> Result<std::path::PathBuf> {
    let manifest = std::fs::read_to_string(crate_dir.join("Cargo.toml")).with_context(|| {
        format!("failed to read example crate manifest {}", crate_dir.join("Cargo.toml").display())
    })?;
    if manifest.contains("path = \"") {
        bail!(
            "ERROR (setup): example crate manifest declares a relative path dependency, which would dangle from the hermetic scratch copy; update this gate alongside the corpus"
        );
    }

    let work_dir = scratch.join("basic-contracts");
    copy_corpus_tree(&crate_dir.join("src"), &work_dir.join("src"))?;
    std::fs::write(work_dir.join("Cargo.toml"), manifest)
        .context("failed to write hermetic corpus manifest")?;
    // The deprecated stand-alone file, for as long as a corpus crate may still
    // carry one. A crate on the canonical surface needs nothing here: its
    // policy travelled with the manifest above.
    let trust_toml = crate_dir.join("trust.toml");
    if std::fs::symlink_metadata(&trust_toml).is_ok_and(|meta| meta.file_type().is_file()) {
        std::fs::copy(&trust_toml, work_dir.join("trust.toml"))
            .context("failed to copy corpus trust.toml")?;
    }
    Ok(work_dir)
}

/// Exact recursive copy for the corpus sources; anything that is not a plain
/// file or directory (symlinks included) is a setup error, matching the
/// gate-wide exact-file hygiene.
fn copy_corpus_tree(from: &Path, to: &Path) -> Result<()> {
    std::fs::create_dir_all(to)
        .with_context(|| format!("failed to create corpus directory {}", to.display()))?;
    let entries = std::fs::read_dir(from)
        .with_context(|| format!("failed to read corpus directory {}", from.display()))?;
    for entry in entries {
        let entry = entry
            .with_context(|| format!("failed to read corpus entry under {}", from.display()))?;
        let file_type = entry.file_type().with_context(|| {
            format!("failed to inspect corpus entry {}", entry.path().display())
        })?;
        let dest = to.join(entry.file_name());
        if file_type.is_dir() {
            copy_corpus_tree(&entry.path(), &dest)?;
        } else if file_type.is_file() {
            std::fs::copy(entry.path(), &dest).with_context(|| {
                format!("failed to copy corpus file {}", entry.path().display())
            })?;
        } else {
            bail!(
                "ERROR (setup): corpus entry is not an exact file or directory: {}",
                entry.path().display()
            );
        }
    }
    Ok(())
}

/// Functions that MUST stay fail-closed under default verification.
/// `divide_exact` additionally requires a hard refutation: its `ensures`
/// (`result * denominator == numerator`) is mathematically false for inexact
/// division, so no verifier improvement can ever legitimately prove it.
const PINNED_FAIL_CLOSED_FUNCTIONS: &[&str] = &["divide_exact", "get_at"];

/// Functions allowed (not required) to carry unproved obligations today:
/// `abs_total`'s domain contract and `running_total`'s loop are verifier
/// coverage gaps, not deliberate refutations, and may flip to proved as the
/// verifier improves. `midpoint_checked`'s `low + (high - low) / 2` no-overflow
/// needs RELATIONAL kernel reasoning (`q ≤ (high-low)/2` with the same `low`,
/// i.e. `low + q ≤ high`) that the summand-bound certificates do not yet
/// cover — the same frontier class. `<crate:basic_contracts>` is the synthetic
/// crate-summary accounting row, not a function; its transport bookkeeping row
/// is unknown by construction. Any unproved obligation OUTSIDE this union with
/// the pinned set is a regression the gate must catch.
const TOLERATED_UNPROVED_FUNCTIONS: &[&str] =
    &["abs_total", "running_total", "midpoint_checked", "<crate:basic_contracts>"];

/// Pin the fail-closed reality of the deliberately-refutable corpus, under
/// every gate policy:
/// - the report must be a complete, internally-consistent typed proof report
///   (evidence, not an advisory summary);
/// - the process must fail closed (exit 1, or cargo's could-not-compile 101);
///   exit 0 means the refutation lane silently broke, exit 2 is a setup error;
/// - `divide_exact` carries at least one hard `failed` obligation and `get_at`
///   stays fail-closed (any unproved outcome);
/// - no function outside the pinned + tolerated set carries an unproved
///   obligation ("nothing unexpected").
fn assert_contracts_check_report(run: &Captured) -> Result<()> {
    let raw = json_object(run, "targo trust check json")?;
    // Capture the producer's declared derived state before the saved-report
    // boundary sanitizes it. `JsonProofReport`'s ordinary Deserialize impl is
    // deliberately fail-closed and recomputes summaries; deserializing first
    // and sanitizing a second time would erase both a forged-summary mismatch
    // and the receipt that the input attempted to assert `Proved`.
    let reported_derived_state = raw_report_derived_state(&raw)?;
    let encoded = serde_json::to_vec(&raw)
        .context("failed to encode native contract output for typed validation")?;
    let (report, sanitization, claims) = JsonProofReport::decode_saved_json(&encoded, None)
        .context("native contract output is not a typed Trust JSON proof report")?;
    validate_contract_cargo_identity(&report)?;
    if report.functions.is_empty() {
        bail!("expected at least one reported function");
    }

    // A proof report is evidence, not an advisory summary. Require a complete,
    // unique row inventory before re-gating it: summary-only obligations and
    // duplicate function identities cannot establish authored clauses.
    let mut qualified_names = BTreeSet::new();
    let mut obligation_ids = BTreeSet::new();
    for function in &report.functions {
        if function.function.trim().is_empty() || !qualified_names.insert(&function.function) {
            bail!("native contract report has an empty or duplicate function identity");
        }
        if canonical_contract_corpus_function(&function.function, &report.crate_name).is_none() {
            bail!(
                "native contract report contains a function outside the exact {CONTRACT_CORPUS_CRATE} corpus: {}",
                function.function
            );
        }
        for obligation in &function.obligations {
            if obligation.description.trim().is_empty()
                || obligation.kind.trim().is_empty()
                || obligation.solver.trim().is_empty()
            {
                bail!("native contract report contains an incomplete obligation row");
            }
            let Some(id) = obligation.obligation_id.as_deref() else {
                bail!("native contract report contains an obligation without a stable identity");
            };
            if id.trim().is_empty() {
                bail!("native contract report contains an empty obligation identity");
            }
            if !obligation_ids.insert(id) {
                bail!("native contract report contains a duplicate obligation identity");
            }
            let Some(transport) = obligation.transport_evidence.as_ref() else {
                bail!(
                    "native contract report contains an obligation without typed transport evidence"
                );
            };
            if transport.obligation_id.as_deref() != Some(id) {
                bail!(
                    "native contract report contains an obligation whose transport identity does not match its row identity"
                );
            }
        }
    }

    for expected in CONTRACT_CORPUS_FUNCTIONS {
        let qualified = format!("{}::{CONTRACT_CORPUS_CRATE}::{expected}", report.crate_name);
        let count =
            report.functions.iter().filter(|function| function.function == qualified).count();
        if count != 1 {
            bail!(
                "native contract report must contain exactly one {expected} function row, found {count}"
            );
        }
    }
    if report.summary.total_obligations < 1 {
        bail!("expected at least one verification obligation");
    }

    let raw_report = reconstruct_and_validate_untrusted_raw_report(
        &raw,
        &reported_derived_state,
        &report,
        sanitization,
        &claims,
    )?;
    validate_contract_verification_gate(&raw, &raw_report, run.exit)?;

    for expected in AUTHORED_ENSURES_FUNCTIONS {
        let qualified = format!("{}::{CONTRACT_CORPUS_CRATE}::{expected}", report.crate_name);
        let matches = report
            .functions
            .iter()
            .filter(|function| function.function == qualified)
            .collect::<Vec<_>>();
        // A parseable `ensures` must retain the exact typed Postcondition DTO.
        // Only get_at's currently unsupported CALL/INDEX-bearing clause may use
        // the fail-closed sentinel, and that sentinel must itself be the exact
        // typed UnsupportedMir payload. A description substring or obligation
        // id is diagnostic text, never clause-classification authority.
        let has_ensures_evidence = matches.len() == 1
            && matches[0].obligations.iter().any(|obligation| {
                exact_contract_clause_location(obligation.location.as_ref(), expected)
                    && (exact_authored_postcondition(obligation)
                        || (expected == "get_at"
                            && exact_fail_closed_unparseable_ensures(obligation)))
            });
        if !has_ensures_evidence {
            bail!(
                "native contract report must contain exactly one {expected} row with exact typed authored-ensures evidence"
            );
        }
    }

    // Collect the producer's fail-closed reality from the exact pre-sanitize
    // outcome snapshot. Classifying the sanitized DTO would turn every raw
    // `Proved` into `Unknown`, letting a favorable claim satisfy a pinned
    // fail-closed requirement. RuntimeChecked is likewise favorable execution
    // credit, and this static proof corpus does not accept it as a discharge.
    let mut hard_failures: Vec<(String, String)> = Vec::new();
    let mut fail_closed_functions: BTreeSet<String> = BTreeSet::new();
    for function in &raw_report.functions {
        let short = canonical_contract_corpus_function(&function.function, &raw_report.crate_name)
            .expect("function identities were validated before raw outcome restoration")
            .to_string();
        for obligation in &function.obligations {
            match &obligation.outcome {
                ObligationOutcome::Failed { .. } => {
                    hard_failures.push((short.clone(), obligation.description.clone()));
                    fail_closed_functions.insert(short.clone());
                }
                ObligationOutcome::Unknown { .. }
                | ObligationOutcome::Timeout { .. }
                | ObligationOutcome::DesignRequirement { .. } => {
                    fail_closed_functions.insert(short.clone());
                }
                ObligationOutcome::RuntimeChecked { .. } => bail!(
                    "native contract proof corpus contains a runtime-checked row for {short}; default verification requires a static proof or a fail-closed outcome"
                ),
                ObligationOutcome::Proved { .. } => {}
                _ => bail!("native contract report contains an unsupported outcome variant"),
            }
        }
    }
    if run.terminated_by_signal {
        bail!("native contract report process terminated by signal");
    }
    match run.exit {
        1 | 101 => {}
        0 => bail!(
            "targo trust check accepted the deliberately-refutable corpus (exit 0) — the fail-closed refutation lane is broken or the corpus stopped being refutable"
        ),
        2 => bail!("targo trust check reported a compiler setup/evidence failure (exit 2)"),
        other => bail!("unexpected trust exit status {other}"),
    }
    let missing_pins: Vec<&str> = PINNED_FAIL_CLOSED_FUNCTIONS
        .iter()
        .copied()
        .filter(|name| !fail_closed_functions.contains(*name))
        .collect();
    let divide_exact_refuted = hard_failures.iter().any(|(name, _)| name == "divide_exact");
    if !missing_pins.is_empty() || !divide_exact_refuted {
        bail!(
            "native contract fail-closed set changed: missing_fail_closed={missing_pins:?}, divide_exact_hard_failure={divide_exact_refuted}, hard_failures={hard_failures:?}"
        );
    }
    let unexpected: Vec<&String> = fail_closed_functions
        .iter()
        .filter(|name| {
            !PINNED_FAIL_CLOSED_FUNCTIONS.contains(&name.as_str())
                && !TOLERATED_UNPROVED_FUNCTIONS.contains(&name.as_str())
        })
        .collect();
    if !unexpected.is_empty() {
        bail!(
            "functions outside the deliberate corpus set carry unproved obligations: {unexpected:?}"
        );
    }
    Ok(())
}

fn validate_contract_verification_gate(
    raw: &Value,
    raw_report: &JsonProofReport,
    captured_exit: i32,
) -> Result<()> {
    let gate: trust_types::VerificationGateReport = serde_json::from_value(
        raw.get("verification_gate")
            .cloned()
            .context("native contract report is missing its strict verification gate")?,
    )
    .context("native contract report has a malformed verification gate")?;
    if gate.lane != "strict" || gate.verification_level.as_deref() != Some("L2") {
        bail!(
            "native contract report has the wrong gate policy: lane={}, level={:?}",
            gate.lane,
            gate.verification_level
        );
    }
    if gate.decision != "fail" {
        bail!(
            "native contract report gate must record the pinned refutation as fail, got {}",
            gate.decision
        );
    }
    let captured_exit = u8::try_from(captured_exit)
        .context("native contract process exit does not fit the report gate schema")?;
    if gate.exit_code != captured_exit {
        bail!(
            "native contract report gate exit {} does not match process exit {captured_exit}",
            gate.exit_code
        );
    }
    if gate.test_execution.is_some() {
        bail!("native contract check report unexpectedly carries test-execution evidence");
    }

    let counts = &gate.counts;
    let partition_total = [
        counts.proved,
        counts.failed,
        counts.unknown,
        counts.runtime_checked,
        counts.assumed,
        counts.mandated,
        counts.contract_panics,
    ]
    .into_iter()
    .try_fold(0usize, usize::checked_add)
    .context("native contract report gate count overflow")?;
    if partition_total != counts.total {
        bail!("native contract report gate counts do not form an exact disjoint total");
    }
    // `assumed` is NOT rejected here. The ratified summary-partition semantics
    // (f9fe3fa12b0) split the inconclusive rows into genuine `unknown`,
    // `mandated`, and `assumed` (compiler `assumption:*` rows — the
    // requires-entry assumptions the corpus's requires-bearing functions,
    // divide_exact and get_at, produce by definition). A proof-CLAIMING
    // assumption row is already fail-closed to `unknown` upstream at partition
    // time (`partition_outcome_counts` in pipeline/hardened.rs), so a non-zero
    // `assumed` here is exactly the sound entry-assumption partition, never a
    // laundered proof. `runtime_checked`/`mandated`/`contract_panics` must still
    // be empty in this proof corpus.
    if counts.runtime_checked != 0 || counts.mandated != 0 || counts.contract_panics != 0 {
        bail!(
            "native contract proof corpus gate contains a runtime-checked, mandated, or contract-panic outcome bucket"
        );
    }
    // The raw summary carries no separate `total_assumed`: it lumps assumption
    // rows into `total_unknown`. The gate PARTITIONS them out, so the exact
    // reconstruction is `gate.unknown + gate.assumed == summary.total_unknown`.
    if counts.total != raw_report.summary.total_obligations
        || counts.proved != raw_report.summary.total_proved
        || counts.failed != raw_report.summary.total_failed
        || counts.unknown + counts.assumed != raw_report.summary.total_unknown
        || raw_report.summary.total_runtime_checked != 0
        || raw_report.summary.total_design_requirements != 0
    {
        bail!("native contract report gate counts do not match the reconstructed raw summary");
    }
    // The assumption-conditional flag is the CANONICAL invariant
    // (`conditional_on_assumption_rows == assumed > 0`; see pipeline/run.rs and
    // the diff-lane check in diff.rs), so it is legitimately true whenever the
    // entry-assumption partition is non-empty. Only the runtime-checked
    // conditional (forbidden above) remains a hard contradiction.
    if gate.conditional_on_assumption_rows != (counts.assumed > 0) {
        bail!("native contract report gate assumption-conditional flag is inconsistent with its assumed count");
    }
    if gate.conditional_on_runtime_checks {
        bail!("native contract report gate carries a contradictory runtime-checked conditional flag");
    }
    let has_dependency_assumption =
        raw_report.assumptions.iter().any(|entry| entry.source == "dep-tcb-cargo-unit-inventory");
    if gate.conditional_on_dependency_entries != has_dependency_assumption {
        bail!("native contract report gate dependency conditional flag is inconsistent");
    }
    if gate.conditional_on_visitation_entries {
        bail!("native contract report gate unexpectedly claims rowless visitation dependence");
    }
    let expected_coverage = trust_types::VerificationCoverage::from_counts(
        CONTRACT_CORPUS_FUNCTIONS.len(),
        CONTRACT_CORPUS_FUNCTIONS.len(),
    );
    if gate.coverage != Some(expected_coverage) {
        bail!(
            "native contract report gate does not authenticate exact coverage of the five-function corpus"
        );
    }
    Ok(())
}

fn assert_contracts_standalone_report(run: &Captured) -> Result<()> {
    if run.terminated_by_signal {
        bail!("standalone inventory process terminated by signal");
    }
    let report = json_object(run, "targo trust standalone json")?;
    // This is a pinned one-file corpus, not a general source-audit reader. Its
    // two deliberately-unspecified public functions produce the exact seven-row
    // partition (two `unknown` UnspecifiedPublicApi observation rows).
    // 06c732cdd9a ratified that the source audit passes on inventory
    // observations — `standalone_audit_passed` now gates only on `failed == 0`,
    // not `unknown == 0` (unknown rows are honest observations, not defects), so
    // this corpus audits exit 0 / audit_passed=true. `Failed` rows would still
    // fail closed; there are none here.
    if run.exit != 0 {
        bail!("standalone inventory must complete with exit 0, got {}", run.exit);
    }
    if field_str(&report, "schema_version") != "trust.source-audit.v1"
        || field_str(&report, "mode") != "source-audit"
        || field_str(&report, "proof_authority") != "none"
        || report.get("compiler_verification_performed").and_then(Value::as_bool) != Some(false)
        || report.get("audit_passed").and_then(Value::as_bool) != Some(true)
    {
        bail!("standalone report did not preserve its explicit non-proof authority boundary");
    }
    if report.get("duration_ms").and_then(Value::as_u64).is_none() {
        bail!("standalone report is missing its typed duration");
    }
    for (field, expected) in [
        ("files_analyzed", 1),
        ("functions_found", 5),
        ("public_functions", 5),
        ("unsafe_functions", 0),
        ("specified_functions", 3),
        ("total_audit_rows", 7),
        ("present", 5),
        ("failed", 0),
        ("unknown", 2),
    ] {
        if report.get(field).and_then(Value::as_u64) != Some(expected) {
            bail!("standalone report has the wrong exact {field} count");
        }
    }
    for forbidden in ["proved", "vcs", "summary", "verification_gate", "obligations"] {
        if report.get(forbidden).is_some() {
            bail!("standalone source audit exposed proof-shaped field {forbidden}");
        }
    }
    let Some(functions) = report.get("functions").and_then(Value::as_array) else {
        bail!("standalone report should include functions");
    };
    if functions.len() != CONTRACT_CORPUS_FUNCTIONS.len() {
        bail!("standalone report must contain exactly the five corpus functions");
    }
    let mut standalone_names = BTreeSet::new();
    for entry in functions {
        let name = entry.get("name").and_then(Value::as_str).unwrap_or_default();
        if name.is_empty() || !standalone_names.insert(name) {
            bail!("standalone report contains an empty or duplicate function identity");
        }
    }
    let by_name = |name: &str| -> Option<&Value> {
        functions.iter().find(|entry| entry.is_object() && field_str(entry, "name") == name)
    };
    for name in CONTRACT_CORPUS_FUNCTIONS {
        if by_name(name).is_none() {
            bail!("standalone report missing expected function {name}");
        }
    }
    let flag = |entry: &Value, field: &str| entry.get(field).and_then(Value::as_bool) == Some(true);
    let divide = by_name("divide_exact").expect("checked");
    if !flag(divide, "has_requires") || !flag(divide, "has_ensures") {
        bail!("standalone report should preserve divide_exact trust-spec attrs");
    }
    let get_at = by_name("get_at").expect("checked");
    if !flag(get_at, "has_requires") || !flag(get_at, "has_ensures") {
        bail!("standalone report should preserve get_at trust-spec attrs");
    }
    let abs_total = by_name("abs_total").expect("checked");
    if flag(abs_total, "has_requires") || !flag(abs_total, "has_ensures") {
        bail!("standalone report should preserve abs_total ensures-only contract");
    }
    for name in ["running_total", "midpoint_checked"] {
        let entry = by_name(name).expect("checked");
        if flag(entry, "has_requires") || flag(entry, "has_ensures") {
            bail!("standalone report should preserve {name} as an unspecified public function");
        }
    }
    for entry in functions {
        let file = entry.get("file").and_then(Value::as_str).unwrap_or_default();
        if entry.get("is_public").and_then(Value::as_bool) != Some(true)
            || entry.get("is_unsafe").and_then(Value::as_bool) != Some(false)
            || !Path::new(file).ends_with(Path::new("src/lib.rs"))
        {
            bail!("standalone function inventory is not the exact safe public corpus");
        }
    }

    let Some(rows) = report.get("audit_rows").and_then(Value::as_array) else {
        bail!("standalone report is missing its typed audit-row inventory");
    };
    if rows.len() != 7 {
        bail!("standalone report must contain exactly seven audit rows");
    }
    let expected_rows: BTreeSet<(String, String, String, String)> = [
        (
            "divide_exact",
            "PreconditionPresent",
            "Present",
            "divide_exact: requires specification present",
        ),
        (
            "divide_exact",
            "PostconditionPresent",
            "Present",
            "divide_exact: ensures specification present",
        ),
        (
            "abs_total",
            "PostconditionPresent",
            "Present",
            "abs_total: ensures specification present",
        ),
        ("get_at", "PreconditionPresent", "Present", "get_at: requires specification present"),
        ("get_at", "PostconditionPresent", "Present", "get_at: ensures specification present"),
        (
            "running_total",
            "UnspecifiedPublicApi",
            "Unknown",
            "running_total: public function has no specification",
        ),
        (
            "midpoint_checked",
            "UnspecifiedPublicApi",
            "Unknown",
            "midpoint_checked: public function has no specification",
        ),
    ]
    .into_iter()
    .map(|(function, kind, outcome, description)| {
        (function.into(), kind.into(), outcome.into(), description.into())
    })
    .collect();
    let mut actual_rows = BTreeSet::new();
    for row in rows {
        let file = row.get("file").and_then(Value::as_str).unwrap_or_default();
        let identity = (
            field_str(row, "function").to_owned(),
            field_str(row, "kind").to_owned(),
            field_str(row, "outcome").to_owned(),
            field_str(row, "description").to_owned(),
        );
        if !Path::new(file).ends_with(Path::new("src/lib.rs")) || !actual_rows.insert(identity) {
            bail!("standalone report contains a malformed or duplicate audit row");
        }
    }
    if actual_rows != expected_rows {
        bail!("standalone report audit rows do not match the exact corpus inventory");
    }
    Ok(())
}

/// Reconstruct the producer's untrusted typed outcome claims solely for
/// consistency checking and fail-closed classification. This does not restore verifier authority:
/// the returned report remains local to this gate, and every raw `Proved` row
/// must first pass the exact publication-grade structural validator.
fn reconstruct_and_validate_untrusted_raw_report(
    raw: &Value,
    reported_derived_state: &Value,
    sanitized: &JsonProofReport,
    sanitization: SavedReportSanitization,
    claims: &UntrustedSavedReportClaims,
) -> Result<JsonProofReport> {
    let raw_functions = raw
        .get("functions")
        .and_then(Value::as_array)
        .context("native contract report is missing its raw function inventory")?;
    if raw_functions.len() != sanitized.functions.len() {
        bail!("native contract report function cardinality changed during typed decoding");
    }

    let mut restored = sanitized.clone();
    let mut seen_positions = BTreeSet::new();
    let mut raw_proved = 0usize;
    let mut raw_runtime_checked = 0usize;
    for claim in claims.obligations() {
        let function_index = claim.function_index();
        let obligation_index = claim.obligation_index();
        if !seen_positions.insert((function_index, obligation_index)) {
            bail!("native contract report contains duplicate raw outcome coordinates");
        }
        let function = restored
            .functions
            .get_mut(function_index)
            .context("native contract report raw outcome names a missing function")?;
        if function.function != claim.function() {
            bail!("native contract report raw outcome function identity changed during decoding");
        }
        let obligation = function
            .obligations
            .get_mut(obligation_index)
            .context("native contract report raw outcome names a missing obligation")?;
        if obligation.obligation_id.as_deref() != claim.obligation_id() {
            bail!("native contract report obligation identity changed during decoding");
        }
        if !sanitized_outcome_matches_claim(&obligation.outcome, claim.outcome()) {
            bail!(
                "native contract report outcome did not follow the exact saved-report sanitize map"
            );
        }

        let raw_obligation = raw_functions
            .get(function_index)
            .and_then(|function| function.get("obligations"))
            .and_then(Value::as_array)
            .and_then(|obligations| obligations.get(obligation_index))
            .context("native contract report is missing a raw obligation row")?;
        let raw_outcome = raw_obligation
            .get("outcome")
            .context("native contract report is missing a raw obligation outcome")?;

        match claim.outcome() {
            UntrustedSavedOutcomeClaim::Proved => {
                raw_proved = raw_proved
                    .checked_add(1)
                    .context("native contract report proved-row count overflow")?;
                let strength: ProofStrength = serde_json::from_value(
                    raw_outcome
                        .get("strength")
                        .cloned()
                        .context("native contract proved row is missing its typed strength")?,
                )
                .context("native contract proved row has malformed typed strength")?;
                let proof = obligation
                    .proof_evidence
                    .as_ref()
                    .context("native contract proved row lacks typed proof evidence")?;
                if proof.strength != strength
                    || obligation.evidence.as_ref() != Some(&proof.evidence)
                {
                    bail!(
                        "native contract proved row outcome/evidence strength is internally inconsistent"
                    );
                }
                if let Some(defect) =
                    trust_types::saved_obligation_structural_proof_defect(obligation, None)
                {
                    bail!("native contract proved row has malformed structural evidence: {defect}");
                }
                obligation.outcome = ObligationOutcome::Proved { strength };
            }
            UntrustedSavedOutcomeClaim::RuntimeChecked => {
                raw_runtime_checked = raw_runtime_checked
                    .checked_add(1)
                    .context("native contract report runtime-row count overflow")?;
                let note = raw_outcome
                    .get("note")
                    .cloned()
                    .map(serde_json::from_value)
                    .transpose()
                    .context("native contract runtime-checked row has malformed note")?
                    .flatten();
                if obligation.proof_evidence.is_some() {
                    bail!("native contract runtime-checked row carries static proof evidence");
                }
                obligation.outcome = ObligationOutcome::RuntimeChecked { note };
            }
            UntrustedSavedOutcomeClaim::Failed
            | UntrustedSavedOutcomeClaim::Unknown
            | UntrustedSavedOutcomeClaim::Timeout
            | UntrustedSavedOutcomeClaim::DesignRequirement => {
                if obligation.proof_evidence.is_some() {
                    bail!("native contract non-proved row carries static proof evidence");
                }
            }
        }
    }

    let expected_rows = restored.functions.iter().try_fold(0usize, |total, function| {
        total
            .checked_add(function.obligations.len())
            .context("native contract report obligation cardinality overflow")
    })?;
    if seen_positions.len() != expected_rows {
        bail!("native contract report raw outcome inventory is incomplete");
    }
    if sanitization.downgraded_proved != raw_proved
        || sanitization.evidence_defects != raw_proved
        || sanitization.downgraded_runtime_checked != raw_runtime_checked
    {
        bail!("native contract report did not apply the exact favorable-outcome sanitize map");
    }
    if sanitization.structural_evidence_defects != 0 {
        bail!(
            "native contract report contains {} structurally malformed proved row(s)",
            sanitization.structural_evidence_defects
        );
    }
    if sanitization.downgraded_runtime_checked != 0 {
        bail!(
            "native contract proof corpus contains {} runtime-checked row(s); default verification requires static proof or a fail-closed outcome",
            sanitization.downgraded_runtime_checked
        );
    }

    // Rebuild every derived field from the raw rows. In addition to counts and
    // verdicts, this checks max proof level, proof-engine tallies, and checked
    // time arithmetic; none of those fields may be excluded as "verdict-like".
    for (index, function) in restored.functions.iter_mut().enumerate() {
        let raw_function = &raw_functions[index];
        if raw_function.get("function").and_then(Value::as_str) != Some(function.function.as_str())
        {
            bail!("native contract report raw function identity is malformed");
        }
        let reported: trust_types::FunctionSummary = serde_json::from_value(
            raw_function
                .get("summary")
                .cloned()
                .context("native contract report function is missing its raw summary")?,
        )
        .context("native contract report function has a malformed raw summary")?;
        if reported.total_obligations != function.obligations.len() {
            bail!(
                "native contract report has summary-only obligations for {}: summary={}, rows={}",
                function.function,
                reported.total_obligations,
                function.obligations.len()
            );
        }
        if reported.unattributed_failed != 0
            || reported.unattributed_unknown != 0
            || reported.unattributed_proved != 0
        {
            bail!("native contract report contains unattributed function summary outcomes");
        }
        let total_time_ms = function.obligations.iter().try_fold(0u64, |total, obligation| {
            total
                .checked_add(obligation.time_ms)
                .context("native contract report function time overflow")
        })?;
        let max_proof_level = function.obligations.iter().map(|row| row.proof_level).max();
        function.summary.unattributed_failed = 0;
        function.summary.unattributed_unknown = 0;
        function.summary.unattributed_proved = 0;
        function.summary.total_time_ms = total_time_ms;
        function.summary.max_proof_level = max_proof_level;
    }
    let reported_crate: trust_types::CrateSummary = serde_json::from_value(
        raw.get("summary")
            .cloned()
            .context("native contract report is missing its raw crate summary")?,
    )
    .context("native contract report has a malformed raw crate summary")?;
    if reported_crate.total_unattributed_failed != 0
        || reported_crate.total_unattributed_unknown != 0
        || reported_crate.total_unattributed_proved != 0
    {
        bail!("native contract report contains unattributed crate summary outcomes");
    }
    restored.summary.total_unattributed_failed = 0;
    restored.summary.total_unattributed_unknown = 0;
    restored.summary.total_unattributed_proved = 0;
    restored.recompute_summaries_from_obligation_outcomes();
    if *reported_derived_state != derived_report_state(&restored)? {
        bail!("native contract report raw summaries or verdicts do not match obligation rows");
    }

    let mut expected_sanitized = restored.clone();
    for claim in claims.obligations() {
        if matches!(
            claim.outcome(),
            UntrustedSavedOutcomeClaim::Proved | UntrustedSavedOutcomeClaim::RuntimeChecked
        ) {
            expected_sanitized.functions[claim.function_index()].obligations
                [claim.obligation_index()]
            .outcome = ObligationOutcome::Unknown { reason: "saved authority removed".into() };
        }
    }
    expected_sanitized.recompute_summaries_from_obligation_outcomes();
    if derived_report_state(sanitized)? != derived_report_state(&expected_sanitized)? {
        bail!("native contract report sanitized summaries do not match the exact sanitize map");
    }
    Ok(restored)
}

fn sanitized_outcome_matches_claim(
    outcome: &ObligationOutcome,
    claim: UntrustedSavedOutcomeClaim,
) -> bool {
    match claim {
        UntrustedSavedOutcomeClaim::Proved | UntrustedSavedOutcomeClaim::RuntimeChecked => {
            matches!(outcome, ObligationOutcome::Unknown { .. })
        }
        UntrustedSavedOutcomeClaim::Failed => {
            matches!(outcome, ObligationOutcome::Failed { .. })
        }
        UntrustedSavedOutcomeClaim::Unknown => {
            matches!(outcome, ObligationOutcome::Unknown { .. })
        }
        UntrustedSavedOutcomeClaim::Timeout => {
            matches!(outcome, ObligationOutcome::Timeout { .. })
        }
        UntrustedSavedOutcomeClaim::DesignRequirement => {
            matches!(outcome, ObligationOutcome::DesignRequirement { .. })
        }
    }
}

fn derived_report_state(report: &JsonProofReport) -> Result<Value> {
    serde_json::to_value((
        &report.summary,
        report
            .functions
            .iter()
            .map(|function| (&function.function, &function.summary))
            .collect::<Vec<_>>(),
    ))
    .context("failed to serialize typed report derived state")
}

fn raw_report_derived_state(report: &Value) -> Result<Value> {
    let summary = report
        .get("summary")
        .cloned()
        .context("native contract report is missing its crate summary")?;
    let functions = report
        .get("functions")
        .and_then(Value::as_array)
        .context("native contract report is missing its function inventory")?;
    let mut function_state = Vec::with_capacity(functions.len());
    for function in functions {
        let name = function
            .get("function")
            .and_then(Value::as_str)
            .context("native contract report contains a function without a typed identity")?;
        let summary = function
            .get("summary")
            .cloned()
            .context("native contract report contains a function without a typed summary")?;
        function_state.push(Value::Array(vec![Value::String(name.to_string()), summary]));
    }
    Ok(Value::Array(vec![summary, Value::Array(function_state)]))
}

#[cfg(test)]
mod tests {
    mod publication_transport {
        include!(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/support/publication_transport.rs"));
    }

    use trust_types::{
        CargoProofInventoryReport, CargoProofUnitPartitions, CargoProofUnitReport,
        CargoUnitCompilerSemanticsReport, CargoUnitProfileSemanticsReport,
        CargoUnitSemanticsReport, CrateSummary, CrateVerdict, FunctionProofReport, FunctionSummary,
        FunctionVerdict, ObligationEvidenceProvenanceReport, ObligationProofEvidenceReport,
        ObligationReport, ObligationTransportEvidenceReport, ProofLevel, ReportMetadata,
        SourceSpan, TransportProofStatus, VerificationCoverage, VerificationGateCounts,
        VerificationGateReport,
    };

    use super::*;

    #[test]
    fn release_policy_refuses_unattested_repository_bootstrap() {
        assert!(
            require_bootstrap_execution_policy(GatePolicy { strict: true, release: true })
                .expect_err("release execution must fail closed")
                .to_string()
                .contains("no independently authenticated source/build provenance")
        );
        require_bootstrap_execution_policy(GatePolicy { strict: true, release: false })
            .expect("non-release diagnostic retains endpoint checking");
    }

    fn fixture_cargo_unit() -> CargoProofUnitReport {
        let semantics = CargoUnitSemanticsReport {
            schema: "targo.trust-unit-semantics.v1".into(),
            features: Vec::new(),
            target_cfg: vec!["target_arch = \"aarch64\"".into(), "unix".into()],
            cfg_test: false,
            target_edition: "2024".into(),
            target_crate_types: vec!["lib".into()],
            target_harness: true,
            target_proc_macro: false,
            profile: CargoUnitProfileSemanticsReport {
                opt_level: "0".into(),
                requested_lto: "false".into(),
                effective_lto: "only-object".into(),
                codegen_backend: None,
                codegen_units: None,
                debuginfo: "0".into(),
                split_debuginfo: None,
                debug_assertions: true,
                overflow_checks: true,
                rpath: false,
                incremental: false,
                panic: "unwind".into(),
                strip: "none".into(),
                rustflags: Vec::new(),
                trim_paths: None,
                hint_mostly_unused: None,
            },
            compiler: CargoUnitCompilerSemanticsReport {
                frontend: "rustc".into(),
                codegen_backend: "llvm".into(),
                rustc_release: "1.99.0-nightly".into(),
                rustc_commit_hash: Some("a".repeat(40)),
                rustc_host: "aarch64-apple-darwin".into(),
                rustc_verbose_version_sha256: "b".repeat(64),
            },
            unit_rustflags: Vec::new(),
            manifest_lint_rustflags: Vec::new(),
            extra_compiler_args: Vec::new(),
        };
        let digest = crate::pipeline::transport::cargo_unit_semantics_sha256(&semantics)
            .expect("hash fixture Cargo semantics");
        CargoProofUnitReport {
            package_id: "path+file:///tmp/basic-contracts#0.1.0".into(),
            package_name: "basic-contracts".into(),
            target_name: CONTRACT_CORPUS_CRATE.into(),
            target_kinds: vec!["lib".into()],
            compile_target: "aarch64-apple-darwin".into(),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            // `targo trust check` verifies in build mode (optimized MIR), so the
            // pinned proof unit reports `proof_unit_mode = "build"`.
            proof_unit_mode: "build".into(),
            proof_unit_role: "primary".into(),
            graph_role: "primary".into(),
            exclusion_reason: None,
            semantics_sha256: Some(digest),
            semantics: Some(semantics),
        }
    }

    fn fixture_report_subject(unit: &CargoProofUnitReport) -> String {
        format!(
            "cargo-target(package_id={:?},package={:?},kind={:?},target={:?},compile_target={:?},compile_mode={:?},compile_kind={:?},unit_identity_sha256={:?},compile_target_spec_sha256={:?},proof_unit_index={},proof_unit_mode={:?},proof_unit_role={:?},semantics_sha256={:?})",
            unit.package_id,
            unit.package_name,
            unit.target_kinds,
            unit.target_name,
            unit.compile_target,
            unit.proof_unit_mode,
            "host",
            "c".repeat(64),
            unit.compile_target_spec_sha256,
            unit.proof_unit_index,
            unit.proof_unit_mode,
            unit.proof_unit_role,
            unit.semantics_sha256.as_deref().expect("semantic digest"),
        )
    }

    fn failed_function(name: &str, report_subject: &str) -> FunctionProofReport {
        let obligation_id = format!("basic-contracts::{name}::ensures:0");
        let clause_line = match name {
            "divide_exact" => 7,
            "abs_total" => 13,
            "get_at" => 26,
            _ => 31,
        };
        FunctionProofReport {
            function: format!("{report_subject}::basic_contracts::{name}"),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 0,
                runtime_checked: 0,
                failed: 1,
                unknown: 0,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 1,
                max_proof_level: Some(ProofLevel::L1Functional),
                verdict: FunctionVerdict::HasViolations,
            },
            obligations: vec![ObligationReport {
                obligation_id: Some(obligation_id.clone()),
                description: VcKind::Postcondition.description(),
                kind: "postcondition".into(),
                proof_level: ProofLevel::L1Functional,
                location: Some(SourceSpan {
                    file: "src/lib.rs".into(),
                    line_start: clause_line,
                    col_start: 1,
                    line_end: clause_line,
                    col_end: 2,
                }),
                outcome: ObligationOutcome::Failed { counterexample: None },
                solver: "ay".into(),
                time_ms: 1,
                evidence: None,
                proof_evidence: None,
                transport_evidence: Some(ObligationTransportEvidenceReport {
                    obligation_id: Some(obligation_id),
                    claim_digest_sha256: None,
                    typed_kind: Some(Box::new(VcKind::Postcondition)),
                    native_trust_ir: None,
                    proof_evidence: None,
                    monitor: None,
                }),
            }],
        }
    }

    fn failed_report() -> JsonProofReport {
        let unit = fixture_cargo_unit();
        let report_subject = fixture_report_subject(&unit);
        let frontier = CargoProofUnitPartitions {
            primary_roots: vec![unit],
            test_execution_units: Vec::new(),
            dependency_units: Vec::new(),
        };
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "trust.report.v1".into(),
                trust_version: "test".into(),
                timestamp: "2026-07-11T00:00:00Z".into(),
                total_time_ms: 5,
                timeout_ms: Some(5_000),
                function_budget_ms: Some(10_000),
            },
            crate_name: report_subject.clone(),
            summary: CrateSummary {
                functions_analyzed: 5,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 5,
                functions_inconclusive: 0,
                total_obligations: 5,
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 5,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: CrateVerdict::HasViolations,
            },
            functions: CONTRACT_CORPUS_FUNCTIONS
                .into_iter()
                .map(|name| failed_function(name, &report_subject))
                .collect(),
            hardened: None,
            assumptions: Vec::new(),
            cargo_proof_inventory: Some(CargoProofInventoryReport {
                schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2.into(),
                include_dependencies: false,
                declared: frontier.clone(),
                completed: frontier.clone(),
                covered: frontier,
                excluded_active_units: Vec::new(),
            }),
            verification_gate: None,
        }
    }

    fn captured_report(report: &JsonProofReport, exit: i32) -> Captured {
        let mut report = report.clone();
        let summary = &report.summary;
        report.verification_gate = Some(VerificationGateReport {
            lane: "strict".into(),
            verification_level: Some("L2".into()),
            decision: "fail".into(),
            exit_code: u8::try_from(exit).expect("fixture exit fits gate schema"),
            counts: VerificationGateCounts {
                total: summary.total_obligations,
                proved: summary.total_proved,
                failed: summary.total_failed,
                unknown: summary.total_unknown,
                runtime_checked: summary.total_runtime_checked,
                assumed: 0,
                mandated: summary.total_design_requirements,
                contract_panics: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: report
                .assumptions
                .iter()
                .any(|entry| entry.source == "dep-tcb-cargo-unit-inventory"),
            conditional_on_runtime_checks: summary.total_runtime_checked > 0,
            conditional_on_visitation_entries: false,
            coverage: Some(VerificationCoverage::from_counts(
                report.functions.len(),
                report.functions.len(),
            )),
            test_execution: None,
        });
        Captured {
            exit,
            terminated_by_signal: false,
            stdout: serde_json::to_string(&report).expect("serialize report fixture"),
            stderr: String::new(),
        }
    }

    fn set_exact_obligation_kind(report: &mut JsonProofReport, index: usize, kind: VcKind) {
        let obligation = &mut report.functions[index].obligations[0];
        obligation.kind = match &kind {
            VcKind::Postcondition => "postcondition".into(),
            VcKind::UnsupportedMir { .. } => "unsupported_mir".into(),
            _ => panic!("test helper only models authored-ensures carriers"),
        };
        obligation.description = kind.description();
        obligation.proof_level = kind.proof_level();
        let obligation_id = obligation.obligation_id.clone();
        let evidence = obligation.transport_evidence.get_or_insert_with(|| {
            ObligationTransportEvidenceReport {
                obligation_id,
                claim_digest_sha256: None,
                typed_kind: None,
                native_trust_ir: None,
                proof_evidence: None,
                monitor: None,
            }
        });
        evidence.typed_kind = Some(Box::new(kind));
        report.functions[index].summary.max_proof_level =
            report.functions[index].obligations.iter().map(|row| row.proof_level).max();
    }

    fn install_publishable_proof(
        report: &mut JsonProofReport,
        index: usize,
        request_id: &str,
        proof_id: &str,
    ) {
        let function = report.functions[index].function.clone();
        let semantic_function = function
            .strip_prefix(&report.crate_name)
            .and_then(|function| function.strip_prefix("::"))
            .expect("fixture function is scoped by the Cargo report subject");
        let transport = publication_transport::proved_result(
            VcKind::Postcondition,
            semantic_function,
            request_id,
            proof_id,
        );
        let proof = transport.proof_evidence.clone().expect("transport proof");
        let native = transport.native_trust_ir.clone().expect("native TrustIr evidence");
        let strength = proof.strength.clone().expect("proof strength");
        let evidence = proof.evidence.clone().expect("normalized proof evidence");
        let proof_report = ObligationProofEvidenceReport {
            suite: Some(proof.suite.clone()),
            backend: proof.backend.clone(),
            request_id: proof.request_id.clone(),
            proof_id: proof.proof_id.clone(),
            native_id: proof.native_id.clone(),
            status: Some(TransportProofStatus::Proved),
            provenance: ObligationEvidenceProvenanceReport::NativeBackend {
                verifier: proof.backend.clone(),
            },
            strength: strength.clone(),
            evidence: evidence.clone(),
            proof_certificate: None,
            native_trust_ir: Some(native.clone()),
            artifacts: proof.artifacts.clone(),
            diagnostics: proof.diagnostics.clone(),
            solver_warnings: None,
        };
        let (time_ms, proof_level) = {
            let obligation = &mut report.functions[index].obligations[0];
            obligation.obligation_id = transport.obligation_id.clone();
            obligation.description = VcKind::Postcondition.description();
            obligation.kind = "postcondition".into();
            obligation.outcome = ObligationOutcome::Proved { strength };
            obligation.solver = transport.solver;
            obligation.time_ms = transport.time_ms;
            obligation.evidence = Some(evidence);
            obligation.proof_evidence = Some(proof_report);
            obligation.transport_evidence = Some(ObligationTransportEvidenceReport {
                obligation_id: transport.obligation_id,
                claim_digest_sha256: transport.claim_digest_sha256,
                typed_kind: transport.typed_kind,
                native_trust_ir: Some(native),
                proof_evidence: Some(proof),
                monitor: None,
            });
            (obligation.time_ms, obligation.proof_level)
        };
        report.functions[index].summary.total_time_ms = time_ms;
        report.functions[index].summary.max_proof_level = Some(proof_level);
        report.recompute_summaries_from_obligation_outcomes();
    }

    #[test]
    fn typed_contract_report_rejects_forged_or_incomplete_evidence() {
        let report = failed_report();
        assert!(assert_contracts_check_report(&captured_report(&report, 1)).is_ok());

        let mut forged_summary = report.clone();
        forged_summary.summary.total_failed = 0;
        forged_summary.summary.total_proved = 3;
        assert!(assert_contracts_check_report(&captured_report(&forged_summary, 1)).is_err());

        let mut summary_only = report.clone();
        summary_only.functions[0].summary.total_obligations = 2;
        assert!(assert_contracts_check_report(&captured_report(&summary_only, 1)).is_err());

        let mut duplicate_function = report.clone();
        duplicate_function.functions[1].function = duplicate_function.functions[0].function.clone();
        assert!(assert_contracts_check_report(&captured_report(&duplicate_function, 1)).is_err());

        let mut wrong_subject = report.clone();
        wrong_subject.crate_name.push_str("-attacker");
        assert!(
            assert_contracts_check_report(&captured_report(&wrong_subject, 1)).is_err(),
            "the Cargo report subject must match the exact proof-unit inventory"
        );

        let mut wrong_package = report.clone();
        let inventory = wrong_package.cargo_proof_inventory.as_mut().expect("Cargo inventory");
        inventory.declared.primary_roots[0].package_name = "attacker".into();
        inventory.completed.primary_roots[0].package_name = "attacker".into();
        inventory.covered.primary_roots[0].package_name = "attacker".into();
        assert!(
            assert_contracts_check_report(&captured_report(&wrong_package, 1)).is_err(),
            "a self-consistent non-corpus Cargo unit cannot borrow the corpus function names"
        );

        let mut wrong_function_scope = report.clone();
        wrong_function_scope.functions[0].function = "attacker::divide_exact".into();
        assert!(
            assert_contracts_check_report(&captured_report(&wrong_function_scope, 1)).is_err(),
            "short-name aliases outside the exact Cargo subject must be rejected"
        );

        let mut missing_obligation_id = report.clone();
        missing_obligation_id.functions[0].obligations[0].obligation_id = None;
        assert!(
            assert_contracts_check_report(&captured_report(&missing_obligation_id, 1)).is_err(),
            "every corpus obligation needs a stable identity"
        );

        let mut empty_obligation_id = report.clone();
        empty_obligation_id.functions[0].obligations[0].obligation_id = Some("  ".into());
        assert!(
            assert_contracts_check_report(&captured_report(&empty_obligation_id, 1)).is_err(),
            "whitespace cannot stand in for a stable obligation identity"
        );

        let mut missing_transport_id = report.clone();
        missing_transport_id.functions[0].obligations[0]
            .transport_evidence
            .as_mut()
            .expect("transport evidence")
            .obligation_id = None;
        assert!(
            assert_contracts_check_report(&captured_report(&missing_transport_id, 1)).is_err(),
            "every outcome row must retain the exact nested transport identity"
        );

        let mut missing_clause_location = report.clone();
        missing_clause_location.functions[0].obligations[0].location = None;
        assert!(
            assert_contracts_check_report(&captured_report(&missing_clause_location, 1)).is_err(),
            "authored ensures evidence must remain at the pinned source clause"
        );

        let mut missing_contract = report.clone();
        missing_contract.functions[2].obligations[0].kind = "arithmetic_safety".into();
        assert!(assert_contracts_check_report(&captured_report(&missing_contract, 1)).is_err());

        let sentinel = VcKind::UnsupportedMir {
            kind: "SpecEnsuresUnparseable".into(),
            detail: "call/index clause remains fail-closed".into(),
        };
        let mut exact_get_at_sentinel = report.clone();
        set_exact_obligation_kind(&mut exact_get_at_sentinel, 2, sentinel.clone());
        let exact_get_at_result =
            assert_contracts_check_report(&captured_report(&exact_get_at_sentinel, 1));
        assert!(
            exact_get_at_result.is_ok(),
            "get_at may use the exact typed fail-closed sentinel: {exact_get_at_result:?}"
        );

        let mut substring_forgery = report.clone();
        let forged = &mut substring_forgery.functions[2].obligations[0];
        forged.kind = "unsupported_mir".into();
        forged.description = "forged description mentions SpecEnsuresUnparseable".into();
        assert!(
            assert_contracts_check_report(&captured_report(&substring_forgery, 1)).is_err(),
            "diagnostic text cannot manufacture authored-ensures identity"
        );

        let mut wrong_typed_kind = exact_get_at_sentinel.clone();
        wrong_typed_kind.functions[2].obligations[0]
            .transport_evidence
            .as_mut()
            .expect("typed evidence")
            .typed_kind = Some(Box::new(VcKind::Postcondition));
        assert!(
            assert_contracts_check_report(&captured_report(&wrong_typed_kind, 1)).is_err(),
            "the canonical row and exact typed kind must agree"
        );

        let mut unparseable_divide_exact = report.clone();
        set_exact_obligation_kind(&mut unparseable_divide_exact, 0, sentinel);
        assert!(
            assert_contracts_check_report(&captured_report(&unparseable_divide_exact, 1)).is_err(),
            "the fallback is scoped only to get_at's pinned call/index clause"
        );

        let mut invented = serde_json::to_value(&report).expect("serialize invented outcome");
        invented["functions"][0]["obligations"][0]["outcome"]["status"] =
            Value::String("invented".into());
        let invented = Captured {
            exit: 1,
            terminated_by_signal: false,
            stdout: invented.to_string(),
            stderr: String::new(),
        };
        assert!(assert_contracts_check_report(&invented).is_err());
    }

    #[test]
    fn proved_rows_require_exact_structural_evidence_and_cannot_be_transplanted() {
        let mut valid = failed_report();
        install_publishable_proof(&mut valid, 1, "11", "21");
        let valid_result = assert_contracts_check_report(&captured_report(&valid, 1));
        assert!(
            valid_result.is_ok(),
            "a structurally complete proved abs_total row is allowed while the pinned corpus remains fail-closed: {valid_result:?}"
        );

        let mut malformed = valid.clone();
        malformed.functions[1].obligations[0]
            .proof_evidence
            .as_mut()
            .expect("proof evidence")
            .native_id = Some("trust_ir-native-trust-wp-request-11-proof-attacker".into());
        let error = assert_contracts_check_report(&captured_report(&malformed, 1)).unwrap_err();
        assert!(error.to_string().contains("malformed"), "{error}");

        let mut missing_transport_identity = valid.clone();
        missing_transport_identity.functions[1].obligations[0]
            .transport_evidence
            .as_mut()
            .expect("transport evidence")
            .obligation_id = None;
        let error = assert_contracts_check_report(&captured_report(&missing_transport_identity, 1))
            .unwrap_err();
        assert!(error.to_string().contains("transport identity"), "{error}");

        let mut mismatched_normalized_evidence = valid.clone();
        let wrong_evidence = trust_types::ProofEvidence::from(ProofStrength::inductive());
        let obligation = &mut mismatched_normalized_evidence.functions[1].obligations[0];
        obligation.evidence = Some(wrong_evidence.clone());
        obligation.proof_evidence.as_mut().expect("proof evidence").evidence =
            wrong_evidence.clone();
        obligation
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof evidence")
            .evidence = Some(wrong_evidence);
        let error =
            assert_contracts_check_report(&captured_report(&mismatched_normalized_evidence, 1))
                .unwrap_err();
        assert!(error.to_string().contains("malformed"), "{error}");

        let mut transplanted = failed_report();
        install_publishable_proof(&mut transplanted, 1, "31", "41");
        install_publishable_proof(&mut transplanted, 4, "32", "42");
        let left_proof = transplanted.functions[1].obligations[0].proof_evidence.take();
        let left_transport = transplanted.functions[1].obligations[0].transport_evidence.take();
        let right_proof = transplanted.functions[4].obligations[0].proof_evidence.take();
        let right_transport = transplanted.functions[4].obligations[0].transport_evidence.take();
        transplanted.functions[1].obligations[0].proof_evidence = right_proof;
        transplanted.functions[1].obligations[0].transport_evidence = right_transport;
        transplanted.functions[4].obligations[0].proof_evidence = left_proof;
        transplanted.functions[4].obligations[0].transport_evidence = left_transport;
        let error = assert_contracts_check_report(&captured_report(&transplanted, 1)).unwrap_err();
        assert!(error.to_string().contains("transport identity"), "{error}");
    }

    #[test]
    fn raw_proved_outcome_does_not_satisfy_a_fail_closed_pin() {
        let mut report = failed_report();
        install_publishable_proof(&mut report, 2, "51", "61");
        let error = assert_contracts_check_report(&captured_report(&report, 1)).unwrap_err();
        assert!(error.to_string().contains("fail-closed set changed"), "{error}");
    }

    #[test]
    fn raw_runtime_outcome_is_mapped_then_rejected_for_the_static_corpus() {
        let mut report = failed_report();
        report.functions[1].obligations[0].outcome =
            ObligationOutcome::RuntimeChecked { note: Some("forged runtime fallback".into()) };
        report.recompute_summaries_from_obligation_outcomes();
        let error = assert_contracts_check_report(&captured_report(&report, 1)).unwrap_err();
        assert!(error.to_string().contains("runtime-checked"), "{error}");
    }

    #[test]
    fn raw_summary_verdict_fields_cannot_hide_behind_sanitization() {
        let report = failed_report();
        let raw = serde_json::to_value(&report).expect("serialize report");
        let reject = |forged: Value| {
            let error =
                assert_contracts_check_report(&captured(1, forged.to_string())).unwrap_err();
            assert!(error.to_string().contains("raw summaries or verdicts"), "{error}");
        };

        let mut forged = raw.clone();
        forged["summary"]["verdict"] =
            serde_json::to_value(CrateVerdict::Verified).expect("serialize verdict");
        reject(forged);

        let mut forged = raw.clone();
        forged["summary"]["functions_verified"] = Value::from(5_u64);
        reject(forged);

        let mut forged = raw.clone();
        forged["functions"][0]["summary"]["verdict"] =
            serde_json::to_value(FunctionVerdict::Verified).expect("serialize verdict");
        reject(forged);

        let mut forged = raw.clone();
        forged["functions"][0]["summary"]["max_proof_level"] = Value::Null;
        reject(forged);

        let mut forged = raw;
        forged["summary"]["proof_grade_engine_statuses"] = serde_json::json!([{
            "engine": "forged",
            "total_obligations": 5,
            "proof_grade_obligations": 5,
            "functions_routed": 5
        }]);
        reject(forged);
    }

    /// The ratified summary-partition (f9fe3fa12b0): the requires-bearing
    /// corpus functions (divide_exact, get_at) emit `assumption:*` entry rows,
    /// which the gate partitions out of `unknown` into `assumed` while the raw
    /// summary still lumps them into `total_unknown`. The gate validator must
    /// ACCEPT that shape (a non-zero `assumed` with the canonical
    /// `conditional_on_assumption_rows == assumed > 0` flag and the
    /// `unknown + assumed == total_unknown` reconstruction) and REJECT its
    /// inconsistent forgeries. Modeled on the exact real report shape
    /// (proved 10, failed 1, gate unknown 10, assumed 2, summary
    /// total_unknown 12).
    #[test]
    fn gate_validator_accepts_the_ratified_entry_assumption_partition() {
        let mut report = failed_report();
        report.summary.total_obligations = 23;
        report.summary.total_proved = 10;
        report.summary.total_failed = 1;
        // The summary lumps the 2 entry-assumption rows into total_unknown.
        report.summary.total_unknown = 12;
        report.summary.total_runtime_checked = 0;
        report.summary.total_design_requirements = 0;

        let make_gate = |unknown: u64, assumed: u64, conditional_assumption: bool| -> Value {
            serde_json::json!({
                "lane": "strict",
                "verification_level": "L2",
                "decision": "fail",
                "exit_code": 1,
                "counts": {
                    "total": 23, "proved": 10, "failed": 1,
                    "unknown": unknown, "runtime_checked": 0,
                    "assumed": assumed, "mandated": 0, "contract_panics": 0,
                },
                "conditional_on_assumption_rows": conditional_assumption,
                "conditional_on_dependency_entries": false,
                "conditional_on_runtime_checks": false,
                "conditional_on_visitation_entries": false,
                "coverage": { "eligible": 5, "processed": 5, "coverage_complete": true },
            })
        };
        let raw_with = |gate: Value| serde_json::json!({ "verification_gate": gate });

        // ACCEPT: the sanctioned partition (unknown 10 + assumed 2 == 12).
        validate_contract_verification_gate(
            &raw_with(make_gate(10, 2, true)),
            &report,
            1,
        )
        .expect("the ratified entry-assumption partition must validate");

        // REJECT: assumed rows present but the conditional flag denies them
        // (breaks the canonical `conditional == assumed > 0` invariant).
        assert!(
            validate_contract_verification_gate(&raw_with(make_gate(10, 2, false)), &report, 1)
                .is_err(),
            "a non-zero assumed count with a false assumption-conditional flag must fail closed"
        );

        // REJECT: the partition does not reconstruct the summary
        // (unknown 9 + assumed 2 = 11 != total_unknown 12) — a row went missing.
        assert!(
            validate_contract_verification_gate(&raw_with(make_gate(9, 2, true)), &report, 1)
                .is_err(),
            "a partition that does not reconstruct summary.total_unknown must fail closed"
        );

        // REJECT: a runtime-checked row is still forbidden in this proof corpus.
        let mut rt = make_gate(9, 2, true);
        rt["counts"]["runtime_checked"] = Value::from(1_u64);
        rt["counts"]["unknown"] = Value::from(8_u64);
        rt["conditional_on_runtime_checks"] = Value::Bool(true);
        assert!(
            validate_contract_verification_gate(&raw_with(rt), &report, 1).is_err(),
            "a runtime-checked row must still fail the proof corpus gate"
        );
    }

    #[test]
    fn raw_verification_gate_is_exactly_bound_to_the_same_failing_run() {
        let report = failed_report();
        let base: Value = serde_json::from_str(&captured_report(&report, 1).stdout)
            .expect("parse captured report fixture");
        let reject = |forged: Value| {
            assert!(
                assert_contracts_check_report(&captured(1, forged.to_string())).is_err(),
                "forged verification-gate side channel must fail closed"
            );
        };

        let mut missing = base.clone();
        missing.as_object_mut().expect("report object").remove("verification_gate");
        reject(missing);

        for (field, value) in [
            ("lane", Value::String("advisory".into())),
            ("verification_level", Value::String("L0".into())),
            ("decision", Value::String("pass".into())),
            ("exit_code", Value::from(0_u64)),
        ] {
            let mut forged = base.clone();
            forged["verification_gate"][field] = value;
            reject(forged);
        }

        let mut count_drift = base.clone();
        count_drift["verification_gate"]["counts"]["proved"] = Value::from(1_u64);
        reject(count_drift);

        let mut bucket_shift = base.clone();
        bucket_shift["verification_gate"]["counts"]["failed"] = Value::from(4_u64);
        bucket_shift["verification_gate"]["counts"]["runtime_checked"] = Value::from(1_u64);
        bucket_shift["verification_gate"]["conditional_on_runtime_checks"] = Value::Bool(true);
        reject(bucket_shift);

        let mut malformed_coverage = base.clone();
        malformed_coverage["verification_gate"]["coverage"] = serde_json::json!({
            "eligible": 5,
            "processed": 4,
            "coverage_complete": true,
        });
        reject(malformed_coverage);

        let mut test_execution = base;
        test_execution["verification_gate"]["test_execution"] = serde_json::json!({
            "schema": trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION,
            "completion_scope": "top-level-cargo-child-exit-only-v1",
            "requested": true,
            "scope": trust_types::CERTIFIED_TEST_EXECUTION_SCOPE,
            "compile_only": true,
            "phase_a_status": 0,
            "phase_a_success": true,
            "phase_b_state": "not-requested",
            "authorized_executables": [],
        });
        reject(test_execution);
    }

    #[test]
    fn function_time_arithmetic_overflow_fails_closed() {
        let mut report = failed_report();
        let mut second = report.functions[0].obligations[0].clone();
        second.obligation_id = Some("basic-contracts::divide_exact::ensures:overflow".into());
        second.transport_evidence.as_mut().expect("transport evidence").obligation_id =
            second.obligation_id.clone();
        report.functions[0].obligations[0].time_ms = u64::MAX;
        second.time_ms = 1;
        report.functions[0].obligations.push(second);
        report.functions[0].summary.total_time_ms = u64::MAX;
        report.recompute_summaries_from_obligation_outcomes();
        let error = assert_contracts_check_report(&captured_report(&report, 1)).unwrap_err();
        assert!(error.to_string().contains("time overflow"), "{error}");
    }

    #[test]
    fn forged_summary_count_overflow_returns_error_instead_of_panicking() {
        let report = failed_report();
        let mut raw = serde_json::to_value(&report).expect("serialize report");
        raw["summary"]["total_proved"] = Value::from(1_u64);
        raw["summary"]["total_unknown"] = Value::from(u64::MAX);
        let checked = std::panic::catch_unwind(|| {
            assert_contracts_check_report(&captured(1, raw.to_string()))
        });
        assert!(checked.is_ok(), "malformed summary arithmetic must never unwind");
        assert!(checked.expect("checked above").is_err());
    }

    #[test]
    fn all_five_corpus_function_rows_are_required() {
        for missing_index in [3_usize, 4] {
            let mut report = failed_report();
            let missing = report.functions.remove(missing_index).function;
            report.recompute_summaries_from_obligation_outcomes();
            let error = assert_contracts_check_report(&captured_report(&report, 1)).unwrap_err();
            let missing_leaf = missing.rsplit("::").next().expect("non-empty function name");
            assert!(error.to_string().contains(missing_leaf), "{error}");
        }
    }

    fn captured(exit: i32, stdout: String) -> Captured {
        Captured { exit, terminated_by_signal: false, stdout, stderr: String::new() }
    }

    /// Like [`failed_function`], but left short of a proof by an `unknown`
    /// outcome instead of a hard refutation.
    fn unknown_function(name: &str, report_subject: &str) -> FunctionProofReport {
        let mut function = failed_function(name, report_subject);
        function.summary.failed = 0;
        function.summary.unknown = 1;
        function.summary.verdict = FunctionVerdict::Inconclusive;
        function.obligations[0].outcome =
            ObligationOutcome::Unknown { reason: "coverage gap".into() };
        function
    }

    #[test]
    fn pinned_fail_closed_report_is_accepted_on_cargo_exit() {
        let report = failed_report();
        assert!(assert_contracts_check_report(&captured_report(&report, 101)).is_ok());
    }

    #[test]
    fn accepting_the_refutable_corpus_is_a_broken_refutation_lane() {
        let report = failed_report();
        let error = assert_contracts_check_report(&captured_report(&report, 0)).unwrap_err();
        assert!(error.to_string().contains("refutation lane"), "{error}");
    }

    #[test]
    fn setup_exit_is_not_a_fail_closed_outcome() {
        let report = failed_report();
        assert!(assert_contracts_check_report(&captured_report(&report, 2)).is_err());
    }

    #[test]
    fn divide_exact_must_carry_a_hard_refutation() {
        let mut report = failed_report();
        let report_subject = report.crate_name.clone();
        report.functions[0] = unknown_function("divide_exact", &report_subject);
        report.summary.total_failed = 4;
        report.summary.total_unknown = 1;
        report.summary.functions_with_violations = 4;
        report.summary.functions_inconclusive = 1;
        let error = assert_contracts_check_report(&captured_report(&report, 101)).unwrap_err();
        assert!(error.to_string().contains("fail-closed set changed"), "{error}");
    }

    fn standalone_report() -> String {
        serde_json::json!({
            "schema_version": "trust.source-audit.v1",
            "mode": "source-audit",
            "proof_authority": "none",
            "compiler_verification_performed": false,
            "audit_passed": true,
            "duration_ms": 1,
            "files_analyzed": 1,
            "functions_found": 5,
            "public_functions": 5,
            "unsafe_functions": 0,
            "specified_functions": 3,
            "total_audit_rows": 7,
            "present": 5,
            "failed": 0,
            "unknown": 2,
            "functions": [
                { "name": "divide_exact", "file": "/tmp/basic-contracts/src/lib.rs", "is_public": true, "is_unsafe": false, "has_requires": true, "has_ensures": true },
                { "name": "abs_total", "file": "/tmp/basic-contracts/src/lib.rs", "is_public": true, "is_unsafe": false, "has_requires": false, "has_ensures": true },
                { "name": "get_at", "file": "/tmp/basic-contracts/src/lib.rs", "is_public": true, "is_unsafe": false, "has_requires": true, "has_ensures": true },
                { "name": "running_total", "file": "/tmp/basic-contracts/src/lib.rs", "is_public": true, "is_unsafe": false, "has_requires": false, "has_ensures": false },
                { "name": "midpoint_checked", "file": "/tmp/basic-contracts/src/lib.rs", "is_public": true, "is_unsafe": false, "has_requires": false, "has_ensures": false },
            ],
            "audit_rows": [
                { "function": "divide_exact", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "PreconditionPresent", "description": "divide_exact: requires specification present", "outcome": "Present" },
                { "function": "divide_exact", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "PostconditionPresent", "description": "divide_exact: ensures specification present", "outcome": "Present" },
                { "function": "abs_total", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "PostconditionPresent", "description": "abs_total: ensures specification present", "outcome": "Present" },
                { "function": "get_at", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "PreconditionPresent", "description": "get_at: requires specification present", "outcome": "Present" },
                { "function": "get_at", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "PostconditionPresent", "description": "get_at: ensures specification present", "outcome": "Present" },
                { "function": "running_total", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "UnspecifiedPublicApi", "description": "running_total: public function has no specification", "outcome": "Unknown" },
                { "function": "midpoint_checked", "file": "/tmp/basic-contracts/src/lib.rs", "kind": "UnspecifiedPublicApi", "description": "midpoint_checked: public function has no specification", "outcome": "Unknown" },
            ],
        })
        .to_string()
    }

    #[test]
    fn standalone_inventory_passes_on_unspecified_public_functions() {
        // 06c732cdd9a: the source audit passes on inventory observations —
        // `unknown` UnspecifiedPublicApi rows are observations, not defects, so
        // this corpus (failed=0, unknown=2) completes exit 0 / audit_passed=true.
        assert!(assert_contracts_standalone_report(&captured(0, standalone_report())).is_ok());
    }

    #[test]
    fn standalone_inventory_exit_must_cohere_with_audit_result() {
        // audit_passed=true must cohere with exit 0; a non-zero exit is
        // incoherent with the passing inventory and fails the gate.
        let error =
            assert_contracts_standalone_report(&captured(1, standalone_report())).unwrap_err();
        assert!(error.to_string().contains("must complete with exit 0"), "{error}");
        assert!(assert_contracts_standalone_report(&captured(2, standalone_report())).is_err());
    }

    #[test]
    fn standalone_inventory_requires_running_total_and_midpoint_checked() {
        for missing in ["running_total", "midpoint_checked"] {
            let mut report: Value =
                serde_json::from_str(&standalone_report()).expect("parse standalone fixture");
            let entry = report["functions"]
                .as_array_mut()
                .expect("function inventory")
                .iter_mut()
                .find(|entry| field_str(entry, "name") == missing)
                .expect("fixture function");
            entry["name"] = Value::String("attacker".into());
            let error =
                assert_contracts_standalone_report(&captured(0, report.to_string())).unwrap_err();
            assert!(error.to_string().contains(missing), "{error}");
        }
    }

    #[test]
    fn standalone_inventory_requires_exact_nonproof_envelope_and_rows() {
        for mutation in ["schema", "authority", "count", "row", "proof_field"] {
            let mut report: Value =
                serde_json::from_str(&standalone_report()).expect("parse standalone fixture");
            match mutation {
                "schema" => report["schema_version"] = Value::String("attacker.v1".into()),
                "authority" => report["proof_authority"] = Value::String("compiler".into()),
                "count" => report["total_audit_rows"] = Value::from(8),
                "row" => {
                    report["audit_rows"][0]["outcome"] = Value::String("Proved".into());
                }
                "proof_field" => report["proved"] = Value::from(5),
                _ => unreachable!(),
            }
            assert!(
                assert_contracts_standalone_report(&captured(0, report.to_string())).is_err(),
                "standalone mutation {mutation} must fail closed"
            );
        }
    }

    #[test]
    fn unproved_obligations_outside_the_corpus_set_are_rejected() {
        let mut report = failed_report();
        let report_subject = report.crate_name.clone();
        report.functions.push(failed_function("midpoint_unchecked", &report_subject));
        report.summary.functions_analyzed = 6;
        report.summary.functions_with_violations = 6;
        report.summary.total_obligations = 6;
        report.summary.total_failed = 6;
        let error = assert_contracts_check_report(&captured_report(&report, 101)).unwrap_err();
        assert!(error.to_string().contains("outside the exact"), "{error}");
    }
}
