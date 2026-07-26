// Pipeline test module. Tests reach into multiple submodules — sibling-module
// helpers are imported explicitly; mod.rs re-exports cover the public surface.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs};

use sha2::{Digest, Sha256};

use super::discovery::{
    canonicalize_or_self, host_executable_name, native_trust_cargo_path,
    repo_local_rustc_candidates, select_native_rustc_discovery, sibling_rustc_path,
};
use super::hardened::{
    GateDecision, GateLane, OutcomeCounts, aggregate_coverage, apply_coverage_gate,
    compiler_verification_success, evaluate_run_gate, evaluate_verification_gate,
    hardened_proof_gate_failure_for_results, memory_safe_gate_counts, partition_outcome_counts,
};
use super::probe::{
    apply_native_runtime_env, apply_trustd_runtime_closure, inspect_trustd_runtime_closure,
    native_runtime_library_paths, trusted_runtime_search_path_value,
};
use super::provenance::runtime_binary_source_provenance_for_rewrite_loop;
use super::run::{
    CompilerRun, canonical_single_file_report_subject, cargo_child_rustc_path,
    live_report_consumer_rejection, missing_trust_json_diagnostic,
    resolve_cargo_selection_for_compiler, rewrite_iteration_success, run_compiler,
    single_file_report_subject,
};
use super::standalone::standalone_hardened_help;
use super::surface::{LINKED_TRUST_SURFACE_TOOLS, detect_linked_trust_cargo_surface_with_search};
use super::transport::{CargoTargetIdentity, ParsedCompilerOutput};
use super::*;
use crate::config::TrustConfig;
use crate::source_analysis;
use crate::types::{OutputFormat, VerificationOutcome, VerificationResult};

fn temp_test_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    env::temp_dir().join(format!("targo-trust-pipeline-{label}-{}-{unique}", std::process::id()))
}

fn canonicalize_native_test_json(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                canonicalize_native_test_json(value);
            }
        }
        serde_json::Value::Object(object) => {
            let old = std::mem::take(object);
            let mut entries = old.into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            for (key, mut value) in entries {
                canonicalize_native_test_json(&mut value);
                object.insert(key, value);
            }
        }
        _ => {}
    }
}

fn native_shape_materialization(
    role: &str,
    suite: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
    payload: serde_json::Value,
    native_id: &str,
    references: Vec<trust_types::TransportArtifactReference>,
) -> (trust_types::TransportArtifactMaterialization, trust_types::TransportArtifactDigest) {
    let mut value = serde_json::json!({
        "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
        "role": role,
        "suite": suite,
        "request_id": request_id,
        "proof_id": proof_id,
        "payload": payload,
    });
    canonicalize_native_test_json(&mut value);
    let bytes = serde_json::to_vec(&value).expect("serialize native TrustIr materialization");
    let digest = trust_types::TransportArtifactDigest {
        algorithm: "sha256".into(),
        value: format!("{:x}", Sha256::digest(&bytes)),
    };
    (
        trust_types::TransportArtifactMaterialization::from_exact_bytes(
            &bytes, native_id, references,
        )
        .expect("native TrustIr materialization"),
        digest,
    )
}

fn native_shape_artifact(
    kind: &str,
    materialized: (
        trust_types::TransportArtifactMaterialization,
        trust_types::TransportArtifactDigest,
    ),
    uri: String,
) -> trust_types::TransportEvidenceArtifact {
    trust_types::TransportEvidenceArtifact {
        kind: kind.into(),
        format: Some("trust_ir-json".into()),
        artifact_id: None,
        digest: Some(materialized.1),
        uri: Some(uri),
        materialization: Some(materialized.0),
        metadata: None,
    }
}

fn native_shape_artifacts(
    suite: &str,
    request_id: &str,
    proof_id: &str,
) -> Vec<trust_types::TransportEvidenceArtifact> {
    let native_id = format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
    let bundle = native_shape_materialization(
        "bundle",
        None,
        None,
        None,
        serde_json::json!({"bundle": "exact"}),
        &native_id,
        vec![],
    );
    let bundle_digest = bundle.1.value.clone();
    let bundle_uri = format!("trust_ir-native://verification-bundle/{bundle_digest}");
    let request = native_shape_materialization(
        "request",
        Some(suite),
        Some(request_id),
        None,
        serde_json::json!({"request": "exact"}),
        &native_id,
        vec![trust_types::TransportArtifactReference {
            kind: "EngineInput".into(),
            digest: bundle.1.clone(),
        }],
    );
    let request_digest = request.1.value.clone();
    let normalized = native_shape_materialization(
        "normalized_obligation",
        Some(suite),
        Some(request_id),
        Some(proof_id),
        serde_json::json!({"obligation": "exact"}),
        &native_id,
        vec![trust_types::TransportArtifactReference {
            kind: "EngineInput".into(),
            digest: request.1.clone(),
        }],
    );
    vec![
        native_shape_artifact("EngineInput", bundle, bundle_uri.clone()),
        native_shape_artifact(
            "EngineInput",
            request,
            format!("{bundle_uri}/{suite}/request/{request_id}/{request_digest}"),
        ),
        native_shape_artifact(
            "NormalizedObligation",
            normalized.clone(),
            format!(
                "{bundle_uri}/{suite}/request/{request_id}/{request_digest}/proof/{proof_id}/{}",
                normalized.1.value
            ),
        ),
    ]
}

fn bound_native_proof_artifact(
    kind: &str,
    payload: &[u8],
    binding: &str,
    owner: &str,
    mut references: Vec<trust_types::TransportArtifactReference>,
) -> trust_types::TransportEvidenceArtifact {
    const MAGIC: &[u8] = b"trust.evidence-artifact-binding-envelope.v1\0";
    references.sort();
    let mut bytes = MAGIC.to_vec();
    let push = |bytes: &mut Vec<u8>, value: &[u8]| {
        bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
        bytes.extend_from_slice(value);
    };
    push(&mut bytes, kind.as_bytes());
    push(&mut bytes, owner.as_bytes());
    push(&mut bytes, binding.as_bytes());
    bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
    for reference in &references {
        push(&mut bytes, reference.kind.as_bytes());
        push(&mut bytes, reference.digest.algorithm.as_bytes());
        push(&mut bytes, reference.digest.value.as_bytes());
    }
    bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    bytes.extend_from_slice(payload);
    let digest = format!("{:x}", Sha256::digest(&bytes));
    trust_types::TransportEvidenceArtifact {
        kind: kind.into(),
        format: Some("binary".into()),
        artifact_id: Some(kind.into()),
        digest: Some(trust_types::TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: digest.clone(),
        }),
        uri: Some(format!("artifact://pipeline-test/{kind}/{digest}")),
        materialization: Some(
            trust_types::TransportArtifactMaterialization::from_exact_bytes(
                &bytes, binding, references,
            )
            .expect("bound native proof materialization"),
        ),
        metadata: None,
    }
}

fn hardened_native_proof_result() -> VerificationResult {
    let owner = "crate::paths::render:hardened0";
    let native_id = "trust_ir-native-trust-wp-request-8-proof-9";
    let input = bound_native_proof_artifact(
        "NormalizedObligation",
        b"exact hardened normalized obligation",
        native_id,
        owner,
        vec![],
    );
    let transcript = bound_native_proof_artifact(
        "SolverTranscript",
        b"exact hardened solver transcript",
        native_id,
        owner,
        vec![trust_types::TransportArtifactReference {
            kind: input.kind.clone(),
            digest: input.digest.clone().expect("input digest"),
        }],
    );
    let check = bound_native_proof_artifact(
        "ProofCheckReport",
        b"exact hardened proof-check report",
        native_id,
        owner,
        vec![trust_types::TransportArtifactReference {
            kind: transcript.kind.clone(),
            digest: transcript.digest.clone().expect("transcript digest"),
        }],
    );
    let transport = trust_types::TransportObligationResult {
        obligation_id: Some(owner.into()),
        claim_digest_sha256: Some("b".repeat(64)),
        kind: "hardened_byte_loss".into(),
        typed_kind: None,
        description: "hardened boundary (byte_loss): byte-exact path rendering".into(),
        location: None,
        outcome: trust_types::Outcome::Proved,
        solver: "trust-wp".into(),
        time_ms: 4,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
            suite: "trust-wp".into(),
            backend: "trust-wp".into(),
            request_id: Some("8".into()),
            native_id: Some(native_id.into()),
            present: true,
            artifacts: native_shape_artifacts("trust-wp", "8", "9"),
            diagnostics: Vec::new(),
        }),
        proof_evidence: Some(trust_types::TransportProofEvidence {
            suite: "trust-wp".into(),
            backend: "trust-wp".into(),
            request_id: Some("8".into()),
            proof_id: Some("9".into()),
            native_id: Some(native_id.into()),
            status: trust_types::TransportProofStatus::Proved,
            strength: Some(trust_types::ProofStrength::deductive()),
            evidence: Some(trust_types::ProofEvidence::from(
                trust_types::ProofStrength::deductive(),
            )),
            artifacts: vec![input, transcript, check],
            diagnostics: Vec::new(),
        }),
        monitor: None,
    };
    crate::types::transport_to_verification_result("crate::paths::render", &transport)
}

#[test]
fn standalone_hardened_help_covers_all_hardened_categories_only() {
    let hardened_kinds = [
        source_analysis::VcKind::HardenedRawPathApi,
        source_analysis::VcKind::HardenedPathIdentity,
        source_analysis::VcKind::HardenedPermissionChange,
        source_analysis::VcKind::HardenedPermissionCreate,
        source_analysis::VcKind::HardenedPermissionWindow,
        source_analysis::VcKind::HardenedByteLoss,
        source_analysis::VcKind::HardenedUtf8Boundary,
        source_analysis::VcKind::HardenedErrorDiscard,
        source_analysis::VcKind::HardenedPanic,
        source_analysis::VcKind::HardenedTrustBoundary,
        source_analysis::VcKind::HardenedTrustDomainOrder,
        source_analysis::VcKind::HardenedCompatibility,
        source_analysis::VcKind::HardenedProcessSemantics,
        source_analysis::VcKind::HardenedUnsafeOperation,
        source_analysis::VcKind::HardenedFfiBoundary,
    ];
    for kind in hardened_kinds {
        let help = standalone_hardened_help(kind)
            .unwrap_or_else(|| panic!("missing standalone hardened help for {kind:?}"));
        assert!(!help.is_empty());
        assert!(
            !help.contains('\n') && !help.ends_with('.'),
            "help should be concise terminal guidance: {help}"
        );
    }

    for kind in [
        source_analysis::VcKind::PreconditionPresent,
        source_analysis::VcKind::PostconditionPresent,
        source_analysis::VcKind::UnsafeFunction,
        source_analysis::VcKind::UnspecifiedPublicApi,
    ] {
        assert_eq!(standalone_hardened_help(kind), None);
    }
}

#[test]
fn hardened_proof_gate_for_results_rejects_inventory_only_native_hardened_results() {
    let result = VerificationResult {
        function: "crate::paths::render".into(),
        kind: "hardened_byte_loss".into(),
        message: "lossy OS/path conversion must be explicit".into(),
        outcome: VerificationOutcome::Proved,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };
    let config = TrustConfig::default();

    let failure = hardened_proof_gate_failure_for_results(
        &[result],
        &[],
        "hardened-gate-test",
        &[],
        None,
        &config,
        true,
        Some("unix_hardened"),
    )
    .expect("inventory-only hardened results must fail in every native workflow");

    assert_eq!(failure.hardened_obligations, 1);
    assert_eq!(failure.proof_evidence_entries, 0);
}

#[test]
fn hardened_rewrite_gate_accepts_authenticated_native_proof_evidence() {
    let authenticated_results = vec![hardened_native_proof_result()];
    let mut publication_results = authenticated_results.clone();
    crate::types::normalize_authenticated_results_for_publication(&mut publication_results, None);
    assert!(publication_results[0].outcome.is_proved());

    let subject = "hardened-rewrite-native-proof-test";
    let session = "c".repeat(64);
    let authority = crate::report::LiveTransportAuthority::capture_authenticated_projection(
        subject,
        &session,
        &authenticated_results,
        &publication_results,
        None,
    )
    .expect("valid native proof projection must mint rewrite authority");
    let config = TrustConfig::default();

    assert!(
        hardened_proof_gate_failure_for_results(
            &publication_results,
            &[],
            subject,
            &[],
            None,
            &config,
            true,
            Some("unix_hardened"),
        )
        .is_some(),
        "the same DTO without live compiler authority must fail closed"
    );
    assert!(
        hardened_proof_gate_failure_for_results(
            &publication_results,
            &[],
            subject,
            &[],
            Some(&authority),
            &config,
            true,
            Some("unix_hardened"),
        )
        .is_none(),
        "authenticated native proof evidence must satisfy the rewrite hardened gate"
    );
}

#[test]
fn compiler_verification_success_requires_nonzero_obligations() {
    assert!(!compiler_verification_success(0, 0, 0, 0, 0));
    assert!(compiler_verification_success(0, 1, 0, 0, 0));
    assert!(!compiler_verification_success(1, 1, 0, 0, 0));
    assert!(!compiler_verification_success(0, 1, 1, 0, 0));
    assert!(!compiler_verification_success(0, 1, 0, 1, 0));
    assert!(!compiler_verification_success(0, 1, 0, 0, 1));
}

#[test]
fn rewrite_iteration_success_matches_hardened_success_contract() {
    let complete_coverage = trust_types::VerificationCoverage::from_counts(1, 1);
    let proved = VerificationResult {
        function: "fixture::ok".into(),
        kind: "postcondition".into(),
        message: "postcondition proved".into(),
        outcome: VerificationOutcome::Proved,
        backend: "fake".into(),
        time_ms: Some(1),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };
    let unknown = VerificationResult {
        outcome: VerificationOutcome::Unknown,
        reason: Some("unsupported".into()),
        ..proved.clone()
    };
    let runtime_checked =
        VerificationResult { outcome: VerificationOutcome::RuntimeChecked, ..proved.clone() };
    let failed = VerificationResult { outcome: VerificationOutcome::Failed, ..proved.clone() };

    assert!(rewrite_iteration_success(
        0,
        std::slice::from_ref(&proved),
        &[],
        Some(&complete_coverage),
        &[],
        true,
    ));
    assert!(!rewrite_iteration_success(
        1,
        &[proved.clone()],
        &[],
        Some(&complete_coverage),
        &[],
        true,
    ));
    assert!(!rewrite_iteration_success(0, &[], &[], Some(&complete_coverage), &[], true,));
    assert!(!rewrite_iteration_success(
        0,
        &[failed.clone()],
        &[],
        Some(&complete_coverage),
        &[],
        true,
    ));
    assert!(!rewrite_iteration_success(
        0,
        &[unknown.clone()],
        &[],
        Some(&complete_coverage),
        &[],
        true,
    ));
    assert!(!rewrite_iteration_success(
        0,
        &[runtime_checked.clone()],
        &[],
        Some(&complete_coverage),
        &[],
        true,
    ));
}

#[test]
fn rewrite_iteration_success_requires_exact_zero_obligation_inventory_coverage() {
    let exact = trust_types::VerificationCoverage::from_counts(1, 1);
    let larger = trust_types::VerificationCoverage::from_counts(2, 2);
    let incomplete = trust_types::VerificationCoverage::from_counts(1, 0);
    let inventory = vec!["fixture::zero".to_string()];
    let target = CargoTargetIdentity {
        package_id: "path+file:///fixture#demo@0.1.0".into(),
        package_name: "demo".into(),
        target_name: "demo".into(),
        target_kinds: vec!["lib".into()],
        compile_target: "x86_64-unknown-linux-gnu".into(),
        compile_mode: "test".into(),
        compile_kind: "target".into(),
        unit_identity_sha256: "c".repeat(64),
        compile_target_spec_sha256: None,
        proof_unit_index: 0,
        proof_unit_mode: "test".into(),
        proof_unit_role: "primary".into(),
        semantics_sha256: "a".repeat(64),
    };

    assert!(rewrite_iteration_success(0, &[], &inventory, Some(&exact), &[], true));
    assert!(!rewrite_iteration_success(0, &[], &[], Some(&exact), &[], true));
    assert!(!rewrite_iteration_success(0, &[], &inventory, Some(&larger), &[], true));
    assert!(!rewrite_iteration_success(0, &[], &inventory, Some(&incomplete), &[], true));
    assert!(!rewrite_iteration_success(0, &[], &inventory, Some(&exact), &[target], true));
    assert!(!rewrite_iteration_success(1, &[], &inventory, Some(&exact), &[], true));
}

#[test]
fn evaluate_run_gate_requires_authenticated_zero_inventory_not_coverage_alone() {
    use GateDecision::{Inconclusive, Pass};

    let complete = trust_types::VerificationCoverage::from_counts(2, 2);
    let empty = OutcomeCounts::default();
    assert_eq!(
        evaluate_run_gate(GateLane::Strict, 0, empty, Some(&complete), false, true, 2),
        Pass
    );
    assert_eq!(
        evaluate_run_gate(GateLane::Strict, 0, empty, Some(&complete), false, true, 0),
        Inconclusive
    );
    assert_eq!(
        evaluate_run_gate(GateLane::Strict, 0, empty, Some(&complete), false, true, 1),
        Inconclusive
    );
    assert_eq!(
        evaluate_run_gate(GateLane::Strict, 0, empty, Some(&complete), true, true, 2),
        Inconclusive
    );
}

#[test]
fn rewrite_iteration_success_requires_complete_authenticated_target_coverage() {
    let proved = VerificationResult {
        function: "fixture::ok".into(),
        kind: "postcondition".into(),
        message: "postcondition proved".into(),
        outcome: VerificationOutcome::Proved,
        backend: "fake".into(),
        time_ms: Some(1),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };
    let complete = trust_types::VerificationCoverage::from_counts(1, 1);
    let incomplete = trust_types::VerificationCoverage::from_counts(2, 1);
    let target = CargoTargetIdentity {
        package_id: "path+file:///fixture#demo@0.1.0".into(),
        package_name: "demo".into(),
        target_name: "demo".into(),
        target_kinds: vec!["lib".into()],
        compile_target: "x86_64-unknown-linux-gnu".into(),
        compile_mode: "build".into(),
        compile_kind: "target".into(),
        unit_identity_sha256: "c".repeat(64),
        compile_target_spec_sha256: None,
        proof_unit_index: 0,
        proof_unit_mode: "test".into(),
        proof_unit_role: "primary".into(),
        semantics_sha256: "a".repeat(64),
    };

    assert!(!rewrite_iteration_success(0, &[proved.clone()], &[], None, &[], true));
    assert!(!rewrite_iteration_success(0, &[proved.clone()], &[], Some(&incomplete), &[], true,));
    assert!(!rewrite_iteration_success(
        0,
        &[proved.clone()],
        &[],
        Some(&complete),
        &[target.clone()],
        true,
    ));

    // Advisory compatibility permits unknown/legacy coverage, but never an
    // authenticated row that explicitly reports incomplete accounting.
    assert!(rewrite_iteration_success(0, &[proved.clone()], &[], None, &[], false));
    assert!(rewrite_iteration_success(
        0,
        &[proved.clone()],
        &[],
        Some(&complete),
        &[target],
        false,
    ));
    assert!(!rewrite_iteration_success(0, &[proved], &[], Some(&incomplete), &[], false,));
}

// ---------------------------------------------------------------------------
// Trust (green front door, Stage 2): exit-code gate tests.
// ---------------------------------------------------------------------------

/// Build an `OutcomeCounts` from the disjoint bucket sizes.
fn oc(
    proved: usize,
    failed: usize,
    unknown: usize,
    runtime_checked: usize,
    assumed: usize,
    mandated: usize,
) -> OutcomeCounts {
    OutcomeCounts {
        total: proved + failed + unknown + runtime_checked + assumed + mandated,
        proved,
        failed,
        unknown,
        runtime_checked,
        assumed,
        mandated,
        contract_panics: 0,
    }
}

/// `oc` plus a contract-panic bucket (Trust T9).
fn oc_cp(base: OutcomeCounts, contract_panics: usize) -> OutcomeCounts {
    OutcomeCounts { total: base.total + contract_panics, contract_panics, ..base }
}

/// A minimal transport row for partition tests.
fn gate_row(kind: &str, outcome: VerificationOutcome, raw_line: &str) -> VerificationResult {
    VerificationResult {
        function: "crate::f".into(),
        kind: kind.into(),
        message: "m".into(),
        outcome,
        backend: "ay".into(),
        time_ms: Some(1),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: raw_line.into(),
    }
}

/// A raw transport line carrying the compiler's `design_mandate` bit.
fn mandate_raw_line() -> String {
    // Mirrors `StructuredTransportEvidence` serialized under the private
    // `targo-trust-structured-transport-evidence:` prefix. If either changes,
    // the mandate below stops being detected and the partition test fails loudly.
    format!("targo-trust-structured-transport-evidence:{}", r#"{"design_mandate":true}"#)
}

#[test]
fn gate_advisory_lane_matches_contract_table() {
    use GateDecision::*;
    // Row 2: E != 0 -> Fail.
    assert_eq!(evaluate_verification_gate(GateLane::Advisory, 101, oc(3, 0, 0, 0, 0, 0)), Fail);
    // Row 3: F > 0 -> Fail.
    assert_eq!(evaluate_verification_gate(GateLane::Advisory, 0, oc(1, 1, 0, 0, 0, 0)), Fail);
    // Row 4: U > 0 -> Inconclusive.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(1, 0, 1, 0, 0, 0)),
        Inconclusive
    );
    // Row 5: T == 0 -> Inconclusive.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 0, 0)),
        Inconclusive
    );
    // Row 7a: all-assumed (P = 0), the async-lib case -> ConditionalPass.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 2, 0)),
        ConditionalPass { assumed: 2, mandated: 0, runtime_checked: 0, contract_panics: 0 }
    );
    // Row 7b: mandated = 1 (F1 fix) -> ConditionalPass in the advisory lane.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 0, 1)),
        ConditionalPass { assumed: 0, mandated: 1, runtime_checked: 0, contract_panics: 0 }
    );
    // Row 7c: runtime-checked (F6) -> ConditionalPass.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 1, 0, 0)),
        ConditionalPass { assumed: 0, mandated: 0, runtime_checked: 1, contract_panics: 0 }
    );
    // Row 7d: mixed proved + assumed (hello / greet) -> ConditionalPass.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc(1, 0, 0, 0, 1, 0)),
        ConditionalPass { assumed: 1, mandated: 0, runtime_checked: 0, contract_panics: 0 }
    );
    // Row 8: all proved -> Pass.
    assert_eq!(evaluate_verification_gate(GateLane::Advisory, 0, oc(2, 0, 0, 0, 0, 0)), Pass);

    // is_success() mapping: Pass and ConditionalPass exit 0; the rest exit nonzero.
    assert!(evaluate_verification_gate(GateLane::Advisory, 0, oc(2, 0, 0, 0, 0, 0)).is_success());
    assert!(evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 0, 1)).is_success());
    assert!(evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 2, 0)).is_success());
    assert!(!evaluate_verification_gate(GateLane::Advisory, 0, oc(1, 0, 1, 0, 0, 0)).is_success());
    assert!(!evaluate_verification_gate(GateLane::Advisory, 0, oc(0, 0, 0, 0, 0, 0)).is_success());
    assert!(!evaluate_verification_gate(GateLane::Advisory, 1, oc(1, 0, 0, 0, 0, 0)).is_success());
}

#[test]
fn gate_certify_lane_never_conditional_passes() {
    use GateDecision::*;
    // mandated = 1 -> Inconclusive in the strict lane (NOT ConditionalPass).
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(0, 0, 0, 0, 0, 1)), Inconclusive);
    // assumed / runtime-checked likewise fail the strict lane as Inconclusive.
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(0, 0, 0, 0, 1, 0)), Inconclusive);
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(0, 0, 0, 1, 0, 0)), Inconclusive);
    // Genuine unknown / empty -> Inconclusive; refutation / nonzero exit -> Fail.
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(1, 0, 1, 0, 0, 0)), Inconclusive);
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(0, 0, 0, 0, 0, 0)), Inconclusive);
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(1, 1, 0, 0, 0, 0)), Fail);
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 101, oc(2, 0, 0, 0, 0, 0)), Fail);
    // All proved -> Pass.
    assert_eq!(evaluate_verification_gate(GateLane::Certify, 0, oc(2, 0, 0, 0, 0, 0)), Pass);

    // ConditionalPass is UNREACHABLE in the strict lane, whatever the mix.
    for counts in
        [oc(0, 0, 0, 0, 1, 0), oc(0, 0, 0, 0, 0, 1), oc(0, 0, 0, 1, 0, 0), oc(1, 0, 0, 1, 1, 1)]
    {
        let decision = evaluate_verification_gate(GateLane::Certify, 0, counts);
        assert!(
            !matches!(decision, ConditionalPass { .. }),
            "strict lane must never conditional-pass: {counts:?} -> {decision:?}"
        );
    }
}

#[test]
fn memory_safe_lane_only_conditionally_accepts_compiler_marked_safe_assumptions() {
    use GateDecision::*;

    let mut marked = gate_row("assumption:native-lowering", VerificationOutcome::Unknown, "");
    marked.backend = trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE.to_string();
    let unmarked = gate_row("assumption:expected-absent-callee", VerificationOutcome::Unknown, "");
    let results = vec![marked.clone(), unmarked];
    let (reported, _) = partition_outcome_counts(&results);
    assert_eq!(reported.assumed, 2);

    let (restricted, defects) = memory_safe_gate_counts(&results, reported);
    assert_eq!(restricted.assumed, 1);
    assert_eq!(restricted.unknown, 1);
    assert_eq!(defects.len(), 1);
    assert_eq!(evaluate_verification_gate(GateLane::MemorySafe, 0, restricted), Inconclusive);

    let (marked_counts, _) = partition_outcome_counts(&[marked]);
    let (marked_counts, defects) = memory_safe_gate_counts(&results[..1], marked_counts);
    assert!(defects.is_empty());
    assert_eq!(
        evaluate_verification_gate(GateLane::MemorySafe, 0, marked_counts),
        ConditionalPass { assumed: 1, mandated: 0, runtime_checked: 0, contract_panics: 0 }
    );

    for counts in [oc(0, 0, 0, 1, 0, 0), oc(0, 0, 0, 0, 0, 1), oc_cp(oc(0, 0, 0, 0, 0, 0), 1)] {
        assert_eq!(evaluate_verification_gate(GateLane::MemorySafe, 0, counts), Inconclusive);
    }
    assert_eq!(evaluate_verification_gate(GateLane::MemorySafe, 0, oc(1, 1, 0, 0, 0, 0)), Fail);
}

#[test]
fn coroutine_protocol_premise_is_visible_and_cannot_pass_strict_or_memory_safe_gates() {
    use GateDecision::*;

    let mut coroutine = gate_row("assumption:coroutine", VerificationOutcome::Unknown, "");
    coroutine.backend = "trust-classifier".to_string();
    let results = [coroutine];
    let (counts, defects) = partition_outcome_counts(&results);
    assert!(defects.is_empty());
    assert_eq!(counts.assumed, 1);
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, counts),
        ConditionalPass { assumed: 1, mandated: 0, runtime_checked: 0, contract_panics: 0 }
    );
    assert_eq!(evaluate_verification_gate(GateLane::Strict, 0, counts), Inconclusive);
    assert_eq!(evaluate_verification_gate(GateLane::Strict, 1, counts), Fail);

    let (memory_safe_counts, defects) = memory_safe_gate_counts(&results, counts);
    assert_eq!(memory_safe_counts.assumed, 0);
    assert_eq!(memory_safe_counts.unknown, 1);
    assert_eq!(defects.len(), 1);
    assert_eq!(
        evaluate_verification_gate(GateLane::MemorySafe, 0, memory_safe_counts),
        Inconclusive
    );
    assert_eq!(evaluate_verification_gate(GateLane::MemorySafe, 1, memory_safe_counts), Fail);
}

// ---------------------------------------------------------------------------
// Trust (assertion-grade coverage, roadmap §4.1): a run with
// `processed != eligible` must never read as a pass; an absent coverage row
// (older compiler) is coverage-unknown, fails strict proof claims, and remains
// compatible only in explicit advisory lanes.
// ---------------------------------------------------------------------------

fn coverage_row(
    crate_name: &str,
    eligible: usize,
    processed: usize,
) -> trust_types::CoverageTransportSummary {
    trust_types::CoverageTransportSummary {
        crate_name: crate_name.to_string(),
        package_name: crate_name.to_string(),
        primary_package: true,
        verification_session: "pipeline-test-session".to_string(),
        eligible,
        processed,
        function_identities: None,
    }
}

#[test]
fn coverage_gate_caps_passing_decisions_on_shortfall() {
    use GateDecision::*;
    let shortfall = aggregate_coverage(&[coverage_row("demo", 10, 7)]);
    assert_eq!(
        shortfall,
        Some(trust_types::VerificationCoverage {
            eligible: 10,
            processed: 7,
            coverage_complete: false
        })
    );
    // Pass and ConditionalPass are demoted to Inconclusive — never a passing
    // gate when functions were never verified.
    assert_eq!(apply_coverage_gate(Pass, shortfall.as_ref(), true), Inconclusive);
    assert_eq!(
        apply_coverage_gate(
            ConditionalPass { assumed: 1, mandated: 0, runtime_checked: 0, contract_panics: 0 },
            shortfall.as_ref(),
            true
        ),
        Inconclusive
    );
    // Fail-closed hardening only: already-non-passing decisions are unchanged
    // (a shortfall must never mask or soften a refutation).
    assert_eq!(apply_coverage_gate(Fail, shortfall.as_ref(), true), Fail);
    assert_eq!(apply_coverage_gate(Inconclusive, shortfall.as_ref(), true), Inconclusive);
}

#[test]
fn coverage_gate_leaves_complete_and_unknown_coverage_alone() {
    use GateDecision::*;
    // Complete coverage: gate unchanged in every state.
    let complete = aggregate_coverage(&[coverage_row("demo", 10, 10)]);
    assert_eq!(
        complete,
        Some(trust_types::VerificationCoverage {
            eligible: 10,
            processed: 10,
            coverage_complete: true
        })
    );
    let conditional =
        ConditionalPass { assumed: 0, mandated: 1, runtime_checked: 0, contract_panics: 0 };
    for decision in [Pass, conditional, Inconclusive, Fail] {
        assert_eq!(apply_coverage_gate(decision, complete.as_ref(), true), decision);
    }
    // Absent row (an OLDER compiler): strict proof claims fail closed, while an
    // explicit advisory compatibility lane may retain the underlying decision.
    let unknown = aggregate_coverage(&[]);
    assert_eq!(unknown, None);
    for decision in [Pass, conditional, Inconclusive, Fail] {
        let strict_expected = if decision.is_success() { Inconclusive } else { decision };
        assert_eq!(apply_coverage_gate(decision, unknown.as_ref(), true), strict_expected);
        assert_eq!(apply_coverage_gate(decision, unknown.as_ref(), false), decision);
    }
}

#[test]
fn coverage_aggregate_never_nets_shortfall_against_overcount() {
    // Multi-package authenticated Cargo run: one crate's
    // over-count (5/4) must not hide the other crate's shortfall (3/4) even
    // though the summed counts balance (8/8). Fail-closed: any incomplete row
    // makes the aggregate incomplete.
    let aggregate = aggregate_coverage(&[coverage_row("a", 4, 5), coverage_row("b", 4, 3)])
        .expect("rows present");
    assert_eq!(aggregate.eligible, 8);
    assert_eq!(aggregate.processed, 8);
    assert!(!aggregate.coverage_complete);
    assert_eq!(
        apply_coverage_gate(GateDecision::Pass, Some(&aggregate), true),
        GateDecision::Inconclusive
    );
}

#[test]
fn coverage_overcount_and_aggregate_overflow_are_incomplete() {
    let overcount = aggregate_coverage(&[coverage_row("over", 1, 2)]).unwrap();
    assert!(
        !overcount.coverage_complete,
        "processed > eligible is impossible for compiler set accounting and must fail closed"
    );
    assert_eq!(
        apply_coverage_gate(GateDecision::Pass, Some(&overcount), true),
        GateDecision::Inconclusive
    );

    let overflow = aggregate_coverage(&[
        coverage_row("large", usize::MAX, usize::MAX),
        coverage_row("extra", 1, 1),
    ])
    .unwrap();
    assert_eq!(overflow.eligible, usize::MAX);
    assert_eq!(overflow.processed, usize::MAX);
    assert!(
        !overflow.coverage_complete,
        "integer overflow in aggregate accounting must demote rather than wrap or panic"
    );
}

#[test]
fn parse_compiler_stderr_collects_coverage_summary_rows() {
    // The compiler's coverage row must land in `coverage_rows` — structured
    // transport, not an unsupported-message or malformed Unknown row.
    let parsed = parse_transport_message(trust_types::TransportMessage::CoverageSummary(
        coverage_row("demo", 12, 9),
    ));
    assert_eq!(parsed.coverage_rows, vec![coverage_row("demo", 12, 9)]);
    assert!(
        parsed.verification_results.is_empty(),
        "a coverage row is accounting, never an obligation row: {:?}",
        parsed.verification_results
    );
}

#[test]
fn parse_compiler_stderr_without_coverage_row_reports_coverage_unknown() {
    // Back-compat: an OLD compiler emits function rows but no coverage row —
    // parsing must not break, and the absence must surface as coverage-unknown.
    let func = trust_types::FunctionTransportResult {
        function: "crate::f".into(),
        package_name: None,
        crate_name: None,
        primary_package: false,
        verification_session: String::new(),
        results: vec![],
        proved: 0,
        failed: 0,
        unknown: 0,
        timed_out: 0,
        skipped: 0,
        runtime_checked: 0,
        cached: 0,
        total: 0,
    };
    let parsed = parse_transport_message(trust_types::TransportMessage::FunctionResult(func));
    assert!(parsed.coverage_rows.is_empty());
    assert_eq!(aggregate_coverage(&parsed.coverage_rows), None);
}

#[test]
#[test]
fn gate_strict_tolerates_runtime_checked_but_nothing_else() {
    // The completeness-gap ruling (Andrew, 2026-07-25) in one test.
    //
    // A `runtime_checked` row is an obligation the compiler could not prove
    // statically but whose operation KEEPS the check rustc already emits — the
    // shipped program has vanilla Rust semantics, so the default lane reports it
    // and passes. EVERY other non-proved bucket stays fatal, and `--certify`
    // restores the historical all-buckets-fatal predicate.
    //
    // This is the assertion that would catch a regression in either direction:
    // silently re-failing the ratified case, or silently widening tolerance to a
    // bucket with no runtime fallback.
    let rc_only = oc(1, 0, 0, 1, 0, 0);
    assert!(
        evaluate_verification_gate(GateLane::Strict, 0, rc_only).is_success(),
        "default lane must PASS on a runtime-checked-only gap"
    );
    assert!(
        !evaluate_verification_gate(GateLane::Certify, 0, rc_only).is_success(),
        "--certify must still FAIL on it: shipping requires full static discharge"
    );

    // Every other bucket stays fatal under BOTH lanes.
    for (label, counts) in [
        ("failed", oc(1, 1, 0, 0, 0, 0)),
        ("unknown", oc(1, 0, 1, 0, 0, 0)),
        ("assumed", oc(1, 0, 0, 0, 1, 0)),
        ("mandated", oc(1, 0, 0, 0, 0, 1)),
    ] {
        assert!(
            !evaluate_verification_gate(GateLane::Strict, 0, counts).is_success(),
            "default lane must still fail on `{label}` — it has no runtime fallback"
        );
        assert!(
            !evaluate_verification_gate(GateLane::Certify, 0, counts).is_success(),
            "certify lane must fail on `{label}`"
        );
    }

    // A nonzero compiler exit is fatal regardless of buckets, in both lanes.
    for lane in [GateLane::Strict, GateLane::Certify] {
        assert!(
            !evaluate_verification_gate(lane, 1, rc_only).is_success(),
            "a nonzero compiler exit is always fatal"
        );
    }
}

fn gate_certify_is_byte_identical_to_compiler_verification_success() {
    // MIGRATED from `gate_strict_*` by the completeness-gap ruling (2026-07-25):
    // the historical predicate is now the CERTIFY lane. The default `Strict` lane
    // deliberately no longer fails on `runtime_checked` — pinned separately below.
    // The certify lane's is_success() must equal the historical predicate
    // `compiler_verification_success(exit, T, F, U + A + M, RC)` across the
    // whole bucket matrix — A, M, RC, U, T=0, F, E!=0 must all fail.
    for exit in [0, 1, 101] {
        for proved in 0..=2 {
            for failed in 0..=2 {
                for unknown in 0..=1 {
                    for rc in 0..=1 {
                        for assumed in 0..=1 {
                            for mandated in 0..=1 {
                                let counts = oc(proved, failed, unknown, rc, assumed, mandated);
                                let gate =
                                    evaluate_verification_gate(GateLane::Certify, exit, counts)
                                        .is_success();
                                let legacy = compiler_verification_success(
                                    exit,
                                    counts.total,
                                    failed,
                                    unknown + assumed + mandated,
                                    rc,
                                );
                                assert_eq!(gate, legacy, "mismatch exit={exit} counts={counts:?}");
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn gate_certify_pins_historical_predicate_rows() {
    // Byte-identical to the historical `compiler_verification_success` rows
    // (see `compiler_verification_success_requires_nonzero_obligations`), plus
    // the new assumed / mandated / runtime-checked fail cases.
    let ok = |exit, counts: OutcomeCounts| {
        evaluate_verification_gate(GateLane::Certify, exit, counts).is_success()
    };
    assert!(!ok(0, oc(0, 0, 0, 0, 0, 0))); // total == 0
    assert!(ok(0, oc(1, 0, 0, 0, 0, 0))); // one proved
    assert!(!ok(1, oc(1, 0, 0, 0, 0, 0))); // nonzero exit
    assert!(!ok(0, oc(0, 1, 0, 0, 0, 0))); // one failed
    assert!(!ok(0, oc(0, 0, 1, 0, 0, 0))); // one unknown
    assert!(!ok(0, oc(0, 0, 0, 1, 0, 0))); // one runtime-checked
    assert!(!ok(0, oc(0, 0, 0, 0, 1, 0))); // one assumed
    assert!(!ok(0, oc(0, 0, 0, 0, 0, 1))); // one mandated
}

#[test]
fn partition_three_way_splits_inconclusive_rows_disjointly() {
    let rows = vec![
        gate_row("overflow:add", VerificationOutcome::Proved, ""),
        gate_row("div_by_zero", VerificationOutcome::Failed, ""),
        gate_row("bounds", VerificationOutcome::RuntimeChecked, ""),
        gate_row("postcondition", VerificationOutcome::Unknown, ""),
        gate_row("assumption:coroutine", VerificationOutcome::Unknown, ""),
        gate_row("hardened_process_semantics", VerificationOutcome::Unknown, &mandate_raw_line()),
    ];
    let (counts, defects) = partition_outcome_counts(&rows);
    assert_eq!(counts.total, 6);
    assert_eq!(counts.proved, 1);
    assert_eq!(counts.failed, 1);
    assert_eq!(counts.runtime_checked, 1);
    assert_eq!(counts.unknown, 1, "only the non-assumption non-mandate inconclusive row");
    assert_eq!(counts.assumed, 1);
    assert_eq!(counts.mandated, 1);
    assert!(defects.is_empty());
    // Buckets are disjoint and cover every row (also asserted by the internal
    // debug_assert in partition_outcome_counts).
    assert_eq!(
        counts.proved
            + counts.failed
            + counts.runtime_checked
            + counts.unknown
            + counts.assumed
            + counts.mandated,
        counts.total,
    );
}

#[test]
fn partition_fails_closed_on_defective_assumption_rows() {
    // An `assumption:*` row claiming PROVED or RUNTIME-CHECKED must never get
    // proof credit — it is counted as a genuine unknown plus a transport-defect
    // diagnostic. When in doubt, a row is `unknown`, never `assumed`.
    let rows = vec![
        gate_row("assumption:coroutine", VerificationOutcome::Proved, ""),
        gate_row("assumption:extern-call", VerificationOutcome::RuntimeChecked, ""),
        gate_row("assumption:pattern-type", VerificationOutcome::Unknown, ""),
    ];
    let (counts, defects) = partition_outcome_counts(&rows);
    assert_eq!(counts.total, 3);
    assert_eq!(counts.proved, 0, "a defective assumption must not count as proved");
    assert_eq!(
        counts.runtime_checked, 0,
        "a defective assumption must not count as runtime-checked"
    );
    assert_eq!(counts.assumed, 1, "only the genuinely inconclusive assumption row is assumed");
    assert_eq!(counts.unknown, 2, "both defective rows fail closed to unknown");
    assert_eq!(defects.len(), 2, "one transport-defect diagnostic per defective row");
}

// --- Trust (T9 contract-panic) partition + gate tests ---

#[test]
fn partition_counts_contract_panic_rows_into_their_own_bucket() {
    // A FAILED `contract-panic:` row (the compiler's rewrite of an annotated,
    // message-matched panic refutation) lands in the contract_panics bucket —
    // NOT failed, NOT assumed, NOT proof credit — while everything else keeps
    // its bucket. The `contract-panic-unused` kind (dash, not colon) must fall
    // through as a genuine FAILURE.
    let rows = vec![
        gate_row("overflow:add", VerificationOutcome::Proved, ""),
        gate_row("contract-panic:matched", VerificationOutcome::Failed, ""),
        gate_row("contract-panic-unused", VerificationOutcome::Failed, ""),
    ];
    let (counts, defects) = partition_outcome_counts(&rows);
    assert_eq!(counts.total, 3);
    assert_eq!(counts.proved, 1);
    assert_eq!(counts.contract_panics, 1, "the contract-panic: row is its own bucket");
    assert_eq!(
        counts.failed, 1,
        "contract-panic-unused is a genuine failure, never a conditional-pass bucket"
    );
    assert_eq!(counts.assumed, 0);
    assert_eq!(counts.unknown, 0);
    assert!(defects.is_empty());
    // Disjoint + covering (also enforced by the internal debug_assert).
    assert_eq!(
        counts.proved
            + counts.failed
            + counts.runtime_checked
            + counts.unknown
            + counts.assumed
            + counts.mandated
            + counts.contract_panics,
        counts.total,
    );
}

#[test]
fn partition_fails_closed_on_defective_contract_panic_rows() {
    // Fail-closed clause copied from the assumption rows: a `contract-panic:`
    // row claiming PROVED or RUNTIME-CHECKED would launder an intentional
    // reachable panic into proof credit. It must count as a genuine unknown
    // plus a transport defect — never contract_panics, never proved.
    let rows = vec![
        gate_row("contract-panic:matched", VerificationOutcome::Proved, ""),
        gate_row("contract-panic:matched", VerificationOutcome::RuntimeChecked, ""),
        gate_row("contract-panic:matched", VerificationOutcome::Failed, ""),
    ];
    let (counts, defects) = partition_outcome_counts(&rows);
    assert_eq!(counts.total, 3);
    assert_eq!(counts.proved, 0, "a defective contract-panic row must not count as proved");
    assert_eq!(counts.runtime_checked, 0);
    assert_eq!(counts.contract_panics, 1, "only the honest failed row is a contract panic");
    assert_eq!(counts.unknown, 2, "both defective rows fail closed to unknown");
    assert_eq!(defects.len(), 2, "one transport-defect diagnostic per defective row");
}

#[test]
fn gate_advisory_lane_contract_panics_conditional_pass() {
    use GateDecision::*;
    // A run whose only non-proved rows are contract panics: ConditionalPass
    // (exit 0), with the count visible in the decision.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc_cp(oc(1, 0, 0, 0, 0, 0), 1)),
        ConditionalPass { assumed: 0, mandated: 0, runtime_checked: 0, contract_panics: 1 }
    );
    // Mixed with an assumption: both counts carried.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc_cp(oc(0, 0, 0, 0, 1, 0), 2)),
        ConditionalPass { assumed: 1, mandated: 0, runtime_checked: 0, contract_panics: 2 }
    );
    // A genuine failure alongside a contract panic still FAILS (cannot-mask).
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc_cp(oc(1, 1, 0, 0, 0, 0), 1)),
        Fail
    );
    // A genuine unknown alongside a contract panic stays Inconclusive.
    assert_eq!(
        evaluate_verification_gate(GateLane::Advisory, 0, oc_cp(oc(1, 0, 1, 0, 0, 0), 1)),
        Inconclusive
    );
}

#[test]
fn gate_strict_lane_folds_contract_panics_to_failure() {
    use GateDecision::*;
    // STRICT lane: a contract-panic row can never (conditionally) pass — it
    // folds into the non-proved sum exactly like assumed/mandated/runtime-
    // checked, yielding a nonzero exit. (The compiler never mints the row in
    // the strict lane; this pins the fail-closed behavior if one ever arrives.)
    let counts = oc_cp(oc(1, 0, 0, 0, 0, 0), 1);
    let decision = evaluate_verification_gate(GateLane::Strict, 0, counts);
    assert_eq!(decision, Inconclusive, "strict lane must fold contract panics to failure");
    assert!(!decision.is_success());
    // And with contract_panics == 0 the strict arm is byte-identical to the
    // historical predicate (already pinned exhaustively by
    // `gate_strict_is_byte_identical_to_compiler_verification_success`).
    assert_eq!(evaluate_verification_gate(GateLane::Strict, 0, oc(1, 0, 0, 0, 0, 0)), Pass);
}

#[test]
#[cfg(unix)]
fn run_compiler_reports_artifact_gate_failure() {
    let root = temp_test_dir("render-failure-cache-store");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fake bin dir");
    let fake_compiler = bin_dir.join("trustc");
    fs::write(
        &fake_compiler,
        "#!/bin/sh\nprintf '%s\\n' 'TRUST_JSON:{\"type\":\"function_result\",\"function\":\"fixture::ok\",\"results\":[{\"kind\":\"postcondition\",\"description\":\"postcondition proved\",\"outcome\":\"proved\",\"solver\":\"fake\",\"time_ms\":0}],\"proved\":1,\"failed\":0,\"unknown\":0,\"runtime_checked\":0,\"total\":1}' >&2\nexit 0\n",
    )
    .expect("write fake compiler");
    {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = fs::metadata(&fake_compiler).expect("fake compiler metadata").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&fake_compiler, perms).expect("chmod fake compiler");
    }
    let blocked_report_dir = root.join("blocked-report-dir");
    fs::write(&blocked_report_dir, "not a directory").expect("block report artifact directory");

    let cmd_args = vec![fake_compiler.display().to_string()];
    let report_dir = blocked_report_dir.to_str().expect("report dir utf-8");
    let status = run_compiler(CompilerRun {
        cmd_args: &cmd_args,
        rustc_path: &fake_compiler,
        config: &TrustConfig::default(),
        selected_codegen_backend: None,
        supports_json_transport: true,
        strict_artifact_policy: false,
        strict_result_gate: false,
        certify_gate: false,
        allow_l0_gaps: false,
        memory_safe_policy: false,
        survey: false,
        hardened: false,
        trust_profile: None,
        ay_path: None,
        format: OutputFormat::Terminal,
        report_dir: Some(report_dir),
        unsafe_memory_report: None,
        live_report_consumer: None,
        render_output: true,
        ephemeral_single_file_output: false,
    });

    assert_eq!(
        status,
        ExitCode::from(2),
        "report artifact failure should be a setup/evidence error"
    );
    let _ = fs::remove_dir_all(root);
}

#[test]
fn live_report_consumer_rejects_an_active_cargo_exclusion_before_proof_reduction() {
    let excluded = trust_types::CargoProofUnitReport {
        package_id: "path+file:///workspace#root@0.1.0".into(),
        package_name: "root".into(),
        target_name: "build-script-build".into(),
        target_kinds: vec!["custom-build".into()],
        compile_target: "x86_64-unknown-linux-gnu".into(),
        compile_target_spec_sha256: None,
        proof_unit_index: 7,
        proof_unit_mode: "run-custom-build".into(),
        proof_unit_role: "excluded".into(),
        graph_role: "control".into(),
        exclusion_reason: Some(
            super::transport::TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION.into(),
        ),
        semantics_sha256: None,
        semantics: None,
    };
    let inventory = trust_types::CargoProofInventoryReport {
        schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1.into(),
        include_dependencies: true,
        declared: trust_types::CargoProofUnitPartitions::default(),
        completed: trust_types::CargoProofUnitPartitions::default(),
        covered: trust_types::CargoProofUnitPartitions::default(),
        excluded_active_units: vec![excluded],
    };
    let empty = std::collections::BTreeSet::new();
    let reason = live_report_consumer_rejection(
        true,
        0,
        None,
        Some(&inventory),
        None,
        &[],
        false,
        &empty,
        &empty,
        &empty,
        &empty,
    )
    .expect("active Cargo exclusion must withhold every live proof consumer");

    assert!(reason.contains("excluded 1 active Unit(s)"), "{reason}");
    assert!(reason.contains("path+file:///workspace#root@0.1.0"), "{reason}");
    assert!(reason.contains("unit_index=7"), "{reason}");
    assert!(
        reason.contains(super::transport::TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION),
        "{reason}"
    );
}

#[test]
#[cfg(unix)]
fn live_report_consumer_cannot_override_early_proof_followed_by_ice() {
    let root = temp_test_dir("live-report-ice-prefix");
    fs::create_dir_all(&root).expect("create test root");
    let fake_compiler = root.join("trustc");
    fs::write(
        &fake_compiler,
        "#!/bin/sh\nsession=''\nfor arg in \"$@\"; do\n  case \"$arg\" in\n    trust-verify-session=*) session=${arg#trust-verify-session=} ;;\n  esac\ndone\nprintf '%s%s%s\\n' 'TRUST_JSON:{\"type\":\"function_result\",\"function\":\"fixture::early\",\"verification_session\":\"' \"$session\" '\",\"results\":[{\"kind\":\"postcondition\",\"description\":\"early claimed proof\",\"outcome\":\"proved\",\"solver\":\"fake\",\"time_ms\":0}],\"proved\":1,\"failed\":0,\"unknown\":0,\"runtime_checked\":0,\"total\":1}' >&2\nexit 101\n",
    )
    .expect("write fake compiler");
    {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = fs::metadata(&fake_compiler).expect("fake compiler metadata").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&fake_compiler, perms).expect("chmod fake compiler");
    }
    let source = root.join("fixture.rs");
    fs::write(&source, "fn main() {}\n").expect("write source fixture");
    let cmd_args = vec![fake_compiler.display().to_string(), source.display().to_string()];
    let mut consumer_called = false;
    let mut consumer = |_live: &crate::report::LiveCanonicalReport| {
        consumer_called = true;
        Ok(())
    };

    let status = run_compiler(CompilerRun {
        cmd_args: &cmd_args,
        rustc_path: &fake_compiler,
        config: &TrustConfig::default(),
        selected_codegen_backend: None,
        supports_json_transport: true,
        strict_artifact_policy: false,
        strict_result_gate: false,
        certify_gate: false,
        allow_l0_gaps: false,
        memory_safe_policy: false,
        survey: false,
        hardened: false,
        trust_profile: None,
        ay_path: None,
        format: OutputFormat::Terminal,
        report_dir: None,
        unsafe_memory_report: None,
        live_report_consumer: Some(&mut consumer),
        render_output: false,
        ephemeral_single_file_output: false,
    });
    drop(consumer);

    assert_eq!(status, ExitCode::from(101), "the compiler ICE status must be preserved");
    assert!(!consumer_called, "an early proof prefix must not reach a live proof consumer");
    let _ = fs::remove_dir_all(root);
}

#[test]
#[cfg(unix)]
fn live_report_consumer_cannot_override_early_proof_followed_by_signal() {
    let root = temp_test_dir("live-report-signal-prefix");
    fs::create_dir_all(&root).expect("create test root");
    let fake_compiler = root.join("trustc");
    fs::write(
        &fake_compiler,
        "#!/bin/sh\nsession=''\nfor arg in \"$@\"; do\n  case \"$arg\" in\n    trust-verify-session=*) session=${arg#trust-verify-session=} ;;\n  esac\ndone\nprintf '%s%s%s\\n' 'TRUST_JSON:{\"type\":\"function_result\",\"function\":\"fixture::early\",\"verification_session\":\"' \"$session\" '\",\"results\":[{\"kind\":\"postcondition\",\"description\":\"early claimed proof\",\"outcome\":\"proved\",\"solver\":\"fake\",\"time_ms\":0}],\"proved\":1,\"failed\":0,\"unknown\":0,\"runtime_checked\":0,\"total\":1}' >&2\nkill -TERM $$\n",
    )
    .expect("write fake compiler");
    {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = fs::metadata(&fake_compiler).expect("fake compiler metadata").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&fake_compiler, perms).expect("chmod fake compiler");
    }
    let source = root.join("fixture.rs");
    fs::write(&source, "fn main() {}\n").expect("write source fixture");
    let cmd_args = vec![fake_compiler.display().to_string(), source.display().to_string()];
    let mut consumer_called = false;
    let mut consumer = |_live: &crate::report::LiveCanonicalReport| {
        consumer_called = true;
        Ok(())
    };

    let status = run_compiler(CompilerRun {
        cmd_args: &cmd_args,
        rustc_path: &fake_compiler,
        config: &TrustConfig::default(),
        selected_codegen_backend: None,
        supports_json_transport: true,
        strict_artifact_policy: false,
        strict_result_gate: false,
        certify_gate: false,
        allow_l0_gaps: false,
        memory_safe_policy: false,
        survey: false,
        hardened: false,
        trust_profile: None,
        ay_path: None,
        format: OutputFormat::Terminal,
        report_dir: None,
        unsafe_memory_report: None,
        live_report_consumer: Some(&mut consumer),
        render_output: false,
        ephemeral_single_file_output: false,
    });
    drop(consumer);

    assert_eq!(status, ExitCode::from(128 + 15), "the signal shell status must be preserved");
    assert!(!consumer_called, "a signalled proof prefix must not reach a live proof consumer");
    let _ = fs::remove_dir_all(root);
}

// ---------------------------------------------------------------------------
// Evidence frontend authority is a regular executable, never a redirecting
// filename symlink whose directory can supply different protected siblings.
// ---------------------------------------------------------------------------

#[test]
#[cfg(unix)]
fn test_native_trust_cargo_path_rejects_targo_symlink_and_nonexecutable_file() {
    use std::os::unix::fs::PermissionsExt as _;

    let root = temp_test_dir("targo-symlink-name");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fixture bin dir");
    let trustc = bin_dir.join("trustc");
    write_executable_marker(&trustc);
    let cargo = bin_dir.join("cargo");
    write_executable_marker(&cargo);
    let targo = bin_dir.join("targo");
    std::os::unix::fs::symlink(&cargo, &targo).expect("create targo symlink");

    let symlink_error = native_trust_cargo_path(&trustc)
        .expect_err("redirecting targo symlink cannot become evidence frontend authority");
    assert!(symlink_error.contains("missing or not executable"), "{symlink_error}");

    fs::remove_file(&targo).expect("remove targo symlink");
    fs::write(&targo, b"nonexecutable frontend").expect("write nonexecutable targo");
    fs::set_permissions(&targo, fs::Permissions::from_mode(0o644))
        .expect("make targo nonexecutable");
    let nonexec_error = native_trust_cargo_path(&trustc)
        .expect_err("nonexecutable targo cannot become evidence frontend authority");
    assert!(nonexec_error.contains("missing or not executable"), "{nonexec_error}");

    let _ = fs::remove_dir_all(root);
}

// ---------------------------------------------------------------------------
// Tier-1 dogfooding fix 2: a crate-mode check with zero per-function
// TRUST_JSON rows is a hard setup error, never a plausible report
// (docs/dogfooding-wishlist-2026-06-10.md item 2 / issue #4).
// ---------------------------------------------------------------------------

fn transport_placeholder_row() -> VerificationResult {
    VerificationResult {
        function: "<transport>".into(),
        kind: "transport:missing-json".into(),
        message: "missing structured Trust JSON transport".into(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".into(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    }
}

#[test]
fn test_missing_trust_json_diagnostic_flags_transport_only_runs() {
    let diagnostic = missing_trust_json_diagnostic(
        true,
        &[transport_placeholder_row()],
        &Default::default(),
        false,
    )
    .expect("crate-mode run with only synthetic transport rows must hard-error");
    assert!(
        diagnostic.contains("no per-function TRUST_JSON"),
        "diagnostic should say verification did not run: {diagnostic}"
    );
    assert!(
        diagnostic.contains("Likely causes"),
        "diagnostic should name likely causes: {diagnostic}"
    );
    assert!(
        diagnostic.contains("trust-verify")
            && diagnostic.contains("compiler-session rustflag")
            && diagnostic.contains("not accepted as proof evidence"),
        "diagnostic should name nonce invalidation and rule out a silently reused warm cache: {diagnostic}"
    );

    assert!(
        missing_trust_json_diagnostic(true, &[], &Default::default(), false).is_some(),
        "crate-mode run with zero rows of any kind must also hard-error"
    );
}

#[test]
fn test_missing_trust_json_diagnostic_requires_authenticated_single_file_evidence() {
    let per_function_row = VerificationResult {
        function: "fixture::ok".into(),
        kind: "postcondition".into(),
        outcome: VerificationOutcome::Proved,
        ..transport_placeholder_row()
    };
    assert_eq!(
        missing_trust_json_diagnostic(
            true,
            std::slice::from_ref(&per_function_row),
            &Default::default(),
            false,
        ),
        None,
        "a real per-function row is evidence that verification ran"
    );
    assert!(
        missing_trust_json_diagnostic(
            false,
            &[transport_placeholder_row()],
            &Default::default(),
            false,
        )
        .is_some(),
        "a synthetic placeholder must not make an advisory single-file run pass"
    );
    assert_eq!(
        missing_trust_json_diagnostic(false, &[], &Default::default(), true),
        None,
        "an authenticated coverage summary proves a valid empty single-file run executed"
    );

    let completed = [CargoTargetIdentity {
        package_id: "path+file:///fixture#package@0.1.0".to_string(),
        package_name: "package".to_string(),
        target_name: "empty_lib".to_string(),
        target_kinds: vec!["lib".to_string()],
        compile_target: "x86_64-unknown-linux-gnu".to_string(),
        compile_mode: "build".to_string(),
        compile_kind: "target".to_string(),
        unit_identity_sha256: "c".repeat(64),
        compile_target_spec_sha256: None,
        proof_unit_index: 0,
        proof_unit_mode: "test".to_string(),
        proof_unit_role: "primary".to_string(),
        semantics_sha256: "a".repeat(64),
    }]
    .into_iter()
    .collect();
    assert_eq!(
        missing_trust_json_diagnostic(true, &[], &completed, false),
        None,
        "a terminal primary-target inventory proves trustc ran even when the crate has zero functions"
    );
}

#[test]
fn single_file_report_subject_uses_canonical_source_identity() {
    let root = temp_test_dir("single-file-report-subject");
    let first = root.join("first");
    let second = root.join("second");
    fs::create_dir_all(&first).expect("create first source root");
    fs::create_dir_all(&second).expect("create second source root");
    let first_source = first.join("same.rs");
    let second_source = second.join("same.rs");
    fs::write(&first_source, "fn main() {}\n").expect("write first source");
    fs::write(&second_source, "fn main() {}\n").expect("write second source");

    let first_subject = single_file_report_subject(&[first_source.display().to_string()])
        .expect("canonicalize first subject");
    let second_subject = single_file_report_subject(&[second_source.display().to_string()])
        .expect("canonicalize second subject");
    assert_ne!(first_subject, second_subject);
    assert!(first_subject.contains("/first/same.rs"), "{first_subject}");
    assert!(second_subject.contains("/second/same.rs"), "{second_subject}");

    let _ = fs::remove_dir_all(root);
}

#[test]
#[cfg(unix)]
fn single_file_report_subject_rejects_lossy_non_utf8_canonical_identity() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    // macOS rejects non-UTF-8 filenames at the filesystem boundary. Exercise
    // the canonical-identity formatter directly so the fail-closed policy is
    // portable across Unix hosts instead of depending on filesystem support.
    let canonical = PathBuf::from(OsString::from_vec(b"/non-utf8-\xff/source.rs".to_vec()));
    let error = canonical_single_file_report_subject(&canonical)
        .expect_err("lossy canonical report identity must fail closed");
    assert!(error.contains("not valid UTF-8"), "{error}");
}

#[test]
#[cfg(unix)]
fn test_run_compiler_crate_mode_without_trust_json_rows_is_hard_error() {
    let root = temp_test_dir("crate-mode-missing-json");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fake bin dir");
    let fake_trustc = bin_dir.join("trustc");
    write_executable_marker(&fake_trustc);
    // A fake sibling targo that truthfully answers the metadata preflight, then
    // "succeeds" at the build while emitting zero TRUST_JSON rows — the exact
    // silent no-op observed in the first sustained dogfooding run. The
    // metadata branch ensures this test reaches the intended transport gate;
    // an earlier version passed only because unrelated setup failed with the
    // same numeric exit code.
    let fake_targo = bin_dir.join("targo");
    let manifest_path = root.join("Cargo.toml");
    fs::write(
        &manifest_path,
        "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    let package_id = format!("path+file://{}#fixture@0.1.0", root.display());
    let metadata_path = root.join("metadata.json");
    fs::write(
        &metadata_path,
        serde_json::to_vec(&serde_json::json!({
            "packages": [{
                "id": package_id,
                "name": "fixture",
                "version": "0.1.0",
                "manifest_path": manifest_path,
            }],
            "workspace_members": [package_id],
            "workspace_default_members": [package_id],
            "target_directory": root.join("target"),
        }))
        .expect("serialize fixture metadata"),
    )
    .expect("write fixture metadata");
    fs::write(
        &fake_targo,
        format!(
            "#!/bin/sh\nif [ \"$1\" = \"metadata\" ]; then\n  cat \"{}\"\n  exit 0\nfi\nexit 0\n",
            metadata_path.display()
        ),
    )
    .expect("write fake targo");
    {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = fs::metadata(&fake_targo).expect("fake targo metadata").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&fake_targo, perms).expect("chmod fake targo");
    }

    let cmd_args = vec![fake_targo.display().to_string(), "build".to_string()];
    let report_dir = root.join("report");
    let report_dir_str = report_dir.to_str().expect("report dir utf-8");
    let status = run_compiler(CompilerRun {
        cmd_args: &cmd_args,
        rustc_path: &fake_trustc,
        config: &TrustConfig::default(),
        selected_codegen_backend: None,
        supports_json_transport: true,
        strict_artifact_policy: false,
        strict_result_gate: false,
        certify_gate: false,
        allow_l0_gaps: false,
        memory_safe_policy: false,
        survey: false,
        hardened: false,
        trust_profile: None,
        ay_path: None,
        format: OutputFormat::Terminal,
        report_dir: Some(report_dir_str),
        unsafe_memory_report: None,
        live_report_consumer: None,
        render_output: true,
        ephemeral_single_file_output: false,
    });

    assert_eq!(
        status,
        ExitCode::from(2),
        "crate-mode run with no per-function TRUST_JSON rows must exit as a hard setup error"
    );
    let persisted: serde_json::Value = serde_json::from_slice(
        &fs::read(report_dir.join("report.json")).expect("read persisted missing-json report"),
    )
    .expect("persisted missing-json report should be valid JSON");
    assert_eq!(
        persisted["verification_gate"]["exit_code"],
        serde_json::json!(2),
        "the authenticated report gate must record the exact process setup-error exit"
    );
    let _ = fs::remove_dir_all(root);
}

#[test]
#[cfg(unix)]
fn cargo_selection_rejects_a_frontend_that_is_not_the_compiler_sibling() {
    let root = temp_test_dir("cargo-selection-sibling-identity");
    let selected_bin = root.join("selected/bin");
    let other_bin = root.join("other/bin");
    fs::create_dir_all(&selected_bin).expect("create selected bin");
    fs::create_dir_all(&other_bin).expect("create other bin");
    let trustc = selected_bin.join("trustc");
    let sibling_targo = selected_bin.join("targo");
    let other_targo = other_bin.join("targo");
    write_executable_marker(&trustc);
    write_executable_marker(&sibling_targo);
    write_executable_marker(&other_targo);

    let error = resolve_cargo_selection_for_compiler(
        &[],
        &trustc,
        other_targo.to_str().expect("other targo path utf-8"),
    )
    .expect_err("metadata frontend must be the selected compiler's exact sibling");
    assert!(error.contains("not the authenticated sibling"), "{error}");
    let _ = fs::remove_dir_all(root);
}

// ---------------------------------------------------------------------------
// Cargo children execute the exact selected Trust compiler. Compatibility
// aliases are not a second compiler-authority surface.
// ---------------------------------------------------------------------------

#[test]
fn test_cargo_child_rustc_path_ignores_same_bytes_and_same_file_aliases() {
    let root = temp_test_dir("child-rustc-canonical");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fixture bin dir");
    let trustc = bin_dir.join(host_executable_name("trustc"));
    write_executable_marker(&trustc);
    let rustc = bin_dir.join(host_executable_name("rustc"));
    write_executable_marker(&rustc);

    assert_eq!(
        cargo_child_rustc_path(&trustc),
        trustc,
        "an equal-bytes rustc alias must not replace canonical trustc"
    );

    fs::remove_file(&rustc).expect("remove equal-bytes alias");
    fs::hard_link(&trustc, &rustc).expect("create same-file alias");

    assert_eq!(
        cargo_child_rustc_path(&trustc),
        trustc,
        "a same-file rustc alias must not change the executed path"
    );

    let _ = fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_cargo_child_rustc_path_ignores_compatibility_symlink() {
    use std::os::unix::fs::symlink;

    let root = temp_test_dir("child-rustc-bound-symlink");
    let bin_dir = root.join("bin");
    fs::create_dir_all(&bin_dir).expect("create fixture bin dir");
    let trustc = bin_dir.join(host_executable_name("trustc"));
    let rustc = bin_dir.join(host_executable_name("rustc"));
    write_executable_marker(&trustc);
    symlink(host_executable_name("trustc"), &rustc).expect("create compatibility symlink");

    assert_eq!(
        cargo_child_rustc_path(&trustc),
        trustc,
        "a compatibility symlink must not replace canonical trustc"
    );

    let _ = fs::remove_dir_all(root);
}

fn linked_toolchain_status(path: Option<PathBuf>) -> LinkedTrustToolchainStatus {
    LinkedTrustToolchainStatus {
        status: if path.is_some() {
            LinkedTrustToolchainStatusKind::Visible
        } else {
            LinkedTrustToolchainStatusKind::Missing
        },
        rustc: path,
        detail: None,
    }
}

fn write_executable_marker(path: &Path) {
    std::fs::write(path, "").expect("should create executable marker");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = std::fs::metadata(path).expect("marker metadata").permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(path, perms).expect("should chmod executable marker");
    }
}

fn write_required_surface_tool_markers(bin_dir: &Path) {
    for spec in LINKED_TRUST_SURFACE_TOOLS.iter().filter(|spec| spec.required) {
        write_executable_marker(&bin_dir.join(host_executable_name(spec.name)));
        for alias in spec.required_compatibility_aliases {
            write_executable_marker(&bin_dir.join(host_executable_name(alias)));
        }
    }
}

fn surface_tool<'a>(
    status: &'a LinkedTrustCargoSurfaceStatus,
    name: &str,
) -> &'a LinkedTrustSurfaceToolStatus {
    status
        .required_tools
        .iter()
        .chain(status.optional_tools.iter())
        .find(|tool| tool.name == name)
        .unwrap_or_else(|| panic!("missing surface tool status for {name}: {status:?}"))
}

#[test]
fn parse_compiler_stderr_preserves_native_notes_but_fails_closed_without_typed_kind() {
    let transport =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function: "crate::checked_contract".into(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            timed_out: 0,
            skipped: 0,
            results: vec![trust_types::TransportObligationResult {
                obligation_id: Some("trust_ir-native-trust_wp-request-req-7-proof-42".into()),
                claim_digest_sha256: None,
                kind: "unknown".into(),
                typed_kind: None,
                description: "unsupported MIR `FullVerification::Contract`: contract_id=requires:0"
                    .into(),
                location: None,
                outcome: trust_types::Outcome::Proved,
                solver: "trust-full-verifier".into(),
                time_ms: 0,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                    suite: "trust-wp".into(),
                    backend: "trust-full-verifier".into(),
                    request_id: Some("req-7".into()),
                    native_id: Some("proof-42".into()),
                    present: true,
                    artifacts: vec![trust_types::TransportEvidenceArtifact {
                        kind: "native_trust_ir".into(),
                        format: Some("trust_ir-json".into()),
                        artifact_id: Some("trust_ir-artifact-42".into()),
                        digest: None,
                        uri: Some("artifact://native-trust-ir/trust-wp/42".into()),
                        materialization: None,
                        metadata: Some(serde_json::json!({
                            "suite": "trust-wp",
                            "native_trust_ir": {
                                "request_id": "req-7",
                                "proof_obligation_id": 42
                            }
                        })),
                    }],
                    diagnostics: Vec::new(),
                }),
                proof_evidence: Some(trust_types::TransportProofEvidence {
                    suite: "trust-wp".into(),
                    backend: "trust-full-verifier".into(),
                    request_id: Some("req-7".into()),
                    proof_id: Some("proof-42".into()),
                    native_id: Some("proof-42".into()),
                    status: trust_types::TransportProofStatus::Proved,
                    strength: Some(trust_types::ProofStrength::deductive()),
                    evidence: Some(trust_types::ProofEvidence::from(
                        trust_types::ProofStrength::deductive(),
                    )),
                    artifacts: Vec::new(),
                    diagnostics: Vec::new(),
                }),
                monitor: None,
            }],
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
    let transport_json = serde_json::to_string(&transport).expect("serialize transport");
    let stderr = concat!(
        "note: native full verifier status: Proved; requested=1, proved=1\n",
        "note: native full verifier evidence `obligation-1`: trust_wp accepted contract\n",
        "note: unrelated compiler note\n"
    );
    let stderr = format!("{}{}\n{stderr}", trust_types::TRANSPORT_PREFIX, transport_json);

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    assert_eq!(
        parsed.verification_results[0].outcome,
        VerificationOutcome::Unknown,
        "a proof-looking lossy compact tag without exact typed classification must not receive proof credit",
    );
    assert!(
        parsed.verification_results[0]
            .reason
            .as_deref()
            .is_some_and(|reason| reason.contains("omitted the exact typed VC kind"))
    );
    let evidence = crate::types::structured_transport_evidence(&parsed.verification_results[0])
        .expect("structured full-verifier evidence");
    assert_eq!(
        evidence.obligation_id.as_deref(),
        Some("trust_ir-native-trust_wp-request-req-7-proof-42")
    );
    let native_trust_ir = evidence.native_trust_ir.as_ref().expect("native TrustIr evidence");
    assert_eq!(native_trust_ir.suite, "trust-wp");
    assert_eq!(native_trust_ir.request_id.as_deref(), Some("req-7"));
    let proof_evidence = evidence.proof_evidence.as_ref().expect("proof evidence");
    assert_eq!(proof_evidence.suite, "trust-wp");
    assert_eq!(proof_evidence.status, trust_types::TransportProofStatus::Proved);
    assert_eq!(parsed.compiler_diagnostics.len(), 2);
    assert!(parsed.compiler_diagnostics.iter().all(|diagnostic| diagnostic.level == "note"));
    assert!(
        parsed
            .compiler_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("native full verifier status"))
    );
    assert!(
        parsed
            .compiler_diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.message.contains("unrelated compiler note"))
    );
}

fn full_verifier_transport_with_nested_proved(
    outcome: trust_types::Outcome,
) -> trust_types::TransportMessage {
    trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
        function: "crate::cached_contract".into(),
        package_name: None,
        crate_name: None,
        primary_package: false,
        verification_session: String::new(),
        timed_out: 0,
        skipped: 0,
        results: vec![trust_types::TransportObligationResult {
            obligation_id: Some("obl-cache".into()),
            claim_digest_sha256: None,
            kind: "postcondition".into(),
            typed_kind: None,
            description: "cached proof-looking row".into(),
            location: None,
            outcome,
            solver: "trust-full-verifier".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("cache replay row".into()),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-wp".into(),
                backend: "trust-full-verifier".into(),
                request_id: Some("req-cache".into()),
                proof_id: Some("proof-cache".into()),
                native_id: Some("native-cache".into()),
                status: trust_types::TransportProofStatus::Proved,
                strength: Some(trust_types::ProofStrength::deductive()),
                evidence: Some(trust_types::ProofEvidence::from(
                    trust_types::ProofStrength::deductive(),
                )),
                artifacts: Vec::new(),
                diagnostics: Vec::new(),
            }),
            monitor: None,
        }],
        proved: 0,
        failed: 0,
        unknown: 1,
        runtime_checked: 0,
        cached: 0,
        total: 1,
    })
}

fn parse_transport_message(message: trust_types::TransportMessage) -> ParsedCompilerOutput {
    let transport_json = serde_json::to_string(&message).expect("serialize transport");
    let stderr = format!("{}{}\n", trust_types::TRANSPORT_PREFIX, transport_json);
    parse_compiler_stderr(std::io::Cursor::new(stderr), false)
}

#[test]
fn parse_compiler_stderr_rejects_nested_proved_when_transport_unknown() {
    let parsed = parse_transport_message(full_verifier_transport_with_nested_proved(trust_types::Outcome::Unknown));

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "crate::cached_contract");
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.reason.as_deref(), Some("cache replay row"));
    assert!(
        parsed
            .verification_results
            .iter()
            .all(|result| result.kind != "transport:summary-accounting")
    );
}

#[test]
fn parse_compiler_stderr_accumulates_cache_replays() {
    // Trust (verify-cache): a per-function transport record's `cached` count must
    // surface in ParsedCompilerOutput so the report can show a cache hit-rate.
    // Informational only — the per-obligation rows stay conservatively `unknown`.
    let func = trust_types::FunctionTransportResult {
        function: "crate::replayed".into(),
        package_name: None,
        crate_name: None,
        primary_package: false,
        verification_session: String::new(),
        results: vec![],
        proved: 0,
        failed: 0,
        unknown: 2,
        timed_out: 0,
        skipped: 0,
        runtime_checked: 0,
        cached: 2,
        total: 2,
    };
    let parsed = parse_transport_message(trust_types::TransportMessage::FunctionResult(func));
    assert_eq!(parsed.cached_obligations, 2);
}

#[test]
fn parse_compiler_stderr_rejects_nested_proved_when_transport_runtime_checked() {
    let parsed =
        parse_transport_message(full_verifier_transport_with_nested_proved(trust_types::Outcome::RuntimeChecked));

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "crate::cached_contract");
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.reason.as_deref(), Some("cache replay row"));
    assert!(
        parsed
            .verification_results
            .iter()
            .all(|result| result.kind != "transport:summary-accounting")
    );
}

#[test]
fn parse_compiler_stderr_keeps_unsupported_full_verifier_inconclusive() {
    let diagnostic = trust_types::TransportEvidenceDiagnostic {
        code: "full_verifier_evidence".into(),
        severity: trust_types::TransportEvidenceDiagnosticSeverity::Error,
        message: "typed TrustIr native evidence is unavailable".into(),
        detail: Some("native full verifier rejected unsupported lowering".into()),
    };
    let transport =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function: "crate::main".into(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            timed_out: 0,
            skipped: 0,
            results: vec![trust_types::TransportObligationResult {
                obligation_id: Some("vc:main:assertion:0".into()),
                claim_digest_sha256: None,
                kind: "assertion".into(),
                typed_kind: None,
                description: "unsupported MIR `FullVerification::Assertion`".into(),
                location: None,
                outcome: trust_types::Outcome::RuntimeChecked,
                solver: "trust-full-verifier".into(),
                time_ms: 0,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                    suite: "trust-mc".into(),
                    backend: "trust-full-verifier".into(),
                    request_id: None,
                    native_id: None,
                    present: false,
                    artifacts: Vec::new(),
                    diagnostics: vec![diagnostic.clone()],
                }),
                proof_evidence: Some(trust_types::TransportProofEvidence {
                    suite: "trust-mc".into(),
                    backend: "trust-full-verifier".into(),
                    request_id: None,
                    proof_id: None,
                    native_id: None,
                    status: trust_types::TransportProofStatus::Unsupported,
                    strength: None,
                    evidence: None,
                    artifacts: Vec::new(),
                    diagnostics: vec![diagnostic],
                }),
                monitor: None,
            }],
            proved: 0,
            failed: 0,
            unknown: 1,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
    let transport_json = serde_json::to_string(&transport).expect("serialize transport");
    let stderr = format!("{}{}\n", trust_types::TRANSPORT_PREFIX, transport_json);

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.backend, "trust-full-verifier");
    assert!(
        result.reason.as_deref().is_some_and(|reason| {
            reason.contains("typed TrustIr native evidence is unavailable")
        })
    );
}

#[test]
fn parse_compiler_stderr_keeps_results_when_transport_optional_fields_drift() {
    let stderr = format!(
        "{}{}\n",
        trust_types::TRANSPORT_PREFIX,
        serde_json::json!({
            "type": "function_result",
            "function": "midpoint",
            "results": [
                {
                    "kind": "overflow:sub",
                    "description": "arithmetic overflow (Sub)",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 2,
                        "col_start": 8,
                        "line_end": 2,
                        "col_end": 15
                    },
                    "outcome": "failed",
                    "solver": "ay-smtlib",
                    "time_ms": 0,
                    "counterexample": "a = 2147483647, b = -2",
                    "counterexample_model": {
                        "assignments": [
                            ["a", {"future_uint_encoding": 2147483647}],
                            ["b", {"Int": -2}]
                        ]
                    }
                }
            ],
            "proved": 0,
            "failed": 1,
            "unknown": 0,
            "runtime_checked": 0,
            "total": 1
        })
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "midpoint");
    assert_eq!(result.kind, "overflow:sub");
    assert_eq!(result.outcome, VerificationOutcome::Failed);
    assert_eq!(result.backend, "ay-smtlib");
    assert!(result.counterexample.is_none());
    assert_eq!(result.location.as_ref().map(|span| span.file.as_str()), Some("src/lib.rs"));
}

#[test]
fn parse_compiler_stderr_marks_malformed_transport_json_unknown() {
    let stderr = format!("{}{{not-json\n", trust_types::TRANSPORT_PREFIX);

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "<transport>");
    assert_eq!(result.kind, "transport:malformed");
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.backend, "targo-trust");
    assert!(
        result.reason.as_deref().is_some_and(|reason| {
            reason.contains("canonical Trust JSON transport parse failed")
        })
    );
}

#[test]
fn parse_compiler_stderr_does_not_prove_lossy_transport() {
    let stderr = format!(
        "{}{}\n",
        trust_types::TRANSPORT_PREFIX,
        serde_json::json!({
            "type": "function_result",
            "function": "midpoint",
            "results": [
                {
                    "kind": "overflow:add",
                    "description": "arithmetic overflow (Add)",
                    "outcome": "proved",
                    "solver": "ay-smtlib",
                    "time_ms": 0,
                    "counterexample_model": "legacy drift"
                }
            ],
            "proved": 1,
            "failed": 0,
            "unknown": 0,
            "runtime_checked": 0,
            "total": 1
        })
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "midpoint");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.backend, "ay-smtlib");
    assert_eq!(result.raw_line, "targo-trust-lossy-transport");
    assert!(
        result
            .reason
            .as_deref()
            .is_some_and(|reason| { reason.contains("lossy transport cannot prove obligations") })
    );
}

#[test]
fn parse_compiler_stderr_rejects_text_only_proved_when_json_required() {
    let stderr = "note: Trust [test]: test -- PROVED (test, 0ms)\n";

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false)
        .require_structured_json_transport(true);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "<transport>");
    assert_eq!(result.kind, "transport:missing-json");
    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert!(
        result
            .reason
            .as_deref()
            .is_some_and(|reason| reason.contains("human-readable Trust diagnostics cannot prove"))
    );
}

#[test]
fn parse_compiler_stderr_keeps_text_notes_when_json_not_required() {
    let stderr = "note: Trust [test]: test -- PROVED (test, 0ms)\n";

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false)
        .require_structured_json_transport(false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.kind, "test");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
}

#[test]
fn parse_compiler_stderr_adds_unknown_for_unaccounted_function_summary() {
    let stderr = format!(
        "{}{}\n",
        trust_types::TRANSPORT_PREFIX,
        serde_json::json!({
            "type": "function_result",
            "function": "midpoint",
            "results": [
                {
                    "kind": "divzero",
                    "description": "division by zero",
                    "outcome": "proved",
                    "solver": "ay-smtlib",
                    "time_ms": 0
                }
            ],
            "proved": 1,
            "failed": 0,
            "unknown": 1,
            "runtime_checked": 0,
            "total": 2
        })
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 2);
    assert_eq!(parsed.verification_results[0].outcome, VerificationOutcome::Proved);
    let summary = &parsed.verification_results[1];
    assert_eq!(summary.function, "midpoint");
    assert_eq!(summary.kind, "transport:summary-accounting");
    assert_eq!(summary.outcome, VerificationOutcome::Unknown);
    assert!(summary.reason.as_deref().is_some_and(|reason| {
        reason.contains("total rows=1 summary=2") && reason.contains("unknown rows=0 summary=1")
    }));
}

#[test]
fn parse_compiler_stderr_adds_unknown_for_unaccounted_crate_summary() {
    let function = serde_json::json!({
        "type": "function_result",
        "function": "midpoint",
        "crate_name": "demo",
        "results": [
            {
                "kind": "divzero",
                "description": "division by zero",
                "outcome": "proved",
                "solver": "ay-smtlib",
                "time_ms": 0
            }
        ],
        "proved": 1,
        "failed": 0,
        "unknown": 0,
        "runtime_checked": 0,
        "total": 1
    });
    let crate_summary = serde_json::json!({
        "type": "crate_summary",
        "crate_name": "demo",
        "functions_analyzed": 1,
        "functions_verified": 1,
        "total_proved": 1,
        "total_failed": 0,
        "total_unknown": 1,
        "total_runtime_checked": 0,
        "total_obligations": 2
    });
    let stderr = format!(
        "{}{}\n{}{}\n",
        trust_types::TRANSPORT_PREFIX,
        function,
        trust_types::TRANSPORT_PREFIX,
        crate_summary
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 2);
    assert_eq!(parsed.verification_results[0].outcome, VerificationOutcome::Proved);
    let summary = &parsed.verification_results[1];
    assert_eq!(summary.function, "<crate:demo>");
    assert_eq!(summary.kind, "transport:crate-summary-accounting");
    assert_eq!(summary.outcome, VerificationOutcome::Unknown);
    assert!(summary.reason.as_deref().is_some_and(|reason| {
        reason.contains("total rows=1 summary=2") && reason.contains("unknown rows=0 summary=1")
    }));
}

#[test]
fn test_detect_linked_trust_toolchain_reports_trust_roots_only() {
    let status = detect_linked_trust_toolchain();

    if status.is_visible() {
        assert_eq!(status.status, LinkedTrustToolchainStatusKind::Visible);
        assert!(
            status
                .rustc
                .as_deref()
                .and_then(Path::file_name)
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name == "trustc" || (cfg!(windows) && name == "trustc.exe")
                }),
            "visible Trust root must expose canonical trustc: {status:?}"
        );
    } else {
        assert_eq!(status.status, LinkedTrustToolchainStatusKind::Missing);
        assert_eq!(status.detail.as_deref(), Some("Trust product discovery uses only Trust roots"));
        assert!(status.rustc.is_none());
    }
}

#[test]
fn test_detect_linked_trust_cargo_surface_requires_exact_toolchain_tools() {
    let root = temp_test_dir("linked-cargo-surface");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let targo = bin_dir.join(host_executable_name("targo"));
    let targo_trust = bin_dir.join(host_executable_name("targo-trust"));
    write_required_surface_tool_markers(&bin_dir);

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(status.ready, "{status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::InstalledReady);
    assert!(status.same_sysroot);
    assert_eq!(status.sysroot, Some(canonicalize_or_self(root.clone())));
    assert_eq!(status.bin_dir, Some(canonicalize_or_self(bin_dir.clone())));
    assert_eq!(status.targo, Some(canonicalize_or_self(targo.clone())));
    assert_eq!(status.targo_trust, Some(canonicalize_or_self(targo_trust.clone())));
    assert!(status.detail.is_none());
    for expected in [
        "trustc",
        "targo",
        "targo-trust",
        "trustd",
        "trustdoc",
        "trustfmt",
        "targo-fmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
    ] {
        let tool = surface_tool(&status, expected);
        assert_eq!(tool.status, LinkedTrustSurfaceToolStatusKind::Present);
        assert!(tool.path.as_deref().is_some_and(Path::is_absolute));
        assert_eq!(tool.sysroot, Some(canonicalize_or_self(root.clone())));
        assert_eq!(tool.bin_dir, Some(canonicalize_or_self(bin_dir.clone())));
    }
    assert_eq!(
        surface_tool(&status, "trust-miri").status,
        LinkedTrustSurfaceToolStatusKind::OptionalMissing
    );
    assert_eq!(
        surface_tool(&status, "targo-miri").status,
        LinkedTrustSurfaceToolStatusKind::OptionalMissing
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_requires_sibling_trustd() {
    let root = temp_test_dir("linked-cargo-surface-missing-trustd");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    write_required_surface_tool_markers(&bin_dir);
    std::fs::remove_file(bin_dir.join(host_executable_name("trustd")))
        .expect("remove required trustd marker");

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "missing sibling trustd was accepted: {status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Missing);
    let trustd = surface_tool(&status, "trustd");
    assert_eq!(trustd.status, LinkedTrustSurfaceToolStatusKind::Missing);
    assert!(trustd.path.is_none());
    assert!(
        status.detail.as_deref().is_some_and(|detail| {
            detail.contains("missing canonical `trustd`")
                && detail.contains(&bin_dir.display().to_string())
        }),
        "missing-tool detail should bind trustd to the selected Trust root: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_classifies_stage2_ready() {
    let root = temp_test_dir("linked-cargo-surface-stage2");
    let bin_dir = root.join("build").join("host").join("stage2").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage2 bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_required_surface_tool_markers(&bin_dir);

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(status.ready, "{status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Stage2Ready);

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_classifies_stage1_compiler_only() {
    let root = temp_test_dir("linked-cargo-surface-stage1");
    let bin_dir = root.join("build").join("host").join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage1 bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&trustc);
    write_executable_marker(&bin_dir.join(host_executable_name("rustc")));

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready);
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Stage1CompilerOnly);
    assert!(
        status
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("stage1 is compiler-only evidence")),
        "detail should reject stage1 daily-driver evidence: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_classifies_ambient_targo_fallback() {
    let root = temp_test_dir("linked-cargo-surface-ambient");
    let bin_dir = root.join("stage2").join("bin");
    let ambient_bin = root.join("ambient").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage2 bin dir");
    std::fs::create_dir_all(&ambient_bin).expect("should create ambient bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let ambient_targo = ambient_bin.join(host_executable_name("targo"));
    write_executable_marker(&trustc);
    // The selected root must satisfy the trustc rustc-alias contract so the
    // first blocker reached is the ambient-targo classification under test.
    write_executable_marker(&bin_dir.join(host_executable_name("rustc")));
    write_executable_marker(&ambient_targo);

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[ambient_bin]);

    assert!(!status.ready);
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::AmbientFallback);
    assert!(status.targo.is_none());
    assert!(
        status.detail.as_deref().is_some_and(|detail| detail.contains("ambient `targo` exists")),
        "detail should name ambient canonical Trust fallback: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_classifies_missing_canonical_tools() {
    let root = temp_test_dir("linked-cargo-surface-missing");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&trustc);
    write_executable_marker(&bin_dir.join(host_executable_name("rustc")));

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready);
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Missing);
    assert!(
        status.detail.as_deref().is_some_and(|detail| detail.contains("missing canonical")),
        "detail should name the missing canonical Trust tool: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_requires_rustc_and_cargo_aliases() {
    for missing_alias in ["rustc", "cargo"] {
        let root = temp_test_dir(&format!("linked-surface-missing-{missing_alias}"));
        let bin_dir = root.join("bin");
        std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
        write_required_surface_tool_markers(&bin_dir);
        std::fs::remove_file(bin_dir.join(host_executable_name(missing_alias)))
            .expect("remove required compatibility alias");

        let trustc = bin_dir.join(host_executable_name("trustc"));
        let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
        let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

        assert!(!status.ready, "missing {missing_alias} alias was accepted: {status:?}");
        assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Missing);
        assert!(
            status.detail.as_deref().is_some_and(|detail| {
                detail.contains("missing required same-sysroot compatibility alias")
                    && detail.contains(missing_alias)
            }),
            "detail should name the missing load-bearing alias: {status:?}"
        );

        std::fs::remove_dir_all(root).expect("should remove temp dir");
    }
}

#[cfg(unix)]
#[test]
fn test_detect_linked_trust_cargo_surface_accepts_same_bin_compatibility_symlinks() {
    use std::os::unix::fs::symlink;

    let root = temp_test_dir("linked-surface-same-bin-alias-links");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    write_required_surface_tool_markers(&bin_dir);
    for (alias, canonical) in [("rustc", "trustc"), ("cargo", "targo")] {
        let alias = bin_dir.join(host_executable_name(alias));
        std::fs::remove_file(&alias).expect("remove marker alias");
        symlink(host_executable_name(canonical), alias).expect("link compatibility alias");
    }

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(status.ready, "same-bin compatibility symlinks were rejected: {status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::InstalledReady);

    std::fs::remove_dir_all(root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_rejects_same_bin_misbound_compatibility_alias() {
    let root = temp_test_dir("linked-surface-same-bin-misbound-alias");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    write_required_surface_tool_markers(&bin_dir);
    let cargo_alias = bin_dir.join(host_executable_name("cargo"));
    std::fs::write(&cargo_alias, b"unrelated same-bin executable")
        .expect("replace compatibility alias contents");

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "misbound same-bin cargo alias was accepted: {status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::AmbientFallback);
    assert!(
        status.detail.as_deref().is_some_and(|detail| {
            detail.contains("required compatibility alias binding")
                && detail.contains("cargo does not bind to canonical targo")
        }),
        "detail should expose the same-bin identity mismatch: {status:?}"
    );

    std::fs::remove_dir_all(root).expect("remove misbound alias fixture");
}

#[cfg(unix)]
#[test]
fn test_detect_linked_trust_cargo_surface_rejects_alias_symlink_outside_sysroot() {
    use std::os::unix::fs::symlink;

    let root = temp_test_dir("linked-surface-outside-rustc-alias");
    let bin_dir = root.join("toolchain/bin");
    let ambient_bin = root.join("ambient/bin");
    std::fs::create_dir_all(&bin_dir).expect("should create selected bin dir");
    std::fs::create_dir_all(&ambient_bin).expect("should create ambient bin dir");
    write_required_surface_tool_markers(&bin_dir);

    let rustc_alias = bin_dir.join(host_executable_name("rustc"));
    std::fs::remove_file(&rustc_alias).expect("remove same-sysroot rustc alias");
    let ambient_rustc = ambient_bin.join(host_executable_name("rustc"));
    write_executable_marker(&ambient_rustc);
    symlink(&ambient_rustc, &rustc_alias).expect("create outward rustc alias symlink");

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "outward rustc symlink was accepted: {status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::AmbientFallback);
    assert!(
        status.detail.as_deref().is_some_and(|detail| {
            detail.contains("required compatibility alias binding is outside")
                && detail.contains("rustc resolves outside")
        }),
        "detail should expose the cross-sysroot alias binding: {status:?}"
    );

    std::fs::remove_dir_all(root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_requires_canonical_tools_not_alias_only() {
    let root = temp_test_dir("linked-cargo-surface-inherited");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let rustc_alias = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    let cargo = bin_dir.join(host_executable_name("cargo"));
    write_executable_marker(&trustc);
    write_executable_marker(&rustc_alias);
    write_executable_marker(&cargo);

    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready);
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Missing);
    assert!(
        status.detail.as_deref().is_some_and(|detail| detail.contains("missing canonical `targo`")),
        "detail should require canonical targo even when cargo alias exists: {status:?}"
    );
    assert_eq!(surface_tool(&status, "targo").status, LinkedTrustSurfaceToolStatusKind::Missing);

    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    write_executable_marker(&rustc);
    let linked = linked_toolchain_status(Some(canonicalize_or_self(rustc.clone())));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::Missing);
    assert!(
        status.detail.as_deref().is_some_and(|detail| detail.contains("missing canonical `targo`")),
        "detail should reject rustc-only evidence without sibling canonical targo: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_rejects_retired_public_aliases() {
    let root = temp_test_dir("linked-surface-inherited-extended");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    write_required_surface_tool_markers(&bin_dir);
    let rustdoc = bin_dir.join(host_executable_name("rustdoc"));
    write_executable_marker(&rustdoc);

    let rustc = bin_dir.join(host_executable_name("rustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(rustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "{status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::InvalidInheritedNameEvidence);
    assert_eq!(surface_tool(&status, "trustdoc").status, LinkedTrustSurfaceToolStatusKind::Present);
    assert!(
        status.detail.as_deref().is_some_and(|detail| {
            detail.contains("forbidden retired public entrypoint") && detail.contains("rustdoc")
        }),
        "retired alias blocker should identify rustdoc: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_detect_linked_trust_cargo_surface_rejects_retired_libexec_alias() {
    let root = temp_test_dir("linked-surface-retired-libexec");
    let bin_dir = root.join("bin");
    let libexec_dir = root.join("libexec");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    std::fs::create_dir_all(&libexec_dir).expect("should create libexec dir");
    write_required_surface_tool_markers(&bin_dir);
    let retired = libexec_dir.join(host_executable_name("rust-analyzer-proc-macro-srv"));
    write_executable_marker(&retired);

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "{status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::InvalidInheritedNameEvidence);
    assert!(
        status
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("rust-analyzer-proc-macro-srv")),
        "detail should identify the forbidden libexec alias: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_detect_linked_trust_cargo_surface_rejects_dangling_retired_alias() {
    use std::os::unix::fs::symlink;

    let root = temp_test_dir("linked-surface-dangling-retired-alias");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    write_required_surface_tool_markers(&bin_dir);
    let retired = bin_dir.join(host_executable_name("rust-lldb"));
    symlink(root.join("missing-rust-lldb"), &retired).expect("create dangling retired alias");

    let trustc = bin_dir.join(host_executable_name("trustc"));
    let linked = linked_toolchain_status(Some(canonicalize_or_self(trustc)));
    let status = detect_linked_trust_cargo_surface_with_search(&linked, &[]);

    assert!(!status.ready, "{status:?}");
    assert_eq!(status.kind, LinkedTrustCargoSurfaceKind::InvalidInheritedNameEvidence);
    assert!(
        status.detail.as_deref().is_some_and(|detail| detail.contains("rust-lldb")),
        "detail should identify dangling forbidden alias: {status:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_sibling_rustc_path_finds_only_canonical_trustc() {
    let root = temp_test_dir("sibling-trustc-first");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let targo_trust = bin_dir.join(if cfg!(windows) { "targo-trust.exe" } else { "targo-trust" });
    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    write_executable_marker(&targo_trust);
    std::fs::write(&rustc, "").expect("should create rustc marker");
    write_executable_marker(&trustc);

    assert_eq!(sibling_rustc_path(&targo_trust), Some(canonicalize_or_self(trustc.clone())));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_sibling_rustc_path_rejects_non_executable_trustc() {
    let root = temp_test_dir("sibling-non-executable-trustc");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let targo_trust = bin_dir.join(if cfg!(windows) { "targo-trust.exe" } else { "targo-trust" });
    let trustc = bin_dir.join("trustc");
    write_executable_marker(&targo_trust);
    std::fs::write(&trustc, "").expect("should create non-executable trustc marker");

    assert_eq!(sibling_rustc_path(&targo_trust), None);

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_sibling_rustc_path_rejects_redirected_frontend_and_compiler() {
    let root = temp_test_dir("sibling-redirected-evidence-tools");
    let selected_bin = root.join("selected/bin");
    let ambient_bin = root.join("ambient/bin");
    fs::create_dir_all(&selected_bin).expect("create selected bin");
    fs::create_dir_all(&ambient_bin).expect("create ambient bin");

    let ambient_frontend = ambient_bin.join("targo-trust");
    let ambient_compiler = ambient_bin.join("trustc");
    write_executable_marker(&ambient_frontend);
    write_executable_marker(&ambient_compiler);

    let selected_frontend = selected_bin.join("targo-trust");
    let selected_compiler = selected_bin.join("trustc");
    std::os::unix::fs::symlink(&ambient_frontend, &selected_frontend)
        .expect("create redirected frontend");
    write_executable_marker(&selected_compiler);
    assert_eq!(
        sibling_rustc_path(&selected_frontend),
        None,
        "a symlinked targo-trust cannot relocate compiler discovery"
    );

    fs::remove_file(&selected_frontend).expect("remove redirected frontend");
    write_executable_marker(&selected_frontend);
    fs::remove_file(&selected_compiler).expect("remove selected compiler");
    std::os::unix::fs::symlink(&ambient_compiler, &selected_compiler)
        .expect("create redirected compiler");
    assert_eq!(
        sibling_rustc_path(&selected_frontend),
        None,
        "a symlinked trustc cannot become evidence compiler authority"
    );

    fs::remove_dir_all(root).expect("remove redirected evidence fixture");
}

#[test]
fn test_sibling_rustc_path_rejects_rustc_only() {
    let root = temp_test_dir("sibling-rustc-rejected");
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let targo_trust = bin_dir.join(if cfg!(windows) { "targo-trust.exe" } else { "targo-trust" });
    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    write_executable_marker(&targo_trust);
    std::fs::write(&rustc, "").expect("should create rustc marker");

    assert_eq!(sibling_rustc_path(&targo_trust), None);

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_select_native_rustc_discovery_priority() {
    let root = temp_test_dir("native-rustc-selection-priority");
    let sibling_dir = root.join("sibling");
    let repo_dir = root.join("repo/stage2");
    fs::create_dir_all(&sibling_dir).expect("create sibling fixture");
    fs::create_dir_all(&repo_dir).expect("create repo fixture");
    let sibling_rustc = sibling_dir.join(host_executable_name("trustc"));
    let noncanonical_sibling = sibling_dir.join(host_executable_name("rustc"));
    let repo_rustc = repo_dir.join(host_executable_name("trustc"));
    write_executable_marker(&sibling_rustc);
    write_executable_marker(&noncanonical_sibling);
    write_executable_marker(&repo_rustc);
    let repo_candidates = vec![NativeRustcDiscovery {
        rustc: repo_rustc.clone(),
        source: NativeRustcDiscoverySource::RepoLocalStage2,
    }];

    let selected =
        select_native_rustc_discovery(Some(sibling_rustc.clone()), repo_candidates.clone())
            .expect("expected canonical sibling selection");
    assert_eq!(selected.source, NativeRustcDiscoverySource::SiblingTCargoTrust);
    assert_eq!(selected.rustc, sibling_rustc);

    let selected =
        select_native_rustc_discovery(Some(noncanonical_sibling), repo_candidates.clone())
            .expect("expected repo-local trustc before noncanonical sibling rustc");
    assert_eq!(selected.source, NativeRustcDiscoverySource::RepoLocalStage2);
    assert_eq!(selected.rustc, repo_rustc);

    let selected = select_native_rustc_discovery(None, repo_candidates.clone())
        .expect("expected repo-local fallback");
    assert_eq!(selected.source, NativeRustcDiscoverySource::RepoLocalStage2);
    assert_eq!(selected.rustc, repo_candidates[0].rustc);

    assert!(select_native_rustc_discovery(None, Vec::new()).is_none());
    fs::remove_dir_all(root).expect("remove selection fixture");
}

#[test]
fn test_repo_local_rustc_candidates_ignore_rustc_and_keep_trustc() {
    let root = temp_test_dir("repo-local-trustc-first");
    let bin_dir = root.join("build").join("host").join("stage2").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage2 bin dir");

    let trustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    write_executable_marker(&rustc);
    write_executable_marker(&trustc);

    let candidates = repo_local_rustc_candidates(&root);

    assert_eq!(
        candidates.first().map(|candidate| candidate.rustc.clone()),
        Some(canonicalize_or_self(trustc.clone())),
        "repo-local discovery should include canonical trustc and ignore rustc: {candidates:?}"
    );
    assert!(
        candidates.iter().all(|candidate| candidate.rustc != canonicalize_or_self(rustc.clone())),
        "repo-local discovery must not include rustc: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_repo_local_rustc_candidates_include_stage3_fallback() {
    let root = temp_test_dir("repo-local-stage3");
    let bin_dir = root.join("build").join("host").join("stage3").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage3 bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&rustc);

    let candidates = repo_local_rustc_candidates(&root);
    assert!(
        candidates.iter().any(|candidate| {
            candidate.source == NativeRustcDiscoverySource::RepoLocalStage3
                && candidate.rustc == canonicalize_or_self(rustc.clone())
        }),
        "stage3 repo-local compiler should be discoverable: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_repo_local_rustc_candidates_include_discovered_host_stage2() {
    let root = temp_test_dir("repo-local-discovered-host-stage2");
    let bin_dir = root.join("build").join("custom-audit-host").join("stage2").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage2 bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&rustc);

    let candidates = repo_local_rustc_candidates(&root);
    assert!(
        candidates.iter().any(|candidate| {
            candidate.source == NativeRustcDiscoverySource::RepoLocalStage2
                && candidate.rustc == canonicalize_or_self(rustc.clone())
        }),
        "arbitrary build/<host>/stage2/bin/trustc should be discoverable: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_repo_local_rustc_candidates_prefer_any_stage2_before_stage3() {
    let root = temp_test_dir("repo-local-stage2-before-stage3");
    let stage2_bin = root.join("build").join("custom-audit-host").join("stage2").join("bin");
    let stage3_bin = root.join("build").join("host").join("stage3").join("bin");
    std::fs::create_dir_all(&stage2_bin).expect("should create custom stage2 bin dir");
    std::fs::create_dir_all(&stage3_bin).expect("should create host stage3 bin dir");

    let stage2 = stage2_bin.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let stage3 = stage3_bin.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&stage2);
    write_executable_marker(&stage3);

    let candidates = repo_local_rustc_candidates(&root);
    let stage2_index = candidates
        .iter()
        .position(|candidate| candidate.rustc == canonicalize_or_self(stage2.clone()))
        .expect("custom stage2 trustc should be discoverable");
    let stage3_index = candidates
        .iter()
        .position(|candidate| candidate.rustc == canonicalize_or_self(stage3.clone()))
        .expect("host stage3 trustc should be discoverable");
    assert!(
        stage2_index < stage3_index,
        "stage2 Trust compiler must be preferred before stage3 fallback: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_repo_local_rustc_candidates_reject_stage0_release_evidence() {
    let root = temp_test_dir("repo-local-stage0-rejected");
    let bin_dir = root.join("build").join("host").join("stage0").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage0 bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&rustc);

    let candidates = repo_local_rustc_candidates(&root);
    assert!(
        candidates.iter().all(|candidate| candidate.rustc != canonicalize_or_self(rustc.clone())),
        "stage0 trustc must not satisfy native release evidence discovery: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_repo_local_rustc_candidates_skip_non_executable_files() {
    let root = temp_test_dir("repo-local-nonexecutable");
    let bin_dir = root.join("build").join("host").join("stage2").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create stage2 bin dir");

    let rustc = bin_dir.join("trustc");
    std::fs::write(&rustc, "").expect("should create trustc marker");

    let candidates = repo_local_rustc_candidates(&root);
    assert!(
        candidates.iter().all(|candidate| candidate.rustc != canonicalize_or_self(rustc.clone())),
        "non-executable repo-local compiler must not be discoverable: {candidates:?}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_repo_local_rustc_candidates_skip_redirected_compilers() {
    let root = temp_test_dir("repo-local-redirected");
    let bin_dir = root.join("build/host/stage2/bin");
    let ambient_dir = root.join("ambient/bin");
    fs::create_dir_all(&bin_dir).expect("create stage2 bin");
    fs::create_dir_all(&ambient_dir).expect("create ambient bin");
    let ambient = ambient_dir.join("trustc");
    write_executable_marker(&ambient);
    let redirected = bin_dir.join("trustc");
    std::os::unix::fs::symlink(&ambient, &redirected).expect("create redirected trustc");

    let candidates = repo_local_rustc_candidates(&root);
    assert!(
        candidates.iter().all(|candidate| candidate.rustc != redirected),
        "redirected repo-local compiler must not be discoverable: {candidates:?}"
    );

    fs::remove_dir_all(root).expect("remove redirected compiler fixture");
}

#[test]
fn test_native_runtime_library_paths_include_sysroot_rustlib_and_stage_rustc_deps() {
    let root = temp_test_dir("runtime-paths");
    let rustc = root.join("build/host/stage1/bin/rustc");
    let sysroot_lib = root.join("build/host/stage1/lib");
    let rustlib_lib = root.join("build/host/stage1/lib/rustlib/test-triple/lib");
    let stage_deps = root.join("build/host/stage1-rustc/host/release/deps");

    std::fs::create_dir_all(rustc.parent().expect("rustc should have parent"))
        .expect("should create rustc bin dir");
    std::fs::write(&rustc, "").expect("should create rustc marker");
    std::fs::create_dir_all(&sysroot_lib).expect("should create sysroot lib");
    std::fs::create_dir_all(&rustlib_lib).expect("should create rustlib lib");
    std::fs::create_dir_all(&stage_deps).expect("should create stage deps dir");

    let paths = native_runtime_library_paths(&rustc);
    assert_eq!(
        paths,
        [sysroot_lib, rustlib_lib, stage_deps].map(canonicalize_or_self).to_vec(),
        "runtime search order preserves semantic tiers instead of globally sorting paths"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn native_runtime_environment_does_not_forge_build_time_release_identity() {
    let mut command = std::process::Command::new("unused");
    apply_native_runtime_env(&mut command, Path::new("/missing/toolchain/bin/trustc"));
    for forbidden in ["CFG_RELEASE", "CFG_VERSION"] {
        assert!(
            command.get_envs().all(|(name, _)| name != std::ffi::OsStr::new(forbidden)),
            "runtime helper injected build-time environment {forbidden}"
        );
    }
    for forbidden in
        ["LD_PRELOAD", "LD_AUDIT", "DYLD_INSERT_LIBRARIES", "DYLD_FALLBACK_LIBRARY_PATH"]
    {
        let configured = command
            .get_envs()
            .find_map(|(name, value)| (name == std::ffi::OsStr::new(forbidden)).then_some(value));
        assert!(
            matches!(configured, Some(None)),
            "runtime helper did not force-clear loader injection variable {forbidden}: {configured:?}"
        );
    }
}

#[cfg(target_os = "macos")]
#[test]
fn trustd_runtime_closure_is_canonical_empty_and_clears_ambient_authority() {
    let candidate = std::env::current_exe().expect("current test executable");
    let closure =
        inspect_trustd_runtime_closure(&candidate).expect("inspect test executable closure");
    closure.validate().expect("canonical trustd runtime closure");
    assert_eq!(closure.loader_environment, "none");
    assert!(closure.loader_variable.is_none());
    assert!(closure.search_paths.is_empty());
    assert!(closure.directory_entries.is_empty());
    assert_eq!(closure.concurrent_writer_policy, "exclusive-same-uid-release-host");
    assert_eq!(closure.native_format, "mach-o-thin");
    assert_ne!(closure.inspector_path, "/usr/bin/otool");
    assert!(closure.system_dependencies.iter().all(|dependency| {
        dependency.starts_with("/usr/lib/") || dependency.starts_with("/System/Library/")
    }));

    let mut command = std::process::Command::new(&candidate);
    command
        .env("PATH", "/attacker/bin")
        .env("LD_PRELOAD", "/ignored/libattacker.so")
        .env("DYLD_INSERT_LIBRARIES", "/ignored/libattacker.dylib")
        .env("RUSTC_WORKSPACE_WRAPPER", "/attacker/wrapper");
    apply_trustd_runtime_closure(&mut command, &candidate, &closure)
        .expect("apply canonical trustd runtime closure");
    assert_eq!(command.get_envs().count(), 0, "env_clear must remove explicit authority too");
}

#[cfg(target_os = "macos")]
#[test]
fn trustd_runtime_closure_rejects_mutation_addition_symlink_and_path_ordering() {
    let root = temp_test_dir("trustd-runtime-closure-hostile");
    fs::create_dir_all(&root).expect("create hostile runtime fixture");
    let dylib = root.join("libignored.dylib");
    fs::write(&dylib, b"ignored mutable dylib").expect("write hostile dylib");
    let symlink = root.join("libredirect.dylib");
    std::os::unix::fs::symlink(&dylib, &symlink).expect("create hostile dylib symlink");

    let canonical =
        inspect_trustd_runtime_closure(&std::env::current_exe().expect("current test executable"))
            .expect("inspect test executable closure");
    let mut added_file = canonical.clone();
    added_file.directory_entries.push(dylib.display().to_string());
    assert!(added_file.validate().is_err(), "an ignored dylib entered the empty closure");

    let mut added_symlink = canonical.clone();
    added_symlink.directory_entries.push(symlink.display().to_string());
    assert!(added_symlink.validate().is_err(), "a dylib symlink entered the empty closure");

    for paths in [
        vec!["/trusted/first".to_string(), "/attacker/second".to_string()],
        vec!["/attacker/second".to_string(), "/trusted/first".to_string()],
    ] {
        let mut reordered = canonical.clone();
        reordered.search_paths = paths;
        assert!(reordered.validate().is_err(), "any loader ordering must fail closed");
    }

    if canonical.system_dependencies.len() >= 2 {
        let mut reordered_dependencies = canonical.clone();
        reordered_dependencies.system_dependencies.swap(0, 1);
        assert!(
            reordered_dependencies.validate().is_err(),
            "native dependency ordering escaped the closure digest"
        );
    }

    let mut forged_digest = canonical;
    forged_digest.closure_sha256 = "0".repeat(64);
    assert!(forged_digest.validate().is_err(), "a mutated closure digest was accepted");
    fs::remove_dir_all(root).expect("remove hostile runtime fixture");
}

fn runtime_source_provenance_artifact_json(verification: &str) -> String {
    runtime_source_provenance_artifact_json_with(verification, None, None)
}

fn runtime_source_provenance_artifact_json_with(
    verification: &str,
    reconstruction: Option<&str>,
    source_gate: Option<&str>,
) -> String {
    runtime_source_provenance_artifact_json_with_summary(
        verification,
        reconstruction,
        source_gate,
        r#"{
            "status": "exact",
            "exact_mapping_count": 1,
            "ambiguous_mapping_count": 0,
            "source_backpropagation_allowed": true
          }"#,
    )
}

fn runtime_source_provenance_artifact_json_with_summary(
    verification: &str,
    reconstruction: Option<&str>,
    source_gate: Option<&str>,
    source_provenance: &str,
) -> String {
    let reconstruction_field = reconstruction
        .map(|reconstruction| format!(r#","reconstruction": {reconstruction}"#))
        .unwrap_or_default();
    let source_gate_field = source_gate
        .map(|source_gate| format!(r#","source_backpropagation_gate": {source_gate}"#))
        .unwrap_or_default();
    let legacy = format!(
        r#"{{
          "source_provenance": {source_provenance},
          "checked_binary_identity": {{
            "binary_path": "fixtures/tiny.bin",
            "binary_sha256": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            "selected_image_sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
            "function_entry": 4198400
          }},
          "source_provenance_artifact_digest": "sha256:7777777777777777777777777777777777777777777777777777777777777777",
          "source_backpropagation_gate_sha256": "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
          "exact_source_type_ownership": {{
            "schema_version": "targo-trust.exact-source-type-ownership.v1",
            "status": "accepted",
            "artifact_digest": "sha256:9999999999999999999999999999999999999999999999999999999999999999",
            "binary_digest": "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            "selected_image": {{
              "file_offset": 0,
              "file_size": 16,
              "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
            }},
            "source_provenance_artifact_digest": "sha256:7777777777777777777777777777777777777777777777777777777777777777",
            "type_fact_digests": [
              "sha256:2222222222222222222222222222222222222222222222222222222222222222"
            ],
            "checked_proof_identifiers": {{
              "solver_dispatch_ids": ["dispatch-0"],
              "checked_certificate_sha256": [
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
              ],
              "production_checker_evidence_sha256": [
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              ],
              "source_backpropagation_gate_sha256": [
                "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
              ],
              "replay_transcript_digests": [
                "sha256:1111111111111111111111111111111111111111111111111111111111111111"
              ]
            }},
            "ownership_rows": [
              {{
                "binary_address": 4198400,
                "source": {{
                  "file": "/tmp/recovered.rs",
                  "line_start": 1,
                  "col_start": 1,
                  "line_end": 1,
                  "col_end": 10
                }},
                "source_provenance_record_digest": "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
                "type_fact_digest": "sha256:2222222222222222222222222222222222222222222222222222222222222222",
                "solver_dispatch_id": "dispatch-0"
              }}
            ],
            "ambiguous_ownership_count": 0,
            "blockers": []
          }},
          "verification": {verification}{reconstruction_field}{source_gate_field},
          "source_mappings": [
            {{
              "binary_address": 4198400,
              "binary_path": "fixtures/tiny.bin",
              "function_entry": 4198400,
              "instruction_size": 1,
              "instruction_bytes": [144],
              "binary_artifact_digest_identity": {{
                "root_artifact_digest": {{
                  "algorithm": "sha256",
                  "value": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
                }},
                "selected_image": {{
                  "file_offset": 0,
                  "file_size": 16,
                  "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                }}
              }},
              "source_status": "exact",
              "provenance_status": "checked_exact",
              "record_digest": "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
              "proof_evidence": {{
                "solver_dispatch_id": "dispatch-0",
                "checked_certificate_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                "production_checker_evidence_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "source_backpropagation_gate_sha256": "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "replay_transcript_digest": "1111111111111111111111111111111111111111111111111111111111111111"
              }},
              "source": {{
                "file": "/tmp/recovered.rs",
                "line_start": 1,
                "col_start": 1,
                "line_end": 1,
                "col_end": 10
              }}
            }}
          ]
        }}"#
    );
    canonicalize_runtime_source_provenance_fixture(&legacy)
}

fn canonicalize_runtime_source_provenance_fixture(json: &str) -> String {
    #[derive(serde::Serialize)]
    struct RecordDigestMaterial<'a> {
        origin: &'a trust_types::BinaryOrigin,
        artifact_digest_identity: &'a trust_types::BinaryArtifactDigestIdentity,
        source_status: &'a str,
        provenance_status: &'a str,
        proof_evidence: &'a trust_report::BinarySourceProvenanceProofEvidenceReport,
    }

    #[derive(serde::Serialize)]
    struct ArtifactDigestMaterial<'a> {
        kind: &'a str,
        schema_version: &'a str,
        source_provenance: &'a trust_types::BinarySourceProvenanceSummary,
        source_backpropagation_gate_sha256: &'a Option<String>,
        records: &'a [trust_report::BinarySourceProvenanceRecordReport],
    }

    let mut value: serde_json::Value =
        serde_json::from_str(json).expect("runtime provenance fixture JSON should parse");
    value["kind"] = serde_json::json!("binary_source_provenance");
    value["schema_version"] =
        serde_json::json!("trust-report.binary-source-provenance-artifact.v1");
    value["blockers"] = serde_json::json!([]);
    if value.get("source_backpropagation_gate").is_some() {
        value["source_backpropagation_gate"]["source_backpropagation_gate_sha256"] =
            value["source_backpropagation_gate_sha256"].clone();
    }

    let mapping = value["source_mappings"][0].clone();
    let mut record = serde_json::json!({
        "origin": {
            "binary_path": mapping["binary_path"].clone(),
            "function_entry": mapping["function_entry"].clone(),
            "instruction_address": mapping["binary_address"].clone(),
            "instruction_size": mapping["instruction_size"].clone(),
            "instruction_bytes": mapping["instruction_bytes"].clone(),
            "source": mapping["source"].clone()
        },
        "artifact_digest_identity": mapping["binary_artifact_digest_identity"].clone(),
        "source_status": mapping["source_status"].clone(),
        "provenance_status": mapping["provenance_status"].clone(),
        "record_digest": mapping["record_digest"].clone(),
        "proof_evidence": mapping["proof_evidence"].clone()
    });
    let typed_record: trust_report::BinarySourceProvenanceRecordReport =
        serde_json::from_value(record.clone()).expect("canonical provenance record fixture");
    let record_digest = trust_types::digest::stable_sha256_hex(
        &serde_json::to_vec(&RecordDigestMaterial {
            origin: &typed_record.origin,
            artifact_digest_identity: &typed_record.artifact_digest_identity,
            source_status: &typed_record.source_status,
            provenance_status: &typed_record.provenance_status,
            proof_evidence: &typed_record.proof_evidence,
        })
        .expect("serialize record digest material"),
    );
    record["record_digest"] = serde_json::json!(record_digest);
    value["source_mappings"][0]["record_digest"] = serde_json::json!(record_digest);
    value["exact_source_type_ownership"]["ownership_rows"][0]["source_provenance_record_digest"] =
        serde_json::json!(format!("sha256:{record_digest}"));
    value["canonical_binary_provenance"] = serde_json::json!({ "records": [record] });

    let report: trust_report::BinarySourceProvenanceArtifactReport =
        serde_json::from_value(value.clone()).expect("canonical provenance artifact fixture");
    let artifact_digest = trust_types::digest::stable_sha256_hex(
        &serde_json::to_vec(&ArtifactDigestMaterial {
            kind: &report.kind,
            schema_version: &report.schema_version,
            source_provenance: &report.source_provenance,
            source_backpropagation_gate_sha256: &report.source_backpropagation_gate_sha256,
            records: &report.canonical_binary_provenance.records,
        })
        .expect("serialize artifact digest material"),
    );
    let artifact_digest = format!("sha256:{artifact_digest}");
    value["source_provenance_artifact_digest"] = serde_json::json!(artifact_digest);
    value["exact_source_type_ownership"]["source_provenance_artifact_digest"] =
        serde_json::json!(artifact_digest);

    serde_json::to_string_pretty(&value).expect("canonical provenance fixture should serialize")
}

fn proof_grade_binary_verification_json() -> &'static str {
    r#"{
      "status": "Proved",
      "trust_level": "ProofGrade",
      "total_vcs": 1,
      "proved": 1,
      "failed": 0,
      "unknown": 0,
      "timeout": 0,
      "unsupported": 0,
      "rejected": 0,
      "proof_certificate": {
        "Checked": {
          "checker": "ay-proof-checker@1.0.0;production_checker_evidence_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "format": "lfsc",
          "sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        }
      },
      "replay": "Replayed",
      "solver_dispatch": [
        {
          "id": "dispatch-0",
          "solver": "ay-smtlib",
          "status": "Unsat",
          "origin": {
            "binary_path": "fixtures/tiny.bin",
            "function_entry": 4198400,
            "instruction_address": 4198400,
            "instruction_size": 1,
            "instruction_bytes": [144],
            "source": {
              "file": "/tmp/recovered.rs",
              "line_start": 1,
              "col_start": 1,
              "line_end": 1,
              "col_end": 10
            }
          },
          "replay": "Replayed",
          "certificate": {
            "Checked": {
              "checker": "ay-proof-checker@1.0.0;production_checker_evidence_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
              "format": "lfsc",
              "sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
            }
          },
          "binary_artifact_digest_identity": {
            "root_artifact_digest": {
              "algorithm": "sha256",
              "value": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
            },
            "selected_image": {
              "file_offset": 0,
              "file_size": 16,
              "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
            }
          }
        }
      ]
    }"#
}

fn partial_binary_verification_with_digest_identity_json() -> &'static str {
    r#"{
      "status": "NotRun",
      "trust_level": "Partial",
      "total_vcs": 1,
      "unknown": 1,
      "replay": "NotAttempted",
      "solver_dispatch": [
        {
          "id": "dispatch-0",
          "solver": "ay-smtlib",
          "status": "Unknown",
          "binary_artifact_digest_identity": {
            "root_artifact_digest": {
              "algorithm": "sha256",
              "value": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
            },
            "selected_image": {
              "file_offset": 0,
              "file_size": 16,
              "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
            }
          },
          "replay": "NotAttempted"
        }
      ]
    }"#
}

fn accepted_reconstruction_json() -> &'static str {
    r#"{
      "target": "TrustIr",
      "validation": "Validated",
      "trust_level": "ProofGrade",
      "outputs": [
        {
          "target": "TrustIr",
          "validation": "Validated",
          "trust_level": "ProofGrade"
        }
      ]
    }"#
}

fn accepted_source_gate_json() -> &'static str {
    r#"{
      "schema_version": "trust-proof-cert.source-backpropagation-gate.v1",
      "replay_grade_artifact_identity": true,
      "checked_certificate_identity": true,
      "exact_replay_identity": true,
      "accepted_reconstruction_validation": true,
      "accepted_target_validation": true,
      "exact_source_provenance": true,
      "source_provenance": {
        "status": "exact",
        "exact_mapping_count": 1,
        "ambiguous_mapping_count": 0,
        "source_backpropagation_allowed": true
      },
      "checked_source_provenance_binary_identity": {
        "root_artifact_digest": {
          "algorithm": "sha256",
          "value": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
        },
        "selected_image": {
          "file_offset": 0,
          "file_size": 16,
          "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
        }
      },
      "source_backpropagation_allowed": true,
      "blockers": []
    }"#
}

fn schema_mismatched_source_gate_json() -> &'static str {
    r#"{
      "schema_version": "trust-proof-cert.source-backpropagation-gate.v0",
      "replay_grade_artifact_identity": true,
      "checked_certificate_identity": true,
      "exact_replay_identity": true,
      "accepted_reconstruction_validation": true,
      "accepted_target_validation": true,
      "exact_source_provenance": true,
      "source_provenance": {
        "status": "exact",
        "exact_mapping_count": 1,
        "ambiguous_mapping_count": 0,
        "source_backpropagation_allowed": true
      },
      "checked_source_provenance_binary_identity": {
        "root_artifact_digest": {
          "algorithm": "sha256",
          "value": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
        },
        "selected_image": {
          "file_offset": 0,
          "file_size": 16,
          "sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
        }
      },
      "source_backpropagation_allowed": true,
      "blockers": []
    }"#
}

fn checked_source_gate_artifact_json(source_gate: &str) -> String {
    format!(
        r#"{{
          "kind": "checked_source_backpropagation_gate",
          "schema_version": "targo-trust.checked-source-backpropagation-gate.v1",
          "source_backpropagation_gate_sha256": "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
          "source_backpropagation_gate": {source_gate}
        }}"#
    )
}

fn real_debug_checked_source_provenance_artifact_value() -> serde_json::Value {
    serde_json::from_str(include_str!(
        "../../../crates/trust-report/src/fixtures/binary_source_provenance_real_debug_golden.json"
    ))
    .expect("real debug source provenance fixture should parse")
}

fn real_debug_runtime_source_provenance_artifact_json() -> String {
    let mut value = real_debug_checked_source_provenance_artifact_value();
    attach_exact_source_type_ownership(&mut value);
    serde_json::to_string_pretty(&value).expect("runtime artifact should serialize")
}

fn attach_exact_source_type_ownership(value: &mut serde_json::Value) {
    let records = value["canonical_binary_provenance"]["records"]
        .as_array()
        .expect("real debug fixture records")
        .clone();
    let first_identity = records[0]["artifact_digest_identity"].clone();
    let root_digest = first_identity["root_artifact_digest"]["value"]
        .as_str()
        .expect("root artifact digest")
        .to_string();
    let selected_image = first_identity["selected_image"].clone();
    value["checked_binary_identity"] = serde_json::json!({
        "binary_path": records[0]["origin"]["binary_path"].clone(),
        "binary_sha256": root_digest,
        "selected_image_sha256": selected_image["sha256"].clone(),
        "function_entry": records[0]["origin"]["function_entry"].clone()
    });
    value["source_backpropagation_gate"]["checked_source_provenance_binary_identity"] =
        first_identity.clone();
    let source_provenance_artifact_digest = value["source_provenance_artifact_digest"]
        .as_str()
        .expect("source provenance artifact digest")
        .to_string();

    let mut type_fact_digests = Vec::new();
    let mut solver_dispatch_ids = Vec::new();
    let mut checked_certificate_sha256 = Vec::new();
    let mut production_checker_evidence_sha256 = Vec::new();
    let mut source_backpropagation_gate_sha256 = Vec::new();
    let mut replay_transcript_digests = Vec::new();
    let mut ownership_rows = Vec::new();

    for record in records {
        let record_digest = record["record_digest"].as_str().expect("record digest");
        let type_fact_digest = format!("sha256:{record_digest}");
        push_unique(&mut type_fact_digests, type_fact_digest.clone());

        let evidence = &record["proof_evidence"];
        push_unique(
            &mut solver_dispatch_ids,
            evidence["solver_dispatch_id"].as_str().expect("solver dispatch id").to_string(),
        );
        push_unique(
            &mut checked_certificate_sha256,
            sha256_uri(evidence["checked_certificate_sha256"].as_str()),
        );
        push_unique(
            &mut production_checker_evidence_sha256,
            sha256_uri(evidence["production_checker_evidence_sha256"].as_str()),
        );
        push_unique(
            &mut source_backpropagation_gate_sha256,
            sha256_uri(evidence["source_backpropagation_gate_sha256"].as_str()),
        );
        push_unique(
            &mut replay_transcript_digests,
            sha256_uri(evidence["replay_transcript_digest"].as_str()),
        );

        ownership_rows.push(serde_json::json!({
            "binary_address": record["origin"]["instruction_address"].clone(),
            "source": record["origin"]["source"].clone(),
            "source_provenance_record_digest": format!("sha256:{record_digest}"),
            "type_fact_digest": type_fact_digest,
            "solver_dispatch_id": evidence["solver_dispatch_id"].clone()
        }));
    }

    value["exact_source_type_ownership"] = serde_json::json!({
        "schema_version": "targo-trust.exact-source-type-ownership.v1",
        "status": "accepted",
        "artifact_digest": "sha256:9999999999999999999999999999999999999999999999999999999999999999",
        "binary_digest": format!("sha256:{root_digest}"),
        "selected_image": selected_image,
        "source_provenance_artifact_digest": source_provenance_artifact_digest,
        "type_fact_digests": type_fact_digests,
        "checked_proof_identifiers": {
            "solver_dispatch_ids": solver_dispatch_ids,
            "checked_certificate_sha256": checked_certificate_sha256,
            "production_checker_evidence_sha256": production_checker_evidence_sha256,
            "source_backpropagation_gate_sha256": source_backpropagation_gate_sha256,
            "replay_transcript_digests": replay_transcript_digests
        },
        "ownership_rows": ownership_rows,
        "ambiguous_ownership_count": 0,
        "blockers": []
    });
}

fn sha256_uri(digest: Option<&str>) -> String {
    format!("sha256:{}", digest.expect("proof evidence digest"))
}

fn push_unique(values: &mut Vec<String>, value: String) {
    if !values.iter().any(|existing| existing == &value) {
        values.push(value);
    }
}

#[test]
fn test_runtime_rewrite_keeps_binary_source_provenance_handoff_closed() {
    let sub_args = crate::cli::parse_subcommand_args(&["--rewrite".to_string()])
        .expect("rewrite args should parse");

    let provenance = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect("rewrite handoff without an artifact should stay closed");

    assert!(provenance.is_none());
}

#[test]
fn test_runtime_rewrite_rejects_checked_certificate_gate_without_source_provenance() {
    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--checked-cert-artifact".to_string(),
        "proof.json".to_string(),
    ])
    .expect("checked artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("rewrite loop must reject checked gates without source provenance");

    assert!(error.contains("--checked-cert-artifact"));
    assert!(error.contains("--binary-source-provenance-artifact"));
    assert!(error.contains("proof.json"));
}

#[test]
fn test_runtime_rewrite_rejects_multiple_binary_source_provenance_artifacts() {
    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        "source-a.json".to_string(),
        "--binary-source-provenance-artifact=source-b.json".to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("rewrite loop must reject multiple source provenance artifacts");

    assert!(error.contains("exactly one --binary-source-provenance-artifact"));
    assert!(error.contains("got 2"));
}

#[test]
fn test_runtime_rewrite_rejects_malformed_binary_source_provenance_artifact() {
    let root = temp_test_dir("runtime-source-provenance-malformed");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    std::fs::write(&artifact, r#"{ "source_provenance": "#).expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("rewrite loop must reject malformed source provenance artifacts");

    assert!(error.contains("failed to parse --binary-source-provenance-artifact"));
    assert!(error.contains(&artifact.display().to_string()));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_source_provenance_without_checked_binary_identity() {
    let root = temp_test_dir("runtime-source-provenance-missing-identity");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("runtime source provenance fixture should parse");
    value
        .as_object_mut()
        .expect("runtime fixture should be an object")
        .remove("checked_binary_identity");
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("fixture should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("rewrite loop must reject source provenance without checked identity");

    assert!(error.contains("checked source-provenance binary identity"));
    assert!(error.contains("missing binary_path"));
    assert!(error.contains("missing binary_sha256"));
    assert!(error.contains("missing selected_image_sha256"));
    assert!(error.contains("missing function_entry"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_non_exact_source_provenance_statuses() {
    let root = temp_test_dir("runtime-source-provenance-non-exact");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let cases = [
        (
            "heuristic",
            r#"{
              "status": "heuristic",
              "exact_mapping_count": 1,
              "ambiguous_mapping_count": 0,
              "source_backpropagation_allowed": true
            }"#,
        ),
        (
            "unavailable",
            r#"{
              "status": "unavailable",
              "exact_mapping_count": 0,
              "ambiguous_mapping_count": 0,
              "source_backpropagation_allowed": true
            }"#,
        ),
        (
            "ambiguous",
            r#"{
              "status": "ambiguous",
              "exact_mapping_count": 1,
              "ambiguous_mapping_count": 1,
              "source_backpropagation_allowed": true
            }"#,
        ),
    ];

    for (case, source_provenance) in cases {
        let artifact = root.join(format!("{case}-source-provenance.json"));
        std::fs::write(
            &artifact,
            runtime_source_provenance_artifact_json_with_summary(
                proof_grade_binary_verification_json(),
                Some(accepted_reconstruction_json()),
                Some(accepted_source_gate_json()),
                source_provenance,
            ),
        )
        .expect("should write artifact");

        let sub_args = crate::cli::parse_subcommand_args(&[
            "--rewrite".to_string(),
            "--binary-source-provenance-artifact".to_string(),
            artifact.display().to_string(),
        ])
        .expect("source provenance artifact args should parse");

        let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
            .expect_err("runtime rewrite must reject non-exact provenance");

        assert!(
            error.contains("not an accepted checked binary-source provenance artifact"),
            "{case}: {error}"
        );
        assert!(error.contains("source_provenance") && error.contains(case), "{case}: {error}");
    }

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_exact_source_provenance_without_proof_grade_binary_evidence() {
    let root = temp_test_dir("runtime-source-provenance-no-proof");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json(
            partial_binary_verification_with_digest_identity_json(),
        ),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("rewrite loop must reject source provenance without proof-grade evidence");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"), "{error}");
    assert!(error.contains("source_backpropagation_gate is missing"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_legacy_binary_source_provenance_without_full_backprop() {
    let root = temp_test_dir("runtime-source-provenance");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json(proof_grade_binary_verification_json()),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("legacy source provenance artifact must not import without full evidence");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"), "{error}");
    assert!(error.contains("source_backpropagation_gate is missing"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_accepts_full_checked_binary_source_backprop_artifact() {
    let root = temp_test_dir("runtime-source-provenance-full");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let provenance = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect("full checked binary source-backprop evidence should import")
        .expect("source provenance should be imported");

    assert!(provenance.effective_source_backpropagation_allowed());
    let identity = provenance.checked_binary_identity();
    assert_eq!(identity.binary_path.as_deref(), Some("fixtures/tiny.bin"));
    assert_eq!(
        identity.binary_sha256.as_deref(),
        Some("cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
    );
    assert_eq!(
        identity.selected_image_sha256.as_deref(),
        Some("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")
    );
    assert_eq!(identity.function_entry, Some(4198400));
    assert_eq!(
        provenance.exact_source_type_ownership_artifact_digest(),
        Some("sha256:9999999999999999999999999999999999999999999999999999999999999999")
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_exact_provenance_rejects_missing_source_type_ownership_artifact() {
    let root = temp_test_dir("runtime-source-provenance-missing-ownership");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("source provenance artifact fixture should parse");
    value.as_object_mut().expect("fixture artifact object").remove("exact_source_type_ownership");
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("missing source/type ownership artifact must reject runtime rewrites");

    assert!(error.contains("exact source/type-fact ownership"));
    assert!(error.contains("missing exact source/type-fact ownership artifact"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_exact_provenance_rejects_stale_binary_or_selected_image() {
    let root = temp_test_dir("runtime-source-provenance-stale-ownership");
    std::fs::create_dir_all(&root).expect("should create temp root");

    let cases = [
        ("stale-binary", "ownership binary digest does not match"),
        ("stale-selected-image", "ownership selected image digest/range does not match"),
    ];

    for (case, expected) in cases {
        let artifact = root.join(format!("{case}.json"));
        let mut value: serde_json::Value =
            serde_json::from_str(&runtime_source_provenance_artifact_json_with(
                proof_grade_binary_verification_json(),
                Some(accepted_reconstruction_json()),
                Some(accepted_source_gate_json()),
            ))
            .expect("source provenance artifact fixture should parse");
        match case {
            "stale-binary" => {
                value["exact_source_type_ownership"]["binary_digest"] =
                    serde_json::Value::String(format!("sha256:{}", "0".repeat(64)));
            }
            "stale-selected-image" => {
                value["exact_source_type_ownership"]["selected_image"]["sha256"] =
                    serde_json::Value::String(
                        "abababababababababababababababababababababababababababababababab"
                            .to_string(),
                    );
            }
            _ => unreachable!("covered stale ownership case"),
        }
        std::fs::write(
            &artifact,
            serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
        )
        .expect("should write artifact");

        let sub_args = crate::cli::parse_subcommand_args(&[
            "--rewrite".to_string(),
            "--binary-source-provenance-artifact".to_string(),
            artifact.display().to_string(),
        ])
        .expect("source provenance artifact args should parse");

        let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
            .expect_err("stale ownership artifact must reject runtime rewrites");

        assert!(error.contains(expected), "{case}: {error}");
        assert!(
            error.contains("exact-source-type-ownership-runtime-handoff-rejected"),
            "{case}: {error}"
        );
    }

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_exact_provenance_rejects_missing_type_fact_digest() {
    let root = temp_test_dir("runtime-source-provenance-missing-type-fact");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("source provenance artifact fixture should parse");
    value["exact_source_type_ownership"]["type_fact_digests"] = serde_json::json!([]);
    value["exact_source_type_ownership"]["ownership_rows"][0]
        .as_object_mut()
        .expect("ownership row should be object")
        .remove("type_fact_digest");
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("missing type-fact ownership digest must reject runtime rewrites");

    assert!(error.contains("type fact digest"), "{error}");
    assert!(error.contains("exact-source-type-ownership-runtime-handoff-rejected"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_exact_provenance_rejects_ambiguous_source_type_ownership() {
    let root = temp_test_dir("runtime-source-provenance-ambiguous-ownership");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("source provenance artifact fixture should parse");
    value["exact_source_type_ownership"]["ambiguous_ownership_count"] = serde_json::json!(1);
    let duplicate = value["exact_source_type_ownership"]["ownership_rows"][0].clone();
    value["exact_source_type_ownership"]["ownership_rows"]
        .as_array_mut()
        .expect("ownership rows should be an array")
        .push(duplicate);
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("ambiguous source/type ownership must reject runtime rewrites");

    assert!(error.contains("ambiguous"), "{error}");
    assert!(error.contains("duplicate ownership row"), "{error}");
    assert!(error.contains("exact-source-type-ownership-runtime-handoff-rejected"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_imports_checked_exact_provenance_record_artifact() {
    let root = temp_test_dir("runtime-source-provenance-record");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("source provenance artifact fixture should parse");
    let mut mapping =
        value["source_mappings"].as_array_mut().expect("fixture source mappings").remove(0);
    let origin = serde_json::json!({
        "binary_path": mapping["binary_path"].take(),
        "function_entry": mapping["function_entry"].take(),
        "instruction_address": mapping["binary_address"].take(),
        "instruction_size": mapping["instruction_size"].take(),
        "instruction_bytes": mapping["instruction_bytes"].take(),
        "source": mapping["source"].take()
    });
    let record = serde_json::json!({
        "origin": origin,
        "artifact_digest_identity": mapping["binary_artifact_digest_identity"].take(),
        "source_status": mapping["source_status"].take(),
        "provenance_status": mapping["provenance_status"].take(),
        "record_digest": mapping["record_digest"].take(),
        "proof_evidence": mapping["proof_evidence"].take()
    });
    value.as_object_mut().expect("fixture artifact object").remove("source_mappings");
    value["canonical_binary_provenance"] = serde_json::json!({
        "records": [record],
        "rejections": []
    });
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance record artifact args should parse");

    let provenance = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect("checked exact provenance record artifact should import")
        .expect("source provenance should be imported");

    assert!(provenance.effective_source_backpropagation_allowed());

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_imports_real_debug_checked_provenance_artifact() {
    let root = temp_test_dir("runtime-source-provenance-real-debug");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("real-debug-source-provenance.json");
    std::fs::write(&artifact, real_debug_runtime_source_provenance_artifact_json())
        .expect("should write real debug source provenance artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("real debug source provenance artifact args should parse");

    let provenance = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect("real debug checked provenance artifact should import")
        .expect("source provenance should be imported");

    assert!(provenance.effective_source_backpropagation_allowed());
    assert!(provenance.checked_binary_identity().is_checked());
    assert_eq!(
        provenance.exact_source_type_ownership_artifact_digest(),
        Some("sha256:9999999999999999999999999999999999999999999999999999999999999999")
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_real_debug_non_exact_checked_profile() {
    let root = temp_test_dir("runtime-source-provenance-real-debug-non-exact");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("real-debug-source-provenance-ambiguous.json");
    let mut value = real_debug_checked_source_provenance_artifact_value();
    value["source_provenance"]["status"] = serde_json::json!("ambiguous");
    value["source_provenance"]["ambiguous_mapping_count"] = serde_json::json!(1);
    attach_exact_source_type_ownership(&mut value);
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write non-exact real debug source provenance artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("real debug source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("non-exact checked provenance profile must fail closed");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"));
    assert!(error.contains("source_provenance"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_wrong_binary_exact_provenance_handoff() {
    let root = temp_test_dir("runtime-source-provenance-wrong-binary");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ))
        .expect("source provenance artifact fixture should parse");
    value["canonical_binary_provenance"]["records"][0]["origin"]["binary_path"] =
        serde_json::Value::String("fixtures/other.bin".to_string());
    std::fs::write(
        &artifact,
        serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("wrong binary provenance must not import for runtime source rewrites");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"), "{error}");
    assert!(error.contains("digest mismatch"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_ambiguous_checked_provenance_row_status() {
    let root = temp_test_dir("runtime-source-provenance-ambiguous-row");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let json = runtime_source_provenance_artifact_json_with(
        proof_grade_binary_verification_json(),
        Some(accepted_reconstruction_json()),
        Some(accepted_source_gate_json()),
    )
    .replace(r#""source_status": "exact""#, r#""source_status": "ambiguous""#)
    .replace(r#""provenance_status": "checked_exact""#, r#""provenance_status": "ambiguous""#);
    std::fs::write(&artifact, json).expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("ambiguous source provenance row must not import for source rewrites");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"), "{error}");
    assert!(error.contains("ambiguous"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_missing_checked_proof_identifier_import() {
    let root = temp_test_dir("runtime-source-provenance-missing-proof-id");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let json = runtime_source_provenance_artifact_json_with(
        proof_grade_binary_verification_json(),
        Some(accepted_reconstruction_json()),
        Some(accepted_source_gate_json()),
    )
    .replace(
        r#""checked_certificate_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb""#,
        r#""checked_certificate_sha256": null"#,
    );
    std::fs::write(&artifact, json).expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("missing proof identifier must not import for source rewrites");

    assert!(
        error.contains("failed to parse checked binary-source provenance artifact profile"),
        "{error}"
    );
    assert!(error.contains("invalid type: null"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_missing_or_wrong_source_gate_identity_import() {
    let root = temp_test_dir("runtime-source-provenance-source-gate-identity");
    std::fs::create_dir_all(&root).expect("should create temp root");

    let cases = [
        ("missing-source-gate-identity", None, "source_backpropagation_gate_sha256 is missing"),
        (
            "wrong-source-gate-identity",
            Some("abababababababababababababababababababababababababababababababab"),
            "source_backpropagation_gate_sha256 does not match gate details",
        ),
    ];

    for (case, digest, expected) in cases {
        let artifact = root.join(format!("{case}.json"));
        let mut value: serde_json::Value =
            serde_json::from_str(&runtime_source_provenance_artifact_json_with(
                proof_grade_binary_verification_json(),
                Some(accepted_reconstruction_json()),
                Some(accepted_source_gate_json()),
            ))
            .expect("source provenance artifact fixture should parse");
        match digest {
            Some(digest) => {
                value["source_backpropagation_gate_sha256"] =
                    serde_json::Value::String(digest.to_string());
            }
            None => {
                value
                    .as_object_mut()
                    .expect("fixture artifact object")
                    .remove("source_backpropagation_gate_sha256");
            }
        }
        std::fs::write(
            &artifact,
            serde_json::to_string_pretty(&value).expect("source provenance JSON should serialize"),
        )
        .expect("should write artifact");

        let sub_args = crate::cli::parse_subcommand_args(&[
            "--rewrite".to_string(),
            "--binary-source-provenance-artifact".to_string(),
            artifact.display().to_string(),
        ])
        .expect("source provenance artifact args should parse");

        let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
            .expect_err("source gate identity mismatch must reject runtime rewrites");

        assert!(error.contains(expected), "{case}: {error}");
    }

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_imports_checked_source_gate_artifact_before_planning() {
    let root = temp_test_dir("runtime-source-provenance-source-gate");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let source_gate = root.join("source-gate.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ),
    )
    .expect("should write source provenance artifact");
    std::fs::write(&source_gate, checked_source_gate_artifact_json(accepted_source_gate_json()))
        .expect("should write source gate artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
        "--checked-cert-artifact".to_string(),
        source_gate.display().to_string(),
    ])
    .expect("source provenance and source gate artifact args should parse");

    let provenance = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect("checked source gate artifact should corroborate embedded gate before planning")
        .expect("source provenance should be imported");

    assert!(provenance.effective_source_backpropagation_allowed());

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_gate_hidden_in_arbitrary_checked_artifact_json() {
    let root = temp_test_dir("runtime-source-provenance-arbitrary-gate-wrapper");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let source_gate = root.join("arbitrary-wrapper.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ),
    )
    .expect("should write source provenance artifact");
    std::fs::write(
        &source_gate,
        format!(
            r#"{{"unrelated": {{"source_backpropagation_gate": {}}}}}"#,
            accepted_source_gate_json()
        ),
    )
    .expect("should write arbitrary wrapper");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
        "--checked-cert-artifact".to_string(),
        source_gate.display().to_string(),
    ])
    .expect("source provenance args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("arbitrary nested JSON must never create checked gate authority");
    assert!(error.contains("failed to parse --checked-cert-artifact"), "{error}");
    assert!(error.contains("unknown field") || error.contains("missing field"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_oversized_source_provenance_before_json_parsing() {
    let root = temp_test_dir("runtime-source-provenance-oversized");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    let file = std::fs::File::create(&artifact).expect("create oversized provenance artifact");
    file.set_len(crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1)
        .expect("size oversized provenance artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance args should parse");
    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("oversized provenance artifact must fail closed");
    assert!(error.contains("safety limit"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
#[test]
fn test_runtime_rewrite_rejects_symlinked_source_provenance() {
    use std::os::unix::fs::symlink;

    let root = temp_test_dir("runtime-source-provenance-symlink");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let target = root.join("target.json");
    let artifact = root.join("source-provenance.json");
    std::fs::write(
        &target,
        runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(accepted_source_gate_json()),
        ),
    )
    .expect("write target artifact");
    symlink(&target, &artifact).expect("link provenance artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance args should parse");
    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("symlinked provenance artifact must fail closed");
    assert!(error.contains("not a regular file"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_runtime_rewrite_rejects_schema_mismatched_source_gate() {
    let root = temp_test_dir("runtime-source-provenance-bad-source-gate");
    std::fs::create_dir_all(&root).expect("should create temp root");
    let artifact = root.join("source-provenance.json");
    std::fs::write(
        &artifact,
        runtime_source_provenance_artifact_json_with(
            proof_grade_binary_verification_json(),
            Some(accepted_reconstruction_json()),
            Some(schema_mismatched_source_gate_json()),
        ),
    )
    .expect("should write artifact");

    let sub_args = crate::cli::parse_subcommand_args(&[
        "--rewrite".to_string(),
        "--binary-source-provenance-artifact".to_string(),
        artifact.display().to_string(),
    ])
    .expect("source provenance artifact args should parse");

    let error = runtime_binary_source_provenance_for_rewrite_loop(&sub_args)
        .expect_err("schema-mismatched source gate must reject runtime source rewrites");

    assert!(error.contains("not an accepted checked binary-source provenance artifact"), "{error}");
    assert!(error.contains("source_backpropagation_gate"), "{error}");
    assert!(error.contains("schema_version"), "{error}");
    assert!(error.contains("trust-proof-cert.source-backpropagation-gate.v1"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trusted_runtime_search_path_excludes_inherited_directories() {
    let root = temp_test_dir("merged-search-paths");
    let extra_a = root.join("extra-a");
    let extra_b = root.join("extra-b");

    std::fs::create_dir_all(&extra_a).expect("should create extra_a");
    std::fs::create_dir_all(&extra_b).expect("should create extra_b");

    let merged = trusted_runtime_search_path_value(vec![
        canonicalize_or_self(extra_a.clone()),
        canonicalize_or_self(extra_b.clone()),
    ])
    .expect("trusted search path should exist");

    let split: Vec<PathBuf> = env::split_paths(&merged).collect();
    assert_eq!(
        split,
        vec![canonicalize_or_self(extra_a.clone()), canonicalize_or_self(extra_b.clone())]
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}
