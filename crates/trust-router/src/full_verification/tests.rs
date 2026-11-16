use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use trust_bmc::TrustMcVerifierApiAdapter;
use trust_ir_bridge::{
    NativeVerificationBundle, NativeVerificationRequest, ProofDigest,
    native_verification_bundle_from_module,
};
#[cfg(any(not(feature = "trust-vc-native"), feature = "trust-build"))]
use trust_vc_bridge::TrustVcVerificationEngine;
#[cfg(feature = "trust-build")]
use trust_vc_bridge::{
    TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA,
    TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX,
    trust_vc_typed_result_contract_frame_metadata,
};
use trust_verifier_api::{
    ArtifactHash, AssuranceLevel, BundleSubject, ContractKind, ContractPredicate, EngineCapability,
    EngineKind, EngineManifest, EvidenceArtifact, EvidenceArtifactKind,
    EvidenceArtifactMaterialization, EvidenceArtifactReference, EvidenceDisposition,
    EvidencePublicationMetadata, EvidenceStatus, MetadataEntry, ObligationEvidence, ObligationKind,
    ProofStrength, ReasoningKind, SkipReason, SourceLocation, SupportLevel, TrustContract,
    TrustContractBundle, TrustObligation, ValidatedVerificationRequest, VerificationEngine,
    VerificationRunResult, VerificationRunStatus, VerifierExecutionContext, VerifierResourceLimits,
};

use super::engine::{
    TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT, TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY,
};
use super::*;

#[path = "engine/kernel_replay_tests.rs"]
mod kernel_replay_tests;

#[cfg(feature = "trust-build")]
#[path = "native_wp_tests.rs"]
mod native_wp_tests;

#[cfg(feature = "trust-build")]
#[path = "engine/whole_function_receipt_tests.rs"]
mod whole_function_receipt_tests;

// Synthetic unit-fixture issuer only, inside the existing cfg(test) module.
// Keep this conspicuous test-only call separate from the audited production
// issuer; the source census must continue to find exactly one production seam.
#[cfg(feature = "trust-build")]
fn whole_function_fixture_source_authority(
    native: &mut NativeVerificationBundle,
) -> trust_ir::SourceGenerationAuthority {
    trust_ir::SourceGenerationAuthority::mint_from_live_lowering(native).unwrap()
}

fn bundle_with_postcondition(required_strength: Option<ProofStrength>) -> TrustContractBundle {
    bundle_with_obligation(
        ObligationKind::Postcondition,
        "obligation-ensures",
        Some("contract-ensures"),
        required_strength,
    )
}

fn bundle_with_obligation(
    kind: ObligationKind,
    obligation_id: &str,
    contract_id: Option<&str>,
    required_strength: Option<ProofStrength>,
) -> TrustContractBundle {
    let mut bundle = TrustContractBundle::empty(
        "bundle-1",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    if let Some(contract_id) = contract_id {
        bundle.contracts.push(TrustContract {
            contract_id: contract_id.to_string(),
            kind: if kind == ObligationKind::Postcondition {
                ContractKind::Ensures
            } else {
                ContractKind::Asserts
            },
            predicate: ContractPredicate::TrustExpr { text: "result > 0".to_string() },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
    }
    bundle.obligations.push(TrustObligation {
        obligation_id: obligation_id.to_string(),
        kind,
        contract_id: contract_id.map(str::to_string),
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "prove obligation".to_string(),
        required_strength,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });
    bundle
}

fn plain_obligation(kind: ObligationKind, obligation_id: &str) -> TrustObligation {
    bundle_with_obligation(kind, obligation_id, None, None)
        .obligations
        .pop()
        .expect("single-obligation fixture")
}

fn canonicalize_fixture_json(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                canonicalize_fixture_json(value);
            }
        }
        serde_json::Value::Object(object) => {
            let old = std::mem::take(object);
            let mut entries = old.into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            for (key, mut value) in entries {
                canonicalize_fixture_json(&mut value);
                object.insert(key, value);
            }
        }
        _ => {}
    }
}

fn direct_trust_vc_bundle(obligation_id: &str) -> TrustContractBundle {
    let mut bundle = bundle_with_obligation(
        ObligationKind::MemorySafety,
        obligation_id,
        None,
        Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis)),
    );
    let i =
        trust_verifier_api::TrustSpecExpr::variable("i", trust_verifier_api::TrustSpecSort::Int);
    let sixteen = trust_verifier_api::TrustSpecExpr::int_literal("16");
    let public_predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::binary(
            trust_verifier_api::TrustSpecBinaryOp::And,
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Lt,
                i.clone(),
                sixteen.clone(),
            ),
            trust_verifier_api::TrustSpecExpr::binary(
                trust_verifier_api::TrustSpecBinaryOp::Ge,
                i,
                sixteen,
            ),
        ),
        vec![trust_verifier_api::TrustSpecVariable {
            name: "i".to_string(),
            sort: trust_verifier_api::TrustSpecSort::Int,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }],
    );
    let encoded_id = serde_json::to_string(obligation_id).expect("obligation ID serializes");
    let mut proof_unit: serde_json::Value = serde_json::from_str(&format!(
        concat!(
            r#"{{"source_id":"bundle-trust-vc","unit_id":"demo::owned","native_context":{{"function_signature":{{"name":"demo::owned","params":[{{"name":"i","sort":{{"kind":"math_int"}}}}],"return_sort":{{"kind":"bool"}}}},"ownership":{{"places":[{{"place":"x","sort":{{"kind":"bit_vector","width":32,"signed":false}}}}],"borrows":[{{"region":"r0","place":"x","kind":"shared"}}]}}}},"obligations":[{{"id":{},"predicate":{{"kind":"not","expr":{{"kind":"logic","op":"and","left":{{"kind":"compare","op":"lt","left":{{"kind":"variable","name":"i","sort":{{"kind":"math_int"}}}},"right":{{"kind":"int_literal","value":"16","sort":{{"kind":"math_int"}}}}}},"right":{{"kind":"compare","op":"ge","left":{{"kind":"variable","name":"i","sort":{{"kind":"math_int"}}}},"right":{{"kind":"int_literal","value":"16","sort":{{"kind":"math_int"}}}}}}}}}},"location":"src/lib.rs:12:9"}}]}}"#
        ),
        encoded_id
    ))
    .expect("direct MIR-memory fixture must be valid JSON");
    // The compiler transport is byte-exact: mirror the producer's recursive
    // object-key canonicalization rather than attaching source-ordered JSON.
    canonicalize_fixture_json(&mut proof_unit);
    let proof_unit =
        serde_json::to_string(&proof_unit).expect("direct MIR-memory fixture canonicalizes");
    let obligation = &mut bundle.obligations[0];
    obligation.metadata.extend(trust_vc_bridge::trust_vc_typed_proof_metadata());
    obligation.metadata.extend([
        MetadataEntry {
            key: "trust.vc.formula.schema".to_string(),
            value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        },
        MetadataEntry { key: "trust.vc.formula.sort".to_string(), value: "Bool".to_string() },
        MetadataEntry {
            key: "trust.vc.formula.smtlib2".to_string(),
            value: "(and (< i 16) (>= i 16))".to_string(),
        },
        MetadataEntry {
            key: "trust.vc.formula.payload".to_string(),
            // The producer's canonical bytes (sorted keys), the one spelling
            // the direct-carrier validator accepts since 10e364d13f.
            value: String::from_utf8(
                trust_types::canonical_json_bytes(&public_predicate)
                    .expect("direct public predicate serializes canonically"),
            )
            .expect("canonical JSON is UTF-8"),
        },
        MetadataEntry {
            key: "trust.vc.digest.sha256".to_string(),
            value: "1111111111111111111111111111111111111111111111111111111111111111".to_string(),
        },
        MetadataEntry {
            key: trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY.to_string(),
            value: trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
        },
        MetadataEntry {
            key: trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            value: proof_unit,
        },
        MetadataEntry {
            key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY
                .to_string(),
            value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED
                .to_string(),
        },
        MetadataEntry {
            key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY
                .to_string(),
            value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON.to_string(),
        },
    ]);
    bundle
}

#[cfg(feature = "trust-vc-native")]
struct CountingTrustVcSpoof {
    manifest: EngineManifest,
    calls: Arc<AtomicUsize>,
}

#[cfg(feature = "trust-vc-native")]
impl CountingTrustVcSpoof {
    fn new(calls: Arc<AtomicUsize>) -> Self {
        let mut manifest = EngineManifest::new("trust-vc", "spoof", EngineKind::ProofCalculus);
        manifest.repository = Some("trust-vc-bridge".to_string());
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::MemorySafety,
            support: SupportLevel::Preferred,
        });
        Self { manifest, calls }
    }
}

#[cfg(feature = "trust-vc-native")]
impl VerificationEngine for CountingTrustVcSpoof {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::MemorySafety {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported { reason: "spoof only claims memory safety".to_string() }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        request
            .obligations()
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("spoof:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Unsupported,
                decline: None,
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec!["configured spoof was invoked".to_string()],
            })
            .collect()
    }
}

struct ReservedDirectTrustVcNamespaceSpoof {
    manifest: EngineManifest,
    reserve_evidence_id: bool,
    reserve_artifact_uri: bool,
}

impl ReservedDirectTrustVcNamespaceSpoof {
    fn new(reserve_evidence_id: bool, reserve_artifact_uri: bool) -> Self {
        let mut manifest =
            EngineManifest::new("trust-vc", "reserved-spoof", EngineKind::ProofCalculus);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::MemorySafety,
            support: SupportLevel::Preferred,
        });
        Self { manifest, reserve_evidence_id, reserve_artifact_uri }
    }
}

impl VerificationEngine for ReservedDirectTrustVcNamespaceSpoof {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::MemorySafety {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported {
                reason: "reserved-direct spoof only claims memory safety".to_string(),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        request
            .obligations()
            .iter()
            .map(|obligation| {
                let mut artifacts =
                    exact_fixture_trust_vc_certificate(obligation, "reserved-direct-spoof");
                if self.reserve_artifact_uri {
                    artifacts[0].uri = format!(
                        "{}{}",
                        trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX,
                        obligation.obligation_id,
                    );
                }
                ObligationEvidence {
                    evidence_id: if self.reserve_evidence_id {
                        format!("trust-vc:direct-mir-memory:{}", obligation.obligation_id)
                    } else {
                        format!("spoof:trust-vc:{}", obligation.obligation_id)
                    },
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Proved,
                    decline: None,
                    proof_strength: Some(ProofStrength::certified(
                        ReasoningKind::OwnershipAnalysis,
                    )),
                    artifacts,
                    counterexample: None,
                    publication: EvidencePublicationMetadata::default(),
                    diagnostics: vec!["public reserved-direct lookalike".to_string()],
                }
            })
            .collect()
    }
}

#[test]
fn reserved_direct_trust_vc_namespace_stays_receipt_exclusive_when_artifacts_are_optional() {
    for (label, reserve_evidence_id, reserve_artifact_uri) in
        [("evidence-id", true, false), ("artifact-uri", false, true)]
    {
        let engine = FullVerificationEngine::new(
            vec![Box::new(ReservedDirectTrustVcNamespaceSpoof::new(
                reserve_evidence_id,
                reserve_artifact_uri,
            ))],
            FullVerificationPolicy {
                require_proof_artifacts: false,
                require_all_required_engines: false,
                ..FullVerificationPolicy::default()
            },
        );
        let bundle = bundle_with_obligation(
            ObligationKind::MemorySafety,
            &format!("memory.reserved-direct-spoof.{label}"),
            None,
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis)),
        );

        let context = VerifierExecutionContext::new(format!("reserved-direct-spoof-{label}"));
        let live = engine
            .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                &bundle,
                &bundle.obligations,
                None,
                None,
                &context,
            );
        assert!(
            live.direct_trust_vc_receipts().is_empty(),
            "configured public spoof minted a private receipt for {label}"
        );
        let result = live.result();

        assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{label}: {result:#?}");
        assert_eq!(result.summary.proved, 0, "{label}: {result:#?}");
        assert_eq!(result.summary.missing_proof_artifacts, 1, "{label}: {result:#?}");
        assert_eq!(result.evidence[0].status, EvidenceStatus::Proved, "{label}: {result:#?}");
        assert!(result.evidence[0].artifacts.is_empty(), "{label}: {result:#?}");
        assert!(
            result.evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(
                    "direct TrustVC certificate evidence lacked the matching private post-solve receipt",
                ) || diagnostic.contains(
                    "proved evidence failed the exact owner-bound materialization DAG",
                )
            }),
            "{label}: {result:#?}"
        );
    }
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_granular_feature_proves_with_private_receipt_and_skips_spoof() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.router");

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("direct-trust-vc-granular"));

    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
    assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert!(result.evidence[0].evidence_id.starts_with("trust-vc:direct-mir-memory:"));
    assert!(result.evidence[0].artifacts.iter().any(|artifact| {
        artifact
            .uri
            .starts_with(trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX)
    }));
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_live_api_preserves_no_native_affine_receipt() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.live.no-native");
    let context = VerifierExecutionContext::new("direct-trust-vc-live-no-native");

    let live = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle,
        &bundle.obligations,
        None,
        None,
        &context,
    );

    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
    assert_eq!(live.result().status, VerificationRunStatus::Proved, "{live:#?}");
    assert_eq!(live.direct_trust_vc_receipts().len(), 1, "{live:#?}");
    assert!(live.fresh_exact_direct_chc_pdr_receipts().is_empty(), "{live:#?}");

    let (result, mut live_receipts) = live.into_parts();
    let mut direct_receipts = live_receipts.take_direct_trust_vc_receipts();
    assert!(live_receipts.take_fresh_exact_direct_chc_pdr_receipts().is_empty());
    let receipt = direct_receipts
        .remove("memory.direct.live.no-native")
        .expect("genuine direct solve must retain its affine receipt");
    assert!(direct_receipts.is_empty());
    assert_eq!(receipt.public_obligation_id(), "memory.direct.live.no-native");
    assert_eq!(receipt.dispatch_deadline(), context.deadline());
    assert_eq!(
        live_receipts
            .authorizes_direct_trust_vc_receipt(
                &receipt,
                &bundle.obligations[0],
                &result.evidence[0],
            )
            .expect("receipt must authorize the exact final composite row"),
        ProofStrength::certified(ReasoningKind::OwnershipAnalysis),
    );
    context.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
    assert!(
        live_receipts
            .authorizes_direct_trust_vc_receipt(
                &receipt,
                &bundle.obligations[0],
                &result.evidence[0],
            )
            .is_err(),
        "the coupled package must observe cancellation after publication"
    );
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_receipt_rejects_byte_identical_cross_dispatch_transplant() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.cross-dispatch");
    // Reuse the exact same public inputs so both result envelopes are equal
    // after normalizing observational timing and their evidence rows are exact.
    let context = VerifierExecutionContext::new("direct-trust-vc-cross-dispatch");
    let first = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle,
        &bundle.obligations,
        None,
        None,
        &context,
    );
    // The public batch diagnostic deliberately reports measured elapsed
    // milliseconds. Normalize only that observational field at this test seam
    // so host timing cannot decide whether the authority test runs. The exact
    // evidence rows below remain untouched and must still serialize to
    // byte-identical public carriers.
    let normalize_batch_elapsed = |run: &VerificationRunResult| {
        let mut normalized = run.clone();
        let mut normalized_count = 0;
        for diagnostic in &mut normalized.diagnostics {
            let Some((prefix, measured)) = diagnostic.split_once(" elapsed_ms=") else {
                continue;
            };
            if !prefix.starts_with("full-verification engine batch:") {
                continue;
            }
            let (elapsed_ms, suffix) = measured
                .split_once(" worker_threads=")
                .expect("batch diagnostic retains its worker-thread field");
            elapsed_ms.parse::<u128>().expect("batch elapsed value is an integer");
            *diagnostic = format!("{prefix} elapsed_ms=<normalized> worker_threads={suffix}");
            normalized_count += 1;
        }
        assert_eq!(normalized_count, 1, "one batch timing diagnostic is normalized");
        normalized
    };
    // Run independent calls until one agrees with the first in everything but
    // that timing field, so this regression exercises byte-identical public
    // carriers rather than obtaining rejection from a difference in them. The
    // comparison must normalize. 77ce4babd5 (2026-08-20) replaced this loop with
    // one second run compared after normalizing; the b62 squash d24c671211
    // (2026-08-31) brought back the loop over the raw results, so whether any
    // of 64 candidates matched was down to host timing (measured
    // 2026-10-01: the first call's batch took 9-51 ms and later ones 6-9 ms;
    // 0-2 candidates matched in one series of runs, none in 5 of 5 in another,
    // which failed the test before its subject).
    let second = (0..64)
        .find_map(|_| {
            let candidate = engine
                .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                    &bundle,
                    &bundle.obligations,
                    None,
                    None,
                    &context,
                );
            (normalize_batch_elapsed(candidate.result()) == normalize_batch_elapsed(first.result()))
                .then_some(candidate)
        })
        .expect("fixture must produce a byte-identical independent public run");
    let (first_run, mut first_live_receipts) = first.into_parts();
    let (second_run, second_live_receipts) = second.into_parts();
    let mut first_receipts = first_live_receipts.take_direct_trust_vc_receipts();

    assert_eq!(
        normalize_batch_elapsed(&first_run),
        normalize_batch_elapsed(&second_run),
        "independent public runs differ only in observational batch timing",
    );
    assert_eq!(
        serde_json::to_vec(&first_run.evidence[0]).expect("first public carrier serializes"),
        serde_json::to_vec(&second_run.evidence[0]).expect("second public carrier serializes"),
        "the authority-bearing public carriers must be byte-identical",
    );
    let receipt = first_receipts
        .remove("memory.direct.cross-dispatch")
        .expect("first live dispatch must retain its receipt");
    let obligation = &bundle.obligations[0];
    assert!(
        first_live_receipts
            .authorizes_direct_trust_vc_receipt(&receipt, obligation, &first_run.evidence[0],)
            .is_ok()
    );
    assert!(
        second_live_receipts
            .authorizes_direct_trust_vc_receipt(&receipt, obligation, &second_run.evidence[0],)
            .is_err(),
        "byte-identical public evidence carriers retain distinct private dispatch identities",
    );
    let mut mutated_second_row = second_run.evidence[0].clone();
    mutated_second_row.evidence_id.push_str(":mutation-control");
    assert!(
        first_live_receipts
            .authorizes_direct_trust_vc_receipt(&receipt, obligation, &mutated_second_row,)
            .is_err(),
        "a mutated second-dispatch row must remain unauthorized",
    );
    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_public_result_round_trip_carries_no_receipt_authority() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.public-round-trip");
    let context = VerifierExecutionContext::new("direct-trust-vc-public-round-trip");

    let ordinary = engine.verify_bundle(&bundle, &context);
    assert_eq!(ordinary.status, VerificationRunStatus::Proved, "{ordinary:#?}");
    let public_json = serde_json::to_value(&ordinary).expect("public run must serialize");
    assert!(public_json.get("direct_trust_vc_receipts").is_none());
    assert!(public_json.get("fresh_exact_direct_chc_pdr_receipts").is_none());
    let round_trip: VerificationRunResult = serde_json::from_value(public_json)
        .expect("ordinary public run must deserialize independently of live sidecars");
    assert_eq!(round_trip, ordinary);

    let live = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle,
        &bundle.obligations,
        None,
        None,
        &context,
    );
    assert_eq!(live.direct_trust_vc_receipts().len(), 1, "{live:#?}");
    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_receipt_rejects_final_row_and_carrier_mutation() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.receipt-mutation");
    let context = VerifierExecutionContext::new("direct-trust-vc-receipt-mutation");
    let live = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle,
        &bundle.obligations,
        None,
        None,
        &context,
    );
    let (result, mut live_receipts) = live.into_parts();
    let mut receipts = live_receipts.take_direct_trust_vc_receipts();
    let receipt = receipts
        .remove("memory.direct.receipt-mutation")
        .expect("exact live direct solve must mint a receipt");
    let accepted = &result.evidence[0];
    let obligation = &bundle.obligations[0];
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, accepted,).is_ok()
    );

    let mut changed = accepted.clone();
    changed.evidence_id.push_str(":rewritten");
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.engine.version.push_str("-rewritten");
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.artifacts[0].uri.push_str(".rewritten");
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.diagnostics.push("rewritten diagnostic".to_string());
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.publication.dpub_release_id = Some("rewritten-release".to_string());
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.proof_strength = Some(ProofStrength::deductive());
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed = accepted.clone();
    changed.status = EvidenceStatus::Unknown;
    changed.proof_strength = None;
    assert!(
        live_receipts.authorizes_direct_trust_vc_receipt(&receipt, obligation, &changed,).is_err()
    );

    let mut changed_bundle = bundle.clone();
    changed_bundle.bundle_id.push_str("-rewritten");
    assert!(!live_receipts.matches_bundle(&changed_bundle));

    let mut changed_bundle = bundle.clone();
    let mut sibling = obligation.clone();
    sibling.obligation_id = "memory.direct.receipt-mutation.sibling".to_string();
    changed_bundle.obligations.push(sibling);
    assert!(!live_receipts.matches_bundle(&changed_bundle));

    let mut changed_bundle = bundle.clone();
    changed_bundle.subject =
        BundleSubject::Function { crate_name: "other".to_string(), path: "other::f".to_string() };
    assert!(!live_receipts.matches_bundle(&changed_bundle));

    let mut changed_bundle = bundle.clone();
    changed_bundle.obligations[0]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == "trust.vc.formula.payload")
        .expect("fixture carries the public typed predicate")
        .value
        .push(' ');
    assert!(!live_receipts.matches_bundle(&changed_bundle));
    assert!(
        live_receipts
            .authorizes_direct_trust_vc_receipt(&receipt, &changed_bundle.obligations[0], accepted,)
            .is_err()
    );
    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_duplicate_request_inventory_cannot_retain_receipts() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.duplicate-request");
    let duplicate = vec![bundle.obligations[0].clone(), bundle.obligations[0].clone()];
    let context = VerifierExecutionContext::new("direct-trust-vc-duplicate-request");

    let live = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle, &duplicate, None, None, &context,
    );

    assert!(live.direct_trust_vc_receipts().is_empty(), "{live:#?}");
    assert!(live.fresh_exact_direct_chc_pdr_receipts().is_empty(), "{live:#?}");
    assert_ne!(live.result().status, VerificationRunStatus::Proved, "{live:#?}");
    assert_eq!(calls.load(Ordering::SeqCst), 0, "invalid inventory must fail before dispatch");
    let (_, live_receipts) = live.into_parts();
    assert!(
        live_receipts.source_run().is_none(),
        "a zero-receipt result must not retain a source-run snapshot"
    );
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_private_receipt_still_proves_when_ordinary_artifacts_are_optional() {
    let calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
        FullVerificationPolicy {
            require_proof_artifacts: false,
            require_all_required_engines: false,
            ..FullVerificationPolicy::default()
        },
    );
    let bundle = direct_trust_vc_bundle("memory.direct.router.optional-artifacts");

    let result = engine.verify_bundle(
        &bundle,
        &VerifierExecutionContext::new("direct-trust-vc-optional-artifacts"),
    );

    assert_eq!(calls.load(Ordering::SeqCst), 0, "configured spoof must not run");
    assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert!(result.evidence[0].evidence_id.starts_with("trust-vc:direct-mir-memory:"));
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_partial_or_unknown_native_identity_fails_closed_without_spoof() {
    for key in [
        "trust.trust_ir.native.verifier_suite",
        "trust.trust_ir.native.proof_unit.v1",
        "trust.trust_ir.native.artifact_fingerprint",
        "trust.trust_ir.native.future_identity",
    ] {
        let calls = Arc::new(AtomicUsize::new(0));
        let engine = FullVerificationEngine::new(
            vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
            route_only_policy(),
        );
        let mut bundle = direct_trust_vc_bundle(&format!("memory.direct.partial.{key}"));
        bundle.obligations[0]
            .metadata
            .push(MetadataEntry { key: key.to_string(), value: "stale".to_string() });

        let result = engine.verify_bundle(
            &bundle,
            &VerifierExecutionContext::new(format!("direct-partial-{key}")),
        );

        assert_eq!(calls.load(Ordering::SeqCst), 0, "spoof ran for {key}");
        assert_ne!(result.status, VerificationRunStatus::Proved, "{key}: {result:#?}");
        assert_eq!(result.summary.proved, 0, "{key}: {result:#?}");
    }
}

#[cfg(feature = "trust-vc-native")]
#[test]
fn direct_trust_vc_mutated_or_duplicate_deferred_marker_fails_closed_without_spoof() {
    let base = direct_trust_vc_bundle("memory.direct.marker");
    let mut wrong_status = base.clone();
    wrong_status.obligations[0]
        .metadata
        .iter_mut()
        .find(|entry| {
            entry.key == trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY
        })
        .expect("direct fixture has deferred status")
        .value = "proved".to_string();
    let mut wrong_reason = base.clone();
    wrong_reason.obligations[0]
        .metadata
        .iter_mut()
        .find(|entry| {
            entry.key == trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY
        })
        .expect("direct fixture has deferred reason")
        .value = "caller-authored direct lane".to_string();
    let mut duplicate_status = base.clone();
    duplicate_status.obligations[0].metadata.push(MetadataEntry {
        key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY.to_string(),
        value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED.to_string(),
    });
    let mut duplicate_reason = base;
    duplicate_reason.obligations[0].metadata.push(MetadataEntry {
        key: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY.to_string(),
        value: trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON.to_string(),
    });

    for (label, bundle) in [
        ("wrong-status", wrong_status),
        ("wrong-reason", wrong_reason),
        ("duplicate-status", duplicate_status),
        ("duplicate-reason", duplicate_reason),
    ] {
        let calls = Arc::new(AtomicUsize::new(0));
        let engine = FullVerificationEngine::new(
            vec![Box::new(CountingTrustVcSpoof::new(calls.clone()))],
            route_only_policy(),
        );
        let result = engine.verify_bundle(
            &bundle,
            &VerifierExecutionContext::new(format!("direct-marker-{label}")),
        );

        assert_eq!(calls.load(Ordering::SeqCst), 0, "spoof ran for {label}");
        assert_ne!(result.status, VerificationRunStatus::Proved, "{label}: {result:#?}");
        assert_eq!(result.summary.proved, 0, "{label}: {result:#?}");
        assert!(
            result.evidence.iter().all(|row| row.status != EvidenceStatus::Proved
                && row.proof_strength.is_none()
                && row.artifacts.is_empty()),
            "{label}: {result:#?}"
        );
        assert_eq!(result.evidence.len() + result.skipped.len(), 1, "{label}: {result:#?}");
    }
}

#[cfg(not(feature = "trust-vc-native"))]
#[test]
fn direct_trust_vc_lane_is_disabled_without_router_granular_feature() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(TrustVcVerificationEngine::new())],
        route_only_policy(),
    );
    let bundle = direct_trust_vc_bundle("memory.direct.feature_off");

    let result = engine
        .verify_bundle(&bundle, &VerifierExecutionContext::new("direct-trust-vc-feature-off"));

    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
}

fn add_current_compiler_typed_vc_envelope(obligation: &mut TrustObligation) {
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(false),
        Vec::new(),
    );
    obligation.metadata.extend([
        trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                vc_kind: "loop_contract".to_string(),
                vc_index: 0,
                formula_schema: Some(
                    trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                ),
            },
        )
        .to_metadata_entry()
        .expect("typed VC context should serialize"),
        MetadataEntry {
            key: "trust.vc.formula.schema".to_string(),
            value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        },
        MetadataEntry {
            key: "trust.vc.formula.payload".to_string(),
            value: serde_json::to_string(&predicate).expect("typed VC predicate should serialize"),
        },
    ]);
}

fn typed_trust_wp_true_predicate() -> serde_json::Value {
    serde_json::json!({
        "kind": "bool",
        "value": true,
    })
}

fn bundle_with_typed_trust_wp_postcondition() -> TrustContractBundle {
    let mut bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    bundle.obligations[0].obligation_id = "trust_ir-native-trust-wp-request-2-proof-2".to_string();
    bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: "TrustWpPureExprV1".to_string(),
        value: typed_trust_wp_true_predicate(),
    };
    bundle.obligations[0].metadata.extend(native_trust_ir_metadata("trust-wp", 2, 2));
    bundle
}

#[test]
fn required_native_engines_fail_closed_without_typed_proof_input() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-1"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.unsupported, 1);
    assert!(!result.is_fully_proved());
    assert!(!result.evidence[0].diagnostics.is_empty());
    assert!(result.evidence[0].diagnostics.iter().all(|diagnostic| {
        !diagnostic.contains("missing: trust-wp")
            && !diagnostic.contains("requires native trust-wp")
    }));

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 1);
    assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-mc"));
    assert!(!structured[0].has_accepted_proof());
    assert_eq!(structured[0].decisions[0].status, EvidenceStatus::Unsupported);
    assert_eq!(structured[0].decisions[0].diagnostics, result.evidence[0].diagnostics);
    assert!(structured[0].blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id, .. }
                if obligation_id == "obligation-ensures"
        )
    }));
}

#[test]
fn full_verifier_trait_entrypoint_fails_closed_without_execution_context() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

    let evidence = engine.verify(&bundle, &bundle.obligations);

    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
    assert!(evidence[0].proof_strength.is_none());
    assert!(evidence[0].artifacts.is_empty());
    assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("requires VerifierExecutionContext")
            && diagnostic.contains("resource limits")
            && diagnostic.contains("run manifests")
    }));
}

fn ty_proving_engine() -> FullVerificationEngine {
    FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "ty",
            EngineKind::Temporal,
            ObligationKind::Liveness,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                }),
                artifacts: vec![
                    solver_transcript_artifact("ty-wall-time-transcript"),
                    proof_check_artifact("ty-wall-time-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    )
}

#[test]
fn full_verifier_wall_time_limit_times_out_before_accepting_proof() {
    let engine = ty_proving_engine();
    let bundle = bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    let context = VerifierExecutionContext::new("run-wall-time-zero")
        .with_limits(VerifierResourceLimits::unlimited().with_wall_time_ms(0));

    let result = engine.verify_bundle(&bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::TimedOut);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.timed_out, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Timeout);
    assert!(
        result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("full-verification wall-clock budget exceeded")
        })
    );
}

#[test]
fn full_verifier_wall_time_limit_does_not_extend_existing_deadline() {
    let engine = ty_proving_engine();
    let bundle = bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    let elapsed_deadline =
        Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
    let context = VerifierExecutionContext::new("run-existing-deadline")
        .with_limits(VerifierResourceLimits::unlimited().with_wall_time_ms(60_000))
        .with_deadline(elapsed_deadline);

    let result = engine.verify_bundle(&bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::TimedOut);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.timed_out, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Timeout);
}

/// A liveness primary that records the deadline of every context it is handed.
struct DeadlineRecordingEngine {
    manifest: EngineManifest,
    seen: Arc<Mutex<Vec<Option<Instant>>>>,
}

impl DeadlineRecordingEngine {
    fn new(seen: Arc<Mutex<Vec<Option<Instant>>>>) -> Self {
        let mut manifest = EngineManifest::new("ty", "0.1.0", EngineKind::Temporal);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::Liveness,
            support: SupportLevel::Preferred,
        });
        Self { manifest, seen }
    }
}

impl VerificationEngine for DeadlineRecordingEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::Liveness {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported { reason: "liveness only".to_string() }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        request
            .obligations()
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("ty:deadline:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                }),
                artifacts: exact_fixture_proof_artifacts(obligation, "deadline-ty"),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            })
            .collect()
    }

    fn verify_with_context_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        self.seen.lock().expect("seen lock").push(context.deadline());
        let (bundle, obligations) = request.into_parts();
        let evidence = self.verify_validated(request);
        VerificationRunResult::from_evidence(
            context.snapshot(),
            bundle,
            self.manifest.clone(),
            obligations,
            evidence,
        )
    }
}

/// gate-rca deadline (2026-10-17): the native lane's primary solve stops at the context's
/// native solve cutoff — the engine is handed the cutoff as its deadline — while the run
/// itself stays live until the function deadline and keeps the proof the solve made in
/// time. Control: without a cutoff the engine is handed the function deadline.
#[test]
fn full_verifier_hands_the_native_solve_cutoff_to_the_primary_solve() {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![Box::new(DeadlineRecordingEngine::new(seen.clone()))],
        route_only_policy(),
    );
    let bundle = bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    let deadline = Instant::now() + Duration::from_secs(3600);
    let cutoff = Instant::now() + Duration::from_secs(1800);

    let cut = VerifierExecutionContext::new("run-native-cutoff")
        .with_deadline(deadline)
        .with_native_solve_cutoff(Some(cutoff));
    let result = engine.verify_bundle(&bundle, &cut);
    assert_eq!(result.summary.proved, 1, "a solve inside the cutoff keeps its proof");
    assert_eq!(result.summary.timed_out, 0, "the run is not late: its deadline is the function's");

    let plain = VerifierExecutionContext::new("run-no-cutoff").with_deadline(deadline);
    let _ = engine.verify_bundle(&bundle, &plain);
    assert_eq!(
        *seen.lock().expect("seen lock"),
        vec![Some(cutoff), Some(deadline)],
        "the primary solve is clocked by the cutoff, and only when one is set"
    );
}

#[test]
fn full_verifier_obligation_limit_times_out_before_dispatch() {
    let calls = Arc::new(AtomicUsize::new(0));
    let batch_sizes = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![Box::new(BatchCountingEngine::new(calls.clone(), batch_sizes.clone()))],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::Liveness, "obligation-live-1", None, None);
    let mut second_obligation = bundle.obligations[0].clone();
    second_obligation.obligation_id = "obligation-live-2".to_string();
    bundle.obligations.push(second_obligation);
    let context = VerifierExecutionContext::new("run-obligation-limit")
        .with_limits(VerifierResourceLimits::unlimited().with_obligation_limit(1));

    let result = engine.verify_bundle(&bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::TimedOut);
    assert_eq!(result.evidence.len(), 2);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.timed_out, 2);
    assert_eq!(result.summary.skipped, 0);
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(batch_sizes.lock().expect("batch sizes lock").is_empty());
    assert!(result.evidence.iter().all(|evidence| {
        evidence.status == EvidenceStatus::Timeout
            && evidence.proof_strength.is_none()
            && evidence.artifacts.is_empty()
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("full-verification obligation limit exceeded")
            && diagnostic.contains("requested_obligations=2")
            && diagnostic.contains("limit=1")
    }));
}

#[test]
fn full_verifier_obligation_limit_equal_count_allows_dispatch() {
    let calls = Arc::new(AtomicUsize::new(0));
    let batch_sizes = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![Box::new(BatchCountingEngine::new(calls.clone(), batch_sizes.clone()))],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::Liveness, "obligation-live-1", None, None);
    let mut second_obligation = bundle.obligations[0].clone();
    second_obligation.obligation_id = "obligation-live-2".to_string();
    bundle.obligations.push(second_obligation);
    let context = VerifierExecutionContext::new("run-obligation-limit-equal")
        .with_limits(VerifierResourceLimits::unlimited().with_obligation_limit(2));

    let result = engine.verify_bundle(&bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 2);
    assert_eq!(result.summary.timed_out, 0);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(*batch_sizes.lock().expect("batch sizes lock"), vec![2]);
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("obligation limit exceeded"))
    );
}

#[test]
fn required_native_trust_mc_engine_owns_hardened_custom_obligations() {
    // This ownership test is independent of whether optional trust-wp/trust-vc
    // production adapters are compiled. Disable the all-engine availability
    // precondition while retaining the real required engine set.
    let engine = FullVerificationEngine::new(required_native_engines(), route_only_policy());
    let mut names = [
        "raw_path_api",
        "path_identity",
        "permission_change",
        "permission_create",
        "permission_window",
        "utf8_reject",
        "byte_loss",
        "error_discard",
        "panic_boundary",
        "compat_observable",
        "process_semantics",
        "trust_domain",
        "trust_domain_order",
        "unsafe_operation",
        "ffi_boundary",
        "unknown",
        "future_kernel_object_identity",
    ]
    .into_iter();

    for name in names.by_ref() {
        let obligation_id = format!("obligation-hardened-{name}");
        let kind = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: name.to_string(),
        };
        let bundle = bundle_with_obligation(
            kind.clone(),
            &obligation_id,
            None,
            Some(ProofStrength::smt_unsat()),
        );
        assert!(engine.supports(&bundle.obligations[0]).is_supported());

        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-hardened"));
        assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.requested_obligations, 1);
        assert_eq!(result.summary.unsupported, 1);
        let structured = result.full_verification_obligation_evidence();
        assert_eq!(structured.len(), 1);
        assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-mc"));
        assert_eq!(structured[0].decisions[0].status, EvidenceStatus::Unsupported);
        assert!(structured[0].blockers.iter().any(|blocker| {
            matches!(
                blocker,
                FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id: id, .. }
                    if id == &obligation_id
            )
        }));
    }

    let manifest = engine.manifest();
    for name in ["panic_boundary", "trust_domain_order", "unknown", TRUST_VC_HARDENED_WILDCARD] {
        assert!(manifest.capabilities.iter().any(|capability| {
            capability.obligation_kind
                == ObligationKind::Custom {
                    namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                    name: name.to_string(),
                }
        }));
    }
}

#[cfg(feature = "trust-build")]
#[test]
fn required_native_engines_route_primary_obligation_families_fail_closed() {
    let engine = FullVerificationEngine::with_required_native_engines();
    for (kind, expected_suite) in [
        (ObligationKind::Precondition, "trust-mc"),
        (ObligationKind::Postcondition, "trust-mc"),
        (ObligationKind::LoopInvariant, "trust-mc"),
        (ObligationKind::Termination, "trust-mc"),
        (ObligationKind::Refinement, "trust-vc"),
        (ObligationKind::MemorySafety, "trust-vc"),
        (ObligationKind::Ownership, "trust-vc"),
        (ObligationKind::Assertion, "trust-mc"),
        (ObligationKind::Protocol, "trust-mc"),
        (ObligationKind::TemporalSafety, "ty"),
    ] {
        let obligation_id = format!("obligation-route-{expected_suite}-{kind:?}");
        let bundle =
            bundle_with_obligation(kind, &obligation_id, None, Some(ProofStrength::deductive()));

        assert!(engine.supports(&bundle.obligations[0]).is_supported());
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-routes"));

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.requested_obligations, 1);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        let structured = result.full_verification_obligation_evidence();
        assert_eq!(structured[0].primary_suite.as_deref(), Some(expected_suite));
        assert_eq!(structured[0].decisions[0].status, EvidenceStatus::Unsupported);
        assert!(structured[0].blockers.iter().any(|blocker| {
            matches!(
                blocker,
                FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id: id, .. }
                    if id == &obligation_id
            )
        }));
    }
}

// Trust (#nia-oom, batch 6): the `trust.vc.unbounded_allocation` namespace is
// trust-vc-owned via the certificate-import route (the BoundsCheck precedent).
// Ownership is DISPATCH, never proof: without a validated MIR-memory proof unit
// + replayed certificate the obligation stays Unsupported (fail-closed), which
// is exactly what this pin asserts. It must NEVER route to trust-mc — the
// whole-function CHC does not encode `count >= ceiling` and that mapping
// false-proved unbounded allocations (the recorded P0 at trust-verifier-api's
// namespace constant).
#[cfg(feature = "trust-build")]
#[test]
fn unbounded_allocation_namespace_routes_to_trust_vc_fail_closed() {
    let engine = FullVerificationEngine::with_required_native_engines();
    // Namespace-keyed: the name is a label within the admitted namespace.
    for name in ["unbounded_allocation", "a_name_no_consumer_knows"] {
        let kind = ObligationKind::Custom {
            namespace: trust_verifier_api::TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE
                .to_string(),
            name: name.to_string(),
        };
        let obligation_id = format!("obligation-unbounded-alloc-{name}");
        let bundle =
            bundle_with_obligation(kind, &obligation_id, None, Some(ProofStrength::deductive()));
        assert!(engine.supports(&bundle.obligations[0]).is_supported());

        let result =
            engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-unbounded-alloc"));
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0, "no proof may be minted without a certificate");
        assert_eq!(result.summary.unsupported, 1);
        let structured = result.full_verification_obligation_evidence();
        assert_eq!(
            structured[0].primary_suite.as_deref(),
            Some("trust-vc"),
            "the capacity obligation is trust-vc-owned, never trust-mc/CHC"
        );
        assert_eq!(structured[0].decisions[0].status, EvidenceStatus::Unsupported);
    }
}

// Cross-table agreement for the trust-vc MIR-memory certificate-import lane:
// the router's route table, the trust-vc adapter's ownership predicate, and
// the shared producer/consumer native-kind mapping must agree on exactly which
// public kinds ride the proof-unit transport. A drift here is how an
// obligation ends up Pending in a native bundle with no certificate
// (MissingTrustVcEvidenceForObligation poisoning the whole function) — or,
// worse, routed to an engine whose proof does not encode its property.
#[cfg(feature = "trust-build")]
#[test]
fn mir_memory_transport_kind_tables_agree() {
    let unbounded = ObligationKind::Custom {
        namespace: trust_verifier_api::TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE
            .to_string(),
        name: "unbounded_allocation".to_string(),
    };
    let engine = FullVerificationEngine::with_required_native_engines();
    for kind in [
        ObligationKind::MemorySafety,
        ObligationKind::Ownership,
        ObligationKind::BoundsCheck,
        unbounded,
    ] {
        // Router table: trust-vc primary.
        let obligation_id = format!("obligation-agreement-{kind:?}");
        let bundle = bundle_with_obligation(
            kind.clone(),
            &obligation_id,
            None,
            Some(ProofStrength::deductive()),
        );
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-agreement"));
        let structured = result.full_verification_obligation_evidence();
        assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-vc"), "{kind:?}");
        // Adapter ownership predicate.
        assert!(trust_vc_bridge::is_trust_vc_owned_obligation_kind(&kind), "{kind:?}");
        assert!(trust_vc_bridge::requires_trust_vc_ownership_context(&kind), "{kind:?}");
        // Producer/consumer native-suite kind mapping.
        assert_eq!(
            trust_vc_bridge::trust_vc_native_trust_ir_kind_for_public_obligation(&kind),
            Some(trust_ir::ObligationKind::MemorySafety),
            "{kind:?}"
        );
    }
}

#[test]
fn refinement_routes_only_to_trust_vc_contract_frame_transport() {
    let kind = ObligationKind::Refinement;
    let route =
        super::routing::obligation_route_for_kind(&kind).expect("refinement has a v6/D3 route");
    assert_eq!(route.primary.name(), "trust-vc");
    assert!(trust_vc_bridge::is_trust_vc_owned_obligation_kind(&kind));
    assert!(trust_vc_bridge::requires_trust_vc_contract_frame(&kind));
    assert!(!trust_vc_bridge::requires_trust_vc_ownership_context(&kind));
    // The producer/consumer kind mapping is `trust-build`-gated in the
    // bridge (enabled from this crate via `trust-vc-native`, like every
    // other native-mapping assertion in this file); a default-features
    // build cannot reference it at all.
    #[cfg(feature = "trust-vc-native")]
    assert_eq!(
        trust_vc_bridge::trust_vc_native_trust_ir_kind_for_public_obligation(&kind),
        Some(trust_ir::ObligationKind::RefinementType)
    );
    assert!(!trust_wp::is_trust_wp_owned_obligation_kind(&kind));
}

// Trust (P1.2 precedent, extended to preconditions and E4/E5): a body-aware VC
// carrying the accepted typed formula envelope must be DISPATCHED to trust-mc for
// Postcondition (the `#[ensures]` VC), Precondition (the call-site
// `#[requires]` VC), LoopInvariant (E4 initiation/consecution), and Termination
// (E5 non-negative/strict-decrease). This route is both the engine dispatch and the
// expected-suite the native-TrustIr evidence validation compares against the
// compiler's recorded trust-mc proof unit. Payload-less kinds are TrustMC-owned
// too and fail closed there when no body formula exists.
#[test]
fn payload_carrying_body_aware_contract_vcs_route_to_trust_mc() {
    let engine = FullVerificationEngine::with_required_native_engines();
    for kind in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::Termination,
    ] {
        let obligation_id = format!("obligation-payload-route-{kind:?}");
        let mut bundle = bundle_with_obligation(
            kind.clone(),
            &obligation_id,
            None,
            Some(ProofStrength::deductive()),
        );
        if matches!(kind, ObligationKind::LoopInvariant | ObligationKind::Termination) {
            add_current_compiler_typed_vc_envelope(&mut bundle.obligations[0]);
        } else {
            bundle.obligations[0].metadata.push(MetadataEntry {
                key: "trust.vc.formula.payload".to_string(),
                value: "{\"kind\":\"bool\",\"value\":false}".to_string(),
            });
        }

        let result =
            engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-payload-routes"));

        let structured = result.full_verification_obligation_evidence();
        assert_eq!(
            structured[0].primary_suite.as_deref(),
            Some("trust-mc"),
            "payload-carrying {:?} VC must dispatch to trust-mc",
            bundle.obligations[0].kind
        );
    }
}

#[test]
fn payloadless_e4_e5_claims_are_trust_mc_owned_and_fail_closed() {
    let engine = FullVerificationEngine::with_required_native_engines();
    for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
        let obligation_id = format!("obligation-claim-route-{kind:?}");
        let bundle =
            bundle_with_obligation(kind, &obligation_id, None, Some(ProofStrength::deductive()));

        let result =
            engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-claim-routes"));

        let structured = result.full_verification_obligation_evidence();
        assert_eq!(
            structured[0].primary_suite.as_deref(),
            Some("trust-mc"),
            "payload-less {:?} claim stays TrustMC-owned and must fail closed there",
            bundle.obligations[0].kind,
        );
    }
}

#[test]
fn partial_or_forged_e4_e5_formula_envelopes_do_not_change_trust_mc_ownership() {
    let engine = FullVerificationEngine::with_required_native_engines();
    for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
        let obligation_id = format!("obligation-forged-payload-route-{kind:?}");
        let mut bundle =
            bundle_with_obligation(kind, &obligation_id, None, Some(ProofStrength::deductive()));
        bundle.obligations[0].metadata.push(MetadataEntry {
            key: "trust.vc.formula.payload".to_string(),
            value: serde_json::to_string(&trust_verifier_api::TrustSpecPredicate::new(
                trust_verifier_api::TrustSpecExpr::bool_literal(false),
                Vec::new(),
            ))
            .expect("typed VC predicate should serialize"),
        });

        let result = engine
            .verify_bundle(&bundle, &VerifierExecutionContext::new("run-forged-e4-e5-routes"));

        let structured = result.full_verification_obligation_evidence();
        assert_eq!(
            structured[0].primary_suite.as_deref(),
            Some("trust-mc"),
            "partial {:?} formula metadata must not change ownership",
            bundle.obligations[0].kind,
        );
    }
}

#[test]
fn malformed_typed_e4_e5_predicates_do_not_change_dispatch_ownership() {
    let engine = FullVerificationEngine::with_required_native_engines();
    for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
        let obligation_id = format!("obligation-malformed-typed-payload-route-{kind:?}");
        let mut bundle =
            bundle_with_obligation(kind, &obligation_id, None, Some(ProofStrength::deductive()));
        add_current_compiler_typed_vc_envelope(&mut bundle.obligations[0]);

        // This payload has the current schema and a Boolean root, so the
        // former schema/root-only routing check accepted it even though the
        // root references an undeclared variable. TrustMC rejects the same
        // payload in its full typed-predicate validator; routing must apply
        // that validator too so malformed metadata cannot change ownership.
        let malformed = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::variable(
                "undeclared",
                trust_verifier_api::TrustSpecSort::Bool,
            ),
            Vec::new(),
        );
        assert!(malformed.validate().is_err());
        let payload = bundle.obligations[0]
            .metadata
            .iter_mut()
            .find(|entry| entry.key == "trust.vc.formula.payload")
            .expect("compiler envelope must contain a typed VC payload");
        payload.value = serde_json::to_string(&malformed)
            .expect("malformed typed VC predicate should still serialize");

        let result = engine.verify_bundle(
            &bundle,
            &VerifierExecutionContext::new("run-malformed-typed-e4-e5-routes"),
        );

        let structured = result.full_verification_obligation_evidence();
        assert_eq!(
            structured[0].primary_suite.as_deref(),
            Some("trust-mc"),
            "malformed {:?} formula metadata must not change ownership",
            bundle.obligations[0].kind,
        );
    }
}

#[test]
fn historical_trust_wp_metadata_cannot_revive_retired_ownership() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle_with_typed_trust_wp_postcondition();

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-retired-trust-wp"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-mc"));
    assert!(!structured[0].has_accepted_proof());
}

#[test]
fn body_aware_trust_wp_request_preserves_primary_and_historical_wire() {
    let live = native_trust_ir_mc_bundle();
    assert_eq!(
        live.requests
            .iter()
            .filter(|request| matches!(request, NativeVerificationRequest::TrustWp(_)))
            .count(),
        1,
        "the postcondition has one native deductive alternative",
    );

    let historical = historical_native_trust_wp_bundle();
    assert_eq!(
        historical
            .requests
            .iter()
            .filter(|request| matches!(request, NativeVerificationRequest::TrustWp(_)))
            .count(),
        1,
        "the compatibility fixture must contain one genuine historical TrustWP wire row",
    );
    let encoded = serde_json::to_value(&historical).expect("historical bundle serializes");
    let decoded: NativeVerificationBundle =
        serde_json::from_value(encoded).expect("historical TrustWP wire remains readable");
    decoded.validate().expect("historical bundle remains structurally valid");

    let post = bundle_with_typed_trust_wp_postcondition();
    let route = super::routing::obligation_route(&post.obligations[0])
        .expect("postcondition remains routable");
    assert_eq!(route.primary.name(), "trust-mc");
    assert!(!trust_wp::is_trust_wp_owned_obligation_kind(&post.obligations[0].kind));
}

#[cfg(feature = "trust-build")]
#[test]
fn historical_native_trust_wp_bundle_cannot_authorize_a_public_postcondition() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle_with_typed_trust_wp_postcondition();
    let mut native_bundle = historical_native_trust_wp_bundle();
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(2),
        &bundle,
        0,
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-retired-native-trust-wp"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-mc"));
    assert!(!structured[0].has_accepted_proof());
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_rejects_formula_less_assertion_transport_laundering() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-mc",
        BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::router_native_checked_branch".to_string(),
        },
    );
    let native_obligation_id = "trust_ir-native-trust-mc-request-7-proof-0";
    let mut public_obligation = native_trust_ir_obligation(
        "trust-mc",
        7,
        0,
        ObligationKind::Assertion,
        // A caller-requested strength and typed-transport metadata do not make
        // this formula-less Assertion an exact compiler-authenticated E4/E5
        // row or whole-function panic-freedom aggregate.
        Some(ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked }),
    );
    assert_eq!(public_obligation.obligation_id, native_obligation_id);
    public_obligation.source = router_native_source_location(18);
    add_trust_mc_public_typed_chc_binding_metadata(&mut public_obligation, native_obligation_id);
    bundle.obligations = vec![public_obligation];
    let mut native_bundle = native_trust_mc_safe_trust_ir_bundle();
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(0),
        &bundle,
        0,
    );
    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-mc-trust_ir"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.summary.missing_proof_artifacts, 0);
    let evidence = &result.evidence[0];
    assert_eq!(evidence.status, EvidenceStatus::Unsupported);
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .contains("not the exact compiler-authenticated whole-function panic-freedom aggregate")
            && diagnostic.contains("refusing to substitute")
    }));
    assert!(!result.full_verification_obligation_evidence()[0].has_accepted_proof());
}

#[test]
fn full_verifier_rejects_invalid_public_bundle_before_engine_dispatch() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut bundle = bundle_with_obligation(
        ObligationKind::Postcondition,
        "duplicate-public-obligation",
        None,
        None,
    );
    bundle.obligations.push(bundle.obligations[0].clone());

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-invalid-public-bundle"));

    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("verifier rejected non-canonical obligation request")
            && diagnostic.contains("duplicate obligation IDs")
    }));
}

#[test]
fn full_verifier_rejects_id_preserving_obligation_substitution_before_dispatch() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::Postcondition,
            ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked },
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    let mut substituted = bundle.obligations.clone();
    substituted[0].description = "different claim under the same identity".to_string();

    let result = engine.verify_with_context(
        &bundle,
        &substituted,
        &VerifierExecutionContext::new("run-substituted-request"),
    );

    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("verifier rejected non-canonical obligation request")
            && diagnostic.contains("differs from its canonical bundle record")
    }));
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_rejects_trust_mc_when_native_trust_ir_bundle_is_unsupported() {
    let mut native_bundle = native_trust_mc_safe_trust_ir_bundle();
    for request in &mut native_bundle.requests {
        if let NativeVerificationRequest::TrustMc(request) = request {
            request.mode = trust_ir::TrustMcVerificationMode::BoundedModelCheck;
        }
    }

    let mut trust_mc = UnitEngine::new(
        "trust-mc",
        EngineKind::Reachability,
        ObligationKind::Assertion,
        SupportLevel::Preferred,
        UnitEvidenceMode::Evidence {
            status: EvidenceStatus::Proved,
            proof_strength: Some(ProofStrength {
                reasoning: ReasoningKind::Pdr,
                assurance: AssuranceLevel::SmtBacked,
            }),
            artifacts: vec![
                solver_transcript_artifact("trust-mc-direct-proof-transcript"),
                proof_check_artifact("trust-mc-direct-proof-check"),
            ],
            diagnostics: vec!["direct typed trust_mc proof must not be used".to_string()],
        },
    );
    trust_mc.manifest.repository = Some("trust-bmc".to_string());
    trust_mc.manifest.version = "0.1.0+native-trust-ir-bundle".to_string();

    let engine = FullVerificationEngine::new(vec![Box::new(trust_mc)], route_only_policy());
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-mc-rejected",
        BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::router_native_checked_branch".to_string(),
        },
    );
    bundle.obligations = vec![native_trust_ir_obligation(
        "trust-mc",
        7,
        0,
        ObligationKind::Assertion,
        Some(ProofStrength { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::SmtBacked }),
    )];
    bundle.obligations[0].source = router_native_source_location(18);
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(0),
        &bundle,
        0,
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-mc-rejected"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    let evidence = &result.evidence[0];
    assert_eq!(evidence.status, EvidenceStatus::Unsupported);
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(evidence.diagnostics.iter().all(|diagnostic| {
        !diagnostic.contains("direct typed trust_mc proof must not be used")
    }));
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("primary owner trust-mc@")
                && diagnostic.contains("rejected evidence")
        }),
        "{:?}",
        evidence.diagnostics
    );
}

#[test]
fn native_ty_lane_fails_closed_without_transported_model() {
    // The ty primary is now the real NativeTyEngine, but an obligation with no
    // transported temporal model must still fail closed (Unsupported with a
    // diagnostic naming the missing metadata), never silently pass.
    let engine =
        FullVerificationEngine::new(vec![Box::new(NativeTyEngine::new())], route_only_policy());
    let bundle = bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-ty"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].engine.name, "trust-full-verifier");
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("primary owner ty@") && diagnostic.contains("rejected evidence")
    }));
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.contains(trust_types::TY_TEMPORAL_MODEL_METADATA_KEY) })
    );
}

fn bundle_with_temporal_model(
    single_writer: trust_types::SingleWriterEvidence,
) -> TrustContractBundle {
    let mut bundle = bundle_with_obligation(
        ObligationKind::TemporalSafety,
        "obligation-mmap-temporal",
        None,
        None,
    );
    let payload =
        trust_types::TyTemporalModelPayload::from_vc_kind(&trust_types::VcKind::Temporal {
            property: "AG !bad".to_string(),
            machine: Some(trust_types::StateMachineMetadata::mmap_temporal_model(single_writer)),
        })
        .expect("Temporal is a ty-owned kind");
    bundle.obligations[0].metadata.push(MetadataEntry {
        key: trust_types::TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
        value: payload.to_metadata_value().expect("payload serializes"),
    });
    bundle
}

#[test]
fn full_verifier_accepts_native_ty_temporal_proof() {
    // End-to-end through the composite: a TemporalSafety obligation carrying
    // the single-writer mmap model is PROVED by NativeTyEngine with Sound
    // ExplicitStateModel strength, and the TyTemporal route's artifact policy
    // (solver transcript) plus the aggregation replay/check policy both pass.
    // Ty is exempt from the typed TrustIr native-bundle requirement, so no
    // native bundle is supplied.
    let engine =
        FullVerificationEngine::new(vec![Box::new(NativeTyEngine::new())], route_only_policy());
    let bundle = bundle_with_temporal_model(trust_types::SingleWriterEvidence::Verified);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-ty-proof"));

    assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.proved, 1);
    assert!(result.is_fully_proved());
    assert_eq!(result.evidence[0].status, EvidenceStatus::Proved);
    let strength = result.evidence[0].proof_strength.as_ref().expect("proved has strength");
    assert_eq!(strength.reasoning, ReasoningKind::ExplicitStateModel);
    assert_eq!(strength.assurance, AssuranceLevel::Sound);
    assert!(result.evidence[0].satisfies_proof_artifact_policy());
    assert!(result.full_verification_obligation_evidence()[0].has_accepted_proof());
}

#[test]
fn full_verifier_reports_refuted_native_ty_temporal_model() {
    // Without #[trust::single_writer], the mmap model contains the
    // Mapped -> truncate -> stale_access -> BadAccess trace by design; the
    // native ty engine must refute (Failed with a counterexample), and the
    // run must not be Proved.
    let engine =
        FullVerificationEngine::new(vec![Box::new(NativeTyEngine::new())], route_only_policy());
    let bundle = bundle_with_temporal_model(trust_types::SingleWriterEvidence::None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-ty-refute"));

    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.failed, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Failed);
    assert!(result.evidence[0].counterexample.is_some());
}

/// L1b (platform pass): a platform obligation — `TemporalSafety` carrying a
/// refutation-only `TY_TEMPORAL_MODEL_METADATA_KEY` payload, the shape
/// `trust-platform-derive` emits — routes to the ty primary, the ty primary
/// among the required native engines is `NativeTyEngine`, and no fallback is
/// designated. Through the composite it is never proved: no counterexample is
/// `Unknown` with no strength, a counterexample is `Failed` — and only when
/// the payload declares the atom vocabulary its formula is vetted against
/// (derive's payloads do; without one nothing is answered, not even a
/// refutation).
#[test]
fn routing_sends_platform_obligations_to_native_ty() {
    let platform_bundle_with = |single_writer, vocabulary: bool| {
        let mut bundle = bundle_with_obligation(
            ObligationKind::TemporalSafety,
            "vc:census::spawn_capped:temporal_safety:0",
            None,
            None,
        );
        let mut payload =
            trust_types::TyTemporalModelPayload::refutation_only(&trust_types::VcKind::Temporal {
                property: "AG !bad".to_string(),
                machine: Some(trust_types::StateMachineMetadata::mmap_temporal_model(
                    single_writer,
                )),
            })
            .expect("Temporal is a ty-owned kind");
        if vocabulary {
            payload = payload.with_vocabulary(["bad".to_string()]);
        }
        bundle.obligations[0].metadata.push(MetadataEntry {
            key: trust_types::TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("payload serializes"),
        });
        bundle
    };
    let platform_bundle = |single_writer| platform_bundle_with(single_writer, true);
    let bundle = platform_bundle(trust_types::SingleWriterEvidence::Verified);
    let obligation = &bundle.obligations[0];

    let route = super::routing::obligation_route(obligation).expect("TemporalSafety routes");
    assert_eq!(route.primary, super::routing::PrimaryEngine::Ty);
    assert_eq!(route.proof_family, super::routing::ProofFamily::TyTemporal);
    assert!(
        super::routing::fallback_route(obligation).is_none(),
        "a platform obligation has no fallback engine"
    );

    let engines = required_native_engines();
    let ty: Vec<_> =
        engines.iter().filter(|engine| route.primary.matches_manifest(engine.manifest())).collect();
    assert_eq!(ty.len(), 1, "exactly one ty primary among the required native engines");
    assert!(
        ty[0].manifest().version.ends_with("+native-temporal"),
        "the ty primary is NativeTyEngine: {:?}",
        ty[0].manifest()
    );
    assert!(ty[0].supports(obligation).is_supported());

    let engine =
        FullVerificationEngine::new(vec![Box::new(NativeTyEngine::new())], route_only_policy());
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-platform"));
    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert!(
        result.evidence.iter().all(|evidence| evidence.proof_strength.is_none()),
        "{result:#?}"
    );
    assert!(
        result
            .evidence
            .iter()
            .any(|evidence| evidence.diagnostics.iter().any(|d| d.contains("refutation-only"))),
        "{result:#?}"
    );

    let refuted = platform_bundle(trust_types::SingleWriterEvidence::None);
    let result =
        engine.verify_bundle(&refuted, &VerifierExecutionContext::new("run-platform-refuted"));
    assert_eq!(result.summary.failed, 1, "{result:#?}");
    assert_eq!(result.summary.proved, 0);

    let unvetted = platform_bundle_with(trust_types::SingleWriterEvidence::None, false);
    let result =
        engine.verify_bundle(&unvetted, &VerifierExecutionContext::new("run-platform-unvetted"));
    assert_eq!(result.summary.failed, 0, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert!(result.evidence.iter().all(|evidence| evidence.status == EvidenceStatus::Unknown));
}

#[test]
fn bounded_required_strength_is_rejected_in_full_mode() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::Postcondition,
            ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked },
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::bounded(32)));
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-2"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.unsupported, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("bounded BMC is diagnostic only"))
    );
}

#[derive(Clone)]
enum UnitEvidenceMode {
    Empty,
    Evidence {
        status: EvidenceStatus,
        proof_strength: Option<ProofStrength>,
        artifacts: Vec<EvidenceArtifact>,
        diagnostics: Vec<String>,
    },
}

struct UnitEngine {
    manifest: EngineManifest,
    supported_kind: ObligationKind,
    support: SupportLevel,
    mode: UnitEvidenceMode,
}

fn proof_check_artifact(hash_value: &str) -> EvidenceArtifact {
    EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCheckReport,
        uri: format!("artifact://proof-check/{hash_value}.json"),
        hash: ArtifactHash { algorithm: "sha256".to_string(), value: hash_value.to_string() },
        materialization: None,
    }
}

fn solver_transcript_artifact(hash_value: &str) -> EvidenceArtifact {
    EvidenceArtifact {
        kind: EvidenceArtifactKind::SolverTranscript,
        uri: format!("artifact://solver-transcript/{hash_value}.json"),
        hash: ArtifactHash { algorithm: "sha256".to_string(), value: hash_value.to_string() },
        materialization: None,
    }
}

fn exact_fixture_proof_artifacts(
    obligation: &TrustObligation,
    seed: &str,
) -> Vec<EvidenceArtifact> {
    let owner = obligation.obligation_id.as_str();
    let binding = owner;
    let (input_materialization, input_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::NormalizedObligation,
        format!("normalized fixture input:{seed}").as_bytes(),
        binding,
        owner,
        Vec::new(),
    )
    .expect("bounded normalized fixture input");
    let input = EvidenceArtifact {
        kind: EvidenceArtifactKind::NormalizedObligation,
        uri: format!("artifact://router-fixture/normalized/{}", input_hash.value),
        hash: input_hash,
        materialization: Some(input_materialization),
    };
    let (transcript_materialization, transcript_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::SolverTranscript,
        format!("exact fixture transcript:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: input.kind, hash: input.hash.clone() }],
    )
    .expect("bounded fixture transcript");
    let transcript = EvidenceArtifact {
        kind: EvidenceArtifactKind::SolverTranscript,
        uri: format!("artifact://router-fixture/transcript/{}", transcript_hash.value),
        hash: transcript_hash,
        materialization: Some(transcript_materialization),
    };
    let (check_materialization, check_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCheckReport,
        format!("exact fixture check:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: transcript.kind, hash: transcript.hash.clone() }],
    )
    .expect("bounded fixture check");
    let check = EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCheckReport,
        uri: format!("artifact://router-fixture/check/{}", check_hash.value),
        hash: check_hash,
        materialization: Some(check_materialization),
    };
    vec![input, transcript, check]
}

fn exact_fixture_trust_mc_artifacts(
    obligation: &TrustObligation,
    seed: &str,
) -> Vec<EvidenceArtifact> {
    let owner = obligation.obligation_id.as_str();
    let binding = owner;
    let (input_materialization, input_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::NormalizedObligation,
        format!("normalized trust-mc fixture input:{seed}").as_bytes(),
        binding,
        owner,
        Vec::new(),
    )
    .expect("bounded normalized trust-mc fixture input");
    let input = EvidenceArtifact {
        kind: EvidenceArtifactKind::NormalizedObligation,
        uri: format!("artifact://router-fixture/normalized/{}", input_hash.value),
        hash: input_hash,
        materialization: Some(input_materialization),
    };
    let (transcript_materialization, transcript_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::SolverTranscript,
        format!("exact trust-mc fixture transcript:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: input.kind, hash: input.hash.clone() }],
    )
    .expect("bounded trust-mc fixture transcript");
    let transcript = EvidenceArtifact {
        kind: EvidenceArtifactKind::SolverTranscript,
        uri: format!("artifact://router-fixture/transcript/{}", transcript_hash.value),
        hash: transcript_hash,
        materialization: Some(transcript_materialization),
    };
    let (replay_materialization, replay_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ReplayLog,
        format!("exact trust-mc fixture replay:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: transcript.kind, hash: transcript.hash.clone() }],
    )
    .expect("bounded trust-mc fixture replay");
    let replay = EvidenceArtifact {
        kind: EvidenceArtifactKind::ReplayLog,
        uri: format!("artifact://router-fixture/replay/{}", replay_hash.value),
        hash: replay_hash,
        materialization: Some(replay_materialization),
    };
    let (check_materialization, check_hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCheckReport,
        format!("exact trust-mc fixture check:{seed}").as_bytes(),
        binding,
        owner,
        vec![EvidenceArtifactReference { kind: replay.kind, hash: replay.hash.clone() }],
    )
    .expect("bounded trust-mc fixture check");
    let check = EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCheckReport,
        uri: format!("artifact://router-fixture/check/{}", check_hash.value),
        hash: check_hash,
        materialization: Some(check_materialization),
    };
    vec![input, transcript, replay, check]
}

fn exact_fixture_trust_vc_certificate(
    obligation: &TrustObligation,
    seed: &str,
) -> Vec<EvidenceArtifact> {
    let owner = obligation.obligation_id.as_str();
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCertificate,
        format!("exact trust-vc fixture certificate:{seed}").as_bytes(),
        owner,
        owner,
        Vec::new(),
    )
    .expect("bounded trust-vc fixture certificate");
    vec![EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCertificate,
        uri: format!("artifact://router-fixture/certificate/{}", hash.value),
        hash,
        materialization: Some(materialization),
    }]
}

fn exact_fixture_artifacts_for_engine(
    engine_name: &str,
    obligation: &TrustObligation,
    seed: &str,
) -> Vec<EvidenceArtifact> {
    match engine_name {
        "trust-mc" => exact_fixture_trust_mc_artifacts(obligation, seed),
        "trust-vc" => exact_fixture_trust_vc_certificate(obligation, seed),
        _ => exact_fixture_proof_artifacts(obligation, seed),
    }
}

fn materialize_complete_unit_fixture_artifacts(
    engine_name: &str,
    obligation: &TrustObligation,
    artifacts: &[EvidenceArtifact],
) -> Vec<EvidenceArtifact> {
    let has_transcript =
        artifacts.iter().any(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript);
    let has_consumer = artifacts.iter().any(|artifact| {
        matches!(
            artifact.kind,
            EvidenceArtifactKind::ProofCheckReport
                | EvidenceArtifactKind::ProofReplayTrace
                | EvidenceArtifactKind::ReplayLog
        )
    });
    if has_transcript && has_consumer {
        let seed =
            artifacts.iter().map(|artifact| artifact.uri.as_str()).collect::<Vec<_>>().join("|");
        exact_fixture_artifacts_for_engine(engine_name, obligation, &seed)
    } else {
        artifacts.to_vec()
    }
}

const EXACT_ARTIFACT_POLICY_REJECTION: &str =
    "failed the exact owner-bound materialization DAG and route-specific artifact policy";

fn trust_mc_core_proof_grade_verdict(obligation_id: &str) -> trust_bmc::FullVerificationVerdict {
    let obligation = trust_bmc::MirDerivedChcPdrObligation::new(
        obligation_id,
        trust_bmc::MirObligationKind::ArithmeticSafety,
        "(declare-rel entry ())\n(rule entry)\n(query entry)\n",
    );
    let stats = trust_bmc::ChcPdrStats { relation_count: 1, clause_count: 1 };
    let mut proof = trust_bmc::ChcPdrProofEvidence::proof_grade_from_bytes(
        trust_bmc::ChcPdrProofKind::PdrInvariant,
        obligation,
        stats,
        ("ay://chc-pdr/proof-metadata.json", b"solver transcript"),
        ("trust-mc://chc-pdr/replay-log.json", b"replay log"),
        ("trust-mc://chc-pdr/checked-proof-report.json", b"checked report"),
    );
    proof.invariant_count = 1;
    trust_bmc::FullVerificationVerdict::Proved {
        evidence: trust_bmc::FullProofEvidence::ChcPdr(proof),
    }
}

fn native_trust_ir_digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn router_native_obligation_source_formula(
    public_obligation_id: &str,
    line: u32,
) -> trust_ir::ProofFormula {
    let assertion_id = format!("trust-assertion:{public_obligation_id}");
    trust_ir::ProofFormula {
        schema: trust_ir_bridge::TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
        payload: serde_json::json!({
            "source_id": public_obligation_id,
            "assertion_id": assertion_id,
            "native_assertion_id": trust_types::stable_u32_id(assertion_id.as_bytes()),
            "span": {
                "file": "router_native_fixture.rs",
                "line_start": line,
                "col_start": 9,
                "line_end": line,
                "col_end": 19,
            },
        })
        .to_string(),
        smtlib: None,
        sort: None,
        // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
        bindings: Vec::new(),
    }
}

fn router_native_obligation_source_identity(
    _obligation: trust_ir::ProofId,
    public_obligation_id: &str,
    source_file: u32,
    line: u32,
    semantic_digest: ProofDigest,
) -> trust_ir::ProofObligationSourceIdentity {
    trust_ir::ProofObligationSourceIdentity::new(
        public_obligation_id,
        format!("trust-assertion:{public_obligation_id}"),
    )
    .with_range(trust_ir::ProofObligationSourceRange {
        file: source_file,
        start_line: line,
        start_col: 9,
        end_line: line,
        end_col: 19,
    })
    .with_public(trust_ir::PublicObligationIdentity {
        obligation_id: public_obligation_id.to_string(),
        semantic_digest,
    })
}

#[cfg(feature = "trust-build")]
fn router_native_source_location(line: u32) -> SourceLocation {
    SourceLocation {
        file: Some("router_native_fixture.rs".to_string()),
        line: Some(line),
        column: Some(9),
        end_line: Some(line),
        end_column: Some(19),
    }
}

fn trust_wp_true_replay_formula() -> trust_ir::ProofFormula {
    trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")
}

fn replace_router_native_replay_formula(
    bundle: &mut NativeVerificationBundle,
    suite: trust_ir::NativeVerifierSuite,
    obligation: trust_ir::ProofId,
    formula: trust_ir::ProofFormula,
) {
    for request in &mut bundle.requests {
        if request.verifier_suite() != suite || !request.obligations().contains(&obligation) {
            continue;
        }
        let atoms = match request {
            NativeVerificationRequest::TrustVc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            NativeVerificationRequest::TrustMc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            NativeVerificationRequest::TrustWp(request) => {
                &mut request.provenance.replay_context.atoms
            }
        };
        for atom in atoms.iter_mut().filter(|atom| {
            atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                && atom.obligation == Some(obligation)
        }) {
            atom.formula = formula.clone();
            atom.payload_digest = atom.expected_payload_digest();
        }
    }
}

fn replace_native_proof_obligation_formula(
    bundle: &mut NativeVerificationBundle,
    obligation: trust_ir::ProofId,
    formula: trust_ir::ProofFormula,
) {
    let Some(proof_obligation) = bundle
        .module
        .proof_obligations
        .iter_mut()
        .find(|proof_obligation| proof_obligation.id == obligation)
    else {
        panic!("fixture proof obligation {} exists", obligation.index());
    };
    proof_obligation.formula = Some(formula);
}

fn rebind_native_bundle_module_digest(bundle: &mut NativeVerificationBundle) {
    let stale_module_digest = bundle.trust_ir_module_digest;
    let final_module_digest = bundle.module.stable_digest();
    if final_module_digest == stale_module_digest {
        return;
    }

    bundle.trust_ir_module_digest = final_module_digest;
    for node in &mut bundle.lineage.nodes {
        if node.source_module == stale_module_digest {
            node.source_module = final_module_digest;
        }
        if node.target_module == stale_module_digest {
            node.target_module = final_module_digest;
        }
    }
    for evidence in &mut bundle.evidence_bundles {
        match evidence {
            trust_ir::NativeEvidenceBundle::TrustVc(evidence) => {
                evidence.trust_ir_module_digest = final_module_digest;
            }
            trust_ir::NativeEvidenceBundle::TrustMc(evidence) => {
                evidence.trust_ir_module_digest = final_module_digest;
            }
            trust_ir::NativeEvidenceBundle::TrustWp(evidence) => {
                evidence.trust_ir_module_digest = final_module_digest;
            }
        }
    }
}

/// Admission-valid live-planner fixture for router tests that do not exercise
/// proof authority. The third obligation retains historical TrustWP-shaped
/// formula and source metadata, but current ownership deliberately emits only
/// TrustMc requests for all three rows.
fn native_trust_ir_mc_bundle() -> NativeVerificationBundle {
    let mut module = trust_ir::Module::new("router_native_trust_ir_bundle");
    let source_file =
        module.intern_file("router_native_fixture.rs").expect("Module::intern_file: test fixture");
    let function_id = trust_ir::FuncId::new(0);
    let func_ty = module
        .add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = trust_ir::BlockId::new(0);
    let mut function = trust_ir::Function::new(function_id, "checked_transfer", func_ty, entry)
        .with_producer(trust_ir::Producer::TrustIr);
    let mut block = trust_ir::Block::new(entry);
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            "request-id reservation without proof-authority claim",
        )
        .with_formula(router_native_obligation_source_formula(
            "trust_ir-native-trust-mc-request-0-proof-0",
            10,
        ))
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(0),
            "trust_ir-native-trust-mc-request-0-proof-0",
            source_file,
            10,
            native_trust_ir_digest(0xB0),
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(1),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            "trust-mc panic-freedom request",
        )
        .with_formula(router_native_obligation_source_formula(
            "trust_ir-native-trust-mc-request-1-proof-1",
            11,
        ))
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(1),
            "trust_ir-native-trust-mc-request-1-proof-1",
            source_file,
            11,
            native_trust_ir_digest(0xB1),
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(2),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "postcondition carrying historical TrustWP-shaped metadata",
        )
        .with_formula(router_native_obligation_source_formula(
            "trust_ir-native-trust-wp-request-2-proof-2",
            12,
        ))
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(2),
            "trust_ir-native-trust-wp-request-2-proof-2",
            source_file,
            12,
            native_trust_ir_digest(0xB2),
        )),
    );
    let mut bundle =
        native_verification_bundle_from_module(module, native_trust_ir_digest(0xA1), function_id)
            .expect("native TrustIr bundle builds");
    replace_native_proof_obligation_formula(
        &mut bundle,
        trust_ir::ProofId::new(2),
        trust_wp_true_replay_formula(),
    );
    replace_router_native_replay_formula(
        &mut bundle,
        trust_ir::NativeVerifierSuite::TrustMc,
        trust_ir::ProofId::new(1),
        trust_ir::ProofFormula::smtlib2("true", "Bool"),
    );
    replace_router_native_replay_formula(
        &mut bundle,
        trust_ir::NativeVerifierSuite::TrustMc,
        trust_ir::ProofId::new(2),
        trust_wp_true_replay_formula(),
    );
    rebind_native_bundle_module_digest(&mut bundle);
    bundle.validate().expect("native TrustMc fixture remains valid after replay formulas");
    bundle
}

/// Materialize one structurally valid historical TrustWP request without using
/// the current native-request planner. This keeps wire compatibility testable
/// while making the planner's zero-TrustWP invariant anti-vacuous.
fn historical_native_trust_wp_bundle() -> NativeVerificationBundle {
    let mut bundle = native_trust_ir_mc_bundle();
    bundle.requests.retain(|request| !matches!(request, NativeVerificationRequest::TrustWp(_)));
    let request_index = bundle
        .requests
        .iter()
        .position(|request| request.obligations() == [trust_ir::ProofId::new(2)])
        .expect("historical source row has one current TrustMc request");
    let NativeVerificationRequest::TrustMc(active) = bundle.requests.remove(request_index) else {
        panic!("the current planner must own the historical postcondition in TrustMc");
    };
    let historical = trust_ir::TrustWpNativeRequest {
        id: active.id,
        mode: trust_ir::TrustWpVerificationMode::WeakestPrecondition,
        function: active.function,
        obligations: active.obligations,
        lineage_roots: active.lineage_roots,
        options: trust_ir::TrustWpRequestOptions::default(),
        diagnostics: active.diagnostics,
        provenance: trust_ir::NativeRequestProvenance::trust_wp(trust_ir::NativeToolIdentity::new(
            "trust_wp",
        ))
        .with_solver(trust_ir::NativeToolIdentity::new("ay"))
        .with_replay(
            trust_ir::ProofReplayIdentity::new(
                "trust-wp-core.native-pure-replay",
                "historical compatibility fixture",
            )
            .with_transcript_digest(native_trust_ir_digest(0xB2)),
        )
        .with_replay_context(active.provenance.replay_context),
    };
    bundle.requests.insert(request_index, NativeVerificationRequest::TrustWp(historical));
    bundle.validate().expect("historical TrustWP wire fixture remains structurally valid");
    bundle
}

#[cfg(feature = "trust-build")]
fn proof_digest_from_canonical_sha256(value: &str) -> ProofDigest {
    assert_eq!(value.len(), 64, "canonical SHA-256 digest width");
    let mut bytes = [0_u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let nibble = |byte| match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            _ => panic!("canonical SHA-256 digest must use lowercase hex"),
        };
        bytes[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    ProofDigest::sha256(bytes)
}

/// Bind a native fixture row to the exact canonical public claim used by the
/// test. TrustIR schema v6 treats the embedded public ID and semantic digest as
/// an atomic source identity; fixed seed digests are valid structural fixtures
/// but cannot authorize proof evidence for a real public obligation.
#[cfg(feature = "trust-build")]
fn bind_native_obligation_to_public_claim(
    native_bundle: &mut NativeVerificationBundle,
    proof_obligation_id: trust_ir::ProofId,
    public_bundle: &TrustContractBundle,
    public_obligation_index: usize,
) {
    let public_obligation = public_bundle
        .obligations
        .get(public_obligation_index)
        .expect("public fixture obligation exists");
    let semantic_digest = public_bundle
        .canonical_obligation_semantic_digest_sha256(public_obligation)
        .expect("public fixture obligation has a canonical semantic digest");
    let semantic_digest = proof_digest_from_canonical_sha256(&semantic_digest);

    let proof_obligation = native_bundle
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_obligation_id)
        .expect("native fixture proof obligation exists");
    let embedded_source = proof_obligation
        .source
        .as_mut()
        .expect("TrustIR v6 fixture embeds an exact obligation source");
    let embedded_public = embedded_source
        .public
        .as_mut()
        .expect("TrustIR v6 fixture embeds an exact public identity");
    assert_eq!(
        embedded_public.obligation_id, public_obligation.obligation_id,
        "native and public fixture IDs must already agree before digest binding"
    );
    embedded_public.semantic_digest = semantic_digest;

    let sidecar_source = native_bundle
        .compiler_facts
        .obligation_sources
        .iter()
        .find(|source| source.obligation == proof_obligation_id)
        .expect("native fixture has one compiler-owned source row");
    assert_eq!(
        sidecar_source.public_obligation_id, public_obligation.obligation_id,
        "embedded and sidecar public IDs must agree"
    );

    rebind_native_bundle_module_digest(native_bundle);
    native_bundle
        .validate()
        .expect("exactly rebound TrustIR v6 fixture remains structurally valid");
}

#[cfg(feature = "trust-build")]
fn kernel_certified_postcondition_fixture() -> (TrustContractBundle, NativeVerificationBundle) {
    const PUBLIC_OBLIGATION_ID: &str = "router::kernel-certified-postcondition";
    const CONTRACT_ID: &str = "router::kernel-certified-postcondition::ensures";

    let kernel_formula = trust_ir::ProofFormula::smtlib2("(>= 5 0)", "Bool");
    let mut public_bundle = TrustContractBundle::empty(
        "router-kernel-certified-postcondition",
        BundleSubject::Function {
            crate_name: "router_kernel_fixture".to_string(),
            path: "router_kernel_fixture::checked_transfer".to_string(),
        },
    );
    public_bundle.contracts.push(TrustContract {
        contract_id: CONTRACT_ID.to_string(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::TrustIr {
            schema: TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA.to_string(),
            value: serde_json::to_value(&kernel_formula)
                .expect("kernel formula serializes into the typed public contract"),
        },
        source: SourceLocation::default(),
        metadata: Vec::new(),
    });
    let mut public_obligation = TrustObligation {
        obligation_id: PUBLIC_OBLIGATION_ID.to_string(),
        kind: ObligationKind::Postcondition,
        contract_id: Some(CONTRACT_ID.to_string()),
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "kernel-certified ground postcondition".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: trust_vc_typed_result_contract_frame_metadata(),
    };
    public_obligation.metadata.extend(native_trust_ir_metadata("trust-vc", 0, 0));
    public_bundle.obligations.push(public_obligation);
    let public_semantic_digest = public_bundle
        .canonical_obligation_semantic_digest_sha256(&public_bundle.obligations[0])
        .expect("typed public postcondition has a canonical semantic digest");
    let public_semantic_digest = proof_digest_from_canonical_sha256(&public_semantic_digest);

    let mut module = trust_ir::Module::new("router_kernel_certified_trust_vc_trust_mc_bundle");
    let source_file =
        module.intern_file("router_kernel_fixture.rs").expect("Module::intern_file: test fixture");
    let function_id = trust_ir::FuncId::new(0);
    let func_ty = module
        .add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = trust_ir::BlockId::new(0);
    let mut function = trust_ir::Function::new(function_id, "checked_transfer", func_ty, entry)
        .with_producer(trust_ir::Producer::TrustIr);
    let mut block = trust_ir::Block::new(entry);
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    module.try_add_function(function).expect("Module::try_add_function: test fixture");

    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Discharged,
            "kernel-certified public postcondition",
        )
        .with_formula(kernel_formula)
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(0),
            PUBLIC_OBLIGATION_ID,
            source_file,
            20,
            public_semantic_digest,
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(1),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            "independent trust-mc request",
        )
        .with_formula(trust_ir::ProofFormula::smtlib2("true", "Bool"))
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(1),
            "trust_ir-native-trust-mc-request-1-proof-1",
            source_file,
            21,
            native_trust_ir_digest(0xB1),
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(2),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "independent trust-mc postcondition request",
        )
        .with_formula(trust_wp_true_replay_formula())
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(2),
            "trust_ir-native-trust-mc-request-2-proof-2",
            source_file,
            22,
            native_trust_ir_digest(0xB2),
        )),
    );
    let certificate = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
        &module.proof_obligations[0],
        "trust-vc",
    )
    .expect("ground public postcondition is discharged by the Clean kernel");
    module.proof_certificates.push(certificate);

    let native_bundle =
        native_verification_bundle_from_module(module, native_trust_ir_digest(0xA2), function_id)
            .expect("kernel-certified TrustVc/TrustMc native bundle builds");
    public_bundle.obligations[0].metadata.extend(trust_vc_native_import_metadata(
        &native_bundle,
        0,
        0,
    ));
    assert_eq!(
        proof_digest_from_canonical_sha256(
            &public_bundle
                .canonical_obligation_semantic_digest_sha256(&public_bundle.obligations[0])
                .expect("native import transport does not rewrite public semantics")
        ),
        public_semantic_digest,
        "native import metadata must be excluded from the public claim digest"
    );
    (public_bundle, native_bundle)
}

#[cfg(feature = "trust-build")]
fn kernel_certified_trust_vc_full_engine() -> FullVerificationEngine {
    FullVerificationEngine::new(
        vec![Box::new(TrustVcVerificationEngine::new())],
        route_only_policy(),
    )
}

#[cfg(feature = "trust-build")]
#[test]
fn kernel_certified_postcondition_does_not_override_trust_mc_ownership() {
    let (bundle, native_bundle) = kernel_certified_postcondition_fixture();
    let result = kernel_certified_trust_vc_full_engine().verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-kernel-certified-postcondition"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.requested_obligations, 1, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    assert_eq!(
        result.full_verification_obligation_evidence()[0].primary_suite.as_deref(),
        Some("trust-mc")
    );
}

#[cfg(feature = "trust-build")]
#[test]
fn kernel_certified_metadata_without_native_bundle_never_earns_proof_credit() {
    let (bundle, _) = kernel_certified_postcondition_fixture();
    let result = kernel_certified_trust_vc_full_engine().verify_bundle(
        &bundle,
        &VerifierExecutionContext::new("run-kernel-certified-metadata-only"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(
        result.evidence[0]
            .artifacts
            .iter()
            .all(|artifact| { artifact.kind != EvidenceArtifactKind::ProofCertificate })
    );
    assert!(!result.evidence[0].diagnostics.is_empty(), "{result:#?}");
}

#[cfg(feature = "trust-build")]
#[test]
fn producer_suite_metadata_cannot_override_v6_contract_ownership() {
    let (bundle, _) = kernel_certified_postcondition_fixture();
    let obligation = &bundle.obligations[0];
    assert_eq!(
        super::routing::obligation_route(obligation)
            .expect("postcondition has a route")
            .primary
            .name(),
        "trust-mc"
    );

    for replacement in [None, Some("trust-wp"), Some(" trust-vc ")] {
        let mut changed = obligation.clone();
        changed
            .metadata
            .retain(|entry| entry.key != TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY);
        if let Some(value) = replacement {
            changed.metadata.push(MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: value.to_string(),
            });
        }
        assert_eq!(
            super::routing::obligation_route(&changed)
                .expect("postcondition has a route")
                .primary
                .name(),
            "trust-mc",
            "producer suite metadata never changes the v6 owner"
        );
    }

    let mut duplicate = obligation.clone();
    duplicate.metadata.push(MetadataEntry {
        key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
        value: "trust-vc".to_string(),
    });
    assert_eq!(
        super::routing::obligation_route(&duplicate)
            .expect("postcondition has a route")
            .primary
            .name(),
        "trust-mc",
        "even agreeing duplicate declarations cannot change ownership"
    );
}

#[cfg(feature = "trust-build")]
#[test]
fn kernel_certified_trust_vc_marker_cannot_override_body_aware_trust_mc_route() {
    let (mut bundle, native_bundle) = kernel_certified_postcondition_fixture();
    bundle.obligations[0].metadata.push(MetadataEntry {
        key: "trust.vc.formula.payload".to_string(),
        value: serde_json::json!({"kind": "bool", "value": false}).to_string(),
    });
    assert_eq!(
        super::routing::obligation_route(&bundle.obligations[0])
            .expect("body-aware postcondition has a route")
            .primary
            .name(),
        "trust-mc"
    );

    let result = kernel_certified_trust_vc_full_engine().verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-kernel-certified-contradictory-route"),
    );
    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(
        result.evidence[0]
            .artifacts
            .iter()
            .all(|artifact| artifact.kind != EvidenceArtifactKind::ProofCertificate)
    );
}

#[cfg(feature = "trust-build")]
#[test]
fn kernel_certified_public_formula_substitution_rejects_native_certificate() {
    let (mut bundle, native_bundle) = kernel_certified_postcondition_fixture();
    bundle.contracts[0].predicate = ContractPredicate::TrustIr {
        schema: TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA.to_string(),
        value: serde_json::to_value(trust_ir::ProofFormula::smtlib2("(>= 0 5)", "Bool"))
            .expect("substituted TrustIr formula serializes"),
    };

    let result = kernel_certified_trust_vc_full_engine().verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-kernel-certified-formula-substitution"),
    );
    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert!(
        result.evidence[0]
            .artifacts
            .iter()
            .all(|artifact| artifact.kind != EvidenceArtifactKind::ProofCertificate)
    );
    assert!(!result.evidence[0].diagnostics.is_empty());
}

/// Adversarial variant used only to prove that router admission fails before
/// child evidence can launder an opaque TrustVc certificate into authority.
fn native_trust_ir_unreplayed_trust_vc_bundle() -> NativeVerificationBundle {
    let mut bundle = native_trust_ir_mc_bundle();
    let proof = trust_ir::ProofId::new(0);
    let obligation = bundle
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof)
        .expect("request-zero proof obligation");
    obligation.kind = trust_ir::ObligationKind::MemorySafety;
    obligation.status = trust_ir::ProofStatus::Discharged;
    obligation.description = "unreplayed opaque TrustVc certificate".to_string();
    let formula = obligation.formula.clone().expect("request-zero proof formula");

    let certificate = trust_ir::ProofCertificate {
        obligation: proof,
        prover: "trust-vc".to_string(),
        evidence: trust_ir::ProofEvidence::LeanProof(
            "exact trust_vc.Router.unreplayed_fixture".to_string(),
        ),
        // v41: no native evidence bundle to project a coverage assurance from.
        assurance: None,
    };
    let certificate_ref = certificate.lineage_ref();
    bundle.module.proof_certificates.push(certificate);
    bundle.lineage.nodes[0].certificates.push(certificate_ref.clone());

    let source = bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == proof)
        .expect("request-zero obligation source");
    source.cause = trust_ir::NativeObligationCause::BorrowCheck;
    let mut atom =
        trust_ir::NativeReplayAtom::assertion(trust_ir::NativeReplayAtomId::new(0), formula)
            .with_obligation(proof);
    if let Some(assertion_id) = source.assertion_id {
        atom = atom.with_assertion_id(assertion_id);
    }
    if let Some(span) = source.span {
        atom = atom.with_span(span);
    }
    let provenance = trust_ir::NativeRequestProvenance::trust_vc(
        trust_ir::NativeToolIdentity::new("trust-vc").with_version("unreplayed-test-v1"),
    )
    .with_solver(trust_ir::NativeToolIdentity::new("lean4").with_version("opaque-test"))
    .with_replay(
        trust_ir::ProofReplayIdentity::new("trust-vc", "unreplayed negative fixture")
            .with_transcript_digest(native_trust_ir_digest(0xD1)),
    )
    .with_replay_context(trust_ir::NativeReplayContext::default().with_atom(atom));
    bundle.requests[0] = NativeVerificationRequest::TrustVc(trust_ir::TrustVcNativeRequest {
        id: trust_ir::NativeRequestId::new(0),
        mode: trust_ir::TrustVcVerificationMode::ImportProofCertificates,
        obligations: vec![proof],
        certificates: vec![certificate_ref],
        lineage_roots: vec![trust_ir::ProofLineageId::new(0)],
        options: trust_ir::TrustVcRequestOptions::default(),
        diagnostics: trust_ir::NativeDiagnosticsPolicy::default(),
        provenance,
        // Stays None. This is a hand-built negative fixture that does NOT go
        // through `obligation_sources_for_module`, so a Some(_) here would trip
        // `RequestObligationFunctionMismatch` unless the bundle's matching
        // obligation source were given the same function — changing what this
        // test is actually testing.
        function: None,
    });

    rebind_native_bundle_module_digest(&mut bundle);
    bundle
}

#[cfg(feature = "trust-build")]
fn native_trust_mc_safe_trust_ir_bundle() -> NativeVerificationBundle {
    use trust_ir::inst::ICmpOp;
    use trust_ir::ty::Ty;
    use trust_ir::{
        NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
        NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
        NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
        NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
        NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
        ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
        ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
        TrustMcNativeRequest, TrustMcVerificationMode,
    };
    use trust_ir_build::ModuleBuilder;

    let source_digest = ProofDigest::sha256([0x61; 32]);

    let mut mb = ModuleBuilder::new("router_native_trust_ir_chc_safe_bundle");
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);
    {
        let mut fb = mb.function("router_native_checked_branch", ft);
        let entry = fb.create_block();
        let then_block = fb.create_block();
        let exit_block = fb.create_block();

        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let zero = fb.iconst(Ty::I32, 0);
        let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
        fb.condbr(is_non_negative, then_block, vec![is_non_negative], exit_block, vec![]);

        let branch_fact = fb.add_block_param(then_block, Ty::Bool);
        fb.switch_to_block(then_block);
        fb.assert(branch_fact);
        fb.ret(vec![]);

        fb.switch_to_block(exit_block);
        fb.ret(vec![]);
        fb.build();
    }

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let source_file =
        module.intern_file("router_native_fixture.rs").expect("Module::intern_file: test fixture");
    let trust_mc_function = module
        .functions
        .iter()
        .find(|func| func.name == "router_native_checked_branch")
        .expect("fixture includes requested trust_mc function")
        .id;
    let native_assertion_id = NativeAssertionId::new(trust_types::stable_u32_id(
        b"trust-assertion:trust_ir-native-trust-mc-request-7-proof-0",
    ));
    let source_formula =
        router_native_obligation_source_formula("trust_ir-native-trust-mc-request-7-proof-0", 18);
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "native TrustIr branch assertion is unreachable",
        )
        .with_formula(source_formula.clone())
        .with_function(trust_mc_function)
        .with_source(router_native_obligation_source_identity(
            ProofId::new(0),
            "trust_ir-native-trust-mc-request-7-proof-0",
            source_file,
            18,
            native_trust_ir_digest(0xB7),
        )),
    );
    let trust_ir_module_digest = module.stable_digest();

    let mut lineage_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "Trust",
            "native-request-schema-v1",
        ),
        source_digest,
        trust_ir_module_digest,
    );
    lineage_node.obligations.push(ProofId::new(0));

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        trust_ir_module_digest,
        module,
        lineage,
    );
    let source_span = trust_ir::SourceSpan { file: source_file, line: 18, col: 9 };
    bundle.compiler_facts = NativeCompilerFacts {
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "router_native_trust_ir_chc_safe_bundle::router_native_checked_branch"
                .to_owned(),
            symbol: "_RNvNtC6native28router_native_checked_branch".to_owned(),
            generic_args: Vec::new(),
            function: Some(trust_mc_function),
            stable_digest: ProofDigest::sha256([0x63; 32]),
        }],
        obligation_sources: vec![NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "trust_ir-native-trust-mc-request-7-proof-0".to_string(),
            function: Some(trust_mc_function),
            span: Some(source_span),
            assertion_id: Some(native_assertion_id),
            cause: NativeObligationCause::Panic,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0))],
        }],
        ..NativeCompilerFacts::default()
    };
    bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(7),
        mode: TrustMcVerificationMode::Chc,
        function: trust_mc_function,
        obligations: vec![ProofId::new(0)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: trust_ir_bridge::trust_mc_chc_request_options(),
        diagnostics: Default::default(),
        provenance: NativeRequestProvenance::trust_mc(
            NativeToolIdentity::new("trust-mc")
                .with_version("trust-mc-native-admission-contract-v1"),
        )
        .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
        .with_replay(
            ProofReplayIdentity::new(
                "trust-mc",
                "trust-mc-native-admission-contract-v1 router replay",
            )
            .with_transcript_digest(ProofDigest::sha256([0x64; 32])),
        )
        .with_replay_context(
            NativeReplayContext::default()
                .with_atom(
                    NativeReplayAtom::assumption(
                        NativeReplayAtomId::new(0),
                        ProofFormula::smtlib2("router_native_checked_branch_guard", "Bool"),
                    )
                    .with_obligation(ProofId::new(0))
                    .with_span(source_span),
                )
                .with_atom(
                    NativeReplayAtom::assertion(NativeReplayAtomId::new(1), source_formula)
                        .with_obligation(ProofId::new(0))
                        .with_assertion_id(native_assertion_id)
                        .with_span(source_span),
                ),
        ),
    }));
    bundle
}

fn native_trust_ir_metadata(
    suite: &str,
    request_id: u32,
    proof_obligation_id: u32,
) -> Vec<MetadataEntry> {
    vec![
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
            value: suite.to_string(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
            value: request_id.to_string(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
            value: proof_obligation_id.to_string(),
        },
    ]
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_import_metadata(
    bundle: &NativeVerificationBundle,
    request_id: u32,
    proof_obligation_id: u32,
) -> Vec<MetadataEntry> {
    let imports =
        trust_vc_bridge::trust_vc_native_trust_ir_imported_proof_artifacts_from_bundle(bundle)
            .expect("kernel-certified native bundle yields validated TrustVc imports");
    let mut matching = imports.iter().filter(|import| {
        import.request_id == request_id && import.trust_ir_obligation_id == proof_obligation_id
    });
    let import = matching.next().expect("requested TrustVc import identity exists");
    assert!(matching.next().is_none(), "TrustVc import identity must be unique");
    trust_vc_bridge::trust_vc_native_trust_ir_import_metadata_entries(import)
}

#[cfg(feature = "trust-build")]
fn add_trust_mc_public_typed_chc_binding_metadata(
    obligation: &mut TrustObligation,
    native_obligation_id: &str,
) {
    const TRUST_SOURCE_DIGEST_METADATA_KEY: &str = "trust.mir-extract.source.digest.sha256";
    const TRUST_VC_DIGEST_METADATA_KEY: &str = "trust.vc.digest.sha256";

    let source_digest = "1".repeat(64);
    let vc_digest = "2".repeat(64);
    let synthetic_chc_digest = "a".repeat(64);
    let synthetic_contract_id = format!("synthetic-contract-{}", obligation.obligation_id);
    let binding = serde_json::json!({
        "schema_version": trust_bmc::TRUST_MC_TYPED_CHC_BINDING_SCHEMA,
        "typed_chc_schema": trust_bmc::TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA,
        "public_obligation_id": obligation.obligation_id,
        "native_obligation_id": native_obligation_id,
        "synthetic_contract_id": synthetic_contract_id,
        "source_digest": {
            "algorithm": "sha256",
            "value": source_digest,
        },
        "vc_digest": {
            "algorithm": "sha256",
            "value": vc_digest,
        },
        "synthetic_chc_digest": {
            "algorithm": "sha256",
            "value": synthetic_chc_digest,
        },
    });

    obligation.metadata.extend([
        MetadataEntry {
            key: trust_bmc::TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY.to_string(),
            value: source_digest.clone(),
        },
        MetadataEntry {
            key: trust_bmc::TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY.to_string(),
            value: vc_digest.clone(),
        },
        MetadataEntry {
            key: trust_bmc::TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY.to_string(),
            value: synthetic_chc_digest,
        },
        MetadataEntry { key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(), value: source_digest },
        MetadataEntry { key: TRUST_VC_DIGEST_METADATA_KEY.to_string(), value: vc_digest },
        MetadataEntry {
            key: trust_bmc::TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY.to_string(),
            value: serde_json::to_string(&binding).expect("trust-mc typed CHC binding serializes"),
        },
    ]);
}

fn native_trust_ir_obligation(
    suite: &str,
    request_id: u32,
    proof_obligation_id: u32,
    kind: ObligationKind,
    required_strength: Option<ProofStrength>,
) -> TrustObligation {
    TrustObligation {
        obligation_id: format!(
            "trust_ir-native-{suite}-request-{request_id}-proof-{proof_obligation_id}"
        ),
        kind,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("{suite} native TrustIr obligation"),
        required_strength,
        summary_facts: Vec::new(),
        metadata: native_trust_ir_metadata(suite, request_id, proof_obligation_id),
    }
}

impl UnitEngine {
    fn new(
        name: &str,
        engine_kind: EngineKind,
        supported_kind: ObligationKind,
        support: SupportLevel,
        mode: UnitEvidenceMode,
    ) -> Self {
        let mut manifest = EngineManifest::new(name, "0.1.0", engine_kind);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: supported_kind.clone(),
            support: support.clone(),
        });
        Self { manifest, supported_kind, support, mode }
    }

    fn proving(
        name: &str,
        engine_kind: EngineKind,
        supported_kind: ObligationKind,
        proof_strength: ProofStrength,
    ) -> Self {
        Self::new(
            name,
            engine_kind,
            supported_kind,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(proof_strength),
                artifacts: vec![
                    solver_transcript_artifact("proof-transcript"),
                    proof_check_artifact("proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        )
    }
}

impl VerificationEngine for UnitEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == self.supported_kind {
            self.support.clone()
        } else {
            SupportLevel::Unsupported {
                reason: format!("{} only handles {:?}", self.manifest.name, self.supported_kind),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        obligations
            .iter()
            .filter_map(|obligation| {
                if obligation.kind != self.supported_kind {
                    return None;
                }
                let UnitEvidenceMode::Evidence { status, proof_strength, artifacts, diagnostics } =
                    &self.mode
                else {
                    return None;
                };
                Some(ObligationEvidence {
                    evidence_id: format!("{}:{}", self.manifest.name, obligation.obligation_id),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: *status,
                    decline: None,
                    proof_strength: proof_strength.clone(),
                    artifacts: materialize_complete_unit_fixture_artifacts(
                        &self.manifest.name,
                        obligation,
                        artifacts,
                    ),
                    counterexample: None,
                    publication: EvidencePublicationMetadata::default(),
                    diagnostics: diagnostics.clone(),
                })
            })
            .collect()
    }
}

struct ProvedFailedConflictEngine {
    manifest: EngineManifest,
}

impl ProvedFailedConflictEngine {
    fn new() -> Self {
        let mut manifest =
            EngineManifest::new("trust-mc", "conflict-test", EngineKind::Reachability);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::Postcondition,
            support: SupportLevel::Preferred,
        });
        Self { manifest }
    }
}

impl VerificationEngine for ProvedFailedConflictEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::Postcondition {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported {
                reason: "conflict fixture handles only postconditions".to_string(),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        request
            .obligations()
            .iter()
            .flat_map(|obligation| {
                let proved = ObligationEvidence {
                    evidence_id: format!("conflict:proved:{}", obligation.obligation_id),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Proved,
                    decline: None,
                    proof_strength: Some(ProofStrength {
                        reasoning: ReasoningKind::Chc,
                        assurance: AssuranceLevel::SmtBacked,
                    }),
                    artifacts: exact_fixture_artifacts_for_engine(
                        "trust-mc",
                        obligation,
                        "proved-failed-conflict",
                    ),
                    counterexample: None,
                    publication: EvidencePublicationMetadata::default(),
                    diagnostics: vec!["fixture proof".to_string()],
                };
                let failed = ObligationEvidence {
                    evidence_id: format!("conflict:failed:{}", obligation.obligation_id),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Failed,
                    decline: None,
                    proof_strength: None,
                    artifacts: Vec::new(),
                    counterexample: None,
                    publication: EvidencePublicationMetadata::default(),
                    diagnostics: vec!["fixture refutation".to_string()],
                };
                [proved, failed]
            })
            .collect()
    }
}

#[test]
fn full_router_never_selects_a_proof_over_same_obligation_failed_evidence() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(ProvedFailedConflictEngine::new())],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(None);

    let result = engine
        .verify_bundle(&bundle, &VerifierExecutionContext::new("proved-failed-hard-conflict"));

    assert_eq!(result.status, VerificationRunStatus::Failed, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(result.summary.failed, 1, "{result:#?}");
    assert_eq!(result.evidence.len(), 1, "{result:#?}");
    assert_eq!(result.evidence[0].status, EvidenceStatus::Failed, "{result:#?}");
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("conflicting Proved and Failed evidence")
            && diagnostic.contains("failed closed on the Failed row")
    }));
}

fn route_only_policy() -> FullVerificationPolicy {
    FullVerificationPolicy {
        require_all_required_engines: false,
        ..FullVerificationPolicy::default()
    }
}

struct BatchCountingEngine {
    manifest: EngineManifest,
    calls: Arc<AtomicUsize>,
    batch_sizes: Arc<Mutex<Vec<usize>>>,
}

impl BatchCountingEngine {
    fn new(calls: Arc<AtomicUsize>, batch_sizes: Arc<Mutex<Vec<usize>>>) -> Self {
        let mut manifest = EngineManifest::new("ty", "0.1.0", EngineKind::Temporal);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::Liveness,
            support: SupportLevel::Preferred,
        });
        Self { manifest, calls, batch_sizes }
    }
}

impl VerificationEngine for BatchCountingEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::Liveness {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported {
                reason: "batch-counting engine only handles liveness".to_string(),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        self.calls.fetch_add(1, Ordering::SeqCst);
        self.batch_sizes.lock().expect("batch sizes lock").push(obligations.len());
        obligations
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("ty:batch:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                }),
                artifacts: exact_fixture_proof_artifacts(obligation, "batched-ty"),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            })
            .collect()
    }
}

struct RecordingEngine {
    manifest: EngineManifest,
    supported_kind: ObligationKind,
    proof_strength: ProofStrength,
    calls: Arc<Mutex<Vec<String>>>,
}

impl RecordingEngine {
    fn new(
        name: &str,
        engine_kind: EngineKind,
        supported_kind: ObligationKind,
        proof_strength: ProofStrength,
        calls: Arc<Mutex<Vec<String>>>,
    ) -> Self {
        let mut manifest = EngineManifest::new(name, "0.1.0", engine_kind);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: supported_kind.clone(),
            support: SupportLevel::Preferred,
        });
        Self { manifest, supported_kind, proof_strength, calls }
    }
}

impl VerificationEngine for RecordingEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == self.supported_kind {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported {
                reason: format!("{} only handles {:?}", self.manifest.name, self.supported_kind),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        self.calls.lock().expect("calls lock").push(self.manifest.name.clone());
        obligations
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("{}:{}", self.manifest.name, obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(self.proof_strength.clone()),
                artifacts: exact_fixture_artifacts_for_engine(
                    &self.manifest.name,
                    obligation,
                    &format!("{}-recording", self.manifest.name),
                ),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            })
            .collect()
    }
}

struct SlowRecordingEngine {
    manifest: EngineManifest,
    supported_kind: ObligationKind,
    proof_strength: ProofStrength,
    active_calls: Arc<AtomicUsize>,
    max_active_calls: Arc<AtomicUsize>,
    sleep: Duration,
}

impl SlowRecordingEngine {
    fn new(
        name: &str,
        engine_kind: EngineKind,
        supported_kind: ObligationKind,
        proof_strength: ProofStrength,
        active_calls: Arc<AtomicUsize>,
        max_active_calls: Arc<AtomicUsize>,
    ) -> Self {
        let mut manifest = EngineManifest::new(name, "0.1.0", engine_kind);
        manifest.capabilities.push(EngineCapability {
            obligation_kind: supported_kind.clone(),
            support: SupportLevel::Preferred,
        });
        Self {
            manifest,
            supported_kind,
            proof_strength,
            active_calls,
            max_active_calls,
            sleep: Duration::from_millis(150),
        }
    }

    fn update_max_active(&self, active: usize) {
        let mut observed = self.max_active_calls.load(Ordering::SeqCst);
        while active > observed {
            match self.max_active_calls.compare_exchange(
                observed,
                active,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(current) => observed = current,
            }
        }
    }
}

impl VerificationEngine for SlowRecordingEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == self.supported_kind {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported {
                reason: format!("{} only handles {:?}", self.manifest.name, self.supported_kind),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        let active = self.active_calls.fetch_add(1, Ordering::SeqCst) + 1;
        self.update_max_active(active);
        std::thread::sleep(self.sleep);
        self.active_calls.fetch_sub(1, Ordering::SeqCst);

        obligations
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("{}:{}", self.manifest.name, obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(self.proof_strength.clone()),
                artifacts: exact_fixture_artifacts_for_engine(
                    &self.manifest.name,
                    obligation,
                    &format!("slow-{}-recording", self.manifest.name),
                ),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            })
            .collect()
    }
}

#[test]
fn full_verifier_batches_same_primary_obligations_once() {
    let calls = Arc::new(AtomicUsize::new(0));
    let batch_sizes = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![Box::new(BatchCountingEngine::new(calls.clone(), batch_sizes.clone()))],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    bundle.obligations.push(TrustObligation {
        obligation_id: "obligation-live-second".to_string(),
        kind: ObligationKind::Liveness,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "prove second liveness obligation".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });

    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-batched"));

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 2);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(*batch_sizes.lock().expect("batch sizes lock"), vec![2]);
    let evidence_ids =
        result.evidence.iter().map(|item| item.obligation_id.as_str()).collect::<Vec<_>>();
    assert_eq!(evidence_ids, vec!["obligation-live", "obligation-live-second"]);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("full-verification engine batch")
            && diagnostic.contains("engine=ty@0.1.0")
            && diagnostic.contains("obligations=2")
            && diagnostic.contains("elapsed_ms=")
            && diagnostic.contains("worker_threads=unbounded")
    }));
    let manifest = result.to_manifest();
    assert!(manifest.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("full-verification engine batch")
            && diagnostic.contains("engine=ty@0.1.0")
            && diagnostic.contains("obligations=2")
    }));
}

#[test]
fn full_verifier_preserves_requested_evidence_order_across_primary_batches() {
    let calls = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(RecordingEngine::new(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::ArithmeticSafety,
                ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                },
                calls.clone(),
            )),
            Box::new(RecordingEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                },
                calls.clone(),
            )),
        ],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-batch-order",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        plain_obligation(ObligationKind::Liveness, "obligation-liveness"),
        native_trust_ir_obligation(
            "trust-mc",
            1,
            1,
            ObligationKind::ArithmeticSafety,
            Some(ProofStrength {
                reasoning: ReasoningKind::Pdr,
                assurance: AssuranceLevel::SmtBacked,
            }),
        ),
    ];

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-mixed"),
    );

    assert_eq!(result.status, VerificationRunStatus::Proved);
    let mut called_engines = calls.lock().expect("calls lock").clone();
    called_engines.sort();
    assert_eq!(called_engines, vec!["trust-mc".to_string(), "ty".to_string()]);
    let evidence_ids =
        result.evidence.iter().map(|item| item.obligation_id.as_str()).collect::<Vec<_>>();
    assert_eq!(
        evidence_ids,
        vec!["obligation-liveness", "trust_ir-native-trust-mc-request-1-proof-1"]
    );
}

#[test]
fn full_verifier_runs_independent_primary_batches_in_parallel_when_worker_threads_allow() {
    let active_calls = Arc::new(AtomicUsize::new(0));
    let max_active_calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(SlowRecordingEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                },
                active_calls.clone(),
                max_active_calls.clone(),
            )),
            Box::new(SlowRecordingEngine::new(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::ArithmeticSafety,
                ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                },
                active_calls.clone(),
                max_active_calls.clone(),
            )),
        ],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-parallel-batches",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        plain_obligation(ObligationKind::Liveness, "obligation-liveness"),
        native_trust_ir_obligation(
            "trust-mc",
            1,
            1,
            ObligationKind::ArithmeticSafety,
            Some(ProofStrength {
                reasoning: ReasoningKind::Pdr,
                assurance: AssuranceLevel::SmtBacked,
            }),
        ),
    ];
    let context =
        VerifierExecutionContext::new("run-parallel-batches").with_limits(VerifierResourceLimits {
            worker_threads: Some(2),
            ..VerifierResourceLimits::unlimited()
        });

    let result =
        engine.verify_bundle_with_native_trust_ir_bundle(&bundle, &native_bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 2);
    assert_eq!(max_active_calls.load(Ordering::SeqCst), 2);
    let evidence_ids =
        result.evidence.iter().map(|item| item.obligation_id.as_str()).collect::<Vec<_>>();
    assert_eq!(
        evidence_ids,
        vec!["obligation-liveness", "trust_ir-native-trust-mc-request-1-proof-1"]
    );
    let batch_diagnostics = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.contains("full-verification engine batch"))
        .collect::<Vec<_>>();
    assert_eq!(batch_diagnostics.len(), 2);
    assert!(batch_diagnostics.iter().all(|diagnostic| {
        diagnostic.contains("elapsed_ms=") && diagnostic.contains("worker_threads=2")
    }));
    let manifest = result.to_manifest();
    assert_eq!(manifest.context.limits.worker_threads, Some(2));
    let manifest_batch_diagnostics = manifest
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.contains("full-verification engine batch"))
        .collect::<Vec<_>>();
    assert_eq!(manifest_batch_diagnostics.len(), 2);
    assert!(
        manifest_batch_diagnostics.iter().all(|diagnostic| diagnostic.contains("worker_threads=2"))
    );
}

#[test]
fn full_verifier_runs_independent_primary_batches_serially_when_worker_threads_is_one() {
    let active_calls = Arc::new(AtomicUsize::new(0));
    let max_active_calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(SlowRecordingEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                },
                active_calls.clone(),
                max_active_calls.clone(),
            )),
            Box::new(SlowRecordingEngine::new(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::ArithmeticSafety,
                ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                },
                active_calls.clone(),
                max_active_calls.clone(),
            )),
        ],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-serial-batches",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        plain_obligation(ObligationKind::Liveness, "obligation-liveness"),
        native_trust_ir_obligation(
            "trust-mc",
            1,
            1,
            ObligationKind::ArithmeticSafety,
            Some(ProofStrength {
                reasoning: ReasoningKind::Pdr,
                assurance: AssuranceLevel::SmtBacked,
            }),
        ),
    ];
    let context =
        VerifierExecutionContext::new("run-serial-batches").with_limits(VerifierResourceLimits {
            worker_threads: Some(1),
            ..VerifierResourceLimits::unlimited()
        });

    let result =
        engine.verify_bundle_with_native_trust_ir_bundle(&bundle, &native_bundle, &context);

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 2);
    assert_eq!(max_active_calls.load(Ordering::SeqCst), 1);
    let batch_diagnostics = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.contains("full-verification engine batch"))
        .collect::<Vec<_>>();
    assert_eq!(batch_diagnostics.len(), 2);
    assert!(batch_diagnostics.iter().all(|diagnostic| {
        diagnostic.contains("elapsed_ms=") && diagnostic.contains("worker_threads=1")
    }));
    let manifest = result.to_manifest();
    assert_eq!(manifest.context.limits.worker_threads, Some(1));
}

#[test]
fn full_verifier_rejects_child_proof_when_trust_vc_authority_was_not_replayed() {
    let native_bundle = native_trust_ir_unreplayed_trust_vc_bundle();
    let validation_errors =
        native_bundle.validate().expect_err("negative fixture must fail strict admission");
    assert!(
        validation_errors.iter().any(|error| matches!(
            error,
            trust_ir::NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                request: trust_ir::NativeRequestId(0),
                obligation: trust_ir::ProofId(0),
                prover,
                status: trust_ir::ProofStatus::Discharged,
            } if prover == "trust-vc"
        )),
        "negative fixture must exercise replay authority: {validation_errors:?}"
    );

    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-vc",
            EngineKind::Deductive,
            ObligationKind::MemorySafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::OwnershipAnalysis,
                    assurance: AssuranceLevel::Sound,
                }),
                artifacts: vec![
                    solver_transcript_artifact("forged-trust-vc-transcript"),
                    proof_check_artifact("forged-trust-vc-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle = TrustContractBundle::empty(
        "bundle-unreplayed-trust-vc",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations =
        vec![native_trust_ir_obligation("trust-vc", 0, 0, ObligationKind::MemorySafety, None)];

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-unreplayed-trust-vc"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(result.summary.missing_proof_artifacts, 1, "{result:#?}");
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("missing a valid typed TrustIr NativeVerificationBundle")
            && diagnostic.contains("TrustVcCertificateNotDischarged")
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr NativeVerificationBundle validation failed")
            && diagnostic.contains("TrustVcCertificateNotDischarged")
    }));
}

#[test]
fn full_verifier_accepts_publication_grade_child_evidence() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            ProofStrength { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::SmtBacked },
        ))],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-mc-publication-grade",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![native_trust_ir_obligation(
        "trust-mc",
        1,
        1,
        ObligationKind::ArithmeticSafety,
        Some(ProofStrength { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::SmtBacked }),
    )];
    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-3"),
    );

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 1);
    assert_eq!(result.evidence[0].engine.name, "trust-full-verifier");
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-mc"))
    );
}

#[test]
fn proof_grade_without_replay_check_metadata_fails_full_mode() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "ty",
            EngineKind::Temporal,
            ObligationKind::Liveness,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                }),
                artifacts: Vec::new(),
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-no-proof-artifacts"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.contains(EXACT_ARTIFACT_POLICY_REJECTION) })
    );
}

#[test]
fn primary_native_route_proved_evidence_requires_native_bundle_without_identity_hints() {
    for (engine_name, engine_kind, obligation_kind, proof_strength) in [
        (
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked },
        ),
        (
            "trust-vc",
            EngineKind::Deductive,
            ObligationKind::MemorySafety,
            ProofStrength {
                reasoning: ReasoningKind::OwnershipAnalysis,
                assurance: AssuranceLevel::Sound,
            },
        ),
    ] {
        let artifacts = vec![
            solver_transcript_artifact(&format!("{engine_name}-text-transcript")),
            proof_check_artifact(&format!("{engine_name}-text-proof-check")),
        ];
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                engine_name,
                engine_kind,
                obligation_kind.clone(),
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(proof_strength.clone()),
                    artifacts,
                    diagnostics: vec![format!("{engine_name} fixture/text-only proof evidence")],
                },
            ))],
            route_only_policy(),
        );
        let obligation_id = format!("obligation-{engine_name}-text-only");
        let bundle = bundle_with_obligation(obligation_kind, &obligation_id, None, None);
        let result = engine.verify_bundle(
            &bundle,
            &VerifierExecutionContext::new(format!("run-{engine_name}-missing-native-bundle")),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{engine_name}");
        assert_eq!(result.summary.proved, 0, "{engine_name}");
        assert_eq!(result.summary.missing_proof_artifacts, 1, "{engine_name}");
        assert!(result.evidence[0].artifacts.is_empty(), "{engine_name}");
        assert!(
            result.evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("requires typed TrustIr native request/proof artifacts")
                    && diagnostic.contains("no typed TrustIr NativeVerificationBundle was supplied")
            }),
            "{engine_name}"
        );

        let structured = result.full_verification_obligation_evidence();
        let native_trust_ir =
            structured[0].native_trust_ir.as_ref().expect("native TrustIr evidence view");
        assert_eq!(native_trust_ir.expected_suite, engine_name);
        assert!(!native_trust_ir.has_matching_artifacts(), "{engine_name}");
        assert!(
            structured[0].blockers.iter().any(|blocker| {
                matches!(
                    blocker,
                    FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch {
                        obligation_id: id,
                        expected_suite,
                        identity_error: Some(_),
                        ..
                    } if id == &obligation_id && expected_suite == engine_name
                )
            }),
            "{engine_name}"
        );
    }
}

#[test]
fn native_trust_ir_bundle_identity_is_preserved_for_active_trust_mc() {
    let native_bundle = native_trust_ir_mc_bundle();
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![
                    solver_transcript_artifact("trust-mc-native-transcript"),
                    proof_check_artifact("trust-mc-native-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-ir",
        BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::checked_transfer".to_string(),
        },
    );
    bundle.obligations =
        vec![native_trust_ir_obligation("trust-mc", 1, 1, ObligationKind::ArithmeticSafety, None)];

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-ir-mc"),
    );

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 1);
    assert_eq!(result.summary.missing_proof_artifacts, 0);

    for (suite, request_id, proof_id) in [("trust-mc", 1, 1)] {
        let obligation_id =
            format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
        let evidence = result
            .evidence
            .iter()
            .find(|item| item.obligation_id == obligation_id)
            .expect("native evidence should be present");
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("typed TrustIr native request identity accepted")
                && diagnostic.contains(&format!("suite={suite}"))
                && diagnostic.contains(&format!("request_id={request_id}"))
                && diagnostic.contains(&format!("proof_obligation_id={proof_id}"))
        }));
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::EngineInput
                && artifact.uri.contains(&format!("/{suite}/request/{request_id}"))
        }));
        assert!(
            evidence.artifacts.iter().any(|artifact| {
                artifact.kind == EvidenceArtifactKind::NormalizedObligation
                    && artifact.uri.contains(&format!("/{suite}/request/{request_id}/"))
                    && artifact.uri.contains(&format!("/proof/{proof_id}/"))
            }),
            "suite={suite} artifacts={:?}",
            evidence.artifacts
        );
    }

    let manifest = result.to_manifest();
    assert_eq!(manifest.accepted_evidence.len(), 1);
    assert!(manifest.rejected_evidence.is_empty());
    assert!(manifest.artifacts.iter().any(|artifact| {
        artifact.uri.starts_with("trust_ir-native://verification-bundle/")
            && artifact.uri.contains("/trust-mc/request/1/")
            && artifact.uri.contains("/proof/1/")
    }));
    assert!(manifest.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr NativeVerificationBundle indexed")
            // The three original primary requests keep their identities; the
            // postcondition also carries one separate native WP alternative.
            && diagnostic.contains("requests=4")
    }));

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 1);
    for item in &structured {
        assert!(item.has_accepted_proof(), "missing accepted proof for {}", item.obligation_id);
        assert!(
            item.blockers.is_empty(),
            "unexpected blockers for {}: {:?}",
            item.obligation_id,
            item.blockers
        );
        let native_trust_ir = item.native_trust_ir.as_ref().expect("native TrustIr evidence view");
        assert_eq!(native_trust_ir.expected_suite.as_str(), item.primary_suite.as_deref().unwrap());
        assert!(
            native_trust_ir.has_matching_artifacts(),
            "native TrustIr artifacts did not match for {}",
            item.obligation_id
        );
    }
}

#[test]
fn native_trust_ir_mode_rejects_proved_evidence_without_native_obligation_identity() {
    let native_bundle = native_trust_ir_mc_bundle();
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![
                    solver_transcript_artifact("trust-mc-transcript"),
                    proof_check_artifact("trust-mc-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-ir-missing-identity"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("missing TrustIr native proof-obligation identity")
    }));

    let manifest = result.to_manifest();
    assert_eq!(manifest.accepted_evidence.len(), 0);
    assert_eq!(manifest.rejected_evidence.len(), 1);
    assert_eq!(
        manifest.rejected_evidence[0].disposition,
        EvidenceDisposition::RejectedMissingProofArtifacts
    );

    let structured = result.full_verification_obligation_evidence();
    let native_trust_ir =
        structured[0].native_trust_ir.as_ref().expect("native TrustIr evidence view");
    assert_eq!(native_trust_ir.expected_suite, "trust-mc");
    assert!(!native_trust_ir.has_matching_artifacts());
    assert!(native_trust_ir.identity_error.as_ref().is_some_and(|error| {
        error.contains("missing TrustIr native proof-obligation identity")
    }));
    assert!(structured[0].blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch {
                obligation_id,
                expected_suite,
                identity_error: Some(_),
                ..
            } if obligation_id == "obligation-overflow" && expected_suite == "trust-mc"
        )
    }));
}

#[test]
fn proved_evidence_with_native_trust_ir_identity_requires_native_bundle() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![
                    solver_transcript_artifact("trust-mc-transcript"),
                    proof_check_artifact("trust-mc-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);
    bundle.obligations[0] =
        native_trust_ir_obligation("trust-mc", 1, 1, ObligationKind::ArithmeticSafety, None);

    let result = engine.verify_bundle(
        &bundle,
        &VerifierExecutionContext::new("run-native-trust-ir-identity-without-bundle"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("requires typed TrustIr native request/proof artifacts")
            && diagnostic.contains("no typed TrustIr NativeVerificationBundle was supplied")
    }));

    let structured = result.full_verification_obligation_evidence();
    let native_trust_ir =
        structured[0].native_trust_ir.as_ref().expect("native TrustIr evidence view");
    assert_eq!(native_trust_ir.expected_suite, "trust-mc");
    assert_eq!(native_trust_ir.request_id, Some(1));
    assert_eq!(native_trust_ir.proof_obligation_id, Some(1));
    assert!(!native_trust_ir.has_matching_artifacts());
    assert!(structured[0].blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch {
                obligation_id,
                expected_suite,
                request_id: Some(1),
                proof_obligation_id: Some(1),
                ..
            } if obligation_id == "trust_ir-native-trust-mc-request-1-proof-1"
                && expected_suite == "trust-mc"
        )
    }));
}

#[test]
fn native_trust_ir_mode_rejects_proved_evidence_when_bundle_validation_fails() {
    let mut native_bundle = native_trust_ir_mc_bundle();
    native_bundle.requests.clear();
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![
                    solver_transcript_artifact("trust-mc-transcript"),
                    proof_check_artifact("trust-mc-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);
    bundle.obligations[0] =
        native_trust_ir_obligation("trust-mc", 1, 1, ObligationKind::ArithmeticSafety, None);

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-ir-invalid-bundle"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("missing a valid typed TrustIr NativeVerificationBundle")
            && diagnostic.contains("EmptyRequests")
    }));
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr NativeVerificationBundle validation failed")
            && diagnostic.contains("EmptyRequests")
    }));
}

#[test]
fn trust_mc_solver_transcript_without_replay_check_is_rejected() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![solver_transcript_artifact("trust-mc-transcript-only")],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);
    let result = engine
        .verify_bundle(&bundle, &VerifierExecutionContext::new("run-trust-mc-transcript-only"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.contains(EXACT_ARTIFACT_POLICY_REJECTION) })
    );
}

#[test]
fn trust_vc_requires_suite_native_replay_check_artifacts() {
    for (run_id, engine_name, engine_kind, obligation_kind, proof_strength) in [(
        "run-trust-vc-transcript-only",
        "trust-vc",
        EngineKind::Deductive,
        ObligationKind::MemorySafety,
        ProofStrength {
            reasoning: ReasoningKind::OwnershipAnalysis,
            assurance: AssuranceLevel::Sound,
        },
    )] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                engine_name,
                engine_kind,
                obligation_kind.clone(),
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(proof_strength.clone()),
                    artifacts: vec![solver_transcript_artifact(&format!(
                        "{engine_name}-transcript-only"
                    ))],
                    diagnostics: Vec::new(),
                },
            ))],
            route_only_policy(),
        );
        let bundle = bundle_with_obligation(obligation_kind, "obligation-suite-native", None, None);
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new(run_id));

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.missing_proof_artifacts, 1);
        assert!(result.evidence[0].artifacts.is_empty());
        assert!(
            result.evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains(EXACT_ARTIFACT_POLICY_REJECTION) })
        );
    }
}

#[test]
fn full_verifier_rejects_trust_mc_adapter_serialized_metadata_as_diagnostic_only() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(TrustMcVerifierApiAdapter::default())],
        route_only_policy(),
    );
    let mut bundle = bundle_with_obligation(
        ObligationKind::ArithmeticSafety,
        "obligation-trust-mc-pdr",
        None,
        None,
    );
    let verdict = trust_mc_core_proof_grade_verdict("obligation-trust-mc-pdr");
    bundle.obligations[0].metadata.push(
        trust_bmc::trust_mc_full_verification_verdict_metadata_entry(
            "obligation-trust-mc-pdr",
            &verdict,
        )
        .expect("trust-mc verdict metadata should serialize"),
    );

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-trust-mc-adapter-pdr"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.summary.missing_proof_artifacts, 0);
    assert_eq!(result.evidence[0].engine.name, "trust-full-verifier");
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert_eq!(result.evidence[0].proof_strength, None);
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic
            .contains("serialized trust_mc FullVerificationVerdict metadata is diagnostic-only")
    }));
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("primary owner trust-mc@") && diagnostic.contains("rejected evidence")
    }));

    let manifest = result.to_manifest();
    assert_eq!(manifest.accepted_evidence, Vec::new());
    assert_eq!(manifest.rejected_evidence.len(), 1);
    assert_ne!(manifest.rejected_evidence[0].disposition, EvidenceDisposition::AcceptedProof);
}

#[test]
fn ay_backed_evidence_without_solver_transcript_is_rejected() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![proof_check_artifact("ay-proof-check-only")],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);
    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-ay-transcript-required"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.missing_proof_artifacts, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.contains(EXACT_ARTIFACT_POLICY_REJECTION) })
    );
}

#[test]
fn ty_temporal_evidence_requires_model_check_transcript() {
    for (run_id, artifacts, expected_status) in [
        (
            "run-ty-proof-check-only",
            vec![proof_check_artifact("ty-proof-check-only")],
            VerificationRunStatus::Inconclusive,
        ),
        (
            "run-ty-transcript",
            vec![
                solver_transcript_artifact("ty-model-check-transcript"),
                proof_check_artifact("ty-proof-check"),
            ],
            VerificationRunStatus::Proved,
        ),
    ] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(ProofStrength {
                        reasoning: ReasoningKind::TemporalModelCheck,
                        assurance: AssuranceLevel::Sound,
                    }),
                    artifacts,
                    diagnostics: Vec::new(),
                },
            ))],
            route_only_policy(),
        );
        let bundle =
            bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new(run_id));

        assert_eq!(result.status, expected_status);
        if expected_status == VerificationRunStatus::Inconclusive {
            assert_eq!(result.summary.missing_proof_artifacts, 1);
            assert!(
                result.evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| { diagnostic.contains(EXACT_ARTIFACT_POLICY_REJECTION) })
            );
        } else {
            assert_eq!(result.summary.proved, 1);
            assert_eq!(result.summary.missing_proof_artifacts, 0);
        }
    }
}

#[test]
fn ay_or_ty_unknown_and_timeout_block_full_verification() {
    for (run_id, engine_name, engine_kind, obligation_kind, status, expected_summary) in [
        (
            "run-ay-unknown",
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            EvidenceStatus::Unknown,
            EvidenceStatus::Unknown,
        ),
        (
            "run-ay-timeout",
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            EvidenceStatus::Timeout,
            EvidenceStatus::Timeout,
        ),
        (
            "run-ty-unknown",
            "ty",
            EngineKind::Temporal,
            ObligationKind::Liveness,
            EvidenceStatus::Unknown,
            EvidenceStatus::Unknown,
        ),
        (
            "run-ty-timeout",
            "ty",
            EngineKind::Temporal,
            ObligationKind::Liveness,
            EvidenceStatus::Timeout,
            EvidenceStatus::Timeout,
        ),
    ] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                engine_name,
                engine_kind,
                obligation_kind.clone(),
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status,
                    proof_strength: None,
                    artifacts: Vec::new(),
                    diagnostics: vec!["non-definitive native lane result".to_string()],
                },
            ))],
            route_only_policy(),
        );
        let bundle = bundle_with_obligation(obligation_kind, "obligation-native-lane", None, None);
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new(run_id));

        assert!(
            matches!(
                result.status,
                VerificationRunStatus::Inconclusive | VerificationRunStatus::TimedOut
            ),
            "non-definitive evidence must not prove the run"
        );
        assert_eq!(result.summary.proved, 0);
        match expected_summary {
            EvidenceStatus::Unknown => assert_eq!(result.summary.unknown, 1),
            EvidenceStatus::Timeout => assert_eq!(result.summary.timed_out, 1),
            _ => unreachable!("test only covers unknown and timeout"),
        }
        assert!(!result.is_fully_proved());
    }
}

#[test]
fn unchecked_and_runtime_evidence_remain_rejected_in_full_mode() {
    for (run_id, proof_strength) in [
        (
            "run-unchecked",
            ProofStrength {
                reasoning: ReasoningKind::TemporalModelCheck,
                assurance: AssuranceLevel::Unchecked,
            },
        ),
        (
            "run-runtime",
            ProofStrength {
                reasoning: ReasoningKind::TemporalModelCheck,
                assurance: AssuranceLevel::RuntimeObserved,
            },
        ),
    ] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(proof_strength),
                    artifacts: vec![proof_check_artifact(run_id)],
                    diagnostics: Vec::new(),
                },
            ))],
            route_only_policy(),
        );
        let bundle =
            bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new(run_id));

        assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.insufficient_strength, 1);
        assert_eq!(result.summary.proved, 0);
    }
}

#[test]
fn secondary_engine_cannot_replace_missing_primary_owner() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-vc",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-4"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.summary.skipped, 0);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-mc is required"))
    );
}

#[test]
fn missing_primary_evidence_fails_without_skipping_obligation() {
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::new(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::Postcondition,
                SupportLevel::Preferred,
                UnitEvidenceMode::Empty,
            )),
            Box::new(UnitEngine::proving(
                "trust-vc",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
            )),
        ],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-5"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.evidence_count, 1);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.summary.skipped, 0);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("silently dropped obligations"))
    );
}

#[test]
fn pre_solve_stop_generic_primary_cannot_copy_native_or_router_phase() {
    for (name, kind, obligation_kind) in [
        ("trust-mc", EngineKind::Reachability, ObligationKind::ArithmeticSafety),
        ("trust-vc", EngineKind::Deductive, ObligationKind::MemorySafety),
    ] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                name,
                kind,
                obligation_kind.clone(),
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Unsupported,
                    proof_strength: None,
                    artifacts: Vec::new(),
                    diagnostics: vec![
                        trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into(),
                        trust_verifier_api::ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into(),
                    ],
                },
            ))],
            route_only_policy(),
        );
        let bundle = bundle_with_obligation(obligation_kind, "copied-phase", None, None);
        let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("copied-phase"));
        assert!(!result.is_fully_proved());
        assert_eq!(result.evidence.len(), 1);
        let row = &result.evidence[0];
        assert_eq!(row.status, EvidenceStatus::Unsupported);
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty() && row.decline.is_none());
        assert!(
            !row.diagnostics.iter().any(|d| {
                d == trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                    || d == trust_verifier_api::ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
            }),
            "generic primary {name} copied a native stop phase through the composite"
        );
    }
}

#[test]
fn bounded_primary_evidence_fails_full_mode() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::ArithmeticSafety,
            ProofStrength::bounded(8),
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::ArithmeticSafety, "obligation-overflow", None, None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-6"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.bounded_proved, 1);
    assert!(!result.is_fully_proved());
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("bounded proof is diagnostic-only"))
    );
}

#[test]
fn manifest_accounts_for_primary_routed_accepted_rejected_and_skipped_obligations() {
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::new(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(ProofStrength {
                        reasoning: ReasoningKind::TemporalModelCheck,
                        assurance: AssuranceLevel::Sound,
                    }),
                    artifacts: vec![
                        solver_transcript_artifact("ty-manifest-transcript"),
                        proof_check_artifact("ty-manifest-proof-check"),
                    ],
                    diagnostics: Vec::new(),
                },
            )),
            Box::new(UnitEngine::proving(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::ArithmeticSafety,
                ProofStrength::bounded(8),
            )),
            Box::new(UnitEngine::proving(
                "trust-vc",
                EngineKind::Deductive,
                ObligationKind::Ownership,
                ProofStrength::deductive(),
            )),
        ],
        route_only_policy(),
    );
    let mut bundle =
        bundle_with_obligation(ObligationKind::Liveness, "obligation-live", None, None);
    bundle.obligations.push(TrustObligation {
        obligation_id: "obligation-overflow".to_string(),
        kind: ObligationKind::ArithmeticSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "prove arithmetic safety".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });
    bundle.obligations.push(TrustObligation {
        obligation_id: "obligation-ownership".to_string(),
        kind: ObligationKind::Ownership,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "prove ownership".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });

    let context = VerifierExecutionContext::new("run-manifest");
    // Leave the ownership obligation without evidence to exercise manifest skipped accounting.
    let routed_evidence =
        engine.verify_with_context(&bundle, &bundle.obligations[..2], &context).evidence;
    let result = VerificationRunResult::from_evidence(
        context.snapshot(),
        &bundle,
        engine.manifest().clone(),
        &bundle.obligations,
        routed_evidence,
    );
    let manifest = result.to_manifest();

    assert_eq!(manifest.status, VerificationRunStatus::Inconclusive);
    assert_eq!(manifest.summary.requested_obligations, 3);
    assert_eq!(manifest.summary.proved, 1);
    assert_eq!(manifest.summary.bounded_proved, 1);
    assert_eq!(manifest.summary.skipped, 1);

    assert_eq!(manifest.accepted_evidence.len(), 1);
    assert_eq!(manifest.accepted_evidence[0].obligation_id, "obligation-live");
    assert_eq!(manifest.accepted_evidence[0].disposition, EvidenceDisposition::AcceptedProof);
    assert_eq!(manifest.accepted_evidence[0].engine.name, "trust-full-verifier");

    assert_eq!(manifest.rejected_evidence.len(), 1);
    assert_eq!(manifest.rejected_evidence[0].obligation_id, "obligation-overflow");
    assert_eq!(manifest.rejected_evidence[0].disposition, EvidenceDisposition::RejectedBounded);
    assert_eq!(manifest.rejected_evidence[0].engine.name, "trust-full-verifier");

    assert_eq!(manifest.skipped.len(), 1);
    assert_eq!(manifest.skipped[0].obligation_id, "obligation-ownership");
    assert!(matches!(
        &manifest.skipped[0].reason,
        SkipReason::NotAttempted { reason }
            if reason.contains("engine returned no evidence")
    ));

    let skipped_obligation = manifest
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == "obligation-ownership")
        .expect("manifest should include skipped requested obligation");
    assert_eq!(skipped_obligation.evidence_count, 0);
    assert!(skipped_obligation.skipped);

    let structured = result.full_verification_obligation_evidence();
    let skipped = structured
        .iter()
        .find(|obligation| obligation.obligation_id == "obligation-ownership")
        .expect("structured skipped obligation is present");
    assert!(!skipped.has_accepted_proof());
    assert!(matches!(skipped.skipped, Some(SkipReason::NotAttempted { .. })));
    assert!(skipped.blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::Skipped {
                obligation_id,
                reason: SkipReason::NotAttempted { .. },
            } if obligation_id == "obligation-ownership"
        )
    }));
}

#[test]
fn unsupported_primary_engine_blocks_full_verification() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::Postcondition,
            SupportLevel::Unsupported { reason: "native lowering missing".to_string() },
            UnitEvidenceMode::Empty,
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(None);
    let support = engine.supports(&bundle.obligations[0]);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-7"));

    assert!(matches!(
        support,
        SupportLevel::Unsupported { reason } if reason == "native lowering missing"
    ));
    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.unsupported, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-mc@0.1.0 rejected"))
    );
}

#[test]
fn full_verifier_manifest_includes_every_routed_bounds_obligation() {
    let engine = FullVerificationEngine::new(Vec::new(), route_only_policy());

    assert!(engine.manifest().capabilities.iter().any(|capability| {
        capability.obligation_kind == ObligationKind::BoundsCheck
            && capability.support == SupportLevel::Preferred
    }));
}

#[test]
fn duplicate_primary_engine_registration_is_ambiguous_and_fails_closed() {
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::proving(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::Postcondition,
                ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                },
            )),
            Box::new(UnitEngine::proving(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::Postcondition,
                ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                },
            )),
        ],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(None);

    let support = engine.supports(&bundle.obligations[0]);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-duplicate"));

    assert!(matches!(
        support,
        SupportLevel::Unsupported { reason }
            if reason.contains("ambiguous duplicate primary engines: trust-mc")
    ));
    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("ambiguous duplicate primary engines: trust-mc")
    }));
}

#[test]
fn invalid_primary_manifest_is_rejected_before_dispatch() {
    let mut invalid = UnitEngine::proving(
        "trust-mc",
        EngineKind::Reachability,
        ObligationKind::Postcondition,
        ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked },
    );
    invalid.manifest.api_version = "forged-future-api".to_string();
    let engine = FullVerificationEngine::new(vec![Box::new(invalid)], route_only_policy());
    let bundle = bundle_with_postcondition(None);

    let support = engine.supports(&bundle.obligations[0]);
    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-invalid-engine"));

    assert!(matches!(support, SupportLevel::Unsupported { reason }
        if reason.contains("invalid engine manifests")
            && reason.contains("incompatible API version")));
    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("invalid engine manifests")
            && diagnostic.contains("incompatible API version")
    }));
}

#[test]
fn trust_wp_proof_is_rejected_for_trust_vc_owned_obligation() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Ownership,
            ProofStrength::deductive(),
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::Ownership, "obligation-ownership", None, None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-8"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.unsupported, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-vc is required"))
    );
}

#[test]
fn trust_mc_proof_is_rejected_for_trust_vc_owned_memory_safety() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-mc",
            EngineKind::Reachability,
            ObligationKind::MemorySafety,
            ProofStrength { reasoning: ReasoningKind::Chc, assurance: AssuranceLevel::SmtBacked },
        ))],
        route_only_policy(),
    );
    let bundle =
        bundle_with_obligation(ObligationKind::MemorySafety, "obligation-memory", None, None);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-9"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.unsupported, 1);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-vc is required"))
    );
}

#[test]
fn required_engine_policy_rejects_partial_engine_sets() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
        ))],
        FullVerificationPolicy::default(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

    let support = engine.supports(&bundle.obligations[0]);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-missing"));

    assert!(matches!(
        support,
        SupportLevel::Unsupported { reason }
            if reason.contains("missing: trust-vc, trust-mc, ty")
    ));
    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("missing: trust-vc, trust-mc, ty"))
    );
}

#[test]
fn required_engine_policy_rejects_name_only_experimental_placeholder() {
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::proving(
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
            )),
            Box::new(UnitEngine::new(
                "trust-vc",
                EngineKind::Deductive,
                ObligationKind::Ownership,
                SupportLevel::Experimental { reason: "placeholder only".to_string() },
                UnitEvidenceMode::Empty,
            )),
            Box::new(UnitEngine::proving(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::ArithmeticSafety,
                ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                },
            )),
            Box::new(UnitEngine::proving(
                "ty",
                EngineKind::Temporal,
                ObligationKind::Liveness,
                ProofStrength {
                    reasoning: ReasoningKind::TemporalModelCheck,
                    assurance: AssuranceLevel::Sound,
                },
            )),
        ],
        FullVerificationPolicy::default(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

    let support = engine.supports(&bundle.obligations[0]);
    let result = engine
        .verify_bundle(&bundle, &VerifierExecutionContext::new("run-experimental-placeholder"));

    assert!(matches!(
        support,
        SupportLevel::Unsupported { reason } if reason.contains("missing: trust-vc")
    ));
    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("missing: trust-vc"))
    );
}

/// Trust (#59, 2026-08-19) — these concurrency obligations MUST NOT ROUTE.
///
/// Potential-race producers now emit `UnsupportedMir` candidates, not
/// solver-dischargeable race VCs. The typed `trust.vc/insufficient_ordering`
/// obligation still lacks an execution model, and a typed `data_race` obligation
/// must not gain a route independently of authenticated source, event, and
/// happens-before evidence. Local atomic-log ordering checks remain separate.
///
/// These typed obligations cannot route today, but only INCIDENTALLY:
/// `ObligationKind::Custom { .. }
/// => return None` is a catch-all reached after the two privileged namespace arms,
/// and `fallback_route` returns `None` unconditionally. Nothing anywhere asserted
/// the intent, so the protection was a side effect of the match order rather than a
/// stated invariant.
///
/// That is exactly the shape that breaks silently. v6/D2 makes `ty` the owner of
/// concurrency, which makes "add a route for these kinds" the obvious next edit for
/// someone who has not read the hazard note. This test makes that edit go RED
/// instead of green.
///
/// THE UNBLOCK CONDITION, stated so this test is not read as a permanent veto:
/// route these only once the emitters carry a real memory and happens-before model.
/// The gate is the model, not this assertion.
#[test]
fn concurrency_obligations_are_unroutable_until_their_formula_is_real() {
    fn custom(namespace: &str, name: &str) -> TrustObligation {
        TrustObligation {
            obligation_id: format!("{namespace}/{name}"),
            kind: ObligationKind::Custom {
                namespace: namespace.to_string(),
                name: name.to_string(),
            },
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "concurrency obligation".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    for name in ["data_race", "insufficient_ordering"] {
        let obligation = custom(trust_verifier_api::TRUST_VC_OBLIGATION_NAMESPACE, name);

        assert!(
            super::routing::obligation_route(&obligation).is_none(),
            "`trust.vc/{name}` MUST NOT route without an authenticated concurrency model"
        );
        assert!(
            super::routing::fallback_route(&obligation).is_none(),
            "`trust.vc/{name}` MUST NOT reach a fallback engine without an authenticated \
             concurrency model"
        );
    }
}

/// POSITIVE CONTROL for the guard above. A test that only asserts `None` can pass
/// because routing is broken for everything, so pin that the privileged namespace
/// DOES route — the guard is then known to discriminate.
#[test]
fn the_privileged_hardened_namespace_still_routes() {
    let obligation = TrustObligation {
        obligation_id: "hardened/probe".to_string(),
        kind: ObligationKind::Custom {
            namespace: trust_verifier_api::TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
            name: "os_path".to_string(),
        },
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "hardened obligation".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };
    assert!(
        super::routing::obligation_route(&obligation).is_some(),
        "the hardened namespace is the ONE privileged Custom namespace and must still \
         route — without this, the unroutability guard above could pass vacuously"
    );
}

/// A native-trust-mc look-alike that records every obligation it is asked to
/// solve. Default-feature builds have no in-process native trust-mc adapter,
/// so the router falls through to this engine's `verify_validated` whenever it
/// dispatches the row.
struct DispatchRecordingNativeTrustMc {
    manifest: EngineManifest,
    dispatched: Arc<Mutex<Vec<String>>>,
}

impl DispatchRecordingNativeTrustMc {
    fn new(dispatched: Arc<Mutex<Vec<String>>>) -> Self {
        let mut manifest = EngineManifest::new(
            "trust-mc",
            "0.1.0+native-trust-ir-bundle",
            EngineKind::Reachability,
        );
        manifest.repository = Some("trust-bmc".to_string());
        manifest.capabilities.push(EngineCapability {
            obligation_kind: ObligationKind::Assertion,
            support: SupportLevel::Preferred,
        });
        Self { manifest, dispatched }
    }
}

impl VerificationEngine for DispatchRecordingNativeTrustMc {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::Assertion {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported { reason: "assertions only".to_string() }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        request
            .obligations()
            .iter()
            .map(|obligation| {
                self.dispatched
                    .lock()
                    .expect("dispatch log")
                    .push(obligation.obligation_id.clone());
                ObligationEvidence {
                    evidence_id: format!("trust-mc:recorded:{}", obligation.obligation_id),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Proved,
                    decline: None,
                    proof_strength: Some(ProofStrength {
                        reasoning: ReasoningKind::Pdr,
                        assurance: AssuranceLevel::SmtBacked,
                    }),
                    artifacts: exact_fixture_proof_artifacts(obligation, "recorded-trust-mc"),
                    counterexample: None,
                    publication: EvidencePublicationMetadata::default(),
                    diagnostics: Vec::new(),
                }
            })
            .collect()
    }
}

const NATIVE_TRUST_MC_SKIP_DIAGNOSTIC: &str = "native trust-mc solve not dispatched";

fn native_trust_mc_skip_obligation(kind: ObligationKind, exact: bool) -> TrustObligation {
    let mut obligation = native_trust_ir_obligation(
        "trust-mc",
        1,
        1,
        kind,
        Some(ProofStrength { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::SmtBacked }),
    );
    if exact {
        obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
            value: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT.to_string(),
        });
    }
    obligation
}

/// The `bundle`-role materialization's payload of `bundle`, decoded.
fn native_bundle_transport_payload_of(bundle: &NativeVerificationBundle) -> serde_json::Value {
    let index = super::native_trust_ir::NativeTrustIrEvidenceIndex::from_bundle(bundle);
    assert!(
        index.validation_errors_for_test().is_empty(),
        "fixture bundle must index cleanly: {:?}",
        index.validation_errors_for_test()
    );
    let bytes = index
        .bundle_artifact_for_test()
        .materialization
        .as_ref()
        .expect("fixture bundle materializes inline")
        .bytes()
        .to_vec();
    let mut envelope: serde_json::Value =
        serde_json::from_slice(&bytes).expect("bundle envelope is JSON");
    assert_eq!(envelope["role"], "bundle");
    envelope["payload"].take()
}

fn native_bundle_transport_atoms(payload: &serde_json::Value) -> Vec<serde_json::Value> {
    payload["bundle"]["requests"]
        .as_array()
        .expect("requests")
        .iter()
        .flat_map(|request| request.as_object().expect("tagged request").values())
        .flat_map(|request| {
            request["provenance"]["replay_context"]["atoms"].as_array().cloned().unwrap_or_default()
        })
        .collect()
}

/// G3 (2026-10-27): the bundle materialization carried every obligation formula
/// twice (once in the module, once in its request's replay atom), which put
/// agy-alab's `civil_from_days` bundle at 19.7 MB, over the 16 MiB inline cap, and
/// cost every row of the function its native evidence. A replay atom whose formula
/// is byte-identical to its obligation's now carries a reference; an atom whose
/// formula differs (obligation 1 in this fixture) stays inline; and the reader
/// restores the exact typed bundle.
#[test]
fn native_bundle_transport_references_duplicate_replay_formulas_and_rehydrates_exactly() {
    let bundle = native_trust_ir_mc_bundle();
    let payload = native_bundle_transport_payload_of(&bundle);
    assert_eq!(payload["encoding"], super::NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING);
    assert_eq!(payload.as_object().map(serde_json::Map::len), Some(2));

    let atoms = native_bundle_transport_atoms(&payload);
    let referenced = atoms
        .iter()
        .filter(|atom| atom.get("formula_ref").is_some())
        .map(|atom| {
            assert!(atom.get("formula").is_none(), "a referenced atom keeps no inline copy");
            assert_eq!(atom["formula_ref"]["obligation"], atom["obligation"]);
            atom["obligation"].as_u64().expect("obligation id")
        })
        .collect::<Vec<_>>();
    let inline = atoms
        .iter()
        .filter(|atom| atom.get("formula").is_some())
        .map(|atom| atom["obligation"].as_u64().expect("obligation id"))
        .collect::<Vec<_>>();
    assert_eq!(referenced, vec![0, 2], "byte-identical replay formulas are referenced");
    assert_eq!(inline, vec![1], "a replay formula that differs from its obligation stays inline");

    let rehydrated = super::rehydrate_native_bundle_transport_payload(&payload)
        .expect("the reader restores the bundle");
    assert_eq!(rehydrated, bundle, "the transport encoding is lossless");
    assert_eq!(rehydrated.stable_digest(), bundle.stable_digest());
}

/// The cap itself, through `NativeTrustIrEvidenceIndex::from_bundle` (the in-process
/// engine's index): a bundle whose obligation formula and its replay-atom copy are
/// each ~12 MB of JSON (6 MB of SMT-LIB, carried in both `payload` and `smtlib`)
/// serializes to ~24 MB, more than `MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES`
/// (16 MiB), with the copy inline, and to ~12 MB with the copy referenced. Before the fix this
/// index reported "canonical TrustIr bundle payload is empty or exceeds inline
/// transport limit" and refused every proof on the bundle; the positive control
/// below measures that the plain JSON is over the cap, so the test cannot pass by
/// the fixture being small.
#[test]
fn native_bundle_over_the_inline_cap_only_by_replay_duplicates_still_materializes() {
    let mut bundle = native_trust_ir_mc_bundle();
    let large = trust_ir::ProofFormula::smtlib2(
        format!("(and {})", vec!["true"; 1_200_000].join(" ")),
        "Bool",
    );
    replace_native_proof_obligation_formula(&mut bundle, trust_ir::ProofId::new(0), large.clone());
    replace_router_native_replay_formula(
        &mut bundle,
        trust_ir::NativeVerifierSuite::TrustMc,
        trust_ir::ProofId::new(0),
        large,
    );
    rebind_native_bundle_module_digest(&mut bundle);
    bundle.validate().expect("large fixture remains a valid bundle");
    let plain = serde_json::to_vec(&bundle).expect("plain bundle JSON");
    assert!(
        plain.len() > trust_verifier_api::MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES,
        "positive control: the plain bundle must exceed the inline cap ({} bytes)",
        plain.len()
    );

    let payload = native_bundle_transport_payload_of(&bundle);
    let rehydrated = super::rehydrate_native_bundle_transport_payload(&payload)
        .expect("the reader restores the large bundle");
    assert_eq!(rehydrated, bundle);
}

fn first_referenced_transport_atom_mut(payload: &mut serde_json::Value) -> &mut serde_json::Value {
    payload["bundle"]["requests"]
        .as_array_mut()
        .expect("requests")
        .iter_mut()
        .flat_map(|request| request.as_object_mut().expect("tagged request").values_mut())
        .flat_map(|request| {
            request["provenance"]["replay_context"]["atoms"].as_array_mut().into_iter().flatten()
        })
        .find(|atom| atom.get("formula_ref").is_some())
        .expect("fixture has a referenced atom")
}

/// Negative controls for the reader: every malformed reference is refused.
#[test]
fn native_bundle_transport_reader_refuses_malformed_references() {
    let bundle = native_trust_ir_mc_bundle();
    let payload = native_bundle_transport_payload_of(&bundle);
    let refuse = |payload: &serde_json::Value, needle: &str| {
        let error = super::rehydrate_native_bundle_transport_payload(payload)
            .expect_err("malformed transport payload must be refused");
        assert!(error.contains(needle), "{needle:?} not in {error:?}");
    };
    let with_atom = |edit: &dyn Fn(&mut serde_json::Value)| {
        let mut payload = payload.clone();
        edit(first_referenced_transport_atom_mut(&mut payload));
        payload
    };

    // Another encoding (the plain bundle JSON, or a forged name).
    refuse(&payload["bundle"], "encoding");
    let mut forged = payload.clone();
    forged["encoding"] = serde_json::json!("trust.native-bundle.replay-formula-ref.v0");
    refuse(&forged, "encoding");
    // A reference to some other obligation than the atom's own.
    refuse(
        &with_atom(&|atom| atom["formula_ref"]["obligation"] = serde_json::json!(1)),
        "not the atom's own",
    );
    // A reference whose target is absent.
    refuse(
        &with_atom(&|atom| {
            atom["formula_ref"]["obligation"] = serde_json::json!(99);
            atom["obligation"] = serde_json::json!(99);
        }),
        "absent obligation 99",
    );
    // Both an inline formula and a reference.
    refuse(
        &with_atom(&|atom| atom["formula"] = serde_json::json!({"schema": "x", "payload": "y"})),
        "both an inline formula and a formula reference",
    );
    // A reference that is not exactly `{"obligation": id}`.
    refuse(
        &with_atom(&|atom| atom["formula_ref"]["extra"] = serde_json::json!(true)),
        "is not `{\"obligation\": <id>}`",
    );
    // The referenced obligation formula was changed: the restored atom no longer
    // reproduces the payload digest the producer recorded over its formula.
    let mut changed = payload.clone();
    let obligations =
        changed["bundle"]["module"]["proof_obligations"].as_array_mut().expect("obligations");
    let target = obligations
        .iter_mut()
        .find(|obligation| obligation["id"] == serde_json::json!(0))
        .expect("obligation 0");
    target["formula"]["smtlib"] = serde_json::json!("(not true)");
    refuse(&changed, "does not reproduce its recorded payload digest");
    // A repeated obligation id makes every reference to it ambiguous.
    let mut repeated = payload.clone();
    let obligations =
        repeated["bundle"]["module"]["proof_obligations"].as_array_mut().expect("obligations");
    let copy = obligations[0].clone();
    obligations.push(copy);
    refuse(&repeated, "is repeated");
}

/// The admission-valid TrustMc fixture with a validation error injected: an
/// unsupported schema version. The over-limit bundle measured on tla-cert
/// reaches the same refusal through the inline-materialization check.
fn invalid_native_trust_ir_mc_bundle() -> NativeVerificationBundle {
    let mut native_bundle = native_trust_ir_mc_bundle();
    native_bundle.schema_version = u32::MAX;
    assert!(native_bundle.validate().is_err(), "fixture must fail native bundle validation");
    native_bundle
}

fn native_manifest_for_skip_tests() -> EngineManifest {
    DispatchRecordingNativeTrustMc::new(Arc::new(Mutex::new(Vec::new()))).manifest
}

/// fix10 (tla-cert timeouts): the dispatch predicate itself. It fires only when
/// neither of the native trust-mc lane's countable outcomes is possible.
#[test]
fn native_trust_mc_skip_predicate_fires_only_when_no_outcome_could_publish() {
    let invalid = super::native_trust_ir::NativeTrustIrEvidenceIndex::from_bundle(
        &invalid_native_trust_ir_mc_bundle(),
    );
    let valid = super::native_trust_ir::NativeTrustIrEvidenceIndex::from_bundle(
        &native_trust_ir_mc_bundle(),
    );
    let native = native_manifest_for_skip_tests();
    let policy = FullVerificationPolicy::default();
    assert!(policy.require_proof_artifacts);
    let assertion = native_trust_mc_skip_obligation(ObligationKind::Assertion, false);
    let route = super::routing::obligation_route(&assertion).expect("assertion routes");
    assert_eq!(route.primary, super::routing::PrimaryEngine::TrustMc);

    let reason = super::engine::native_trust_mc_solve_cannot_publish(
        policy,
        route,
        &native,
        &assertion,
        Some(&invalid),
    )
    .expect("invalid bundle + unattested non-postcondition row must not dispatch");
    assert!(reason.contains(NATIVE_TRUST_MC_SKIP_DIAGNOSTIC), "{reason}");
    assert!(reason.contains("missing a valid typed TrustIr NativeVerificationBundle"), "{reason}");

    let skip = |policy, manifest: &EngineManifest, obligation: &TrustObligation, index| {
        super::engine::native_trust_mc_solve_cannot_publish(
            policy, route, manifest, obligation, index,
        )
    };
    // A valid bundle, or none at all: proofs can count, so dispatch.
    assert_eq!(skip(policy, &native, &assertion, Some(&valid)), None);
    assert_eq!(skip(policy, &native, &assertion, None), None);
    // Artifacts not required: the bundle refusal is not consulted for proofs.
    let lax = FullVerificationPolicy { require_proof_artifacts: false, ..policy };
    assert_eq!(skip(lax, &native, &assertion, Some(&invalid)), None);
    // A refutation that could count keeps the row dispatched.
    let exact = native_trust_mc_skip_obligation(ObligationKind::Assertion, true);
    assert_eq!(skip(policy, &native, &exact, Some(&invalid)), None);
    let postcondition = native_trust_mc_skip_obligation(ObligationKind::Postcondition, false);
    assert_eq!(skip(policy, &native, &postcondition, Some(&invalid)), None);
    // Only the native trust-mc adapter's outcomes are reasoned about.
    let mut other = native.clone();
    other.repository = Some("elsewhere".to_string());
    assert_eq!(skip(policy, &other, &assertion, Some(&invalid)), None);
}

#[cfg(not(feature = "trust-build"))]
fn run_recording_native_trust_mc(
    exact: bool,
    native_bundle: &NativeVerificationBundle,
) -> (VerificationRunResult, Vec<String>) {
    let dispatched = Arc::new(Mutex::new(Vec::new()));
    let engine = FullVerificationEngine::new(
        vec![Box::new(DispatchRecordingNativeTrustMc::new(Arc::clone(&dispatched)))],
        route_only_policy(),
    );
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-mc-skip",
        BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::checked_transfer".to_string(),
        },
    );
    bundle.obligations = vec![native_trust_mc_skip_obligation(ObligationKind::Assertion, exact)];
    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        native_bundle,
        &VerifierExecutionContext::new("run-native-trust-mc-skip"),
    );
    let dispatched = dispatched.lock().expect("dispatch log").clone();
    (result, dispatched)
}

/// End to end through the router: the skipped row is never sent to the
/// engine, is `Unsupported` (never `Proved`), and names why.
#[cfg(not(feature = "trust-build"))]
#[test]
fn native_trust_mc_is_not_dispatched_when_no_outcome_could_publish() {
    let (result, dispatched) =
        run_recording_native_trust_mc(false, &invalid_native_trust_ir_mc_bundle());

    assert!(dispatched.is_empty(), "solve must not be dispatched: {dispatched:?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    let evidence = &result.evidence[0];
    assert_eq!(evidence.status, EvidenceStatus::Unsupported);
    assert!(evidence.proof_strength.is_none());
    assert!(
        evidence
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains(NATIVE_TRUST_MC_SKIP_DIAGNOSTIC)),
        "{:?}",
        evidence.diagnostics
    );
    assert!(!result.full_verification_obligation_evidence()[0].has_accepted_proof());
}

/// The controls: an exact-attested row against the same invalid bundle, and an
/// unattested row against a valid one, both reach the engine.
#[cfg(not(feature = "trust-build"))]
#[test]
fn native_trust_mc_still_dispatches_when_an_outcome_could_publish() {
    let (result, dispatched) =
        run_recording_native_trust_mc(true, &invalid_native_trust_ir_mc_bundle());
    assert_eq!(dispatched.len(), 1, "exact-attested row must dispatch");
    assert_eq!(result.summary.proved, 0, "an invalid bundle still never proves: {result:#?}");
    assert!(
        result.evidence[0].diagnostics.iter().all(|d| !d.contains(NATIVE_TRUST_MC_SKIP_DIAGNOSTIC))
    );

    let (_result, dispatched) = run_recording_native_trust_mc(false, &native_trust_ir_mc_bundle());
    assert_eq!(dispatched.len(), 1, "a valid bundle must dispatch");
}
