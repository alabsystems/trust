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
#[cfg(not(feature = "trust-build"))]
use trust_wp::TrustWpVerificationEngine;

use super::*;

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
            value: serde_json::to_string(&public_predicate)
                .expect("direct public predicate serializes canonically"),
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
    // Reuse the exact same public context so both independent executions
    // intentionally publish byte-identical result envelopes.
    let context = VerifierExecutionContext::new("direct-trust-vc-cross-dispatch");
    let first = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &bundle,
        &bundle.obligations,
        None,
        &context,
    );
    // The public batch diagnostic includes measured elapsed milliseconds. Run
    // a few independent calls until that diagnostic also matches, so this
    // regression genuinely exercises byte-identical public carriers rather
    // than obtaining rejection from an incidental timing difference.
    let second = (0..64)
        .find_map(|_| {
            let candidate = engine
                .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                    &bundle,
                    &bundle.obligations,
                    None,
                    &context,
                );
            (candidate.result() == first.result()).then_some(candidate)
        })
        .expect("fixture must produce a byte-identical independent public run");
    let (first_run, mut first_live_receipts) = first.into_parts();
    let (second_run, second_live_receipts) = second.into_parts();
    let mut first_receipts = first_live_receipts.take_direct_trust_vc_receipts();
    assert_eq!(first_run, second_run, "fixture must exercise equal public bytes");
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
        "byte-identical public runs must retain distinct private dispatch identities",
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
        &bundle, &duplicate, None, &context,
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
    #[cfg(all(not(feature = "trust-build"), not(feature = "trust-vc-native")))]
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("requires native trust-wp, trust-vc, trust-mc, and TY engines")
            && diagnostic.contains("missing: trust-wp, trust-vc")
    }));
    #[cfg(all(not(feature = "trust-build"), feature = "trust-vc-native"))]
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("requires native trust-wp, trust-vc, trust-mc, and TY engines")
            && diagnostic.ends_with("missing: trust-wp")
    }));
    #[cfg(feature = "trust-build")]
    assert!(
        result.evidence[0].diagnostics.iter().any(|diagnostic| diagnostic.contains("trust-wp"))
    );

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 1);
    assert_eq!(structured[0].primary_suite.as_deref(), Some("trust-wp"));
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
        (ObligationKind::Precondition, "trust-wp"),
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

// Trust (P1.2 precedent, extended to preconditions and E4/E5): a body-aware VC
// carrying the accepted typed formula envelope must be DISPATCHED to trust-mc for
// Postcondition (the `#[ensures]` VC), Precondition (the call-site
// `#[requires]` VC), LoopInvariant (E4 initiation/consecution), and Termination
// (E5 non-negative/strict-decrease). This route is both the engine dispatch and the
// expected-suite the native-TrustIr evidence validation compares against the
// compiler's recorded trust-mc proof unit. Payload-less kinds keep their
// per-kind routes (pinned by
// `required_native_engines_route_primary_obligation_families_fail_closed`).
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
fn payloadless_e4_e5_claims_remain_trust_wp_owned() {
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
            Some("trust-wp"),
            "payload-less {:?} claim must not acquire trust-mc authority",
            bundle.obligations[0].kind,
        );
    }
}

#[test]
fn partial_or_forged_e4_e5_formula_envelopes_remain_trust_wp_owned() {
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
            Some("trust-wp"),
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
            Some("trust-wp"),
            "malformed {:?} formula metadata must not change ownership",
            bundle.obligations[0].kind,
        );
    }
}

#[cfg(not(feature = "trust-build"))]
#[test]
fn full_verifier_keeps_typed_trust_wp_lowering_fail_closed_without_aggregate_gate() {
    // Isolate the optional trust-wp adapter's own fail-closed behavior from
    // the composite all-required-engine availability gate.
    let engine = FullVerificationEngine::new(
        vec![Box::new(TrustWpVerificationEngine::new())],
        route_only_policy(),
    );
    let bundle = bundle_with_typed_trust_wp_postcondition();
    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-trust-wp-native"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert!(!result.is_fully_proved());
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("local typed TrustWpPureExprV1 replay")
            && diagnostic.contains("trust_wp.verify-bundle.aggregate-native-replay-gate.v1")
    }));
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("primary owner trust-wp")
            && diagnostic.contains("produced rejected evidence")
    }));
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_accepts_typed_trust_wp_lowering_with_aggregate_gate() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle_with_typed_trust_wp_postcondition();
    let mut native_bundle = native_trust_ir_mc_wp_bundle();
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(2),
        &bundle,
        0,
    );
    for key in TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS {
        assert!(
            !bundle.obligations[0].metadata.iter().any(|entry| entry.key == key),
            "trust-wp native metadata key `{key}` must be generated from the native bundle, not pre-attached public metadata"
        );
    }
    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-trust-wp-native"),
    );

    assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.proved, 1);
    assert_eq!(result.summary.unsupported, 0);
    assert!(result.is_fully_proved());
    assert_eq!(result.evidence[0].status, EvidenceStatus::Proved);
    assert!(result.evidence[0].proof_strength.is_some());
    assert!(result.evidence[0].satisfies_proof_artifact_policy());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("NativeTrustWpBundleVerifier aggregate VerifyBundleResult")
    }));
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr native request identity accepted")
            && diagnostic.contains("suite=trust-wp")
            && diagnostic.contains("request_id=2")
            && diagnostic.contains("proof_obligation_id=2")
    }));
    assert!(result.full_verification_obligation_evidence()[0].has_accepted_proof());
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_rejects_native_trust_wp_claim_for_different_public_predicate() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut bundle = bundle_with_typed_trust_wp_postcondition();
    bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: "TrustWpPureExprV1".to_string(),
        value: serde_json::json!({
            "kind": "bool",
            "value": false,
        }),
    };
    let mut native_bundle = native_trust_ir_mc_wp_bundle();
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(2),
        &bundle,
        0,
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-trust-wp-native-public-claim-substitution"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("public/native claim semantic mismatch")
            && diagnostic.contains("public=sha256:")
            && diagnostic.contains("native=sha256:")
    }));
    assert!(!result.full_verification_obligation_evidence()[0].has_accepted_proof());
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_rejects_trust_wp_metadata_only_when_native_request_is_missing() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut bundle = bundle_with_typed_trust_wp_postcondition();
    let mut original_native_bundle = native_trust_ir_mc_wp_bundle();
    bind_native_obligation_to_public_claim(
        &mut original_native_bundle,
        trust_ir::ProofId::new(2),
        &bundle,
        0,
    );
    let mut native_bundle_without_trust_wp = original_native_bundle.clone();
    native_bundle_without_trust_wp
        .requests
        .retain(|request| request.verifier_suite() != trust_ir::NativeVerifierSuite::TrustWp);
    attach_trust_wp_native_replay_metadata(
        &mut bundle,
        &original_native_bundle,
        0,
        trust_ir::ProofId::new(2),
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle_without_trust_wp,
        &VerifierExecutionContext::new("run-trust-wp-metadata-only"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].artifacts.is_empty());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("trust-wp native TrustIr bundle evidence rejected")
            && (diagnostic.contains("missing matching trust_wp native TrustIr request")
                || diagnostic.contains("NativeVerificationBundle validation failed"))
    }));
}

#[cfg(feature = "trust-build")]
#[test]
fn full_verifier_rejects_trust_wp_mismatched_native_request_identity() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut bundle = bundle_with_typed_trust_wp_postcondition();
    let mut native_bundle = native_trust_ir_mc_wp_bundle();
    bind_native_obligation_to_public_claim(
        &mut native_bundle,
        trust_ir::ProofId::new(2),
        &bundle,
        0,
    );
    let request_id = bundle.obligations[0]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
        .expect("test obligation has TrustIr request metadata");
    request_id.value = "99".to_string();

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-trust-wp-mismatch"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(result.evidence[0].proof_strength.is_none());
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("native request metadata `99`")
            && diagnostic
                .contains("canonical obligation id `trust_ir-native-trust-wp-request-2-proof-2`")
            && diagnostic.contains("request `2`")
    }));
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
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
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

fn bundle_with_temporal_model(single_writer: bool) -> TrustContractBundle {
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
    let bundle = bundle_with_temporal_model(true);
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
    let bundle = bundle_with_temporal_model(false);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-ty-refute"));

    assert_ne!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.failed, 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Failed);
    assert!(result.evidence[0].counterexample.is_some());
}

#[test]
fn bounded_required_strength_is_rejected_in_full_mode() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::proving(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
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
            "public_obligation_id": public_obligation_id,
        })
        .to_string(),
        smtlib: None,
        sort: None,
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

/// Admission-valid native fixture for router tests that do not exercise proof
/// authority. Request zero deliberately reserves the former TrustVc position
/// with a pending TrustMc obligation, so the long-standing TrustMc/TrustWp
/// request identities (1 and 2) remain stable without forging a TrustVc proof.
fn native_trust_ir_mc_wp_bundle() -> NativeVerificationBundle {
    let mut module = trust_ir::Module::new("router_native_trust_ir_bundle");
    let source_file = module.intern_file("router_native_fixture.rs");
    let function_id = trust_ir::FuncId::new(0);
    let func_ty = module.add_func_type(trust_ir::FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    });
    let entry = trust_ir::BlockId::new(0);
    let mut function = trust_ir::Function::new(function_id, "checked_transfer", func_ty, entry)
        .with_producer(trust_ir::Producer::TrustIr);
    let mut block = trust_ir::Block::new(entry);
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    module.add_function(function);
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
            "trust-wp postcondition request",
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
        trust_ir::NativeVerifierSuite::TrustWp,
        trust_ir::ProofId::new(2),
        trust_wp_true_replay_formula(),
    );
    rebind_native_bundle_module_digest(&mut bundle);
    bundle.validate().expect("native TrustMc/TrustWp fixture remains valid after replay formulas");
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

    let mut module = trust_ir::Module::new("router_kernel_certified_three_suite_bundle");
    let source_file = module.intern_file("router_kernel_fixture.rs");
    let function_id = trust_ir::FuncId::new(0);
    let func_ty = module.add_func_type(trust_ir::FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    });
    let entry = trust_ir::BlockId::new(0);
    let mut function = trust_ir::Function::new(function_id, "checked_transfer", func_ty, entry)
        .with_producer(trust_ir::Producer::TrustIr);
    let mut block = trust_ir::Block::new(entry);
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    module.add_function(function);

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
            "independent trust-wp request",
        )
        .with_formula(trust_wp_true_replay_formula())
        .with_function(function_id)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(2),
            "trust_ir-native-trust-wp-request-2-proof-2",
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
            .expect("kernel-certified three-suite native bundle builds");
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
fn kernel_certified_postcondition_is_credited_only_through_typed_trust_vc_import() {
    let (bundle, native_bundle) = kernel_certified_postcondition_fixture();
    let result = kernel_certified_trust_vc_full_engine().verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-kernel-certified-postcondition"),
    );

    assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
    assert_eq!(result.summary.requested_obligations, 1, "{result:#?}");
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert_eq!(
        result.evidence[0].proof_strength,
        Some(ProofStrength::certified(ReasoningKind::Deductive)),
        "a contract-frame certificate is deductive, not ownership analysis"
    );
    assert!(result.evidence[0].artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::ProofCertificate
            && artifact.uri.starts_with(TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX)
            && artifact.materialization.is_some()
    }));
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("native trust_vc TrustIr proof certificate import accepted")
    }));
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
    assert!(
        result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("exact typed TrustContractBundle request")
                || diagnostic.contains("did not produce proved evidence")
                || diagnostic.contains(
                    "did not carry an exact compiler-deferred direct TrustVC receipt input",
                )
        }),
        "{result:#?}"
    );
}

#[cfg(feature = "trust-build")]
#[test]
fn kernel_certified_contract_routing_requires_exact_unique_suite_declaration() {
    let (bundle, _) = kernel_certified_postcondition_fixture();
    let obligation = &bundle.obligations[0];
    assert_eq!(
        super::routing::obligation_route(obligation)
            .expect("postcondition has a route")
            .primary
            .name(),
        "trust-vc"
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
            "trust-wp",
            "missing, mismatched, or non-canonical suite declarations retain the default owner"
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
        "trust-wp",
        "even agreeing duplicate declarations are ambiguous"
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
    assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("public typed contract formula differs")
            || diagnostic.contains("semantic")
    }));
}

/// Adversarial variant used only to prove that router admission fails before
/// child evidence can launder an opaque TrustVc certificate into authority.
fn native_trust_ir_unreplayed_trust_vc_bundle() -> NativeVerificationBundle {
    let mut bundle = native_trust_ir_mc_wp_bundle();
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

    let mut module = mb.build();
    let source_file = module.intern_file("router_native_fixture.rs");
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
        options: {
            let mut options = trust_ir::TrustMcRequestOptions::default();
            options.chc.emit_horn_clauses = true;
            options
        },
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

#[cfg(feature = "trust-build")]
fn attach_trust_wp_native_replay_metadata(
    bundle: &mut TrustContractBundle,
    native_bundle: &NativeVerificationBundle,
    obligation_index: usize,
    proof_obligation_id: trust_ir::ProofId,
) {
    let request = native_bundle
        .requests
        .iter()
        .find(|request| {
            request.verifier_suite() == trust_ir::NativeVerifierSuite::TrustWp
                && request.obligations().contains(&proof_obligation_id)
        })
        .expect("native bundle contains requested trust_wp obligation");
    let metadata = trust_wp_native_replay_metadata_entries_for_request(
        native_bundle,
        request,
        proof_obligation_id,
    )
    .expect("trust-wp native replay metadata is built through controlled trust_wp API");
    bundle.obligations[obligation_index].metadata.extend(metadata);
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
        let mut manifest = EngineManifest::new("trust-wp", "conflict-test", EngineKind::Deductive);
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
                    proof_strength: Some(ProofStrength::deductive()),
                    artifacts: exact_fixture_artifacts_for_engine(
                        "trust-wp",
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
                evidence_id: format!("trust-wp:batch:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Proved,
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
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
                calls.clone(),
            )),
        ],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-batch-order",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        native_trust_ir_obligation(
            "trust-wp",
            2,
            2,
            ObligationKind::Postcondition,
            Some(ProofStrength::deductive()),
        ),
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
    assert_eq!(called_engines, vec!["trust-mc".to_string(), "trust-wp".to_string()]);
    let evidence_ids =
        result.evidence.iter().map(|item| item.obligation_id.as_str()).collect::<Vec<_>>();
    assert_eq!(
        evidence_ids,
        vec![
            "trust_ir-native-trust-wp-request-2-proof-2",
            "trust_ir-native-trust-mc-request-1-proof-1"
        ]
    );
}

#[test]
fn full_verifier_runs_independent_primary_batches_in_parallel_when_worker_threads_allow() {
    let active_calls = Arc::new(AtomicUsize::new(0));
    let max_active_calls = Arc::new(AtomicUsize::new(0));
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(SlowRecordingEngine::new(
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
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
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-parallel-batches",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        native_trust_ir_obligation(
            "trust-wp",
            2,
            2,
            ObligationKind::Postcondition,
            Some(ProofStrength::deductive()),
        ),
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
        vec![
            "trust_ir-native-trust-wp-request-2-proof-2",
            "trust_ir-native-trust-mc-request-1-proof-1"
        ]
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
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
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
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-serial-batches",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![
        native_trust_ir_obligation(
            "trust-wp",
            2,
            2,
            ObligationKind::Postcondition,
            Some(ProofStrength::deductive()),
        ),
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
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength { reasoning: ReasoningKind::Deductive, assurance: AssuranceLevel::Sound },
        ))],
        route_only_policy(),
    );
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-wp-publication-grade",
        BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
    );
    bundle.obligations = vec![native_trust_ir_obligation(
        "trust-wp",
        2,
        2,
        ObligationKind::Postcondition,
        Some(ProofStrength::deductive()),
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
            .any(|diagnostic| diagnostic.contains("primary owner trust-wp"))
    );
}

#[test]
fn proof_grade_without_replay_check_metadata_fails_full_mode() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength::deductive()),
                artifacts: Vec::new(),
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
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
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
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
fn native_trust_ir_bundle_identity_is_preserved_for_trust_mc_and_trust_wp() {
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::new(
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
            )),
            Box::new(UnitEngine::new(
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                SupportLevel::Preferred,
                UnitEvidenceMode::Evidence {
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(ProofStrength::deductive()),
                    artifacts: vec![
                        solver_transcript_artifact("trust-wp-native-transcript"),
                        proof_check_artifact("trust-wp-proof-check"),
                    ],
                    diagnostics: Vec::new(),
                },
            )),
        ],
        route_only_policy(),
    );
    let mut bundle = TrustContractBundle::empty(
        "bundle-native-trust-ir",
        BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::checked_transfer".to_string(),
        },
    );
    bundle.obligations = vec![
        native_trust_ir_obligation("trust-mc", 1, 1, ObligationKind::ArithmeticSafety, None),
        native_trust_ir_obligation(
            "trust-wp",
            2,
            2,
            ObligationKind::Postcondition,
            Some(ProofStrength::deductive()),
        ),
    ];

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("run-native-trust-ir-mc-wp"),
    );

    assert_eq!(result.status, VerificationRunStatus::Proved);
    assert_eq!(result.summary.proved, 2);
    assert_eq!(result.summary.missing_proof_artifacts, 0);

    for (suite, request_id, proof_id) in [("trust-mc", 1, 1), ("trust-wp", 2, 2)] {
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
    assert_eq!(manifest.accepted_evidence.len(), 2);
    assert!(manifest.rejected_evidence.is_empty());
    assert!(manifest.artifacts.iter().any(|artifact| {
        artifact.uri.starts_with("trust_ir-native://verification-bundle/")
            && artifact.uri.contains("/trust-mc/request/1/")
            && artifact.uri.contains("/proof/1/")
    }));
    assert!(manifest.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr NativeVerificationBundle indexed")
            && diagnostic.contains("requests=3")
    }));

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 2);
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
    let native_bundle = native_trust_ir_mc_wp_bundle();
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength::deductive()),
                artifacts: vec![
                    solver_transcript_artifact("trust-wp-transcript"),
                    proof_check_artifact("trust-wp-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

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
    assert_eq!(native_trust_ir.expected_suite, "trust-wp");
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
            } if obligation_id == "obligation-ensures" && expected_suite == "trust-wp"
        )
    }));
}

#[test]
fn proved_evidence_with_native_trust_ir_identity_requires_native_bundle() {
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength::deductive()),
                artifacts: vec![
                    solver_transcript_artifact("trust-wp-transcript"),
                    proof_check_artifact("trust-wp-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    bundle.obligations[0] =
        native_trust_ir_obligation("trust-wp", 2, 2, ObligationKind::Postcondition, None);

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
    assert_eq!(native_trust_ir.expected_suite, "trust-wp");
    assert_eq!(native_trust_ir.request_id, Some(2));
    assert_eq!(native_trust_ir.proof_obligation_id, Some(2));
    assert!(!native_trust_ir.has_matching_artifacts());
    assert!(structured[0].blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch {
                obligation_id,
                expected_suite,
                request_id: Some(2),
                proof_obligation_id: Some(2),
                ..
            } if obligation_id == "trust_ir-native-trust-wp-request-2-proof-2"
                && expected_suite == "trust-wp"
        )
    }));
}

#[test]
fn native_trust_ir_mode_rejects_proved_evidence_when_bundle_validation_fails() {
    let mut native_bundle = native_trust_ir_mc_wp_bundle();
    native_bundle.requests.clear();
    let engine = FullVerificationEngine::new(
        vec![Box::new(UnitEngine::new(
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            SupportLevel::Preferred,
            UnitEvidenceMode::Evidence {
                status: EvidenceStatus::Proved,
                proof_strength: Some(ProofStrength::deductive()),
                artifacts: vec![
                    solver_transcript_artifact("trust-wp-transcript"),
                    proof_check_artifact("trust-wp-proof-check"),
                ],
                diagnostics: Vec::new(),
            },
        ))],
        route_only_policy(),
    );
    let mut bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    bundle.obligations[0] =
        native_trust_ir_obligation("trust-wp", 2, 2, ObligationKind::Postcondition, None);

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
fn trust_wp_and_trust_vc_require_suite_native_replay_check_artifacts() {
    for (run_id, engine_name, engine_kind, obligation_kind, proof_strength) in [
        (
            "run-trust-wp-transcript-only",
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            ProofStrength::deductive(),
        ),
        (
            "run-trust-vc-transcript-only",
            "trust-vc",
            EngineKind::Deductive,
            ObligationKind::MemorySafety,
            ProofStrength {
                reasoning: ReasoningKind::OwnershipAnalysis,
                assurance: AssuranceLevel::Sound,
            },
        ),
    ] {
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
                reasoning: ReasoningKind::Deductive,
                assurance: AssuranceLevel::Unchecked,
            },
        ),
        (
            "run-runtime",
            ProofStrength {
                reasoning: ReasoningKind::RuntimeMonitoring,
                assurance: AssuranceLevel::RuntimeObserved,
            },
        ),
    ] {
        let engine = FullVerificationEngine::new(
            vec![Box::new(UnitEngine::new(
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
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
        let bundle = bundle_with_postcondition(None);
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
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-4"));

    assert_eq!(result.status, trust_verifier_api::VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.requested_obligations, 1);
    assert_eq!(result.summary.unsupported, 1);
    assert_eq!(result.summary.skipped, 0);
    assert!(
        result.evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("primary owner trust-wp is required"))
    );
}

#[test]
fn missing_primary_evidence_fails_without_skipping_obligation() {
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(UnitEngine::new(
                "trust-wp",
                EngineKind::Deductive,
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
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
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
            "trust-wp",
            EngineKind::Deductive,
            ObligationKind::Postcondition,
            SupportLevel::Unsupported { reason: "native lowering missing".to_string() },
            UnitEvidenceMode::Empty,
        ))],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));
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
            .any(|diagnostic| diagnostic.contains("primary owner trust-wp@0.1.0 rejected"))
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
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
            )),
            Box::new(UnitEngine::proving(
                "trust-wp",
                EngineKind::Deductive,
                ObligationKind::Postcondition,
                ProofStrength::deductive(),
            )),
        ],
        route_only_policy(),
    );
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

    let support = engine.supports(&bundle.obligations[0]);
    let result = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("run-duplicate"));

    assert!(matches!(
        support,
        SupportLevel::Unsupported { reason }
            if reason.contains("ambiguous duplicate primary engines: trust-wp")
    ));
    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert_eq!(result.summary.proved, 0);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("ambiguous duplicate primary engines: trust-wp")
    }));
}

#[test]
fn invalid_primary_manifest_is_rejected_before_dispatch() {
    let mut invalid = UnitEngine::proving(
        "trust-wp",
        EngineKind::Deductive,
        ObligationKind::Postcondition,
        ProofStrength::deductive(),
    );
    invalid.manifest.api_version = "forged-future-api".to_string();
    let engine = FullVerificationEngine::new(vec![Box::new(invalid)], route_only_policy());
    let bundle = bundle_with_postcondition(Some(ProofStrength::deductive()));

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
