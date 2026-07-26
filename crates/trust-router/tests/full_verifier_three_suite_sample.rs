#![cfg_attr(not(feature = "trust-build"), allow(dead_code, unused_imports))]

use serde_json::json;
use trust_bmc::{
    ChcPdrProofEvidence, ChcPdrProofKind, ChcPdrStats, FullProofEvidence, FullVerificationVerdict,
    MirDerivedChcPdrObligation, MirObligationKind,
    trust_mc_full_verification_verdict_metadata_entry,
};
use trust_ir_bridge::{
    NativeVerificationBundle, ProofDigest, TRUST_OBLIGATION_SOURCE_SCHEMA,
    native_verification_bundle_from_module,
};
use trust_router::full_verification::{
    FullVerificationEvidenceBlocker, FullVerificationRunResultExt, NativeTrustMcTrustIrEngine,
    TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS, TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
    trust_wp_native_replay_metadata_entries_for_request,
};
use trust_router::{FullVerificationEngine, FullVerificationPolicy, NativeTyEngine};
#[cfg(not(feature = "trust-build"))]
use trust_vc_bridge::{
    TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED, TRUST_VC_TYPED_OBLIGATION_REQUIRED,
};
use trust_vc_bridge::{
    TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION, TRUST_VC_TYPED_PROOF_INPUT_REQUIRED,
    TrustVcVerificationEngine, trust_vc_typed_proof_metadata,
};
#[cfg(not(feature = "trust-build"))]
use trust_verifier_api::VerificationEngine;
use trust_verifier_api::{
    BundleSubject, ContractKind, ContractPredicate, EvidenceDisposition, EvidenceStatus,
    MetadataEntry, ObligationEvidence, ObligationKind, ProofStrength, SourceLocation, TrustContract,
    TrustContractBundle, TrustObligation, VerificationRunStatus, VerifierExecutionContext,
};
use trust_wp::TrustWpVerificationEngine;

const TRUST_WP_OBLIGATION_ID: &str = "sample::trust-wp-postcondition";
const TRUST_MC_OBLIGATION_ID: &str = "sample::trust-mc-arithmetic-safety";
const TRUST_VC_OBLIGATION_ID: &str = "sample::trust-vc-ownership";
const THREE_SUITE_SAMPLE_MODE_ENV: &str = "TRUST_FULL_VERIFIER_THREE_SUITE_MODE";
const REQUIRED_NATIVE_SUITES_MODE: &str = "required-native-suites";

#[test]
#[cfg(feature = "trust-build")]
fn sample_bundle_exercises_trust_mc_trust_wp_and_trust_vc_full_verifier_routes() {
    let bundle = sample_three_suite_bundle();
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTrustMcTrustIrEngine::new()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("sample-three-suite"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.evidence_count, 3);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 3, "{result:#?}");
    assert_eq!(result.summary.missing_proof_artifacts, 0, "{result:#?}");
    assert_eq!(result.summary.skipped, 0);

    let trust_mc = evidence_for(&result.evidence, TRUST_MC_OBLIGATION_ID);
    assert_trust_mc_serialized_metadata_fails_closed(trust_mc);

    let trust_vc = evidence_for(&result.evidence, TRUST_VC_OBLIGATION_ID);
    assert_eq!(trust_vc.status, EvidenceStatus::Unsupported, "{trust_vc:#?}");
    assert!(trust_vc.proof_strength.is_none());
    assert!(trust_vc.artifacts.is_empty());
    assert!(
        trust_vc.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_VC_TYPED_PROOF_INPUT_REQUIRED)
                && diagnostic.contains("typed ownership/borrow context")
        }),
        "{trust_vc:#?}"
    );

    let trust_wp = evidence_for(&result.evidence, TRUST_WP_OBLIGATION_ID);
    assert_eq!(trust_wp.status, EvidenceStatus::Unsupported);
    assert_eq!(trust_wp.engine.name, "trust-full-verifier");
    assert!(trust_wp.proof_strength.is_none());
    assert_trust_wp_missing_native_metadata_rejection(trust_wp);

    let manifest = result.to_manifest();
    assert!(manifest.accepted_evidence.is_empty());
    assert_eq!(manifest.rejected_evidence.len(), 3);
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_WP_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedStatus
    }));
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_MC_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedStatus
    }));
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_VC_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedStatus
    }));

    let structured = result.full_verification_obligation_evidence();
    let trust_mc_structured = structured
        .iter()
        .find(|obligation| obligation.obligation_id == TRUST_MC_OBLIGATION_ID)
        .expect("structured trust_mc obligation evidence");
    assert_eq!(trust_mc_structured.primary_suite.as_deref(), Some("trust-mc"));
    assert!(!trust_mc_structured.has_accepted_proof());
    assert!(trust_mc_structured.blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id, .. }
                if obligation_id == TRUST_MC_OBLIGATION_ID
        )
    }));
    let trust_vc_structured = structured
        .iter()
        .find(|obligation| obligation.obligation_id == TRUST_VC_OBLIGATION_ID)
        .expect("structured trust_vc obligation evidence");
    assert!(!trust_vc_structured.has_accepted_proof());
    assert!(trust_vc_structured.blockers.iter().any(|blocker| {
        matches!(
            blocker,
            FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id, .. }
                if obligation_id == TRUST_VC_OBLIGATION_ID
        )
    }));
}

#[test]
#[cfg(feature = "trust-build")]
fn sample_bundle_without_native_bundle_rejects_unbound_proof_claims() {
    let (bundle, _native_bundle) = sample_three_suite_with_native_mc_wp_bundle();
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTrustMcTrustIrEngine::new()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("sample-three-suite-proved"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.evidence_count, 3);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 2, "{result:#?}");
    assert_eq!(result.summary.missing_proof_artifacts, 1, "{result:#?}");

    let trust_wp = evidence_for(&result.evidence, TRUST_WP_OBLIGATION_ID);
    assert_rejected_missing_native_bundle_proof(trust_wp, "trust-wp");
    let trust_mc = evidence_for(&result.evidence, TRUST_MC_OBLIGATION_ID);
    assert_trust_mc_serialized_metadata_fails_closed(trust_mc);

    assert_missing_native_bundle_rejection(trust_wp, "trust-wp");
    let trust_vc = evidence_for(&result.evidence, TRUST_VC_OBLIGATION_ID);
    assert_trust_vc_fail_closed(trust_vc);

    let manifest = result.to_manifest();
    assert!(manifest.accepted_evidence.is_empty());
    assert_eq!(manifest.rejected_evidence.len(), 3);
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_WP_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedMissingProofArtifacts
    }));
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_VC_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedStatus
    }));
    assert!(manifest.rejected_evidence.iter().any(|decision| {
        decision.obligation_id == TRUST_MC_OBLIGATION_ID
            && decision.disposition == EvidenceDisposition::RejectedStatus
    }));
}

#[test]
#[cfg(feature = "trust-build")]
fn sample_bundle_uses_native_trust_ir_bundle_when_public_trust_wp_replay_metadata_is_absent() {
    let (mut bundle, native_bundle) = sample_three_suite_with_native_mc_wp_bundle();
    remove_trust_wp_native_replay_metadata(&mut bundle);
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTrustMcTrustIrEngine::new()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("sample-three-suite-missing-trust-wp-native-metadata"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert_eq!(result.summary.unsupported, 2);
    assert_eq!(result.summary.missing_proof_artifacts, 0);

    assert_suite_accepted(&result.evidence, TRUST_WP_OBLIGATION_ID, "trust-wp");
    assert_trust_mc_native_bundle_authority_unavailable(evidence_for(
        &result.evidence,
        TRUST_MC_OBLIGATION_ID,
    ));
    assert_native_trust_vc_request_unavailable(evidence_for(
        &result.evidence,
        TRUST_VC_OBLIGATION_ID,
    ));
    let trust_wp = evidence_for(&result.evidence, TRUST_WP_OBLIGATION_ID);
    assert_eq!(trust_wp.proof_strength, Some(ProofStrength::deductive()));
    assert!(trust_wp.satisfies_proof_artifact_policy());
    assert!(trust_wp.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr native request identity accepted")
            && diagnostic.contains("suite=trust-wp")
    }));
}

#[test]
#[cfg(feature = "trust-build")]
fn sample_bundle_uses_native_trust_ir_bundle_when_public_trust_wp_solver_metadata_is_tampered() {
    let (mut bundle, native_bundle) = sample_three_suite_with_native_mc_wp_bundle();
    tamper_trust_wp_native_solver_metadata(&mut bundle);
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTrustMcTrustIrEngine::new()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("sample-three-suite-tampered-trust-wp-native-metadata"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert_eq!(result.summary.unsupported, 2);
    assert_eq!(result.summary.missing_proof_artifacts, 0);

    assert_suite_accepted(&result.evidence, TRUST_WP_OBLIGATION_ID, "trust-wp");
    assert_trust_mc_native_bundle_authority_unavailable(evidence_for(
        &result.evidence,
        TRUST_MC_OBLIGATION_ID,
    ));
    assert_native_trust_vc_request_unavailable(evidence_for(
        &result.evidence,
        TRUST_VC_OBLIGATION_ID,
    ));
    let trust_wp = evidence_for(&result.evidence, TRUST_WP_OBLIGATION_ID);
    assert_eq!(trust_wp.proof_strength, Some(ProofStrength::deductive()));
    assert!(trust_wp.satisfies_proof_artifact_policy());
    assert!(!trust_wp.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("native_solvers") && diagnostic.contains("empty placeholder")
    }));
}

#[test]
#[cfg(feature = "trust-build")]
fn sample_bundle_required_suite_mode_rejects_missing_native_suite() {
    assert_deterministic_three_suite_mode();

    let (bundle, native_bundle) = sample_three_suite_with_native_mc_wp_bundle();
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("sample-three-suite-missing-trust-mc"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.evidence_count, 3);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 3);
    assert_eq!(result.summary.skipped, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 0);
    for evidence in &result.evidence {
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.proof_strength.is_none());
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("requires native trust-wp, trust-vc, trust-mc, and TY engines")
                && diagnostic.contains("missing: trust-mc")
        }));
    }

    let manifest = result.to_manifest();
    assert!(manifest.accepted_evidence.is_empty());
    assert_eq!(manifest.rejected_evidence.len(), 3);
    assert!(
        manifest
            .rejected_evidence
            .iter()
            .all(|decision| { decision.disposition == EvidenceDisposition::RejectedStatus })
    );
    assert!(manifest.skipped.is_empty());
}

#[test]
#[cfg(feature = "trust-build")]
// The sample is an honest 1/3 result: only trust-wp supplies same-run
// materialized native proof evidence. trust-mc and trust-vc are BOTH native-
// authority debt. The b62 "reject unreplayed native proof authority" hardening
// makes NativeTrustMcTrustIrEngine refuse the sample's serialized
// FullVerificationVerdict metadata as diagnostic-only (it requires a live opaque
// native-bundle CHC/PDR authority the synthetic sample does not carry), and
// trust-vc still lacks a replay-authorized TrustVc request. Both remain rejected
// until real native authority lands. The trust-router native-acceptance path is
// itself healthy — this is a fixture/authority gap, not an engine regression.
fn sample_bundle_records_trust_vc_memory_bridge_debt() {
    assert_deterministic_three_suite_mode();

    let (bundle, native_bundle) = sample_three_suite_with_native_mc_wp_bundle();
    let engine = FullVerificationEngine::new(
        vec![
            Box::new(TrustWpVerificationEngine::new()),
            Box::new(trust_vc_engine()),
            Box::new(NativeTrustMcTrustIrEngine::new()),
            Box::new(NativeTyEngine::new()),
        ],
        FullVerificationPolicy::default(),
    );

    let result = engine.verify_bundle_with_native_trust_ir_bundle(
        &bundle,
        &native_bundle,
        &VerifierExecutionContext::new("sample-three-suite-required-native-suites"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert!(!result.is_fully_proved());
    assert_eq!(result.summary.requested_obligations, 3);
    assert_eq!(result.summary.evidence_count, 3);
    assert_eq!(result.summary.proved, 1);
    assert_eq!(result.summary.unsupported, 2);
    assert_eq!(result.summary.skipped, 0);
    assert_eq!(result.summary.missing_proof_artifacts, 0);
    assert!(result.skipped.is_empty(), "full-verifier sample skipped at least one suite");

    assert_suite_accepted(&result.evidence, TRUST_WP_OBLIGATION_ID, "trust-wp");
    assert_trust_mc_native_bundle_authority_unavailable(evidence_for(
        &result.evidence,
        TRUST_MC_OBLIGATION_ID,
    ));
    assert_native_trust_vc_request_unavailable(evidence_for(
        &result.evidence,
        TRUST_VC_OBLIGATION_ID,
    ));

    let trust_wp = evidence_for(&result.evidence, TRUST_WP_OBLIGATION_ID);
    assert_eq!(trust_wp.proof_strength, Some(ProofStrength::deductive()));
    assert!(trust_wp.satisfies_proof_artifact_policy());
    assert!(trust_wp.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("NativeTrustWpBundleVerifier aggregate VerifyBundleResult")
    }));
    assert!(trust_wp.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("typed TrustIr native request identity accepted")
            && diagnostic.contains("suite=trust-wp")
            && diagnostic.contains("request_id=2")
            && diagnostic.contains("proof_obligation_id=2")
    }));

    let structured = result.full_verification_obligation_evidence();
    assert_eq!(structured.len(), 3);
    let trust_wp_structured = structured
        .iter()
        .find(|item| item.obligation_id == TRUST_WP_OBLIGATION_ID)
        .expect("missing structured evidence for trust-wp");
    assert!(trust_wp_structured.has_accepted_proof(), "trust-wp was not accepted");
    assert!(
        trust_wp_structured.blockers.is_empty(),
        "trust-wp had unexpected full-verifier blockers: {:?}",
        trust_wp_structured.blockers
    );
    let native_trust_ir =
        trust_wp_structured.native_trust_ir.as_ref().expect("native TrustIr evidence");
    assert!(
        native_trust_ir.has_matching_artifacts(),
        "trust-wp was not bound to native TrustIr request/proof artifacts"
    );
    for obligation_id in [TRUST_MC_OBLIGATION_ID, TRUST_VC_OBLIGATION_ID] {
        let item = structured
            .iter()
            .find(|item| item.obligation_id == obligation_id)
            .unwrap_or_else(|| panic!("missing structured evidence for {obligation_id}"));
        assert!(!item.has_accepted_proof(), "{obligation_id} was unexpectedly accepted");
        assert!(
            item.blockers.iter().any(|blocker| {
                matches!(
                    blocker,
                    FullVerificationEvidenceBlocker::UnsupportedEvidence { obligation_id: blocked, .. }
                        if blocked == obligation_id
                )
            }),
            "{obligation_id} did not record an UnsupportedEvidence blocker: {:?}",
            item.blockers
        );
    }

    let manifest = result.to_manifest();
    assert_eq!(manifest.accepted_evidence.len(), 1);
    assert_eq!(manifest.rejected_evidence.len(), 2);
    assert!(manifest.skipped.is_empty());
    assert!(
        manifest
            .artifacts
            .iter()
            .any(|artifact| artifact.uri.starts_with("trust_ir-native://verification-bundle/")),
        "native TrustIr artifacts were not published in the full-verifier manifest"
    );
    assert!(
        manifest.accepted_evidence.iter().any(|decision| {
            decision.obligation_id == TRUST_WP_OBLIGATION_ID
                && decision.disposition == EvidenceDisposition::AcceptedProof
        }),
        "full-verifier manifest skipped accepted proof accounting for trust-wp"
    );
    for obligation_id in [TRUST_MC_OBLIGATION_ID, TRUST_VC_OBLIGATION_ID] {
        assert!(
            manifest.rejected_evidence.iter().any(|decision| {
                decision.obligation_id == obligation_id
                    && decision.disposition == EvidenceDisposition::RejectedStatus
            }),
            "full-verifier manifest skipped rejected accounting for {obligation_id}"
        );
    }
    write_required_suite_manifest_if_requested(&manifest);
}

#[cfg(feature = "trust-build")]
fn write_required_suite_manifest_if_requested(
    manifest: &trust_verifier_api::VerificationRunManifest,
) {
    let Some(path) = std::env::var_os("TRUST_THREE_SUITE_MANIFEST_OUT") else {
        return;
    };
    let bytes =
        serde_json::to_vec_pretty(manifest).expect("serialize validated three-suite manifest");
    let mut output =
        std::fs::OpenOptions::new().write(true).create_new(true).open(&path).unwrap_or_else(
            |error| {
                panic!(
                    "create new required native three-suite manifest at {}: {error}",
                    path.to_string_lossy()
                )
            },
        );
    std::io::Write::write_all(&mut output, &bytes).unwrap_or_else(|error| {
        panic!("write required native three-suite manifest to {}: {error}", path.to_string_lossy())
    });
}

#[test]
#[cfg(not(feature = "trust-build"))]
fn sample_trust_vc_lane_fails_closed_without_compiled_proof_unit_bridge() {
    let bundle = sample_three_suite_bundle();
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == TRUST_VC_OBLIGATION_ID)
        .expect("sample trust_vc obligation exists")
        .clone();
    let engine = trust_vc_engine();

    let evidence = engine.verify(&bundle, &[obligation]);

    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
    assert!(evidence[0].proof_strength.is_none());
    assert!(evidence[0].artifacts.is_empty());
    assert!(
        evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains(TRUST_VC_TYPED_PROOF_INPUT_REQUIRED))
    );
    assert!(
        evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains(TRUST_VC_TYPED_OBLIGATION_REQUIRED))
    );
    assert!(
        evidence[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
    );
}

fn sample_three_suite_bundle() -> TrustContractBundle {
    let mut bundle = TrustContractBundle::empty(
        "sample-full-verifier-three-suite",
        BundleSubject::Function {
            crate_name: "sample_full_verifier".to_string(),
            path: "sample_full_verifier::checked_transfer".to_string(),
        },
    );
    bundle.contracts.push(TrustContract {
        contract_id: "contract::trust-vc-memory-proof-unit".to_string(),
        kind: ContractKind::Asserts,
        predicate: ContractPredicate::MemoryIr {
            schema: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
            value: trust_vc_mir_memory_proof_unit_payload(),
        },
        source: SourceLocation::default(),
        metadata: Vec::new(),
    });
    bundle.contracts.push(TrustContract {
        contract_id: "contract::trust-wp-ensures-positive".to_string(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::CanonicalJson {
            schema: "TrustWpPureExprV1".to_string(),
            value: json!({
                "kind": "bool",
                "value": true,
            }),
        },
        source: SourceLocation::default(),
        metadata: Vec::new(),
    });
    bundle.obligations.push(trust_wp_postcondition_obligation());
    bundle.obligations.push(trust_mc_arithmetic_obligation());
    bundle.obligations.push(trust_vc_ownership_obligation());
    bundle
}

fn sample_three_suite_with_native_mc_wp_bundle() -> (TrustContractBundle, NativeVerificationBundle)
{
    let mut bundle = sample_three_suite_bundle();
    for obligation in &mut bundle.obligations {
        match obligation.obligation_id.as_str() {
            TRUST_VC_OBLIGATION_ID => {
                // Deliberately request the absent TrustVc identity. This proves
                // that public routing metadata cannot manufacture a native
                // request or proof authority when the admitted bundle contains
                // only TrustMc and TrustWp work.
                obligation.metadata.extend(native_trust_ir_metadata("trust-vc", 0, 0));
            }
            TRUST_MC_OBLIGATION_ID => {
                obligation.metadata.extend(native_trust_ir_metadata("trust-mc", 1, 1));
                add_trust_mc_public_typed_chc_binding_metadata(
                    obligation,
                    "trust_ir-native-trust_mc-request-1-proof-1",
                );
            }
            TRUST_WP_OBLIGATION_ID => {
                obligation.metadata.extend(native_trust_ir_metadata("trust-wp", 2, 2));
            }
            _ => {}
        }
    }
    // The native source identity is an authenticated binding to the canonical
    // public claim, so build it only after every semantic public metadata entry
    // has been attached. Replay/import transport metadata added below is
    // deliberately excluded from that digest.
    let native_bundle = sample_native_verification_bundle(&bundle);
    attach_trust_wp_native_replay_metadata(&mut bundle, &native_bundle);
    (bundle, native_bundle)
}

fn sample_native_verification_bundle(
    public_bundle: &TrustContractBundle,
) -> NativeVerificationBundle {
    use trust_ir::inst::ICmpOp;
    use trust_ir::ty::Ty;
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("sample_full_verifier_three_suite_native");
    let func_ty = mb.add_func_type(vec![], vec![]);
    {
        let mut fb = mb.function("checked_transfer", func_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let zero = fb.iconst(Ty::I32, 0);
        let assertion = fb.icmp(ICmpOp::Eq, Ty::I32, zero, zero);
        fb.assert(assertion);
        fb.ret(vec![]);
        fb.build();
    }

    let mut module = mb.build();
    // The bridge fail-closes on unlabelled provenance (it cannot infer that an
    // unlabelled function came from the retained MIR path), so declare what is
    // true by construction here: this module comes from the native TrustIr
    // builder pipeline. Mirrors native_request.rs's own fixtures.
    for function in &mut module.functions {
        function.producer = Some(trust_ir::Producer::TrustIr);
    }
    let function_id = module
        .functions
        .iter()
        .find(|function| function.name == "checked_transfer")
        .expect("sample native TrustIr fixture includes checked_transfer")
        .id;
    let source_file = module.intern_file("sample_full_verifier.rs");
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            "request-id reservation without proof-authority claim",
        )
        .with_formula(native_obligation_source_formula(trust_ir::ProofId::new(0), 100))
        .with_function(function_id)
        .with_source(native_obligation_source_identity(
            trust_ir::ProofId::new(0),
            "sample::native-trust-mc-request-reservation",
            source_file,
            100,
            native_trust_ir_digest(0xB0),
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(1),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            "trust-mc arithmetic-safety request",
        )
        .with_formula(native_obligation_source_formula(trust_ir::ProofId::new(1), 101))
        .with_function(function_id)
        .with_source(native_obligation_source_identity(
            trust_ir::ProofId::new(1),
            TRUST_MC_OBLIGATION_ID,
            source_file,
            101,
            canonical_public_obligation_digest(public_bundle, TRUST_MC_OBLIGATION_ID),
        )),
    );
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(2),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "trust-wp postcondition request",
        )
        .with_formula(native_obligation_source_formula(trust_ir::ProofId::new(2), 102))
        .with_function(function_id)
        .with_source(native_obligation_source_identity(
            trust_ir::ProofId::new(2),
            TRUST_WP_OBLIGATION_ID,
            source_file,
            102,
            canonical_public_obligation_digest(public_bundle, TRUST_WP_OBLIGATION_ID),
        )),
    );
    let mut bundle =
        native_verification_bundle_from_module(module, native_trust_ir_digest(0xA1), function_id)
            .expect("sample native TrustIr verification bundle builds");
    replace_native_proof_obligation_formula(
        &mut bundle,
        trust_ir::ProofId::new(1),
        trust_ir::ProofFormula::smtlib2("true", "Bool"),
    );
    replace_native_proof_obligation_formula(
        &mut bundle,
        trust_ir::ProofId::new(2),
        trust_wp_true_replay_formula(),
    );
    replace_native_replay_formula(
        &mut bundle,
        trust_ir::NativeVerifierSuite::TrustMc,
        trust_ir::ProofId::new(1),
        trust_ir::ProofFormula::smtlib2("true", "Bool"),
    );
    replace_native_replay_formula(
        &mut bundle,
        trust_ir::NativeVerifierSuite::TrustWp,
        trust_ir::ProofId::new(2),
        trust_wp_true_replay_formula(),
    );
    rebind_native_bundle_module_digest(&mut bundle);
    bundle
        .validate()
        .expect("sample native TrustMc/TrustWp bundle remains valid after replay formulas");
    bundle
}

fn canonical_public_obligation_digest(
    bundle: &TrustContractBundle,
    obligation_id: &str,
) -> ProofDigest {
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| obligation.obligation_id == obligation_id)
        .unwrap_or_else(|| panic!("sample public obligation `{obligation_id}` exists"));
    let digest = bundle
        .canonical_obligation_semantic_digest_sha256(obligation)
        .expect("sample public obligation has a canonical semantic digest");
    assert_eq!(digest.len(), 64, "canonical SHA-256 digest width");
    let mut bytes = [0_u8; 32];
    for (index, pair) in digest.as_bytes().chunks_exact(2).enumerate() {
        let nibble = |byte| match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            _ => panic!("canonical SHA-256 digest must use lowercase hex"),
        };
        bytes[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    ProofDigest::sha256(bytes)
}

fn native_obligation_source_formula(
    obligation: trust_ir::ProofId,
    line: u32,
) -> trust_ir::ProofFormula {
    let public_obligation_id = match obligation.index() {
        0 => "sample::native-trust-mc-request-reservation",
        1 => TRUST_MC_OBLIGATION_ID,
        2 => TRUST_WP_OBLIGATION_ID,
        index => panic!("unexpected sample native obligation id {index}"),
    };
    let assertion_id = format!("trust-assertion:{public_obligation_id}");
    trust_ir::ProofFormula {
        schema: TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
        payload: json!({
            "source_id": public_obligation_id,
            "assertion_id": assertion_id.clone(),
            "native_assertion_id": trust_types::stable_u32_id(assertion_id.as_bytes()),
            "span": {
                "file": "sample_full_verifier.rs",
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

fn native_obligation_source_identity(
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

fn trust_wp_true_replay_formula() -> trust_ir::ProofFormula {
    trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")
}

fn replace_native_replay_formula(
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
            trust_ir::NativeVerificationRequest::TrustVc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            trust_ir::NativeVerificationRequest::TrustMc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            trust_ir::NativeVerificationRequest::TrustWp(request) => {
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
    let Some(proof_obligation) =
        bundle.module.proof_obligations.iter_mut().find(|item| item.id == obligation)
    else {
        panic!("sample native TrustIr proof obligation {} exists", obligation.index());
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

fn native_trust_ir_digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
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
    let binding = json!({
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
        MetadataEntry { key: "trust.vc.formula.schema".to_string(), value: "smtlib2".to_string() },
        MetadataEntry { key: "trust.vc.formula.payload".to_string(), value: "true".to_string() },
        MetadataEntry { key: "trust.vc.formula.smtlib2".to_string(), value: "true".to_string() },
        MetadataEntry { key: "trust.vc.formula.sort".to_string(), value: "Bool".to_string() },
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

fn attach_trust_wp_native_replay_metadata(
    bundle: &mut TrustContractBundle,
    native_bundle: &NativeVerificationBundle,
) {
    let proof_obligation_id = trust_ir::ProofId::new(2);
    let request = native_bundle
        .requests
        .iter()
        .find(|request| {
            request.verifier_suite() == trust_ir::NativeVerifierSuite::TrustWp
                && request.obligations().contains(&proof_obligation_id)
        })
        .expect("sample native bundle contains the trust_wp postcondition request");
    let metadata = trust_wp_native_replay_metadata_entries_for_request(
        native_bundle,
        request,
        proof_obligation_id,
    )
    .expect("sample trust_wp native replay metadata is generated from typed TrustIr");
    for key in TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS {
        assert!(
            metadata.iter().any(|entry| entry.key == key),
            "trust-wp native metadata key `{key}` should be generated from typed TrustIr"
        );
    }
    trust_wp_obligation_mut(bundle).metadata.extend(metadata);
}

fn remove_trust_wp_native_replay_metadata(bundle: &mut TrustContractBundle) {
    trust_wp_obligation_mut(bundle)
        .metadata
        .retain(|entry| entry.key != TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY);
}

fn tamper_trust_wp_native_solver_metadata(bundle: &mut TrustContractBundle) {
    let solver = trust_wp_obligation_mut(bundle)
        .metadata
        .iter_mut()
        .find(|entry| entry.key == TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY)
        .expect("sample trust_wp native metadata includes solver identity");
    let mut value: serde_json::Value =
        serde_json::from_str(&solver.value).expect("trust-wp solver metadata is typed JSON");
    value["name"] = json!("unknown");
    solver.value = value.to_string();
}

fn trust_wp_obligation_mut(bundle: &mut TrustContractBundle) -> &mut TrustObligation {
    bundle
        .obligations
        .iter_mut()
        .find(|obligation| obligation.obligation_id == TRUST_WP_OBLIGATION_ID)
        .expect("sample bundle contains the trust_wp postcondition obligation")
}

fn trust_wp_postcondition_obligation() -> TrustObligation {
    TrustObligation {
        obligation_id: TRUST_WP_OBLIGATION_ID.to_string(),
        kind: ObligationKind::Postcondition,
        contract_id: Some("contract::trust-wp-ensures-positive".to_string()),
        proof_item_id: None,
        source: sample_source_location(102),
        description: "trust-wp proves the typed postcondition for the sample transfer".to_string(),
        required_strength: Some(ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    }
}

fn trust_mc_arithmetic_obligation() -> TrustObligation {
    TrustObligation {
        obligation_id: TRUST_MC_OBLIGATION_ID.to_string(),
        kind: ObligationKind::ArithmeticSafety,
        contract_id: None,
        proof_item_id: None,
        source: sample_source_location(101),
        description: "trust-mc proves arithmetic safety for the sample transfer".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![
            trust_mc_full_verification_verdict_metadata_entry(
                TRUST_MC_OBLIGATION_ID,
                &trust_mc_proof_grade_verdict(TRUST_MC_OBLIGATION_ID),
            )
            .expect("trust-mc proof-grade verdict metadata serializes"),
        ],
    }
}

fn sample_source_location(line: u32) -> SourceLocation {
    SourceLocation {
        file: Some("sample_full_verifier.rs".to_string()),
        line: Some(line),
        column: Some(9),
        end_line: Some(line),
        end_column: Some(19),
    }
}

fn trust_vc_ownership_obligation() -> TrustObligation {
    TrustObligation {
        obligation_id: TRUST_VC_OBLIGATION_ID.to_string(),
        kind: ObligationKind::Ownership,
        contract_id: Some("contract::trust-vc-memory-proof-unit".to_string()),
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "trust-vc proves ownership state for the sample transfer".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: trust_vc_typed_proof_metadata(),
    }
}

fn trust_mc_proof_grade_verdict(obligation_id: &str) -> FullVerificationVerdict {
    let obligation = MirDerivedChcPdrObligation::new(
        obligation_id,
        MirObligationKind::ArithmeticSafety,
        "(declare-rel checked_transfer ())\n(rule checked_transfer)\n(query checked_transfer)\n",
    );
    let stats = ChcPdrStats { relation_count: 1, clause_count: 1 };
    let mut proof = ChcPdrProofEvidence::proof_grade_from_bytes(
        ChcPdrProofKind::PdrInvariant,
        obligation,
        stats,
        ("ay://sample/checked-transfer/transcript.smt2", b"sample solver transcript"),
        ("trust-mc://sample/checked-transfer/replay-log.json", b"sample trust_mc replay log"),
        (
            "trust-mc://sample/checked-transfer/checked-proof-report.json",
            b"sample trust_mc checked proof report",
        ),
    );
    proof.invariant_count = 1;
    FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) }
}

fn trust_vc_mir_memory_proof_unit_payload() -> serde_json::Value {
    json!({
        "source_id": "sample-full-verifier-three-suite",
        "unit_id": "sample_full_verifier::checked_transfer",
        "display_name": "checked_transfer",
        "native_context": {
            "function_signature": {
                "name": "sample_full_verifier::checked_transfer",
                "params": [
                    {
                        "name": "owner_live",
                        "sort": { "kind": "bool" }
                    }
                ],
                "return_sort": { "kind": "bool" }
            },
            "ownership": {
                "places": [
                    {
                        "place": "account",
                        "sort": {
                            "kind": "bit_vector",
                            "width": 32,
                            "signed": false
                        }
                    }
                ],
                "borrows": [
                    {
                        "region": "transfer_shared",
                        "place": "account",
                        "kind": "shared"
                    }
                ]
            }
        },
        "obligations": [
            {
                "id": TRUST_VC_OBLIGATION_ID,
                "predicate": {
                    "kind": "compare",
                    "op": "eq",
                    "left": {
                        "kind": "variable",
                        "name": "owner_live",
                        "sort": { "kind": "bool" }
                    },
                    "right": {
                        "kind": "variable",
                        "name": "owner_live",
                        "sort": { "kind": "bool" }
                    }
                },
                "location": "sample_full_verifier.rs:12:9"
            }
        ],
        "metadata": {
            "sample": "full-verifier-three-suite"
        }
    })
}

fn trust_vc_engine() -> TrustVcVerificationEngine {
    TrustVcVerificationEngine::new()
}

fn assert_trust_mc_serialized_metadata_fails_closed(evidence: &ObligationEvidence) {
    assert_eq!(evidence.status, EvidenceStatus::Unsupported);
    assert_eq!(evidence.engine.name, "trust-full-verifier");
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(!evidence.has_solver_transcript_artifacts());
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_mc diagnostic-only evidence is not a full proof")
                && diagnostic.contains("not native proof-grade")
        }),
        "{evidence:#?}"
    );
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .contains("serialized trust_mc FullVerificationVerdict metadata is diagnostic-only")
            && diagnostic.contains("direct typed CHC/PDR solving")
    }));
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("primary owner trust-mc@") && diagnostic.contains("rejected evidence")
    }));
}

/// Under the native-bundle path the sample's trust-mc obligation carries only a
/// serialized FullVerificationVerdict plus a trivial native formula, so the
/// hardened NativeTrustMcTrustIrEngine refuses it: serialized verdict metadata is
/// diagnostic-only and proof-grade admission requires a live opaque native-bundle
/// CHC/PDR authority the synthetic sample does not supply.
fn assert_trust_mc_native_bundle_authority_unavailable(evidence: &ObligationEvidence) {
    assert_eq!(evidence.status, EvidenceStatus::Unsupported, "{evidence:#?}");
    assert_eq!(evidence.engine.name, "trust-full-verifier");
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(!evidence.has_solver_transcript_artifacts());
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("serialized FullVerificationVerdict metadata is diagnostic-only")
                && diagnostic.contains("is not proof evidence")
        }),
        "{evidence:#?}"
    );
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(
                "trust-mc proof-grade admission requires a live opaque native-bundle authority",
            )
        }),
        "{evidence:#?}"
    );
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("primary owner trust-mc@")
                && diagnostic.contains("rejected evidence")
        }),
        "{evidence:#?}"
    );
}

fn assert_missing_native_bundle_rejection(evidence: &ObligationEvidence, suite: &str) {
    assert_eq!(evidence.engine.name, "trust-full-verifier");
    assert!(evidence.artifacts.is_empty(), "{suite} text-only evidence artifacts must be cleared");
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("requires typed TrustIr native request/proof artifacts")
            && diagnostic.contains("no typed TrustIr NativeVerificationBundle was supplied")
    }));
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains(&format!("primary owner {suite}@"))
            && diagnostic.contains("rejected evidence")
    }));
}

fn assert_rejected_missing_native_bundle_proof(evidence: &ObligationEvidence, suite: &str) {
    assert_eq!(evidence.status, EvidenceStatus::Proved, "{suite}");
    assert!(
        evidence.proof_strength.is_some(),
        "{suite} should preserve the child proof strength while rejecting acceptance"
    );
    assert_missing_native_bundle_rejection(evidence, suite);
}

fn assert_trust_vc_fail_closed(evidence: &ObligationEvidence) {
    assert_eq!(evidence.status, EvidenceStatus::Unsupported, "{evidence:#?}");
    assert_eq!(evidence.engine.name, "trust-full-verifier");
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("proof_strength is intentionally omitted")
            || (diagnostic.contains("primary owner trust-vc@")
                && diagnostic.contains("rejected evidence"))
    }));
}

fn assert_native_trust_vc_request_unavailable(evidence: &ObligationEvidence) {
    assert_trust_vc_fail_closed(evidence);
    assert!(
        evidence
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("contains no TrustVc requests")),
        "{evidence:#?}"
    );
}

fn assert_trust_wp_missing_native_metadata_rejection(evidence: &ObligationEvidence) {
    assert_eq!(evidence.engine.name, "trust-full-verifier");
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("invalid trust_wp native replay metadata")
                && diagnostic.contains("missing required trust-wp metadata key")
        }),
        "{evidence:#?}"
    );
    assert!(evidence.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("primary owner trust-wp@") && diagnostic.contains("rejected evidence")
    }));
}

fn assert_deterministic_three_suite_mode() {
    match std::env::var(THREE_SUITE_SAMPLE_MODE_ENV) {
        Ok(mode) => assert_eq!(
            mode, REQUIRED_NATIVE_SUITES_MODE,
            "{THREE_SUITE_SAMPLE_MODE_ENV} must be unset or `{REQUIRED_NATIVE_SUITES_MODE}`"
        ),
        Err(std::env::VarError::NotPresent) => {}
        Err(std::env::VarError::NotUnicode(_)) => {
            panic!("{THREE_SUITE_SAMPLE_MODE_ENV} must be valid UTF-8")
        }
    }
}

fn assert_suite_accepted(
    evidence: &[trust_verifier_api::ObligationEvidence],
    obligation_id: &str,
    suite: &str,
) {
    let evidence = evidence_for(evidence, obligation_id);
    assert_eq!(
        evidence.status,
        EvidenceStatus::Proved,
        "{suite} suite did not produce accepted proof evidence for {obligation_id}"
    );
    assert_eq!(evidence.engine.name, "trust-full-verifier", "{suite}");
    assert!(
        evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(&format!("primary owner {suite}@"))
                && diagnostic.contains("accepted evidence")
        }),
        "{suite} suite was skipped or not accepted by the full verifier for {obligation_id}"
    );
}

fn evidence_for<'a>(
    evidence: &'a [trust_verifier_api::ObligationEvidence],
    obligation_id: &str,
) -> &'a trust_verifier_api::ObligationEvidence {
    evidence
        .iter()
        .find(|item| item.obligation_id == obligation_id)
        .unwrap_or_else(|| panic!("missing evidence for {obligation_id}"))
}
