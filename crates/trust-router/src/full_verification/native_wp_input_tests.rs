//! Production replay checks, with the outer artifact hash rebuilt by the attacker.

use super::*;

fn proof() -> (TrustContractBundle, NativeVerificationBundle, ObligationEvidence) {
    let (public, native) = fixture(false);
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .unwrap();
    let proof = crate::full_verification::engines::NativeTrustWpTrustIrEngine::new()
        .verify_obligation_with_native_trust_ir_request(
            &public,
            &public.obligations[0],
            &native,
            request,
            trust_ir::ProofId::new(0),
        );
    assert_eq!(proof.status, EvidenceStatus::Proved);
    (public, native, proof)
}

fn mutate(proof: &mut ObligationEvidence, change: impl FnOnce(&mut serde_json::Value)) {
    let artifact = &mut proof.artifacts[0];
    let bytes = artifact
        .materialization
        .as_ref()
        .unwrap()
        .bound_payload_bytes(artifact.kind, &proof.obligation_id)
        .unwrap();
    let mut payload: serde_json::Value = serde_json::from_slice(bytes).unwrap();
    change(&mut payload);
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        artifact.kind,
        &serde_json::to_vec(&payload).unwrap(),
        "input-identity-control",
        &proof.obligation_id,
        Vec::new(),
    )
    .unwrap();
    artifact.uri = format!("trust-wp-body://input-control/{}", hash.value);
    artifact.hash = hash;
    artifact.materialization = Some(materialization);
    assert!(proof.satisfies_proof_artifact_policy());
}

fn replay_count(
    public: &TrustContractBundle,
    native: &NativeVerificationBundle,
    proof: ObligationEvidence,
) -> usize {
    let mut engines = configured_engines(EvidenceStatus::Unknown);
    let slot = engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
    let mut manifest = proof.engine.clone();
    manifest.repository = Some("input-identity-control".into());
    engines[slot] = Box::new(ReplayedProof { manifest, proof });
    FullVerificationEngine::new(engines, FullVerificationPolicy::default())
        .verify_obligations_with_native_trust_ir_bundle(
            public,
            &public.obligations,
            native,
            &VerifierExecutionContext::new("input-identity-control"),
        )
        .summary
        .proved
}

#[test]
fn exact_v2_input_replays_but_legacy_schema_is_refused() {
    let (public, native, mut proof) = proof();
    assert_eq!(replay_count(&public, &native, proof.clone()), 1);
    mutate(&mut proof, |payload| {
        payload["statement"]["schema"] = "trust-wp.trust-ir-body-wp.v1".into();
    });
    assert_eq!(replay_count(&public, &native, proof), 0);
}

#[test]
fn relabelled_outer_source_cannot_transfer_the_inner_proof() {
    let (public, original, mut proof) = proof();
    let native = native_verification_bundle_from_module(
        original.module.clone(),
        trust_ir::ProofDigest::sha256([0xEF; 32]),
        trust_ir::FuncId::new(0),
    )
    .expect("rebuild the same module with a different coherent source identity");
    native.validate().expect("changed source is an otherwise admitted input");
    assert_eq!(native.trust_ir_module_digest, original.trust_ir_module_digest);
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .unwrap();
    let fresh = crate::full_verification::engines::NativeTrustWpTrustIrEngine::new()
        .verify_obligation_with_native_trust_ir_request(
            &public,
            &public.obligations[0],
            &native,
            request,
            trust_ir::ProofId::new(0),
        );
    assert_eq!(fresh.status, EvidenceStatus::Proved);
    assert_eq!(replay_count(&public, &native, fresh), 1);
    mutate(&mut proof, |payload| {
        payload["statement"]["source_digest"] =
            serde_json::to_value(native.provenance.source_digest).unwrap();
        payload["statement"]["request"] = serde_json::to_value(request).unwrap();
    });
    // Outer source and exact request now agree, and fresh output succeeds.
    // The re-derived v2 question must still reject the original inner output.
    assert_eq!(replay_count(&public, &native, proof), 0);
}
