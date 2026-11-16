//! Selected work retains the full native question and a checked diagnostic witness.

use trust_wp_lib::trust_ir_body::{
    NativeBodyWpTranslationCoverage, NativeBodyWpTranslationWitness,
};

use super::*;
use crate::full_verification::engines::NativeTrustWpTrustIrEngine;
use crate::full_verification::native_trust_ir::NativeTrustIrEvidenceIndex;

fn selected_request(native: &NativeVerificationBundle) -> &trust_ir::TrustWpNativeRequest {
    native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.mode == trust_ir::TrustWpVerificationMode::WeakestPrecondition =>
            {
                Some(request)
            }
            _ => None,
        })
        .unwrap()
}

fn prove_selected(
    public: &TrustContractBundle,
    native: &NativeVerificationBundle,
) -> ObligationEvidence {
    let request = selected_request(native);
    NativeTrustWpTrustIrEngine::new().verify_obligation_with_native_trust_ir_request(
        public,
        &public.obligations[0],
        native,
        request,
        request.obligations[0],
    )
}

fn certificate_value(row: &ObligationEvidence) -> serde_json::Value {
    let artifact = row
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate)
        .unwrap();
    let bytes = artifact
        .materialization
        .as_ref()
        .unwrap()
        .bound_payload_bytes(artifact.kind, &row.obligation_id)
        .unwrap();
    serde_json::from_slice(bytes).unwrap()
}

fn rewrite_certificate(
    original: &ObligationEvidence,
    change: impl FnOnce(&mut serde_json::Value),
) -> ObligationEvidence {
    let mut value = certificate_value(original);
    change(&mut value);
    let mut row = original.clone();
    let artifact = row
        .artifacts
        .iter_mut()
        .find(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate)
        .unwrap();
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        artifact.kind,
        &serde_json::to_vec(&value).unwrap(),
        "selected-boundary-control",
        &row.obligation_id,
        Vec::new(),
    )
    .unwrap();
    artifact.uri = format!("trust-wp-body://selected-boundary/{}", hash.value);
    artifact.hash = hash;
    artifact.materialization = Some(materialization);
    assert!(row.satisfies_proof_artifact_policy(), "hostile certificate is structurally valid");
    row
}

#[test]
fn selected_native_wp_keeps_mixed_unsupported_siblings_in_the_question() {
    let (public, mut native) = fixture(false);
    assert!(
        native
            .requests
            .iter()
            .any(|request| matches!(request, NativeVerificationRequest::TrustMc(_)))
    );
    let mut sibling = selected_request(&native).clone();
    sibling.id = trust_ir::NativeRequestId::new(
        native.requests.iter().map(|request| request.id().index()).max().unwrap() + 1,
    );
    // Abduction is valid native input but has no body-WP semantics. Explicit
    // selection must avoid converting it without erasing it from identity.
    sibling.mode = trust_ir::TrustWpVerificationMode::Abduction;
    native.requests.push(NativeVerificationRequest::TrustWp(sibling));
    native.validate().expect("unsupported does not mean structurally invalid");
    assert!(trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts(&native).is_err());

    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Proved, "{row:#?}");
    assert_eq!(row.proof_strength, Some(ProofStrength::deductive()));
    let certificate = certificate_value(&row);
    let witness: NativeBodyWpTranslationWitness =
        serde_json::from_value(certificate["statement"]["translation_witness"].clone()).unwrap();
    assert_eq!(witness.native_bundle_digest, native.stable_digest());
    assert_eq!(witness.module_digest, native.module.stable_digest());
    assert_eq!(witness.request, selected_request(&native).id);
    assert_eq!(
        certificate["statement"]["results"][0]["bundle_id"],
        witness.derived_request.bundle_id
    );
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    assert!(index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        &row,
        witness.request.index(),
        0,
    ));
}

#[test]
fn selected_native_wp_rejects_old_evidence_after_only_an_unselected_request_changes() {
    let (public, native) = fixture(false);
    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Proved, "{row:#?}");
    let request = selected_request(&native);
    let original_index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    assert!(original_index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        &row,
        request.id.index(),
        0,
    ));

    let mut changed = native.clone();
    let unselected = changed
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .unwrap();
    unselected.options.bmc.unwind_limit += 1;
    changed.validate().unwrap();
    assert_eq!(changed.module, native.module);
    assert_eq!(selected_request(&changed), request);
    assert_ne!(changed.stable_digest(), native.stable_digest());
    let changed_index = NativeTrustIrEvidenceIndex::from_bundle(&changed);
    assert!(!changed_index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        &row,
        request.id.index(),
        0,
    ));
    let fresh = prove_selected(&public, &changed);
    assert_eq!(fresh.status, EvidenceStatus::Proved, "{fresh:#?}");
    assert!(changed_index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        &fresh,
        request.id.index(),
        0,
    ));
}

#[test]
fn selected_native_wp_rejects_rehashed_translation_witness_tampering() {
    let (public, native) = fixture(false);
    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Proved, "{row:#?}");
    let request = selected_request(&native);
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    assert!(index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        &row,
        request.id.index(),
        0,
    ));
    for mutation in 0..8 {
        let changed = rewrite_certificate(&row, |certificate| {
            let field = &mut certificate["statement"]["translation_witness"];
            let mut witness: NativeBodyWpTranslationWitness =
                serde_json::from_value(field.clone()).unwrap();
            match mutation {
                0 => witness.native_bundle_digest = trust_ir::ProofDigest::sha256([0; 32]),
                1 => witness.module_digest = trust_ir::ProofDigest::sha256([0; 32]),
                2 => witness.request = trust_ir::NativeRequestId::new(request.id.index() + 1),
                3 => witness.contracts[0].1.payload.push_str(" && false"),
                4 => witness.derived_request.obligations[0].claim.payload.push(' '),
                5 => witness.parameters[0].1.push_str("_forged"),
                6 => witness.plan.position += 1,
                _ => {
                    witness.coverage = NativeBodyWpTranslationCoverage::Untranslated {
                        reasons: vec!["producer-owned coverage replacement".into()],
                    }
                }
            }
            *field = serde_json::to_value(witness).unwrap();
        });
        assert!(
            !index.accepts_wp_certificate(
                &public,
                &public.obligations[0],
                &changed,
                request.id.index(),
                0,
            ),
            "rehashing must not authorize witness mutation {mutation}"
        );
        assert!(index.checked_wp_proof(&public, &public.obligations[0], &changed).is_none());
    }
}

#[test]
fn selected_native_wp_missing_witness_retains_only_native_replay() {
    let (public, native) = fixture(false);
    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Proved, "{row:#?}");
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    let checked = index.checked_wp_proof(&public, &public.obligations[0], &row).unwrap();
    assert!(checked.translation_witness().is_some());

    let native_only = rewrite_certificate(&row, |certificate| {
        certificate["statement"].as_object_mut().unwrap().remove("translation_witness");
    });
    let checked = index.checked_wp_proof(&public, &public.obligations[0], &native_only).unwrap();
    assert!(checked.translation_witness().is_none());
    assert!(checked.matches(&public, &native, &public.obligations[0], &native_only));
    assert_eq!(checked.proof_strength(), ProofStrength::deductive());
}

#[test]
fn selected_native_wp_still_refuses_invalid_unselected_native_input() {
    let (public, mut native) = fixture(false);
    let duplicate = native
        .requests
        .iter()
        .find(|request| matches!(request, NativeVerificationRequest::TrustMc(_)))
        .unwrap()
        .clone();
    native.requests.push(duplicate);
    assert!(native.validate().is_err());
    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:#?}");
    assert!(row.proof_strength.is_none());
    assert!(row.artifacts.is_empty());
}

#[test]
fn selected_native_wp_long_linear_body_retains_native_proof_with_bounded_decoder() {
    let (public, mut native) = fixture(false);
    let block = &mut native.module.functions[0].blocks[0];
    block.body.clear();
    let mut previous = trust_ir::ValueId::new(0);
    for index in 1..=160 {
        let next = trust_ir::ValueId::new(index);
        block.body.push(
            trust_ir::InstrNode::new(trust_ir::Inst::Copy {
                ty: trust_ir::Ty::Bool,
                operand: previous,
            })
            .with_result(next),
        );
        previous = next;
    }
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![previous] }));
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    let prior = trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts(&native).unwrap();
    assert_eq!(prior[0].status, trust_wp_lib::VerifyBundleStatus::Verified);

    let row = prove_selected(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Proved, "{row:#?}");
    let certificate = certificate_value(&row);
    assert!(certificate["statement"].get("translation_witness").is_none());
    let native_only_bytes = serde_json::to_vec(&certificate).unwrap();
    assert!(crate::full_verification::native_trust_ir::native_wp_certificate_is_decodable(
        &native_only_bytes,
    ));
    let witnesses =
        trust_wp_lib::trust_ir_body::trust_ir_native_bundle_to_body_translation_witnesses(&native)
            .unwrap();
    let mut with_witness = certificate;
    with_witness["statement"]["translation_witness"] = serde_json::to_value(&witnesses[0]).unwrap();
    let with_witness_bytes = serde_json::to_vec(&with_witness).unwrap();
    assert!(
        with_witness_bytes.len() < trust_verifier_api::MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES
    );
    assert!(
        !crate::full_verification::native_trust_ir::native_wp_certificate_is_decodable(
            &with_witness_bytes,
        ),
        "only the optional diagnostic plan exceeds the unchanged decoder depth"
    );
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    let checked = index.checked_wp_proof(&public, &public.obligations[0], &row).unwrap();
    assert!(checked.translation_witness().is_none());
    assert!(checked.matches(&public, &native, &public.obligations[0], &row));
    assert_eq!(checked.proof_strength(), ProofStrength::deductive());
}
