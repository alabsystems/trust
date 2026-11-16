//! Flat source exactness and native replay are different authority scopes.

use super::*;

#[test]
fn flat_exact_metadata_does_not_attest_native_source_correspondence() {
    // Preserve the original real flat query and its actual validated witness.
    let flat = compiler_spec_refutation_evidence_with_fidelity(
        45,
        41,
        Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT),
    );
    assert_eq!(flat.status, EvidenceStatus::Failed);
    assert!(flat.counterexample.is_some());
    assert!(flat.proof_strength.is_none());

    let mut obligation = obligation(ObligationKind::Postcondition, "flat-exact");
    attest_synthetic_typed_chc_encoding_exact(&mut obligation);
    assert!(
        TrustMcChcRefutationAdmissibility::for_obligation(&obligation).rejection_reason().is_none()
    );
    let reason = TrustMcChcRefutationAdmissibility::for_native_obligation(&obligation)
        .rejection_reason()
        .expect("the flat premise does not establish the native source relation");
    assert!(reason.contains("flat typed ChcVc only"));
    assert!(reason.contains("per-obligation source correspondence"));
}

#[test]
fn native_source_scope_rejects_public_classes_and_duplicate_exact_annotations() {
    for class in [
        None,
        Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT),
        Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED),
        Some("future-native-exact"),
    ] {
        let mut row = obligation(ObligationKind::Postcondition, "same-row");
        if let Some(class) = class {
            row.metadata.push(MetadataEntry {
                key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
                value: class.to_string(),
            });
        }
        let flat = TrustMcChcRefutationAdmissibility::for_obligation(&row).rejection_reason();
        let native =
            TrustMcChcRefutationAdmissibility::for_native_obligation(&row).rejection_reason();
        assert!(native.is_some(), "public class cannot grant native authority: {class:?}");
        if class != Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT) {
            assert_eq!(native, flat, "old absence/negative reasons remain unchanged");
        }
    }
    let mut duplicated = obligation(ObligationKind::Postcondition, "duplicated-exact");
    attest_synthetic_typed_chc_encoding_exact(&mut duplicated);
    attest_synthetic_typed_chc_encoding_exact(&mut duplicated);
    assert!(
        TrustMcChcRefutationAdmissibility::for_native_obligation(&duplicated)
            .rejection_reason()
            .unwrap()
            .contains("ambiguous")
    );
}

#[test]
fn native_havoc_module_cannot_borrow_original_flat_exact_scope() {
    let adapter = TrustMcVerifierApiAdapter::new(
        TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
    );
    let mut public = compiler_style_panic_freedom_public_bundle();
    attest_synthetic_typed_chc_encoding_exact(&mut public.obligations[0]);
    let native = bind_compiler_style_native_bundle_to_public(
        compiler_style_loop_overflow_tmir_bundle(),
        &public,
    );
    let mut widened = compiler_style_loop_overflow_tmir_bundle();
    let node = widened
        .module
        .functions
        .iter_mut()
        .flat_map(|function| &mut function.blocks)
        .flat_map(|block| &mut block.body)
        .find(|node| {
            matches!(
                &node.inst,
                trust_ir::Inst::Const {
                    ty: trust_ir::ty::Ty::U8,
                    value: trust_ir::Constant::Int(4)
                }
            )
        })
        .expect("the original literal shift operand is present");
    node.inst = trust_ir::Inst::Undef { ty: trust_ir::ty::Ty::U8 };
    node.proofs.push(trust_ir::ProofAnnotation::FreshSymbolicHavoc);
    let widened = bind_compiler_style_native_bundle_to_public(widened, &public);
    assert_ne!(native.module.stable_digest(), widened.module.stable_digest());
    let before = adapter
        .native_trust_ir_chc_pdr_translated_obligations(&native, None)
        .expect("the unchanged actual fixture translates");
    let after = adapter
        .native_trust_ir_chc_pdr_translated_obligations(&widened, None)
        .expect("the actual fresh-symbolic over-approximation translates");
    assert_eq!(before.len(), 1);
    assert_eq!(after.len(), 1);
    let normalized = |row: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation| {
        trust_mc_driver::normalized_typed_chc_pdr_input(&row.obligation)
            .expect("actual translated request normalizes")
            .normalized_input_hash
            .value
    };
    assert_ne!(normalized(&before[0]), normalized(&after[0]));
    assert!(
        TrustMcChcRefutationAdmissibility::for_obligation(&public.obligations[0])
            .rejection_reason()
            .is_none(),
        "the old flat-only gate would admit this public value"
    );
    assert!(
        TrustMcChcRefutationAdmissibility::for_native_obligation(&public.obligations[0])
            .rejection_reason()
            .unwrap()
            .contains("source correspondence"),
        "the native over-approximation cannot inherit flat exactness"
    );
}
