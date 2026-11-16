//! Data linkage controls; Clean owns the closed-CIC translation qualification.
use clean_olean::semr_native_execution::{
    NativeExecutionIntegerType, NativeExecutionPlace, NativeExecutionType,
};
use trust_ir::{ProofId, ValidatedNativeBundle};
use trust_ir_build::validate_module_report;

use super::*;

fn checked(
    public: &TrustContractBundle,
    native: &NativeVerificationBundle,
) -> (ObligationEvidence, CheckedNativeWpProof) {
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            public,
            &public.obligations,
            native,
            &VerifierExecutionContext::new("same-derivation-math-data"),
        );
    assert_eq!(live.result().summary.proved, 1, "{:#?}", live.result());
    let fact = live.checked_native_wp_proofs()[&public.obligations[0].obligation_id].clone();
    (live.result().evidence[0].clone(), fact)
}

#[test]
fn mathematics_consumes_the_checked_actual_vc_and_complete_original_question() {
    let (public, native) = fixture(false);
    let snapshot = native.clone();
    let (evidence, wp) = checked(&public, &native);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let subject = native_wp_translation_subject(
        &admitted,
        &semantics,
        &public,
        &public.obligations[0],
        &evidence,
        &wp,
    )
    .unwrap();
    let witness = wp.translation_witness().unwrap();
    assert_eq!(witness.native_bundle_digest, native.stable_digest());
    assert_eq!(
        subject.original.module.bytes(),
        trust_ir::binary::serialize_module(&native.module).unwrap()
    );
    assert_eq!(
        subject.vc_bytes.as_ref(),
        witness.derived_request.obligations[0].claim.payload.as_bytes()
    );
    assert_eq!(subject.vc_bindings[0].name, witness.parameters[0].1.as_bytes());
    assert_eq!(subject.vc_bindings[0].place, NativeExecutionPlace::Param(0));
    assert_eq!(subject.vc_bindings[0].ty, NativeExecutionType::Bool);
    assert_eq!(native, snapshot);
    assert_eq!(evidence.proof_strength, Some(ProofStrength::deductive()));
}

fn unsigned_fixture() -> (TrustContractBundle, NativeVerificationBundle) {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let (mut public, seed) = fixture(false);
    let mut module = seed.module;
    let bindings = vec![
        (
            "c".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
        ),
        (
            "x".into(),
            ClauseBinding { sort: ClauseSort::BitVec(64), place: ClausePlace::Param { index: 1 } },
        ),
        (
            "y".into(),
            ClauseBinding { sort: ClauseSort::BitVec(64), place: ClausePlace::Param { index: 2 } },
        ),
        (
            "r".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(64),
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    let schema = trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION;
    let payload = serde_json::json!({"schema":schema,"variables":[
        {"name":"c","sort":"bool"},{"name":"x","sort":"int"},
        {"name":"y","sort":"int"},{"name":"r","sort":"int"}],
        "body":{"op":"and","lhs":{"op":"implies","lhs":{"var":"c"},
            "rhs":{"op":"eq","lhs":{"var":"r"},"rhs":{"var":"x"}}},
            "rhs":{"op":"implies","lhs":{"op":"not","expr":{"var":"c"}},
            "rhs":{"op":"eq","lhs":{"var":"r"},"rhs":{"var":"y"}}}}})
    .to_string();
    public.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: schema.into(),
        value: serde_json::Value::String(payload.clone()),
    };
    public.contracts[0].metadata[0].value = serde_json::to_string(&bindings).unwrap();
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    module.func_types[0].params = vec![trust_ir::Ty::Bool, trust_ir::Ty::U64, trust_ir::Ty::U64];
    module.func_types[0].returns = vec![trust_ir::Ty::U64];
    let block = &mut module.functions[0].blocks[0];
    block.params = vec![
        (trust_ir::ValueId::new(0), trust_ir::Ty::Bool),
        (trust_ir::ValueId::new(1), trust_ir::Ty::U64),
        (trust_ir::ValueId::new(2), trust_ir::Ty::U64),
    ];
    block.body = vec![
        trust_ir::InstrNode::new(trust_ir::Inst::Select {
            ty: trust_ir::Ty::U64,
            cond: trust_ir::ValueId::new(0),
            then_val: trust_ir::ValueId::new(1),
            else_val: trust_ir::ValueId::new(2),
        })
        .with_result(trust_ir::ValueId::new(3)),
        trust_ir::InstrNode::new(trust_ir::Inst::Return {
            values: vec![trust_ir::ValueId::new(3)],
        }),
    ];
    let mut formula = trust_ir::ProofFormula::new(schema, payload);
    formula.bindings = bindings;
    module.proof_obligations[0].formula = Some(formula);
    module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        }));
    let native = native_verification_bundle_from_module(
        module,
        native_trust_ir_digest(1),
        trust_ir::FuncId::new(0),
    )
    .unwrap();
    (public, native)
}

#[path = "native_wp_translation_cic_tests.rs"]
mod closed_translation;

#[test]
fn full_unsigned_width_and_original_result_place_reach_the_actual_vc_subject() {
    let (public, native) = unsigned_fixture();
    let original = native.clone();
    let (evidence, wp) = checked(&public, &native);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let subject = native_wp_translation_subject(
        &admitted,
        &semantics,
        &public,
        &public.obligations[0],
        &evidence,
        &wp,
    )
    .unwrap();
    let u64_type = NativeExecutionType::Int(NativeExecutionIntegerType::U64);
    assert_eq!(
        subject.vc_bindings.iter().map(|binding| binding.ty).collect::<Vec<_>>(),
        [NativeExecutionType::Bool, u64_type, u64_type]
    );
    assert_eq!(subject.original.typed_bindings[3].place, NativeExecutionPlace::Result(0));
    assert_eq!(subject.original.typed_bindings[3].ty, u64_type);
    assert_eq!(
        subject.original.contract_bytes.as_ref(),
        native.module.proof_obligations[0].formula.as_ref().unwrap().payload.as_bytes()
    );
    assert_eq!(
        subject.vc_bytes.as_ref(),
        wp.translation_witness().unwrap().derived_request.obligations[0].claim.payload.as_bytes()
    );
    assert_eq!(native, original);
}

#[test]
fn changed_public_binding_evidence_or_foreign_semantics_cannot_reuse_a_checked_question() {
    let (public, native) = unsigned_fixture();
    let (evidence, wp) = checked(&public, &native);
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let mut altered = public.clone();
    let mut bindings: Vec<(String, trust_ir::proof::ClauseBinding)> =
        serde_json::from_str(&altered.contracts[0].metadata[0].value).unwrap();
    bindings[3].1.place = trust_ir::proof::ClausePlace::Param { index: 1 };
    altered.contracts[0].metadata[0].value = serde_json::to_string(&bindings).unwrap();
    assert!(
        native_wp_translation_subject(
            &admitted,
            &semantics,
            &altered,
            &altered.obligations[0],
            &evidence,
            &wp
        )
        .is_err()
    );
    let mut changed_evidence = evidence.clone();
    changed_evidence.evidence_id.push('_');
    assert!(
        native_wp_translation_subject(
            &admitted,
            &semantics,
            &public,
            &public.obligations[0],
            &changed_evidence,
            &wp
        )
        .is_err()
    );
    let cloned_module = native.module.clone();
    let foreign = validate_module_report(&cloned_module);
    assert!(
        native_wp_translation_subject(
            &admitted,
            &foreign,
            &public,
            &public.obligations[0],
            &evidence,
            &wp
        )
        .is_err()
    );
    assert_eq!(native.module.proof_obligations[0].id, ProofId::new(0));
}

#[test]
fn native_wp_decline_retains_the_actual_leaf_reason_without_proof_authority() {
    // Full U64 r<=1 is false at r=2; the existing 0/1 countermodel search
    // cannot refute it, and the scalar bounds cannot prove it. Its actual
    // Unsupported leaf must remain diagnostic data without proof authority.
    let (mut public, native) = unsigned_fixture();
    let mut module = native.module;
    let schema = trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION;
    let payload = serde_json::json!({"schema":schema,"variables":[{"name":"r","sort":"int"}],
        "body":{"op":"le","lhs":{"var":"r"},"rhs":{"int":1}}})
    .to_string();
    public.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: schema.into(),
        value: serde_json::Value::String(payload.clone()),
    };
    let bindings: Vec<_> = module.proof_obligations[0]
        .formula
        .as_ref()
        .unwrap()
        .bindings
        .iter()
        .filter(|(name, _)| name == "r")
        .cloned()
        .collect();
    assert_eq!(bindings.len(), 1);
    public.contracts[0]
        .metadata
        .iter_mut()
        .find(|entry| entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY)
        .unwrap()
        .value = serde_json::to_string(&bindings).unwrap();
    let formula = module.proof_obligations[0].formula.as_mut().unwrap();
    formula.payload = payload;
    formula.bindings = bindings;
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        proof_digest_from_canonical_sha256(&digest);
    let native = native_verification_bundle_from_module(
        module,
        native_trust_ir_digest(1),
        trust_ir::FuncId::new(0),
    )
    .unwrap();
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .unwrap();
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let verification =
        trust_wp_lib::trust_ir_body::verify_trust_ir_body_request_validated(&admitted, request.id)
            .unwrap();
    let leaf = &verification.result().obligation_results[0];
    let trust_wp_lib::BundleObligationStatus::Unsupported { reason } = &leaf.status else {
        panic!("expected an actual unsupported full-domain bound: {leaf:?}");
    };
    assert!(!reason.is_empty());
    let row = crate::full_verification::engines::NativeTrustWpTrustIrEngine::new()
        .verify_obligation_with_native_trust_ir_request(
            &public,
            &public.obligations[0],
            &native,
            request,
            trust_ir::ProofId::new(0),
        );
    assert_eq!(row.status, EvidenceStatus::Unsupported);
    assert!(row.proof_strength.is_none());
    assert!(row.artifacts.is_empty());
    assert!(row.diagnostics.iter().any(|message| message.contains(reason)), "{row:#?}");
}
