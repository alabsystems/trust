//! Archived compiler capture of the complete signed-min body and its authored bound.
//! Current untrusted envelopes are derived without changing the captured bytes.
//!
//! Producer: source 5751de080bb3f83056200c7433d135790204c5f0, normal Bootstrap
//! stage1 compiler/frontend/daemon, TB1/v2 identity 14f3e31b2fc41dc47f0e841c28fd313e31aefe64.
//! Command: targo trust check -p trust-intbound --dump-verifier-inputs <new-dir>
//! --report-dir <new-dir> --json. The actual capture reported 26/26 obligations
//! proved on that source. This regression replays one original authored clause;
//! it grants no live-source, compiler/ABI, SDK, CIC, or whole-compiler authority.
//! Historical source-only captures and their refusal tests remain unchanged.

use super::*;
use crate::full_verification::native_trust_ir::NativeTrustIrEvidenceIndex;

const ID: &str = "obligation:trust_intbound__signed_min_magnitude:postcondition:0";
const NATIVE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/signed_min_magnitude/native.json"
));
const PUBLIC: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/signed_min_magnitude/public.json"
));
const REQUESTED: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/signed_min_magnitude/requested.json"
));
const PAIR: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/signed_min_magnitude/pair.json"
));
const CLAIM: &str = "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"le\",\"rhs\":{\"int\":9223372036854775808}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"}]}";

fn capture() -> (TrustContractBundle, Vec<TrustObligation>, NativeVerificationBundle) {
    for (bytes, expected) in [
        (NATIVE, "864cd55b2b4d99160101ccf24716cbce7a6c2b8f937a937bd35ee258ac12851f"),
        (PUBLIC, "c68cd0fc208eaf4fc121292532b98f48e6a6764a15b890a7ad0454cf5de862dc"),
        (REQUESTED, "88faeee1797905ef815da09935dc5275b6470e7cf0066bfeb698d4d0b504c5b3"),
        (PAIR, "34e844ba5925ed6eb9836f6f4546f065ac8b7d4f990097a175a6305c62b071e1"),
    ] {
        assert_eq!(trust_types::stable_sha256_hex(bytes.as_bytes()), expected);
    }
    let public: TrustContractBundle = serde_json::from_str(PUBLIC).unwrap();
    let all_requested: Vec<TrustObligation> = serde_json::from_str(REQUESTED).unwrap();
    let native = derived_current_native_input(NATIVE);
    native.validate().unwrap();
    assert_eq!(public.obligations.len(), 3);
    assert_eq!(all_requested.len(), 3);
    assert_eq!(native.module.proof_obligations.len(), 3);
    assert_eq!(native.requests.len(), 4);
    assert_eq!(native.module.functions.len(), 2);
    let shapes: Vec<_> = native
        .module
        .functions
        .iter()
        .map(|function| {
            (
                function.name.as_str(),
                function.blocks.len(),
                function.blocks.iter().map(|block| block.body.len()).sum::<usize>(),
            )
        })
        .collect();
    assert_eq!(shapes, [("signed_min_magnitude", 2, 10), ("raw_signed_min_magnitude", 130, 590)]);
    let formula = native.module.proof_obligations[0].formula.as_ref().unwrap();
    assert_eq!(formula.payload, CLAIM);
    assert_eq!(
        formula.bindings,
        vec![(
            "_0".into(),
            trust_ir::proof::ClauseBinding {
                sort: trust_ir::proof::ClauseSort::BitVec(64),
                place: trust_ir::proof::ClausePlace::ResultSlot { index: 0 },
            }
        )]
    );
    assert!(native.requests.iter().any(|request| matches!(request,
        NativeVerificationRequest::TrustMc(request)
            if request.id.index() == 0 && request.obligations == [trust_ir::ProofId::new(0)])));
    assert!(native.requests.iter().any(|request| matches!(request,
        NativeVerificationRequest::TrustWp(request)
            if request.id.index() == 3 && request.obligations == [trust_ir::ProofId::new(0)])));
    let requested: Vec<_> =
        all_requested.into_iter().filter(|row| row.obligation_id == ID).collect();
    assert_eq!(requested.len(), 1, "select the authored row without changing its complete capture");
    (public, requested, native)
}

fn run(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
) -> FullVerificationRunWithFreshReceipts {
    // No synthetic Unknown engine, forced WP route, request rewrite, or new assumption.
    FullVerificationEngine::with_required_native_engines()
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            public,
            requested,
            native,
            &VerifierExecutionContext::new("fresh-signed-min-self-use"),
        )
}

fn accepted() -> (
    TrustContractBundle,
    Vec<TrustObligation>,
    NativeVerificationBundle,
    FullVerificationRunWithFreshReceipts,
) {
    let (public, requested, native) = capture();
    let live = run(&public, &requested, &native);
    assert_eq!(live.result().summary.proved, 1, "{:#?}", live.result());
    assert_eq!(live.result().evidence.len(), 1);
    assert_eq!(live.checked_native_wp_proofs().len(), 1);
    let row = &live.result().evidence[0];
    assert_eq!(row.status, EvidenceStatus::Proved);
    assert_eq!(row.proof_strength, Some(ProofStrength::deductive()));
    assert!(row.satisfies_proof_artifact_policy());
    let fact = &live.checked_native_wp_proofs()[ID];
    assert_eq!(fact.native_request_id(), 3);
    assert_eq!(fact.native_proof_id(), 0);
    assert!(fact.matches(&public, &native, &requested[0], row));
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    assert!(index.accepts_wp_certificate(&public, &requested[0], row, 3, 0));
    (public, requested, native, live)
}

fn assert_unproved(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
) {
    let live = run(public, requested, native);
    assert_eq!(live.result().summary.proved, 0, "{:#?}", live.result());
    assert_eq!(live.result().evidence.len(), 1);
    assert!(live.checked_native_wp_proofs().is_empty());
}

fn assert_changed_question_has_no_wp_proof(native: &NativeVerificationBundle) {
    // Check the changed semantic question on the complete original input;
    // stale public transport bindings cannot substitute for this control.
    let admitted = trust_ir::ValidatedNativeBundle::new(native).unwrap();
    let outcome = trust_wp_lib::trust_ir_body::verify_trust_ir_body_request_validated(
        &admitted,
        trust_ir::NativeRequestId::new(3),
    )
    .unwrap();
    assert_ne!(outcome.result().status, trust_wp_lib::VerifyBundleStatus::Verified, "{outcome:#?}");
}

#[test]
fn fresh_signed_min_magnitude_routes_real_mc_to_wp() {
    let (public, requested, native, live) = accepted();
    let row = &live.result().evidence[0];
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    for _ in 0..2 {
        assert!(index.accepts_wp_certificate(&public, &requested[0], row, 3, 0));
        assert!(live.checked_native_wp_proofs()[ID].clone().matches(
            &public,
            &native,
            &requested[0],
            row
        ));
    }
}

#[test]
fn fresh_signed_min_magnitude_false_claim_cannot_reuse_proof() {
    let (mut public, requested, mut native, live) = accepted();
    let row = &live.result().evidence[0];
    let contract = public
        .contracts
        .iter_mut()
        .find(|contract| Some(&contract.contract_id) == requested[0].contract_id.as_ref())
        .unwrap();
    let false_predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(false),
        Vec::new(),
    );
    false_predicate.validate().unwrap();
    let false_formula =
        trust_wp::trust_wp_native_formula_from_trust_spec(&false_predicate).unwrap();
    contract.predicate = false_predicate.into_contract_predicate().unwrap();
    native.module.proof_obligations[0].formula = Some(false_formula);
    for entry in &mut contract.metadata {
        if entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY {
            entry.value = "[]".into();
        }
    }
    let digest = public.canonical_obligation_semantic_digest_sha256(&requested[0]).unwrap();
    native.module.proof_obligations[0]
        .source
        .as_mut()
        .unwrap()
        .public
        .as_mut()
        .unwrap()
        .semantic_digest = trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
        u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
    }));
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_changed_question_has_no_wp_proof(&native);
    assert!(!live.checked_native_wp_proofs()[ID].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(
        &public,
        &requested[0],
        row,
        3,
        0
    ));
    assert_unproved(&public, &requested, &native);
}

#[test]
fn fresh_signed_min_magnitude_changed_return_cannot_reuse_proof() {
    let (public, requested, mut native, live) = accepted();
    let function = native
        .module
        .functions
        .iter_mut()
        .find(|function| function.name == "signed_min_magnitude")
        .unwrap();
    let next = function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .flat_map(|node| &node.results)
        .map(|value| value.index())
        .max()
        .unwrap()
        .checked_add(1)
        .unwrap();
    let changed_value = trust_ir::ValueId::new(next);
    let block = function
        .blocks
        .iter_mut()
        .find(|block| {
            block.body.iter().any(|node| matches!(node.inst, trust_ir::Inst::Return { .. }))
        })
        .unwrap();
    let position = block
        .body
        .iter()
        .position(|node| matches!(node.inst, trust_ir::Inst::Return { .. }))
        .unwrap();
    block.body.insert(
        position,
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: trust_ir::Ty::U64,
            value: trust_ir::Constant::Int(i128::from(u64::MAX)),
        })
        .with_result(changed_value),
    );
    let trust_ir::Inst::Return { values } = &mut block.body[position + 1].inst else {
        unreachable!()
    };
    *values = vec![changed_value];
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_changed_question_has_no_wp_proof(&native);
    let row = &live.result().evidence[0];
    assert!(!live.checked_native_wp_proofs()[ID].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(
        &public,
        &requested[0],
        row,
        3,
        0
    ));
    assert_unproved(&public, &requested, &native);
}

#[test]
fn fresh_signed_min_magnitude_changed_result_binding_cannot_reuse_proof() {
    let (public, requested, mut native, live) = accepted();
    let formula = native.module.proof_obligations[0].formula.as_mut().unwrap();
    // Value 8 is the actual U64 callee result in this complete original wrapper.
    // Even an equivalent SSA value must not replace its declared ResultSlot ABI binding.
    formula.bindings[0].1.place = trust_ir::proof::ClausePlace::Value(trust_ir::ValueId::new(8));
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    let row = &live.result().evidence[0];
    assert!(!live.checked_native_wp_proofs()[ID].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(
        &public,
        &requested[0],
        row,
        3,
        0
    ));
    assert_unproved(&public, &requested, &native);
}
