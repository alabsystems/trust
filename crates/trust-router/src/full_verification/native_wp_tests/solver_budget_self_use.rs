//! Archived normal compiler capture of the actual RSS-ceiling budget helper.
//! Current untrusted envelopes are derived without changing the captured bytes.
//!
//! Source d1505e831fd7faa7e3de3fba51c9c418dacac3dd; compiler and same-directory
//! trust frontend/daemon from 5751de080bb3f83056200c7433d135790204c5f0, compiler
//! TB1/v2 14f3e31b2fc41dc47f0e841c28fd313e31aefe64. Only the native Targo
//! frontend was rebuilt at d150 (TB1/v2 c1c2a55797dea9e70f034b25c29ead5aecfb0d3a).
//! `targo trust check -p trust-budget --dump-verifier-inputs <new-dir>
//! --report-dir <new-dir> --json` processed all 6 eligible functions: 35 rows,
//! 30 Proved, 5 Unknown, no runtime/timeout/failed rows; strict exit 1. These
//! two authored bounds were native-WP Deductive/SoundAnalysis. Neither that
//! capture nor this replay grants SDK, source/ABI, CIC, or whole-goal authority.

use super::*;
use crate::full_verification::native_trust_ir::NativeTrustIrEvidenceIndex;

const IDS: [&str; 2] = [
    "obligation:trust_budget__process_ceiling_mb:postcondition:0",
    "obligation:trust_budget__process_ceiling_mb:postcondition:1",
];
const NATIVE: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/process_ceiling_mb/native.json"));
const PUBLIC: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/process_ceiling_mb/public.json"));
const REQUESTED: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/process_ceiling_mb/requested.json"));
const PAIR: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/current_self_use/process_ceiling_mb/pair.json"));
const CLAIMS: [&str; 2] = [
    "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"ge\",\"rhs\":{\"var\":\"budget_mb\"}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"},{\"name\":\"budget_mb\",\"sort\":\"int\"}]}",
    "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"ge\",\"rhs\":{\"int\":2048}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"}]}",
];

fn capture() -> (TrustContractBundle, Vec<TrustObligation>, NativeVerificationBundle) {
    for (bytes, sha) in [
        (NATIVE, "94b8034ad617339911dafc97dfea8723287370fc21ca0e77df9da5a7c58e465d"),
        (PUBLIC, "e44e829523b127fce9f90ca3b10b167b2d98ef856a336447e27c56b96403ef53"),
        (REQUESTED, "66a7fad46874a52861603300778a0c100e743f852a786479e64ac11538e5e0f1"),
        (PAIR, "e97eeedf1ba778aca998afb8a8419a56e1f6a4f99178b93467e0d619ba7af0b8"),
    ] {
        assert_eq!(trust_types::stable_sha256_hex(bytes.as_bytes()), sha);
    }
    let public: TrustContractBundle = serde_json::from_str(PUBLIC).unwrap();
    let all: Vec<TrustObligation> = serde_json::from_str(REQUESTED).unwrap();
    let native = derived_current_native_input(NATIVE);
    native.validate().unwrap();
    assert_eq!(public.obligations.len(), 7);
    assert_eq!(all.len(), 7);
    assert_eq!(native.module.proof_obligations.len(), 7);
    assert_eq!(native.requests.len(), 9);
    assert_eq!(native.module.functions.len(), 1);
    let function = &native.module.functions[0];
    assert_eq!(function.name, "process_ceiling_mb");
    assert_eq!(function.blocks.len(), 4);
    assert_eq!(function.blocks.iter().map(|b| b.body.len()).sum::<usize>(), 22);
    for (index, payload) in CLAIMS.into_iter().enumerate() {
        let formula = native.module.proof_obligations[index].formula.as_ref().unwrap();
        assert_eq!(formula.payload, payload);
        assert_eq!(formula.bindings[0], ("_0".into(), trust_ir::proof::ClauseBinding {
            sort: trust_ir::proof::ClauseSort::BitVec(64),
            place: trust_ir::proof::ClausePlace::ResultSlot { index: 0 },
        }));
        assert!(native.requests.iter().any(|r| matches!(r,
            NativeVerificationRequest::TrustMc(r)
                if r.id.index() == index as u32 && r.obligations == [trust_ir::ProofId::new(index as u32)])));
        assert!(native.requests.iter().any(|r| matches!(r,
            NativeVerificationRequest::TrustWp(r)
                if r.id.index() == 7 + index as u32 && r.obligations == [trust_ir::ProofId::new(index as u32)])));
    }
    let requested: Vec<_> = all.into_iter().filter(|o| IDS.contains(&o.obligation_id.as_str())).collect();
    assert_eq!(requested.len(), 2);
    (public, requested, native)
}

fn run(public: &TrustContractBundle, requested: &[TrustObligation], native: &NativeVerificationBundle)
    -> FullVerificationRunWithFreshReceipts
{
    FullVerificationEngine::with_required_native_engines()
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            public, requested, native, &VerifierExecutionContext::new("fresh-solver-budget-self-use"))
}

fn accepted() -> (TrustContractBundle, Vec<TrustObligation>, NativeVerificationBundle,
                  FullVerificationRunWithFreshReceipts) {
    let (public, requested, native) = capture();
    let live = run(&public, &requested, &native);
    assert_eq!(live.result().summary.proved, 2, "{:#?}", live.result());
    assert_eq!(live.result().evidence.len(), 2);
    assert_eq!(live.checked_native_wp_proofs().len(), 2);
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    for (proof, id) in IDS.into_iter().enumerate() {
        let row = live.result().evidence.iter().find(|r| r.obligation_id == id).unwrap();
        let obligation = requested.iter().find(|o| o.obligation_id == id).unwrap();
        assert_eq!(row.status, EvidenceStatus::Proved);
        assert_eq!(row.proof_strength, Some(ProofStrength::deductive()));
        assert!(row.satisfies_proof_artifact_policy());
        let fact = &live.checked_native_wp_proofs()[id];
        assert_eq!(fact.native_request_id(), 7 + proof as u32);
        assert_eq!(fact.native_proof_id(), proof as u32);
        assert!(fact.matches(&public, &native, obligation, row));
        assert!(index.accepts_wp_certificate(&public, obligation, row, 7 + proof as u32, proof as u32));
    }
    (public, requested, native, live)
}

fn first(requested: &[TrustObligation]) -> &[TrustObligation] {
    assert_eq!(requested[0].obligation_id, IDS[0]);
    &requested[..1]
}

fn assert_unproved(public: &TrustContractBundle, requested: &[TrustObligation], native: &NativeVerificationBundle) {
    let live = run(public, requested, native);
    assert_eq!(live.result().summary.proved, 0, "{:#?}", live.result());
    assert_eq!(live.result().evidence.len(), requested.len());
    assert!(live.checked_native_wp_proofs().is_empty());
}

fn assert_first_changed_question_has_no_wp_proof(native: &NativeVerificationBundle) {
    // Explicitly untrusted negative mutant; retain the entire original module,
    // selecting only its first WP request for a semantic control independent of
    // public transport freshness. Production replay above keeps all 9 requests.
    let mut scoped = native.clone();
    scoped.requests.retain(|r| matches!(r, NativeVerificationRequest::TrustWp(r) if r.id.index() == 7));
    let outcomes = trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts(&scoped).unwrap();
    assert_eq!(outcomes.len(), 1);
    assert_ne!(outcomes[0].status, trust_wp_lib::VerifyBundleStatus::Verified, "{outcomes:#?}");
}

#[test]
fn fresh_process_ceiling_both_bounds_route_real_mc_to_wp() {
    let (public, requested, native, live) = accepted();
    let index = NativeTrustIrEvidenceIndex::from_bundle(&native);
    for (proof, id) in IDS.into_iter().enumerate() {
        let row = live.result().evidence.iter().find(|r| r.obligation_id == id).unwrap();
        let obligation = requested.iter().find(|o| o.obligation_id == id).unwrap();
        for _ in 0..2 {
            assert!(index.accepts_wp_certificate(&public, obligation, row, 7 + proof as u32, proof as u32));
            assert!(live.checked_native_wp_proofs()[id].clone().matches(&public, &native, obligation, row));
        }
    }
}

#[test]
fn fresh_process_ceiling_false_claim_cannot_reuse_proof() {
    let (mut public, requested, mut native, live) = accepted();
    let requested = first(&requested);
    let row = live.result().evidence.iter().find(|r| r.obligation_id == IDS[0]).unwrap();
    let contract = public.contracts.iter_mut()
        .find(|c| Some(&c.contract_id) == requested[0].contract_id.as_ref()).unwrap();
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(false), Vec::new(),
    );
    predicate.validate().unwrap();
    let formula = trust_wp::trust_wp_native_formula_from_trust_spec(&predicate).unwrap();
    contract.predicate = predicate.into_contract_predicate().unwrap();
    native.module.proof_obligations[0].formula = Some(formula);
    for entry in &mut contract.metadata {
        if entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY { entry.value = "[]".into(); }
    }
    let digest = public.canonical_obligation_semantic_digest_sha256(&requested[0]).unwrap();
    native.module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        trust_ir::ProofDigest::sha256(std::array::from_fn(|i| u8::from_str_radix(&digest[2*i..2*i+2], 16).unwrap()));
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_first_changed_question_has_no_wp_proof(&native);
    assert!(!live.checked_native_wp_proofs()[IDS[0]].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(&public, &requested[0], row, 7, 0));
    assert_unproved(&public, requested, &native);
}

#[test]
fn fresh_process_ceiling_changed_return_cannot_reuse_proof() {
    let (public, requested, mut native, live) = accepted();
    let function = &mut native.module.functions[0];
    let block = function.blocks.iter_mut().find(|b|
        b.body.iter().any(|n| matches!(n.inst, trust_ir::Inst::Return { .. }))).unwrap();
    let position = block.body.iter().position(|n| matches!(n.inst, trust_ir::Inst::Return { .. })).unwrap();
    let value = trust_ir::ValueId::new(18);
    block.body.insert(position, trust_ir::InstrNode::new(trust_ir::Inst::Const {
        ty: trust_ir::Ty::U64, value: trust_ir::Constant::Int(0),
    }).with_result(value));
    let trust_ir::Inst::Return { values } = &mut block.body[position + 1].inst else { unreachable!() };
    *values = vec![value];
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_first_changed_question_has_no_wp_proof(&native);
    let row = live.result().evidence.iter().find(|r| r.obligation_id == IDS[0]).unwrap();
    assert!(!live.checked_native_wp_proofs()[IDS[0]].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(&public, &requested[0], row, 7, 0));
    assert_unproved(&public, &requested, &native);
}

#[test]
fn fresh_process_ceiling_changed_result_binding_cannot_reuse_proof() {
    let (public, requested, mut native, live) = accepted();
    // The actual complete capture returns SSA value17. Its equivalent value
    // still cannot replace the authored ResultSlot ABI binding in a receipt.
    native.module.proof_obligations[0].formula.as_mut().unwrap().bindings[0].1.place =
        trust_ir::proof::ClausePlace::Value(trust_ir::ValueId::new(17));
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    let requested = first(&requested);
    let row = live.result().evidence.iter().find(|r| r.obligation_id == IDS[0]).unwrap();
    assert!(!live.checked_native_wp_proofs()[IDS[0]].matches(&public, &native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(&native).accepts_wp_certificate(&public, &requested[0], row, 7, 0));
    assert_unproved(&public, requested, &native);
}
