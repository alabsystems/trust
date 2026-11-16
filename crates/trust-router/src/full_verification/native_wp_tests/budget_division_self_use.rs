//! Full original compiler packets from capture-02 of trust-budget at d1505e83.
//! The original normal compile reported these five authored clauses Unknown.
//! These controls run their complete caller/callee through Root routing and
//! independent native WP replay. No source/ABI, SDK, CIC or grade promotion.
use super::*;
use crate::full_verification::native_trust_ir::NativeTrustIrEvidenceIndex;

struct Capture {
    name: &'static str,
    authored: usize,
    proofs: usize,
    requests: usize,
    blocks: &'static [usize],
    bytes: [&'static str; 4],
    hashes: [&'static str; 4],
    claims: &'static [&'static str],
}

const CAPTURES: &[Capture] = &[
    Capture {
        name: "megabytes_of",
        authored: 2,
        proofs: 11,
        requests: 13,
        blocks: [9, 2].as_slice(),
        bytes: [
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/megabytes_of/native.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/megabytes_of/public.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/megabytes_of/requested.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/megabytes_of/pair.json"
            )),
        ],
        hashes: [
            "9b56bba465fba97ba1555ccfb7bf454b88f7ac2e2675f44c4139e17649cd5390",
            "10a5c8262caf2981c3c96b7e5c9c8f281b9a3361cfde1286cb875ce79fda4b77",
            "6b1e8891654e68d094e59d2411f7e678f2fc3c0fe867ff015253a1dbf37e4654",
            "5e50e91c2c53f8ec1a32deb496d7333aea2f54eb395a1dedb8d144992959ea08",
        ],
        claims: &[
            "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"le\",\"rhs\":{\"var\":\"bytes\"}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"},{\"name\":\"bytes\",\"sort\":\"int\"}]}",
            "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"le\",\"rhs\":{\"int\":17592186044415}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"}]}",
        ],
    },
    Capture {
        name: "per_job_bytes",
        authored: 1,
        proofs: 7,
        requests: 8,
        blocks: [11, 5].as_slice(),
        bytes: [
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/per_job_bytes/native.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/per_job_bytes/public.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/per_job_bytes/requested.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/per_job_bytes/pair.json"
            )),
        ],
        hashes: [
            "0b423b9a504293c3c580ea0271874f00989a686e91dd3b59ca310e3c358ad99e",
            "aecab83c583ba4b611ffa074371532607b87b3e0223691d6b016b7b540535cf4",
            "c2f034c78ddf8373ba43b32309e2f93d3e69a78c2e08d9ca43310d7692eeaf7c",
            "3d1e72a8626307d52a35347c1e58d4179acf0a77c40a8c034ff0ae7d0029e986",
        ],
        claims: &[
            "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"le\",\"rhs\":{\"var\":\"budget_bytes\"}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"},{\"name\":\"budget_bytes\",\"sort\":\"int\"}]}",
        ],
    },
    Capture {
        name: "split_budget_ms",
        authored: 2,
        proofs: 11,
        requests: 13,
        blocks: [9, 5].as_slice(),
        bytes: [
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/split_budget_ms/native.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/split_budget_ms/public.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/split_budget_ms/requested.json"
            )),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/current_self_use/split_budget_ms/pair.json"
            )),
        ],
        hashes: [
            "fb43e651137c152cf804ae53a69aa5043da6f77a4a71a3f248f4793ed238f9f6",
            "33209943e01040531603965fc654cf0c6c179dcd5b80dbb04d9e2f68393d64ec",
            "95b307811c4a97a2e68b4f8aacceee76b09903c8ca47fe9db3a54485850b9ad9",
            "4307c9c366fdef6798e68a0a763f1b67f392783fedb8231e51bfe585373db5b6",
        ],
        claims: &[
            "{\"body\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"le\",\"rhs\":{\"var\":\"total_ms\"}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"},{\"name\":\"total_ms\",\"sort\":\"int\"}]}",
            "{\"body\":{\"lhs\":{\"lhs\":{\"var\":\"total_ms\"},\"op\":\"gt\",\"rhs\":{\"int\":0}},\"op\":\"implies\",\"rhs\":{\"lhs\":{\"var\":\"_0\"},\"op\":\"gt\",\"rhs\":{\"int\":0}}},\"schema\":\"trust_wp.trust-formula.v1\",\"variables\":[{\"name\":\"_0\",\"sort\":\"int\"},{\"name\":\"total_ms\",\"sort\":\"int\"}]}",
        ],
    },
];

fn capture(index: usize) -> (TrustContractBundle, Vec<TrustObligation>, NativeVerificationBundle) {
    let capture = &CAPTURES[index];
    for (bytes, hash) in capture.bytes.into_iter().zip(capture.hashes) {
        assert_eq!(trust_types::stable_sha256_hex(bytes.as_bytes()), hash);
    }
    let pair: serde_json::Value = serde_json::from_str(capture.bytes[3]).unwrap();
    for (index, kind) in ["native", "public", "requested"].into_iter().enumerate() {
        assert_eq!(pair[kind]["sha256"].as_str(), Some(capture.hashes[index]));
        assert_eq!(pair[kind]["bytes"].as_u64(), Some(capture.bytes[index].len() as u64));
    }
    let public: TrustContractBundle = serde_json::from_str(capture.bytes[1]).unwrap();
    let all: Vec<TrustObligation> = serde_json::from_str(capture.bytes[2]).unwrap();
    let native: NativeVerificationBundle = serde_json::from_str(capture.bytes[0]).unwrap();
    native.validate().unwrap();
    assert_eq!(public.obligations.len(), capture.proofs);
    assert_eq!(all.len(), capture.proofs);
    assert_eq!(native.module.proof_obligations.len(), capture.proofs);
    assert_eq!(native.requests.len(), capture.requests);
    assert_eq!(native.module.functions.len(), 2);
    assert_eq!(native.module.functions[0].name, capture.name);
    assert_eq!(
        native.module.functions.iter().map(|f| f.blocks.len()).collect::<Vec<_>>(),
        capture.blocks
    );
    let mut requested = Vec::new();
    for proof in 0..capture.authored {
        let id = format!("obligation:trust_budget__{}:postcondition:{proof}", capture.name);
        let formula = native.module.proof_obligations[proof].formula.as_ref().unwrap();
        assert_eq!(formula.payload, capture.claims[proof]);
        assert_eq!(formula.bindings[0].0, "_0");
        assert_eq!(
            formula.bindings[0].1,
            trust_ir::proof::ClauseBinding {
                sort: trust_ir::proof::ClauseSort::BitVec(64),
                place: trust_ir::proof::ClausePlace::ResultSlot { index: 0 },
            }
        );
        assert!(native.requests.iter().any(|r| matches!(r, NativeVerificationRequest::TrustMc(r)
            if r.obligations == [trust_ir::ProofId::new(proof as u32)])));
        assert!(native.requests.iter().any(|r| matches!(r, NativeVerificationRequest::TrustWp(r)
            if r.id.index() == capture.proofs as u32 + proof as u32
                && r.obligations == [trust_ir::ProofId::new(proof as u32)])));
        requested.push(all.iter().find(|o| o.obligation_id == id).unwrap().clone());
    }
    (public, requested, native)
}

fn run(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
) -> FullVerificationRunWithFreshReceipts {
    FullVerificationEngine::with_required_native_engines()
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            public,
            requested,
            native,
            &VerifierExecutionContext::new("original-budget-division-self-use"),
        )
}

fn accepted(
    index: usize,
    proof: usize,
) -> (
    TrustContractBundle,
    Vec<TrustObligation>,
    NativeVerificationBundle,
    FullVerificationRunWithFreshReceipts,
) {
    let (public, requested, native) = capture(index);
    let requested = vec![requested[proof].clone()];
    let before = native.clone();
    let module_bytes = trust_ir::binary::serialize_module(&native.module).unwrap();
    let live = run(&public, &requested, &native);
    assert_eq!(live.result().summary.proved, 1, "{:#?}", live.result());
    assert_eq!(live.result().evidence.len(), 1);
    assert_eq!(live.checked_native_wp_proofs().len(), 1);
    let row = &live.result().evidence[0];
    assert_eq!(row.status, EvidenceStatus::Proved);
    assert_eq!(row.proof_strength, Some(ProofStrength::deductive()));
    assert!(row.satisfies_proof_artifact_policy());
    let fact = &live.checked_native_wp_proofs()[&requested[0].obligation_id];
    let request = CAPTURES[index].proofs as u32 + proof as u32;
    assert_eq!(fact.native_request_id(), request);
    assert_eq!(fact.native_proof_id(), proof as u32);
    assert!(fact.matches(&public, &native, &requested[0], row));
    // A deep witness may be omitted by the existing certificate decoder bounds.
    // When representable it still carries only untranslated mathematical data.
    if let Some(witness) = fact.translation_witness() {
        assert_eq!(witness.native_bundle_digest, native.stable_digest());
        assert_eq!(witness.module_digest, native.module.stable_digest());
        assert!(matches!(
            witness.coverage,
            trust_wp_lib::trust_ir_body::NativeBodyWpTranslationCoverage::Untranslated { .. }
        ));
    }
    let replay = NativeTrustIrEvidenceIndex::from_bundle(&native);
    for _ in 0..2 {
        assert!(replay.accepts_wp_certificate(&public, &requested[0], row, request, proof as u32));
    }
    assert_eq!(native, before);
    assert_eq!(trust_ir::binary::serialize_module(&native.module).unwrap(), module_bytes);
    (public, requested, native, live)
}

#[test]
fn original_megabytes_bound_routes_and_replays() {
    accepted(0, 0);
}
#[test]
fn original_megabytes_full_width_cap_routes_and_replays() {
    accepted(0, 1);
}
#[test]
fn original_per_job_bound_routes_and_replays() {
    accepted(1, 0);
}
#[test]
fn original_split_bound_routes_and_replays() {
    accepted(2, 0);
}
#[test]
fn original_split_positive_routes_and_replays() {
    accepted(2, 1);
}

fn stale_rejected(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
    old: &FullVerificationRunWithFreshReceipts,
    request: u32,
    proof: u32,
) {
    let id = &requested[0].obligation_id;
    let row = &old.result().evidence[0];
    assert!(!old.checked_native_wp_proofs()[id].matches(public, native, &requested[0], row));
    assert!(!NativeTrustIrEvidenceIndex::from_bundle(native).accepts_wp_certificate(
        public,
        &requested[0],
        row,
        request,
        proof
    ));
}

fn assert_unproved(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
) {
    let live = run(public, requested, native);
    assert_eq!(live.result().summary.proved, 0, "{:#?}", live.result());
    assert!(live.checked_native_wp_proofs().is_empty());
    assert!(live.result().evidence.iter().all(|row| row.proof_strength.is_none()
        && row.artifacts.is_empty()
        && row.counterexample.is_none()));
}

fn semantic_failure(native: &NativeVerificationBundle, request: u32) {
    let admitted = trust_ir::ValidatedNativeBundle::new(native).unwrap();
    let actual = trust_wp_lib::trust_ir_body::verify_trust_ir_body_request_validated(
        &admitted,
        trust_ir::NativeRequestId::new(request),
    )
    .unwrap();
    assert_eq!(actual.result().status, trust_wp_lib::VerifyBundleStatus::Failed, "{actual:#?}");
    assert!(
        trust_wp_lib::trust_ir_body::replay_trust_ir_body_request_validated(
            &admitted,
            trust_ir::NativeRequestId::new(request),
            actual.result(),
            Some(actual.witness())
        )
        .is_err()
    );
}

#[test]
fn original_division_false_claim_cannot_reuse_a_checked_proof() {
    let (mut public, requested, mut native, old) = accepted(1, 0);
    let contract = public
        .contracts
        .iter_mut()
        .find(|c| Some(&c.contract_id) == requested[0].contract_id.as_ref())
        .unwrap();
    let predicate = trust_verifier_api::TrustSpecPredicate::new(
        trust_verifier_api::TrustSpecExpr::bool_literal(false),
        Vec::new(),
    );
    predicate.validate().unwrap();
    native.module.proof_obligations[0].formula =
        Some(trust_wp::trust_wp_native_formula_from_trust_spec(&predicate).unwrap());
    contract.predicate = predicate.into_contract_predicate().unwrap();
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
        .semantic_digest = proof_digest_from_canonical_sha256(&digest);
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    semantic_failure(&native, 7);
    stale_rejected(&public, &requested, &native, &old, 7, 0);
    assert_unproved(&public, &requested, &native);
}

#[test]
fn original_callee_division_by_zero_remains_owed_with_all_siblings() {
    let (public, requested, mut native, old) = accepted(2, 0);
    let original_requests = native.requests.clone();
    let callee = native.module.function_by_id_mut(trust_ir::FuncId::new(1)).unwrap();
    let node = callee.blocks[3]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, trust_ir::Inst::BinOp { op: trust_ir::BinOp::UDiv, .. }))
        .unwrap();
    let trust_ir::Inst::BinOp { rhs, .. } = &mut node.inst else { unreachable!() };
    *rhs = trust_ir::ValueId::new(24);
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_eq!(native.requests, original_requests);
    let one = trust_ir::interpret::InterpretValue::int(trust_ir::Ty::U64, 1).unwrap();
    assert!(
        trust_ir::interpret::Interpreter::with_module(&native.module)
            .execute_func(trust_ir::FuncId::new(0), vec![one.clone(), one])
            .is_err()
    );
    semantic_failure(&native, 11);
    stale_rejected(&public, &requested, &native, &old, 11, 0);
    assert_unproved(&public, &requested, &native);
}

#[test]
fn original_division_result_place_cannot_reuse_a_checked_proof() {
    let (public, requested, mut native, old) = accepted(2, 1);
    native.module.proof_obligations[1].formula.as_mut().unwrap().bindings[0].1.place =
        trust_ir::proof::ClausePlace::Param { index: 1 };
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    stale_rejected(&public, &requested, &native, &old, 12, 1);
    assert_unproved(&public, &requested, &native);
}

#[test]
fn original_division_unselected_metadata_still_binds_the_complete_input() {
    let (public, requested, mut native, old) = accepted(0, 0);
    let before = native.stable_digest();
    native
        .module
        .proof_obligations
        .last_mut()
        .unwrap()
        .description
        .push_str(" changed unselected sibling");
    rebind_native_bundle_module_digest(&mut native);
    native.validate().unwrap();
    assert_ne!(native.stable_digest(), before);
    stale_rejected(&public, &requested, &native, &old, 11, 0);
    // Metadata equivalence may admit a fresh native proof; it never reuses the
    // certificate bound to the complete original input above.
}
