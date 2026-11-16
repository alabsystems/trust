//! Actual opaque-body and unsigned width-conversion captures. Serialized
//! fixture inputs are candidates, never live source or proof authority.

use super::*;

fn captured() -> (TrustContractBundle, Vec<TrustObligation>, trust_ir::NativeVerificationBundle) {
    let public =
        serde_json::from_str(include_str!("../../testdata/n4-opaque-source-stop/public.json"))
            .unwrap();
    let requested =
        serde_json::from_str(include_str!("../../testdata/n4-opaque-source-stop/requested.json"))
            .unwrap();
    let native =
        serde_json::from_str(include_str!("../../testdata/n4-opaque-source-stop/native.json"))
            .unwrap();
    (public, requested, native)
}

fn captured_widthconv()
-> (TrustContractBundle, Vec<TrustObligation>, trust_ir::NativeVerificationBundle) {
    (
        serde_json::from_str(include_str!("../../testdata/widthconv-shift-mask/public.json"))
            .unwrap(),
        serde_json::from_str(include_str!("../../testdata/widthconv-shift-mask/requested.json"))
            .unwrap(),
        serde_json::from_str(include_str!("../../testdata/widthconv-shift-mask/native.json"))
            .unwrap(),
    )
}

fn marker<'a>(
    public: &TrustContractBundle,
    requested: &'a [TrustObligation],
) -> &'a TrustObligation {
    let mut markers =
        requested.iter().filter(|row| is_raw_source_postcondition(public, row) == Ok(true));
    let marker = markers.next().expect("actual raw authored question");
    assert!(markers.next().is_none());
    marker
}

fn adapter() -> TrustMcVerifierApiAdapter {
    TrustMcVerifierApiAdapter::new(
        TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
    )
}

fn has_structural_origin(evidence: &ObligationEvidence) -> bool {
    evidence.diagnostics.iter().any(|row| {
        row == trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
            || row == trust_verifier_api::NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
    })
}

#[test]
fn captured_opaque_raw_source_retains_body_lowering_refusal() {
    let (public, requested, native) = captured();
    assert!(
        native.module.functions.iter().any(|function| function.blocks.iter().any(|block| {
            block.body.iter().any(|node| matches!(node.inst, trust_ir::Inst::Assume { .. }))
        })),
        "the captured program really contains a body Assume"
    );
    let id = &marker(&public, &requested).obligation_id;
    let evidence = adapter().evidence_from_native_trust_ir_bundle(&public, &requested, &native);
    let row = evidence.iter().find(|row| &row.obligation_id == id).unwrap();
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
    assert!(row.proof_strength.is_none() && row.artifacts.is_empty());
    assert!(row.counterexample.is_none());
    assert!(row.decline.is_none(), "{row:?}");
    assert!(
        row.diagnostics.iter().any(|diagnostic| diagnostic
            .contains("cannot bypass native body lowering/admission diagnostics")),
        "an undefined return must remain a terminal lowering refusal: {row:?}"
    );
    assert!(
        row.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.starts_with("native body lowering diagnostic: ")),
        "retain the actual typed lowering cause rather than only a generic stop: {row:?}"
    );
}

#[test]
fn captured_raw_source_false_body_assumption_never_becomes_an_mc_proof() {
    let (public, requested, mut native) = captured();
    let source = marker(&public, &requested);
    let function = &mut native.module.functions[0];
    let false_value = function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .find_map(|node| {
            matches!(
                node.inst,
                trust_ir::Inst::Const { value: trust_ir::Constant::Bool(false), .. }
            )
            .then(|| node.results[0])
        })
        .expect("captured Boolean false constant");
    let cond = function
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find_map(|node| {
            if let trust_ir::Inst::Assume { cond } = &mut node.inst { Some(cond) } else { None }
        })
        .expect("captured body assumption");
    *cond = false_value;
    let digest = native.module.stable_digest();
    native.trust_ir_module_digest = digest;
    for node in &mut native.lineage.nodes {
        node.target_module = digest;
    }
    native.validate().expect("false Assume remains valid IR with exact module/lineage binding");

    // Select only the raw question: its decline must precede any MC solve,
    // regardless of whether the body's assumption makes it unreachable.
    let outcome = adapter().evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
        &public,
        std::slice::from_ref(source),
        &native,
        None,
        None,
    );
    assert_eq!(outcome.evidence.len(), 1);
    let row = &outcome.evidence[0];
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
    assert!(row.decline.is_none(), "{row:?}");
    assert!(
        row.proof_strength.is_none() && row.artifacts.is_empty() && row.counterexample.is_none()
    );
    assert!(outcome.fresh_exact_direct_receipts.is_empty());
    assert!(outcome.fresh_whole_function_receipts.is_empty());
}

#[test]
fn captured_u64_call_summary_limit_is_a_capability_decline_without_mc_authority() {
    let public: TrustContractBundle = serde_json::from_str(include_str!(
        "../../testdata/intbound-u64/clamp_unsigned_to_width/public.json"
    ))
    .unwrap();
    let requested: Vec<TrustObligation> = serde_json::from_str(include_str!(
        "../../testdata/intbound-u64/clamp_unsigned_to_width/requested.json"
    ))
    .unwrap();
    let native: trust_ir::NativeVerificationBundle = serde_json::from_str(include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
        "/../../first-party/trust-wp/crates/trust-wp-lib/tests/body_contract/fixtures/u64_calls/clamp_unsigned_to_width.json"
    ))).unwrap();
    let source = marker(&public, &requested);
    let outcome = adapter().evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
        &public,
        std::slice::from_ref(source),
        &native,
        None,
        None,
    );
    assert_eq!(outcome.evidence.len(), 1);
    let row = &outcome.evidence[0];
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
    assert_eq!(row.decline, Some(trust_verifier_api::DeclineClass::Capability), "{row:?}");
    assert!(row.proof_strength.is_none() && row.artifacts.is_empty());
    assert!(row.counterexample.is_none() && !has_structural_origin(row));
    assert!(outcome.fresh_exact_direct_receipts.is_empty());
    assert!(outcome.fresh_whole_function_receipts.is_empty());
}

#[test]
fn captured_modeled_raw_source_body_assumptions_allow_capability_fallback() {
    check_modeled_raw_source_decline(false);
}

#[test]
fn captured_modeled_raw_source_false_assumption_has_no_mc_proof() {
    check_modeled_raw_source_decline(true);
}

fn check_modeled_raw_source_decline(false_assume: bool) {
    let (public, requested, mut native) = captured_widthconv();
    let raw: Vec<_> = requested
        .into_iter()
        .filter(|row| is_raw_source_postcondition(&public, row) == Ok(true))
        .collect();
    assert_eq!(raw.len(), 2, "retain both original authored postconditions");
    if false_assume {
        let function = &mut native.module.functions[0];
        let false_value = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| {
                matches!(
                    node.inst,
                    trust_ir::Inst::Const { value: trust_ir::Constant::Bool(false), .. }
                )
                .then(|| node.results[0])
            })
            .expect("captured Boolean false constant");
        let cond = function
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
            .find_map(|node| match &mut node.inst {
                trust_ir::Inst::Assume { cond } => Some(cond),
                _ => None,
            })
            .expect("captured body assumption");
        *cond = false_value;
        let digest = native.module.stable_digest();
        native.trust_ir_module_digest = digest;
        for node in &mut native.lineage.nodes {
            node.target_module = digest;
        }
    }
    native.validate().unwrap();
    assert!(trust_ir_build::validate_module(&native.module).is_empty());
    let outcome = adapter().evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
        &public, &raw, &native, None, None,
    );
    assert_eq!(outcome.evidence.len(), 2);
    for row in &outcome.evidence {
        assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
        assert_eq!(row.decline, Some(trust_verifier_api::DeclineClass::Capability), "{row:?}");
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty());
        assert!(row.counterexample.is_none() && !has_structural_origin(row));
    }
    assert!(outcome.fresh_exact_direct_receipts.is_empty());
    assert!(outcome.fresh_whole_function_receipts.is_empty());
}

#[test]
fn captured_raw_source_capability_requires_semantically_valid_body() {
    let (public, requested, mut native) = captured();
    let source = marker(&public, &requested);
    let cond = native.module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find_map(|node| {
            if let trust_ir::Inst::Assume { cond } = &mut node.inst { Some(cond) } else { None }
        })
        .expect("captured body assumption");
    *cond = trust_ir::value::ValueId::new(u32::MAX);
    let digest = native.module.stable_digest();
    native.trust_ir_module_digest = digest;
    for node in &mut native.lineage.nodes {
        node.target_module = digest;
    }
    native.validate().expect("transport and lineage are valid after rebinding");
    assert!(
        !trust_ir_build::validate_module(&native.module).is_empty(),
        "the shared semantic validator must reject the nonexistent SSA value"
    );
    let evidence = adapter().evidence_from_native_trust_ir_bundle(&public, &requested, &native);
    let row = evidence.iter().find(|row| row.obligation_id == source.obligation_id).unwrap();
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
    assert!(
        row.decline.is_none() && row.proof_strength.is_none() && row.artifacts.is_empty(),
        "semantic invalidity must be terminal, before raw-clause capability: {row:?}"
    );
}

#[test]
fn captured_raw_source_body_assumptions_cannot_hide_replay_premises() {
    let (public, requested, mut native) = captured();
    let source = marker(&public, &requested);
    let request_id = canonical_u32_metadata_value(
        obligation_metadata_value(source, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY).unwrap(),
    )
    .unwrap();
    let trust_ir::NativeVerificationRequest::TrustMc(request) = native.requests.iter_mut().find(
        |request| matches!(request, trust_ir::NativeVerificationRequest::TrustMc(row) if row.id.index() == request_id),
    ).unwrap() else { unreachable!() };
    request.provenance.replay_context.atoms.push(trust_ir::NativeReplayAtom::assumption(
        trust_ir::NativeReplayAtomId::new(1_000_000),
        trust_ir::ProofFormula::smtlib2("false", "Bool"),
    ));
    native.validate().expect("extra replay premise is structurally valid, but not admitted");
    let context =
        NativeTrustIrPublicClaimBindingContext::build(&public, &requested, &native).unwrap();
    assert_eq!(
        validate_native_trust_ir_public_claim_binding(&public, source, &native, &context).unwrap(),
        NativePublicClaimKind::RawPostcondition {
            admission_stop: Some(NativeRawPostconditionStop::ReplayAssumptions),
        },
    );
    let evidence = adapter().evidence_from_native_trust_ir_bundle(&public, &requested, &native);
    let row = evidence.iter().find(|row| row.obligation_id == source.obligation_id).unwrap();
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:?}");
    assert!(row.decline.is_none() && row.proof_strength.is_none() && row.artifacts.is_empty());
    assert!(
        has_structural_origin(row),
        "the replay premise remains a terminal admission refusal: {row:?}"
    );
}

#[test]
fn captured_raw_source_body_assumptions_do_not_hide_invalid_module_or_lineage() {
    for mutation in ["module", "lineage"] {
        let (public, requested, mut native) = captured();
        let source = marker(&public, &requested);
        match mutation {
            "module" => native.module.functions.push(native.module.functions[0].clone()),
            "lineage" => {
                for request in &mut native.requests {
                    if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
                        request.lineage_roots.push(trust_ir::ProofLineageId::new(u32::MAX));
                    }
                }
            }
            _ => unreachable!(),
        }
        assert!(native.validate().is_err(), "{mutation} must fail shared input validation");
        let evidence = adapter().evidence_from_native_trust_ir_bundle(&public, &requested, &native);
        let row = evidence.iter().find(|row| row.obligation_id == source.obligation_id).unwrap();
        assert_eq!(row.status, EvidenceStatus::Unsupported, "{mutation}: {row:?}");
        assert!(
            row.decline.is_none() && row.proof_strength.is_none() && row.artifacts.is_empty(),
            "{mutation}: {row:?}"
        );
    }
}

#[test]
fn captured_raw_source_assumptions_cannot_hide_late_replay_identity_errors() {
    for mutation in ["formula", "assertion", "span"] {
        let (public, requested, mut native) = captured();
        let source = marker(&public, &requested);
        let context = NativeTrustIrPublicClaimBindingContext::build(&public, &requested, &native)
            .expect("complete captured inventory");
        let request_id = canonical_u32_metadata_value(
            obligation_metadata_value(source, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
                .unwrap(),
        )
        .unwrap();
        let proof = canonical_u32_metadata_value(
            obligation_metadata_value(
                source,
                TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
            )
            .unwrap(),
        )
        .unwrap();
        let request_index = context.trust_mc_requests[&request_id][0];
        let atom_index = context.replay_assertions[&(request_index, proof)][0];
        let trust_ir::NativeVerificationRequest::TrustMc(request) =
            &mut native.requests[request_index]
        else {
            panic!("actual trust-mc request")
        };
        let atom = &mut request.provenance.replay_context.atoms[atom_index];
        match mutation {
            "formula" => atom.formula.payload.push_str(" foreign"),
            "assertion" => {
                assert!(atom.assertion_id.is_some());
                atom.assertion_id = None;
            }
            "span" => {
                assert!(atom.span.is_some());
                atom.span = None;
            }
            _ => unreachable!(),
        }
        let error =
            validate_native_trust_ir_public_claim_binding(&public, source, &native, &context)
                .expect_err("late identity failure must beat the earlier structural candidate");
        assert!(error.contains("does not exactly project"), "{mutation}: {error}");
        let evidence = adapter().evidence_from_native_trust_ir_bundle(&public, &requested, &native);
        let row = evidence.iter().find(|row| row.obligation_id == source.obligation_id).unwrap();
        assert_ne!(row.status, EvidenceStatus::Proved);
        assert!(row.decline.is_none(), "invalid {mutation} cannot acquire fallback eligibility");
        assert!(
            !has_structural_origin(row),
            "invalid {mutation} gained a structural origin: {row:?}"
        );
    }
}

#[test]
fn captured_raw_source_expired_deadline_remains_timeout() {
    let (public, requested, native) = captured();
    let id = &marker(&public, &requested).obligation_id;
    let evidence = adapter().evidence_from_native_trust_ir_bundle_with_deadline(
        &public,
        &requested,
        &native,
        Some(Instant::now() - std::time::Duration::from_secs(1)),
    );
    let row = evidence.iter().find(|row| &row.obligation_id == id).unwrap();
    assert_eq!(row.status, EvidenceStatus::Timeout, "{row:?}");
    assert!(!has_structural_origin(row), "a clock stop is not a deterministic structural stop");
}
