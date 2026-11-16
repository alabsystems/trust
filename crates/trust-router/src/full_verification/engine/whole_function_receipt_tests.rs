//! Real native solves through the router; synthetic source fixture, not a
//! claim that a rustc source importer or the actual compiler was executed.

use super::*;

fn fixture() -> (TrustContractBundle, NativeVerificationBundle, trust_ir::SourceGenerationAuthority)
{
    let path = "demo::router_native_checked_branch";
    let id = format!(
        "vc:{}:assertion:panic-freedom:0",
        trust_types::canonical_artifact_id_component(path)
    );
    let mut bundle = TrustContractBundle::empty(
        "whole-receipt-router",
        BundleSubject::Function { crate_name: "demo".into(), path: path.into() },
    );
    let mut row = native_trust_ir_obligation("trust-mc", 7, 0, ObligationKind::Assertion, None);
    row.obligation_id = id.clone();
    row.source = router_native_source_location(18);
    let context = trust_verifier_api::ObligationContext::new(
        trust_verifier_api::ObligationProducer::CompilerMirExtract,
        trust_verifier_api::ObligationOrigin::VerificationCondition {
            vc_kind: "panic_freedom".into(),
            vc_index: 0,
            formula_schema: None,
        },
    )
    .with_function(trust_verifier_api::FunctionContext {
        crate_name: "demo".into(),
        path: path.into(),
    });
    row.metadata.extend([
        context.to_metadata_entry().unwrap(),
        MetadataEntry {
            key: "trust-trust-mc.panic-freedom-obligation.v1".into(),
            value: "enabled".into(),
        },
        MetadataEntry { key: "trust.vc.kind".into(), value: "panic_freedom".into() },
        MetadataEntry {
            key: "trust.mir-extract.source.digest.sha256".into(),
            value: "61".repeat(32),
        },
        MetadataEntry { key: "trust.vc.digest.sha256".into(), value: "22".repeat(32) },
    ]);
    bundle.obligations.push(row);
    let digest = proof_digest_from_canonical_sha256(
        &bundle.canonical_obligation_semantic_digest_sha256(&bundle.obligations[0]).unwrap(),
    );
    let mut native = native_trust_mc_safe_trust_ir_bundle();
    native.module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let assertion_id = trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
        format!("trust-assertion:{id}").as_bytes(),
    ));
    let formula = router_native_obligation_source_formula(&id, 18);
    let proof = &mut native.module.proof_obligations[0];
    let file = proof.source.as_ref().unwrap().range.unwrap().file;
    proof.source = Some(router_native_obligation_source_identity(proof.id, &id, file, 18, digest));
    proof.formula = Some(formula.clone());
    let source = &mut native.compiler_facts.obligation_sources[0];
    source.public_obligation_id = id;
    source.assertion_id = Some(assertion_id);
    for request in &mut native.requests {
        if let NativeVerificationRequest::TrustMc(request) = request {
            for atom in &mut request.provenance.replay_context.atoms {
                if atom.kind == trust_ir::NativeReplayAtomKind::Assertion {
                    atom.formula = formula.clone();
                    atom.assertion_id = Some(assertion_id);
                    atom.payload_digest = atom.expected_payload_digest();
                }
            }
        }
    }
    rebind_native_bundle_module_digest(&mut native);
    native.validate().expect("exact synthetic native/public pair");
    // This fixture explicitly models the preexisting audited source issuer;
    // no public metadata or decoded module by itself mints the receipt.
    let source = whole_function_fixture_source_authority(&mut native);
    (bundle, native, source)
}

fn dispatch(
    bundle: &TrustContractBundle,
    native: &NativeVerificationBundle,
    source: &trust_ir::SourceGenerationAuthority,
    context: &VerifierExecutionContext,
) -> (VerificationRunResult, LiveVerificationReceiptBatch) {
    let engine = FullVerificationEngine::with_required_native_engines();
    let live = engine
        .verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts(
            bundle,
            &bundle.obligations,
            native,
            source,
            context,
        );
    assert!(live.fresh_exact_direct_chc_pdr_receipts().is_empty(), "distinct family");
    let (run, receipts) = live.into_parts();
    assert_eq!(run.summary.proved, 1, "{run:#?}");
    assert_eq!(receipts.fresh_whole_function_chc_pdr_receipts().len(), 1, "{run:#?}");
    (run, receipts)
}

#[test]
fn whole_function_router_retains_exact_affine_capability_and_refuses_row_or_native_mutation() {
    let (bundle, native, source) = fixture();
    let context = VerifierExecutionContext::new("whole-router")
        .with_deadline(Instant::now() + Duration::from_secs(60));
    let (run, mut batch) = dispatch(&bundle, &native, &source, &context);
    let row = &bundle.obligations[0];
    let receipt =
        batch.take_fresh_whole_function_chc_pdr_receipts().remove(&row.obligation_id).unwrap();
    assert!(batch.take_fresh_whole_function_chc_pdr_receipts().is_empty());
    let evidence = &run.evidence[0];
    let proof = batch
        .authorizes_fresh_whole_function_chc_pdr_receipt(&receipt, &native, &source, row, evidence)
        .unwrap();
    assert_eq!(proof.assurance, AssuranceLevel::SmtBacked);
    let foreign_dispatch =
        crate::full_verification::native_trust_ir::LiveVerificationDispatchSeal::mint(
            &run, &bundle, &context,
        );
    assert_eq!(foreign_dispatch.source_run(), &run, "byte-identical public run");
    assert!(
        receipt.authorizes_accepted_evidence(row, evidence, &foreign_dispatch).is_err(),
        "identical public contents do not recreate the original private dispatch"
    );
    for kind in 0..5 {
        let mut changed = evidence.clone();
        match kind {
            0 => changed.status = EvidenceStatus::Unknown,
            1 => changed.diagnostics.push("changed".into()),
            2 => changed.proof_strength = Some(ProofStrength::certified(ReasoningKind::Chc)),
            3 => changed.evidence_id.push_str("-changed"),
            _ => changed.artifacts[0].uri.push_str("-changed"),
        }
        assert!(
            batch
                .authorizes_fresh_whole_function_chc_pdr_receipt(
                    &receipt, &native, &source, row, &changed
                )
                .is_err(),
            "case {kind}"
        );
    }
    let cloned = native.clone();
    assert!(
        batch
            .authorizes_fresh_whole_function_chc_pdr_receipt(
                &receipt, &cloned, &source, row, evidence
            )
            .is_err()
    );
    let (_, other_native, other_source) = fixture();
    assert!(
        batch
            .authorizes_fresh_whole_function_chc_pdr_receipt(
                &receipt,
                &native,
                &other_source,
                row,
                evidence
            )
            .is_err()
    );
    // A genuine current source token can reauthenticate equal full contents.
    // This does not remint the receipt or change its original dispatch.
    assert!(source.authorizes_bundle(&native));
    assert!(other_source.authorizes_bundle(&other_native));
    assert_eq!(native, other_native);
    assert!(
        batch
            .authorizes_fresh_whole_function_chc_pdr_receipt(
                &receipt,
                &other_native,
                &other_source,
                row,
                evidence,
            )
            .is_ok()
    );
    assert!(
        batch
            .authorizes_fresh_whole_function_chc_pdr_receipt(
                &receipt,
                &other_native,
                &source,
                row,
                evidence,
            )
            .is_err(),
        "mismatched native/source pair"
    );
    let mut wrong_row = row.clone();
    wrong_row.metadata.push(MetadataEntry { key: "different".into(), value: "1".into() });
    assert!(
        batch
            .authorizes_fresh_whole_function_chc_pdr_receipt(
                &receipt, &native, &source, &wrong_row, evidence
            )
            .is_err()
    );
}

#[test]
fn whole_function_router_rejects_different_dispatch_and_cancellation() {
    let (bundle, native, source) = fixture();
    let context = VerifierExecutionContext::new("whole-same-context")
        .with_deadline(Instant::now() + Duration::from_secs(60));
    let (first, mut a) = dispatch(&bundle, &native, &source, &context);
    let (second, b) = dispatch(&bundle, &native, &source, &context);
    let row = &bundle.obligations[0];
    let receipt =
        a.take_fresh_whole_function_chc_pdr_receipts().remove(&row.obligation_id).unwrap();
    assert!(
        a.authorizes_fresh_whole_function_chc_pdr_receipt(
            &receipt,
            &native,
            &source,
            row,
            &first.evidence[0]
        )
        .is_ok()
    );
    assert!(
        b.authorizes_fresh_whole_function_chc_pdr_receipt(
            &receipt,
            &native,
            &source,
            row,
            &second.evidence[0]
        )
        .is_err()
    );
    context.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
    assert!(
        a.authorizes_fresh_whole_function_chc_pdr_receipt(
            &receipt,
            &native,
            &source,
            row,
            &first.evidence[0]
        )
        .is_err()
    );
}

#[test]
fn whole_function_router_never_mints_for_ordinary_late_or_cancelled_entry() {
    let (bundle, native, source) = fixture();
    let engine = FullVerificationEngine::with_required_native_engines();
    let ordinary = engine.verify_bundle_with_native_trust_ir_bundle_and_fresh_receipts(
        &bundle,
        &native,
        &VerifierExecutionContext::new("ordinary-whole"),
    );
    assert!(ordinary.fresh_whole_function_chc_pdr_receipts().is_empty());
    let late = VerifierExecutionContext::new("late-whole")
        .with_deadline(Instant::now() - Duration::from_secs(1));
    let cancelled = VerifierExecutionContext::new("cancelled-whole");
    cancelled.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
    for context in [late, cancelled] {
        let result = engine
            .verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts(
                &bundle,
                &bundle.obligations,
                &native,
                &source,
                &context,
            );
        assert!(result.fresh_whole_function_chc_pdr_receipts().is_empty());
    }
}

/// Trust (C1, 2026-11-06): the router's facts entry carries the compiler's live
/// source reference facts down every hop to trust-bmc. With facts bound to this
/// exact bundle the row proves and the whole-function receipt binds (the
/// pre-solve and solved rows came from the same facts translation). With facts
/// bound to ANOTHER live bundle the TrustMC row fails closed with trust-bmc's
/// refusal: a hop that dropped the facts (`NativeLiveSource::authority_only`)
/// would instead prove the row through the authority-only solve.
#[test]
fn source_reference_facts_reach_trust_bmc_through_every_router_hop() {
    let (bundle, native, source) = fixture();
    let context = VerifierExecutionContext::new("router-source-reference-facts")
        .with_deadline(Instant::now() + Duration::from_secs(60));
    let engine = FullVerificationEngine::with_required_native_engines();

    let facts = NativeSourceReferenceFacts::from_live_source_lowering(
        &native,
        &source,
        Vec::new(),
        Vec::new(),
    )
    .expect("an exact empty claim set binds to this live bundle");
    let (run, receipts) = engine
        .verify_obligations_with_native_trust_ir_bundle_and_source_reference_facts_and_live_receipts(
            &bundle,
            &bundle.obligations,
            &native,
            &source,
            &facts,
            &context,
        )
        .into_parts();
    assert_eq!(run.summary.proved, 1, "{run:#?}");
    assert_eq!(receipts.fresh_whole_function_chc_pdr_receipts().len(), 1, "{run:#?}");

    let (_, other_native, other_source) = fixture();
    let foreign = NativeSourceReferenceFacts::from_live_source_lowering(
        &other_native,
        &other_source,
        Vec::new(),
        Vec::new(),
    )
    .expect("facts bound to the other live bundle");
    let (run, receipts) = engine
        .verify_obligations_with_native_trust_ir_bundle_and_source_reference_facts_and_live_receipts(
            &bundle,
            &bundle.obligations,
            &native,
            &source,
            &foreign,
            &context,
        )
        .into_parts();
    assert_eq!(run.summary.proved, 0, "{run:#?}");
    assert!(receipts.fresh_whole_function_chc_pdr_receipts().is_empty());
    assert!(
        run.evidence.iter().flat_map(|evidence| &evidence.diagnostics).any(|diagnostic| diagnostic
            .contains("source reference facts do not authorize this exact live native bundle")),
        "the refusal must come from trust-bmc's facts entry: {run:#?}"
    );
}
