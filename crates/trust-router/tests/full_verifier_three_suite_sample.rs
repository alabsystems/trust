//! Cross-crate sample for the active v6/D3 full-verifier fleet.
//!
//! The three primary suites are TrustMC, TrustVC, and TY: every routed
//! obligation's primary is one of them. Since the 2026-11-03 native WP
//! reintegration (docs/DECISION_QUEUE.md, "one program semantics; native WP
//! reintegration") TrustWP is a required engine again, but only as the
//! body-aware deductive *fallback* for postconditions: it owns no primary
//! route, and its historical suite metadata cannot claim one.

use trust_router::FullVerificationEngine;
use trust_router::full_verification::{
    FullVerificationPolicy, FullVerificationRunResultExt,
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, required_native_engines,
};
use trust_verifier_api::{
    BundleSubject, EngineCapability, EngineKind, EvidenceStatus, MetadataEntry, ObligationKind,
    ReasoningKind, SourceLocation, SupportLevel, TrustContractBundle, TrustObligation,
    VerificationRunStatus, VerifierExecutionContext,
};

fn obligation(kind: ObligationKind, id: &str) -> TrustObligation {
    TrustObligation {
        obligation_id: id.to_string(),
        kind,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "v6/D3 routing sample".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    }
}

fn bundle(obligations: Vec<TrustObligation>) -> TrustContractBundle {
    let mut bundle = TrustContractBundle::empty(
        "v6-d3-three-suite-sample",
        BundleSubject::Function {
            crate_name: "sample".to_string(),
            path: "sample::routing".to_string(),
        },
    );
    bundle.obligations = obligations;
    bundle
}

#[test]
fn required_native_fleet_is_the_three_primary_suites_and_the_trust_wp_postcondition_fallback() {
    let engines = required_native_engines();
    let names = engines.iter().map(|engine| engine.manifest().name.clone()).collect::<Vec<_>>();
    assert_eq!(names, ["trust-vc", "trust-mc", "ty", "trust-wp"]);

    // TrustWP is in the fleet only as the postcondition deductive fallback
    // (`routing::fallback_route`). Its manifest must not advertise any other
    // obligation kind or reasoning mode: a wider manifest would let it be
    // offered obligations no fallback route admits. That it is never a
    // primary is pinned by the routing sample below.
    let wp = engines
        .iter()
        .find(|engine| engine.manifest().name == "trust-wp")
        .expect("trust-wp is in the required fleet")
        .manifest();
    assert_eq!(wp.kind, EngineKind::Deductive);
    assert_eq!(wp.proof_modes, [ReasoningKind::Deductive]);
    assert_eq!(
        wp.capabilities,
        [EngineCapability {
            obligation_kind: ObligationKind::Postcondition,
            support: SupportLevel::Supported,
        }]
    );
}

#[test]
fn active_three_suite_routes_cover_the_v6_d3_split_fail_closed() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let bundle = bundle(vec![
        obligation(ObligationKind::Precondition, "pre"),
        obligation(ObligationKind::Postcondition, "post"),
        obligation(ObligationKind::LoopInvariant, "loop"),
        obligation(ObligationKind::Termination, "termination"),
        obligation(ObligationKind::Refinement, "refinement"),
        obligation(ObligationKind::TemporalSafety, "temporal"),
    ]);

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("v6-d3-three-suite-sample"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(result.summary.unsupported, 6, "{result:#?}");
    assert!(result.evidence.iter().all(|evidence| {
        evidence.status == EvidenceStatus::Unsupported
            && evidence.proof_strength.is_none()
            && evidence.artifacts.is_empty()
    }));

    let routed = result
        .full_verification_obligation_evidence()
        .into_iter()
        .map(|row| {
            (
                row.obligation_id,
                row.primary_suite.expect("every sample obligation has a primary suite"),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(routed["pre"], "trust-mc");
    assert_eq!(routed["post"], "trust-mc");
    assert_eq!(routed["loop"], "trust-mc");
    assert_eq!(routed["termination"], "trust-mc");
    assert_eq!(routed["refinement"], "trust-vc");
    assert_eq!(routed["temporal"], "ty");
    assert!(routed.values().all(|suite| suite != "trust-wp"));

    if let Some(path) = std::env::var_os("TRUST_THREE_SUITE_MANIFEST_OUT") {
        let manifest = result.to_manifest();
        manifest.validate_derived_state().expect("sample manifest has coherent derived state");
        let bytes = serde_json::to_vec_pretty(&manifest).expect("serialize sample manifest");
        std::fs::write(path, bytes).expect("write requested three-suite manifest");
    }
}

#[test]
fn required_native_fleet_rejects_a_missing_active_engine() {
    let mut engines = required_native_engines();
    engines.retain(|engine| engine.manifest().name != "ty");
    let engine = FullVerificationEngine::new(engines, FullVerificationPolicy::default());
    let result = engine.verify_bundle(
        &bundle(vec![obligation(ObligationKind::TemporalSafety, "missing-ty")]),
        &VerifierExecutionContext::new("missing-active-engine"),
    );

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    // The refusal must name the removed engine in its missing list. The list
    // is checked element-wise: without `trust-build`, trust-vc advertises only
    // Experimental capabilities and is legitimately reported missing alongside
    // ty, so a literal "missing: ty" match would be feature-dependent.
    assert!(
        result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("requires native trust-vc, trust-mc, and TY engines")
                && diagnostic
                    .rsplit("missing: ")
                    .next()
                    .is_some_and(|list| list.split(", ").any(|name| name == "ty"))
        }),
        "{:#?}",
        result.evidence[0].diagnostics
    );
}

#[test]
fn historical_trust_wp_suite_metadata_is_readable_but_cannot_change_ownership() {
    let engine = FullVerificationEngine::with_required_native_engines();
    let mut post = obligation(ObligationKind::Postcondition, "historical-post");
    post.metadata.push(MetadataEntry {
        key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
        value: "trust-wp".to_string(),
    });
    let bundle = bundle(vec![post]);

    let result =
        engine.verify_bundle(&bundle, &VerifierExecutionContext::new("historical-trust-wp-suite"));

    assert_eq!(result.status, VerificationRunStatus::Inconclusive, "{result:#?}");
    assert_eq!(result.summary.proved, 0);
    assert_eq!(result.summary.unsupported, 1);
    let row = &result.full_verification_obligation_evidence()[0];
    assert_eq!(row.primary_suite.as_deref(), Some("trust-mc"));
    assert!(!row.has_accepted_proof());
}
