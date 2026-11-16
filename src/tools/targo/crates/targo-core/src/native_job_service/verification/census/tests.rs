//! DATA-parser controls only. No fixture can issue native/session/kernel owners.
use super::*;
use trust_types::{CoverageFunctionIdentityInventory, MemorySummary};

fn scope() -> Scope<'static> {
    Scope {
        package: "native-pkg",
        krate: "native_crate",
        primary: true,
        session: "fresh-session",
    }
}
pub(in crate::native_job_service::verification) fn messages() -> Vec<TransportMessage> {
    let function = FunctionTransportResult {
        function: "native_crate::f".into(),
        package_name: Some("native-pkg".into()),
        crate_name: Some("native_crate".into()),
        primary_package: true,
        verification_session: "fresh-session".into(),
        runtime_checks: None,
        modeled_facts: vec![],
        stable_ids: vec!["row".into()],
        source_sha256: None,
        expanded_function_identity: None,
        results: vec![TransportObligationResult {
            assumes: vec![],
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: "overflow".into(),
            original_vc_snapshot: None,
            typed_kind: None,
            description: "deliberately unknown parser row".into(),
            location: None,
            outcome: Outcome::Unknown,
            solver: "none".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        }],
        proved: 0,
        failed: 0,
        unknown: 1,
        timed_out: 0,
        skipped: 0,
        runtime_checked: 0,
        cached: 0,
        total: 1,
        transport_budget: None,
    };
    vec![
        TransportMessage::FunctionResult(function),
        TransportMessage::CoverageSummary(CoverageTransportSummary {
            crate_name: "native_crate".into(),
            package_name: "native-pkg".into(),
            primary_package: true,
            verification_session: "fresh-session".into(),
            eligible: 1,
            processed: 1,
            function_identities: Some(CoverageFunctionIdentityInventory {
                schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.into(),
                eligible_functions: vec!["native_crate::f".into()],
                processed_functions: vec!["native_crate::f".into()],
            }),
            noted_stops: vec![],
            degraded_anchors: 0,
            memory: MemorySummary::default(),
        }),
        TransportMessage::CrateSummary(CrateTransportSummary {
            crate_name: "native_crate".into(),
            package_name: Some("native-pkg".into()),
            primary_package: true,
            verification_session: "fresh-session".into(),
            functions_analyzed: 1,
            functions_verified: 0,
            total_proved: 0,
            total_failed: 0,
            total_unknown: 1,
            total_timed_out: 0,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 1,
        }),
    ]
}
fn bytes(messages: &[TransportMessage]) -> Vec<u8> {
    messages
        .iter()
        .map(|message| {
            format!(
                "{}{}\n",
                trust_types::TRANSPORT_PREFIX,
                serde_json::to_string(message).unwrap()
            )
        })
        .collect::<String>()
        .into_bytes()
}

#[test]
fn complete_unknown_inventory_keeps_its_full_denominator_without_proof_credit() {
    let census = parse(&bytes(&messages()), &scope()).unwrap();
    assert_eq!(census.terminal.total_obligations, 1);
    assert_eq!(census.functions[0].results[0].outcome, Outcome::Unknown);
    assert_eq!(census.terminal.total_proved, 0);
}

#[test]
fn coverage_counts_cannot_replace_the_actual_function_population() {
    let mut rows = messages();
    let TransportMessage::CoverageSummary(coverage) = &mut rows[1] else {
        unreachable!()
    };
    let identities = coverage.function_identities.as_mut().unwrap();
    identities.eligible_functions[0] = "native_crate::different".into();
    identities.processed_functions[0] = "native_crate::different".into();
    assert!(parse(&bytes(&rows), &scope()).is_err());
    rows = messages();
    let TransportMessage::CrateSummary(terminal) = &mut rows[2] else {
        unreachable!()
    };
    terminal.total_unknown = 0;
    terminal.total_obligations = 0;
    assert!(parse(&bytes(&rows), &scope()).is_err());
}

#[test]
fn stale_session_missing_terminal_and_reordered_or_duplicate_inventory_refuse() {
    let rows = messages();
    let mut stale = scope();
    stale.session = "other-real-session";
    assert!(parse(&bytes(&rows), &stale).is_err());
    assert!(parse(&bytes(&rows[..2]), &scope()).is_err());
    let mut reordered = rows.clone();
    reordered.swap(0, 1);
    assert!(parse(&bytes(&reordered), &scope()).is_err());
    let mut repeated = rows.clone();
    repeated.insert(1, rows[0].clone());
    assert!(parse(&bytes(&repeated), &scope()).is_err());
    assert!(parse(&[], &scope()).is_err());
}

#[test]
fn duplicate_json_keys_do_not_acquire_a_second_interpretation() {
    let original = String::from_utf8(bytes(&messages())).unwrap();
    let substituted = original.replacen("\"total\":1", "\"total\":1,\"total\":0", 1);
    assert_ne!(substituted, original);
    assert!(parse(substituted.as_bytes(), &scope()).is_err());
}
