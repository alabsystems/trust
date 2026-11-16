// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Producer attribution controls: these exercise the actual transport,
// publication, alias-elision and unit/package accounting paths.

fn publication_stop_identity(row: &mut VerificationResult, package: &str, n: u32) {
    let mut evidence = structured_transport_evidence(row).expect("structured fixture");
    evidence.identity = Some(trust_types::obligation_identity::ObligationIdentity {
        key: trust_types::obligation_identity::obligation_key(
            &row.function,
            &trust_types::obligation_identity::local_id(&row.kind, "none:test", n),
        ),
        package: package.into(),
        function_source_sha256: Some("a".repeat(64)),
        expanded_function_identity: None,
    });
    crate::types::replace_structured_transport_evidence(row, &evidence).unwrap();
}

fn publication_stop_a_like_row() -> VerificationResult {
    let mut transport = native_full_verifier_transport();
    transport.solver = "trust-exact-source-clause-discharge".into();
    transport.proof_evidence = None;
    let native = transport.native_trust_ir.as_mut().unwrap();
    native.present = false;
    native.artifacts.clear();
    native.diagnostics.clear();
    transport.reason = Some("source clause discharged; no attachable envelope".into());
    let mut row = transport_to_verification_result("crate::source_clause", &transport, None, None);
    publication_stop_identity(&mut row, "demo", 0);
    row
}

#[test]
fn publication_stop_no_envelope_preserves_original_verdict_without_proof_credit() {
    use trust_types::determinism::{StopCause, UnitOutcome};
    let mut rows = vec![publication_stop_a_like_row()];
    let boundary = crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, VerificationOutcome::Unknown);
    let reason = rows[0].reason.as_deref().unwrap();
    assert!(reason.contains("downgraded before publication"));
    assert!(reason.contains("source clause discharged; no attachable envelope"));
    assert_eq!(crate::determinism_report::row_stop_cause(&rows[0]), StopCause::Solved);
    assert_eq!(boundary.withheld_relabelled, 1);
    assert_eq!(boundary.published_favorable, 0);
    assert_eq!(
        crate::determinism_report::UnitDeterminism::of_rows(&rows, &[]).outcome,
        UnitOutcome::Measured
    );
    assert!(!authenticated_proved_row_has_publication_evidence(&rows[0], None));
    let once = rows.clone();
    crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(
        publication_projection_is_byte_identical(&rows, &once),
        Some(true),
        "normalizing twice must not alter the prior reason or promote it"
    );
}

#[test]
fn publication_stop_demotion_preserves_explicit_and_nested_stops() {
    use trust_types::determinism::{StopCause, StopItem, UnitOutcome};
    for cause in [
        StopCause::Solved,
        StopCause::Steps,
        StopCause::Effort,
        StopCause::Unsupported,
        StopCause::WallBackstop,
        StopCause::RssBackstop,
        StopCause::SolverFault,
        StopCause::AdmissionRefused,
        StopCause::Unclassified,
    ] {
        for nested in [false, true] {
            let mut row = publication_stop_a_like_row();
            row.reason = Some(if nested {
                format!("outer ({}) [stop:solved]", cause.stamp("original lane"))
            } else {
                cause.stamp("original lane")
            });
            let expected = trust_types::determinism::StopCause::of_outcome(
                trust_types::Outcome::Proved,
                row.reason.as_deref(),
            );
            let prior = row.reason.clone().unwrap();
            let mut rows = vec![row];
            crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
            assert_eq!(rows[0].outcome, VerificationOutcome::Unknown);
            assert!(rows[0].reason.as_deref().unwrap().contains(&prior));
            assert_eq!(
                crate::determinism_report::row_stop_cause(&rows[0]),
                expected,
                "{cause:?}, nested={nested}"
            );
            assert_eq!(
                crate::determinism_report::UnitDeterminism::of_rows(&rows, &[]).outcome,
                UnitOutcome::from_causes([expected])
            );
        }
    }
    let mut row = publication_stop_a_like_row();
    row.reason = Some(
        StopCause::WallBackstop.stamp_item(StopItem::StrictCheckCancelled, "inner cancellation"),
    );
    let mut rows = vec![row];
    crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(
        crate::determinism_report::row_stop_item(&rows[0]),
        Some(StopItem::StrictCheckCancelled)
    );
}

#[test]
fn publication_stop_typed_unsupported_detail_survives_the_transport_producer() {
    use trust_types::determinism::StopCause;
    for cause in [
        StopCause::Steps,
        StopCause::WallBackstop,
        StopCause::RssBackstop,
        StopCause::SolverFault,
        StopCause::AdmissionRefused,
        StopCause::Unclassified,
    ] {
        let row = typed_transport_result(
            "crate::unsupported",
            VcKind::UnsupportedMir {
                kind: "source gap".into(),
                detail: cause.stamp("typed original detail"),
            },
            "ay",
            trust_types::Outcome::Proved,
        );
        assert_eq!(row.outcome, VerificationOutcome::Unknown);
        assert_eq!(crate::determinism_report::row_stop_cause(&row), cause);
        assert_eq!(
            StopCause::from_reason(row.reason.as_deref().unwrap()),
            Some(cause),
            "the producer must persist the cause, rather than relying on a consumer fallback"
        );
        assert!(row.reason.as_deref().unwrap().contains("typed original detail"));
        assert!(row.reason.as_deref().unwrap().contains("downgraded before publication"));
    }
    let row = typed_transport_result(
        "crate::unsupported",
        VcKind::UnsupportedMir {
            kind: "source gap".into(),
            detail: "unsupported source work".into(),
        },
        "ay",
        trust_types::Outcome::Proved,
    );
    assert_eq!(crate::determinism_report::row_stop_cause(&row), StopCause::Unsupported);
}

#[test]
fn publication_stop_inline_structural_refusal_and_path_failure_are_distinct() {
    use trust_types::determinism::StopCause;
    let mut inline = publishing_bounds_sibling();
    let mut evidence = structured_transport_evidence(&inline).unwrap();
    evidence.proof_evidence.as_mut().unwrap().artifacts[0].metadata =
        Some(serde_json::json!({"malformed":true}));
    crate::types::replace_structured_transport_evidence(&mut inline, &evidence).unwrap();
    let mut rows = vec![inline];
    crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(rows[0].outcome, VerificationOutcome::Unknown);
    assert_eq!(crate::determinism_report::row_stop_cause(&rows[0]), StopCause::Solved);

    // A native path descriptor whose file is absent: the production Boolean
    // predicate cannot distinguish IO failure from a structural rejection.
    for prior in [None, Some(StopCause::WallBackstop), Some(StopCause::AdmissionRefused)] {
        let transport = native_full_verifier_transport();
        let mut row = transport_to_verification_result("crate::native", &transport, None, None);
        let mut evidence = structured_transport_evidence(&row).unwrap();
        let artifact = &mut evidence.proof_evidence.as_mut().unwrap().artifacts[0];
        let digest = artifact.digest.as_ref().unwrap().clone();
        let inline = artifact.materialization.take().unwrap();
        let bytes = inline.decoded_bytes().unwrap();
        let relative_path = format!(".trust-proof-artifacts/sha256/{}", digest.value);
        let descriptor = inline.with_materialized_path(&relative_path).unwrap();
        assert!(descriptor.path_is_digest_derived(&digest));
        artifact.materialization = Some(descriptor.clone());
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        fs::create_dir_all(root.join(".trust-proof-artifacts/sha256")).unwrap();
        let error = descriptor.decoded_bytes_at_root(&digest, &root).unwrap_err();
        assert!(error.starts_with("could not inspect artifact materialization file:"), "{error}");
        crate::types::replace_structured_transport_evidence(&mut row, &evidence).unwrap();
        row.reason = prior.map(|cause| cause.stamp("prior native lane"));
        let original = row.clone();
        let mut rows = vec![row];
        crate::types::normalize_authenticated_results_for_publication(&mut rows, Some(&root));
        assert_eq!(rows[0].outcome, VerificationOutcome::Unknown);
        assert_eq!(
            crate::determinism_report::row_stop_cause(&rows[0]),
            prior.unwrap_or(StopCause::Unclassified)
        );
        // The exact same descriptor and envelope succeed when its genuine
        // bytes are present: this is an IO neighbor, not a malformed path.
        fs::write(root.join(relative_path), bytes).unwrap();
        assert!(authenticated_proved_row_has_publication_evidence(&original, Some(&root)));
        let mut valid = vec![original.clone()];
        crate::types::normalize_authenticated_results_for_publication(&mut valid, Some(&root));
        assert_eq!(publication_projection_is_byte_identical(&valid, &[original]), Some(true));
    }
}

#[test]
fn publication_stop_valid_native_and_kernel_evidence_remain_unchanged() {
    for transport in [native_full_verifier_transport(), clean_cic_hardened_transport()] {
        let row = transport_to_verification_result("crate::valid", &transport, None, None);
        assert!(authenticated_proved_row_has_publication_evidence(&row, None));
        let mut rows = vec![row.clone()];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
        assert_eq!(publication_projection_is_byte_identical(&rows, &[row]), Some(true));
        assert_eq!(boundary.published_favorable, 1);
        assert_eq!(boundary.withheld(), 0);
    }
}

#[test]
fn publication_stop_runtime_checked_policy_and_prior_attribution_are_preserved() {
    use trust_types::determinism::StopCause;
    let (function, mut transport) = real_p7_closure_assert_refute_transport();
    transport.reason = Some(StopCause::WallBackstop.stamp("prior closure clock"));
    let row = transport_to_verification_result(&function, &transport, None, None);
    let mut rows = vec![row];
    let boundary = crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(rows[0].outcome, VerificationOutcome::RuntimeChecked);
    assert_eq!(crate::determinism_report::row_stop_cause(&rows[0]), StopCause::WallBackstop);
    assert_eq!(boundary.withheld_relabelled_runtime_checked, 1);
    let once = rows.clone();
    crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(publication_projection_is_byte_identical(&rows, &once), Some(true));

    transport.outcome = trust_types::Outcome::RuntimeChecked;
    let original = transport_to_verification_result(&function, &transport, None, None);
    let mut rows = vec![original.clone()];
    crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(publication_projection_is_byte_identical(&rows, &[original]), Some(true));
}

#[test]
fn publication_stop_elision_cannot_hide_backstops_or_unclassified_work() {
    use trust_types::determinism::{NotedStop, StopCause, UnitOutcome};
    for original in [trust_types::Outcome::Proved, trust_types::Outcome::Unknown] {
        for cause in [
            StopCause::WallBackstop,
            StopCause::RssBackstop,
            StopCause::SolverFault,
            StopCause::Unclassified,
            StopCause::AdmissionRefused,
        ] {
            let mut sibling = publishing_bounds_sibling();
            publication_stop_identity(&mut sibling, "demo", 0);
            let mut twin = evidence_free_bounds_twin(original);
            publication_stop_identity(&mut twin, "demo", 1);
            twin.reason = Some(cause.stamp("original elided lane"));
            let mut rows = vec![sibling, twin];
            let boundary =
                crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
            assert_eq!(rows.len(), 1, "retain the existing alias-elision denominator");
            assert_eq!(boundary.elided_diagnostics.len(), 1);
            assert_eq!(boundary.elided_stops.len(), 1);
            let compiler = vec![NotedStop {
                lane: "other".into(),
                cause: StopCause::Effort,
                item: None,
                count: 2,
            }];
            let notes = crate::determinism_report::noted_stops_with_publication(
                &compiler,
                &boundary.elided_stops,
                None,
            );
            assert_eq!(notes.iter().map(|n| n.count).sum::<u64>(), 3);
            assert_eq!(
                crate::determinism_report::UnitDeterminism::of_rows(&rows, &notes).outcome,
                UnitOutcome::from_causes([cause])
            );
            assert_eq!(
                crate::determinism_report::UnitDeterminism::of_rows(&rows, &[]).outcome,
                UnitOutcome::Measured,
                "control: surviving favorable row alone loses the stop"
            );
            assert!(
                crate::determinism_report::noted_stops_with_publication(
                    &[],
                    &boundary.elided_stops,
                    Some("other-package")
                )
                .is_empty()
            );
            assert_eq!(
                crate::determinism_report::noted_stops_with_publication(
                    &[],
                    &boundary.elided_stops,
                    Some("demo")
                )
                .len(),
                1
            );
        }
    }
}

#[test]
fn publication_stop_unstated_unknown_and_runtime_checked_rows_remain_unclassified() {
    use trust_types::determinism::StopCause;
    for outcome in [VerificationOutcome::Unknown, VerificationOutcome::RuntimeChecked] {
        let mut row = publication_stop_a_like_row();
        row.outcome = outcome;
        row.reason = None;
        let original = row.clone();
        let mut rows = vec![row];
        crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
        assert_eq!(publication_projection_is_byte_identical(&rows, &[original]), Some(true));
        assert_eq!(crate::determinism_report::row_stop_cause(&rows[0]), StopCause::Unclassified);
    }
}

#[test]
fn publication_stop_unattributed_elision_keeps_named_stop_and_never_mints_a_row() {
    use trust_types::determinism::{StopCause, StopItem, UnitOutcome};
    let mut sibling = publishing_bounds_sibling();
    publication_stop_identity(&mut sibling, "demo", 0);
    let mut twin = evidence_free_bounds_twin(trust_types::Outcome::Unknown);
    twin.reason = Some(
        StopCause::WallBackstop
            .stamp_item(StopItem::StrictCheckCancelled, "original unkeyed alias cancellation"),
    );
    let mut rows = vec![sibling, twin];
    let boundary = crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
    assert_eq!(rows.len(), 1);
    assert_eq!(boundary.alias_elided, 1);
    assert_eq!(boundary.elided_stops.len(), 1);
    assert_eq!(boundary.elided_stops[0].package, None);
    assert_eq!(boundary.elided_stops[0].stop.item, Some(StopItem::StrictCheckCancelled));
    for package in [None, Some("demo"), Some("other-package")] {
        let notes = crate::determinism_report::noted_stops_with_publication(
            &[],
            &boundary.elided_stops,
            package,
        );
        assert_eq!(notes.len(), 1);
        let determinism = crate::determinism_report::UnitDeterminism::of_rows(&rows, &notes);
        assert_eq!(determinism.outcome, UnitOutcome::NotReproducible);
        assert_eq!(determinism.vector.entries().len(), 1);
    }
}
