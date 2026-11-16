use super::*;

fn fixture() -> (SourceClauseCertificate, Publication, ResultObligationBinding) {
    // Trust: retain the original capture unchanged, rebuild only its
    // canonical predicate values/text, and replay its body proof once.
    static CHECKED: std::sync::OnceLock<CheckedSourceClauseProof> = std::sync::OnceLock::new();
    let proof = CHECKED
        .get_or_init(|| {
            let mut certificate = retained_fixture();
            let source = &certificate.source;
            let current =
                trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
                    &source.function,
                    &source.compiler_contracts,
                    &source.verification_conditions,
                    &source.crate_name,
                    source.stable_crate_id,
                    source.target_pointer_width_bits,
                );
            let mut canonical_projection = source.public_bundle.clone();
            for contract in &mut canonical_projection.contracts {
                if let trust_verifier_api::ContractPredicate::TrustIr { value, .. } =
                    &mut contract.predicate
                {
                    trust_types::canonicalize_json_in_place(value);
                }
            }
            for metadata in
                canonical_projection.obligations.iter_mut().flat_map(|row| &mut row.metadata)
            {
                if metadata.key == "trust.vc.formula.payload" {
                    let payload: serde_json::Value = serde_json::from_str(&metadata.value).unwrap();
                    metadata.value =
                        serde_json::to_string(&trust_types::canonical_json_value(&payload))
                            .unwrap();
                }
            }
            assert_eq!(
                serde_json::to_vec(&canonical_projection).unwrap(),
                serde_json::to_vec(&current).unwrap()
            );
            certificate.source.public_bundle = current;
            trust_certify::source_clause_proof::replay_source_clause(&certificate).unwrap()
        })
        .clone();
    let certificate = proof.certificate().clone();
    let typed_input_digest = trust_certify::source_clause_proof::source_clause_input_digest_sha256(
        &certificate.source,
        &certificate.inferred_returns,
    )
    .unwrap();
    let obligation = certificate
        .source
        .public_bundle
        .obligations
        .iter()
        .find(|row| row.obligation_id == certificate.source.obligation_id)
        .unwrap()
        .clone();
    let binding = ResultObligationBinding {
        row: exact_result_row_identity(0, &certificate.source.source_vc).unwrap(),
        public_obligation_id: obligation.obligation_id.clone(),
        native_identity: native_transport_identity(&obligation),
        canonical_obligation: obligation,
        definition_entry_assumption: false,
        assumed_total_callee_assumption: false,
        monitor: None,
    };
    (
        certificate,
        Publication { proof, typed_input_digest, expanded_function_identity: None },
        binding,
    )
}

// Trust: historical serialized public context is evidence to revalidate,
// never an authority to bypass the native producer's exact comparison.
fn retained_fixture() -> SourceClauseCertificate {
    serde_json::from_slice(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/trust-certify/tests/fixtures/source-clause-actual-certificate.json"
    )))
    .unwrap()
}

#[test]
fn source_publication_refuses_retained_noncanonical_public_context() {
    // CLAMP-SOURCE-REPLAY-1 (`f2c4e2ccce`): pre-canonicalization JSON key order
    // inside a validated `trust.vc.formula.payload` replays without rewriting
    // the certificate, while any unrecognized JSON key or other public-bundle
    // drift still fails closed.
    let retained = retained_fixture();
    let original_bytes = serde_json::to_vec(&retained).unwrap();
    let checked = trust_certify::source_clause_proof::replay_source_clause(&retained).unwrap();
    assert_eq!(serde_json::to_vec(checked.certificate()).unwrap(), original_bytes);
    assert_eq!(checked.proof_strength(), ProofStrength::deductive());

    let mut extra_payload_field = retained.clone();
    let payload_entry = extra_payload_field
        .source
        .public_bundle
        .obligations
        .iter_mut()
        .flat_map(|row| &mut row.metadata)
        .find(|entry| entry.key == "trust.vc.formula.payload")
        .unwrap();
    let mut payload_json: serde_json::Value = serde_json::from_str(&payload_entry.value).unwrap();
    payload_json.as_object_mut().unwrap().insert("extra_unrecognized".into(), serde_json::json!(1));
    payload_entry.value = serde_json::to_string(&payload_json).unwrap();
    assert_eq!(
        trust_certify::source_clause_proof::replay_source_clause(&extra_payload_field).unwrap_err(),
        "complete public semantic context differs from typed producer"
    );

    let mut drifted_bundle = retained;
    drifted_bundle.source.public_bundle.metadata.push(trust_verifier_api::MetadataEntry {
        key: "trust.noncanonical.extra".into(),
        value: "1".into(),
    });
    assert_eq!(
        trust_certify::source_clause_proof::replay_source_clause(&drifted_bundle).unwrap_err(),
        "complete public semantic context differs from typed producer"
    );
}

fn authority(publication: Publication, binding: &ResultObligationBinding) -> ResultProofAuthority {
    ResultProofAuthority::ExactSourceClauseDischarge {
        row: binding.row.clone(),
        binding: binding.clone(),
        body_proofs: vec![ExactSourceClauseBodyProofBinding {
            public_obligation_id: publication.proof.certificate().body_proofs[0]
                .public_obligation_id
                .clone(),
            row: exact_result_row_identity(1, &publication.proof.certificate().body_proofs[0].vc)
                .unwrap(),
        }],
        certificate: Some(publication),
    }
}

#[test]
fn source_publication_binds_the_original_typed_input_before_transport() {
    let (certificate, publication, binding) = fixture();
    let typed_digest = publication.typed_input_digest.clone();
    let original = certificate.source.source_vc.clone();
    let result = VerificationResult::Proved {
        solver: "trust-exact-source-clause-discharge".into(),
        time_ms: 0,
        strength: ProofStrength::deductive(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let rows = build_transport_results_with_runtime_checks_bound(
        certificate.source.overflow_checks,
        Some(&certificate.source.target),
        &[(original.clone(), result)],
        None,
        &[None],
        &[Some(binding.clone())],
        &[Some(authority(publication, &binding))],
    );
    let row = &rows[0];
    assert_eq!(row.outcome, Outcome::Proved);
    let snapshot = row.original_vc_snapshot.as_ref().unwrap();
    assert_eq!(snapshot.typed_input_digest_sha256.as_deref(), Some(typed_digest.as_str()));
    let decoded = snapshot
        .decode_for_row(&binding.public_obligation_id, row.claim_digest_sha256.as_deref().unwrap())
        .unwrap();
    assert_eq!(serde_json::to_vec(&decoded).unwrap(), serde_json::to_vec(&original).unwrap());
    assert_eq!(row.proof_evidence.as_ref().unwrap().suite, "trust-source-contract");
    let mut wrong_snapshot = snapshot.as_ref().clone();
    wrong_snapshot.typed_input_digest_sha256 = Some("f".repeat(64));
    assert!(
        wrong_snapshot
            .decode_for_row(
                &binding.public_obligation_id,
                row.claim_digest_sha256.as_deref().unwrap()
            )
            .is_err()
    );
}

#[test]
fn source_publication_revokes_previous_attachment_before_refusal() {
    let (_, publication, binding) = fixture();
    let mut authorities = vec![Some(authority(publication, &binding)), None];
    // Called before any fragment, capture, or graph check in attach().
    clear_attachments(&mut authorities);
    assert!(matches!(
        authorities[0],
        Some(ResultProofAuthority::ExactSourceClauseDischarge { certificate: None, .. })
    ));
    assert!(authorities[1].is_none());
}

#[test]
fn independent_source_question_requires_unchanged_selected_clause() {
    let (certificate, _, _) = fixture();
    let original = &certificate.source.public_bundle;
    let owner = &certificate.source.obligation_id;
    let mut routed = original.clone();
    let selected = routed.obligations.iter_mut().find(|row| &row.obligation_id == owner).unwrap();
    selected.metadata.push(trust_verifier_api::MetadataEntry {
        key: "test.native-route".into(),
        value: "separate-obligation".into(),
    });
    let mut other = selected.clone();
    other.obligation_id.push_str(":native-panic");
    routed.obligations.push(other);
    assert!(selected_source_preserved(original, &routed, owner));
    assert_eq!(routed.obligations.len(), original.obligations.len() + 1);
    let mut mutated = routed.clone();
    mutated
        .obligations
        .iter_mut()
        .find(|row| &row.obligation_id == owner)
        .unwrap()
        .description
        .push_str(" changed");
    assert!(!selected_source_preserved(original, &mutated, owner));
    let mut mutated = routed.clone();
    mutated.contracts[0].predicate = trust_verifier_api::ContractPredicate::TrustIr {
        schema: "wrong".into(),
        value: serde_json::json!(false),
    };
    assert!(!selected_source_preserved(original, &mutated, owner));
    let selected =
        routed.obligations.iter().find(|row| &row.obligation_id == owner).unwrap().clone();
    routed.obligations.push(selected);
    assert!(!selected_source_preserved(original, &routed, owner));
}

#[test]
fn source_publication_preserves_final_row_inventory_and_unrelated_rows() {
    let (certificate, publication, binding) = fixture();
    let mut unrelated = certificate.source.source_vc.clone();
    unrelated.kind = VcKind::Assertion { message: "unrelated native panic row".into() };
    unrelated.formula = Formula::Bool(true);
    let unknown = || VerificationResult::Unknown {
        solver: "unresolved".into(),
        time_ms: 0,
        reason: "retained obligation".into(),
    };
    let rows = vec![
        (
            certificate.source.source_vc.clone(),
            VerificationResult::Proved {
                solver: "trust-exact-source-clause-discharge".into(),
                time_ms: 0,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (certificate.body_proofs[0].vc.clone(), unknown()),
        (unrelated, unknown()),
    ];
    // Preserve the real pre-publication mapping: source IDs are assigned
    // by the returned full-verifier carrier even when its evidence declined.
    let evidence = super::super::tests::unsupported_evidence_for(&binding.canonical_obligation);
    let run = trust_verifier_api::VerificationRunResult::from_evidence(
        trust_router::VerifierExecutionContext::new("source-publication-inventory").snapshot(),
        &certificate.source.public_bundle,
        evidence.engine.clone(),
        std::slice::from_ref(&binding.canonical_obligation),
        vec![evidence],
    );
    let render = |authority| {
        build_transport_results_with_runtime_checks_bound(
            certificate.source.overflow_checks,
            Some(&certificate.source.target),
            &rows,
            Some(&run),
            &[None, None, None],
            &[Some(binding.clone()), None, None],
            &[Some(authority), None, None],
        )
    };
    let mut before_authority = authority(publication.clone(), &binding);
    if let ResultProofAuthority::ExactSourceClauseDischarge { certificate, .. } =
        &mut before_authority
    {
        *certificate = None;
    }
    let before = render(before_authority);
    let after = render(authority(publication, &binding));
    assert_eq!(before.len(), rows.len());
    assert_eq!(after.len(), before.len());
    assert_eq!(
        before.iter().map(|row| &row.obligation_id).collect::<Vec<_>>(),
        after.iter().map(|row| &row.obligation_id).collect::<Vec<_>>()
    );
    assert_eq!(serde_json::to_vec(&before[1..]).unwrap(), serde_json::to_vec(&after[1..]).unwrap());
    assert!(
        before[0]
            .proof_evidence
            .as_ref()
            .is_none_or(|proof| proof.suite != "trust-source-contract")
    );
    assert_eq!(after[0].proof_evidence.as_ref().unwrap().suite, "trust-source-contract");
}
