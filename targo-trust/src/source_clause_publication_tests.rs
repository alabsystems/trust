// Included in report::tests to exercise the ordinary live report pipeline.
fn actual_source_clause_certificate() -> trust_certify::source_clause_proof::SourceClauseCertificate
{
    actual_source_clause_fixture().0.certificate().clone()
}

fn actual_source_clause_fixture()
-> &'static (trust_certify::source_clause_proof::CheckedSourceClauseProof, TransportProofEvidence) {
    static FIXTURE: std::sync::OnceLock<(
        trust_certify::source_clause_proof::CheckedSourceClauseProof,
        TransportProofEvidence,
    )> = std::sync::OnceLock::new();
    FIXTURE.get_or_init(|| {
        let certificate =
            current_source_clause_certificate(retained_actual_source_clause_certificate());
        let checked =
            trust_certify::source_clause_proof::replay_source_clause(&certificate).unwrap();
        let transport = checked.transport_evidence().unwrap();
        (checked, transport)
    })
}

fn retained_actual_source_clause_certificate()
-> trust_certify::source_clause_proof::SourceClauseCertificate {
    trust_types::json_depth::from_str_deep(include_str!(
        "../../crates/trust-types/tests/fixtures/source_clause_certificate.json"
    ))
    .unwrap()
}

fn retained_source_clause_certificate(
    compressed: &[u8],
    digest: &str,
) -> trust_certify::source_clause_proof::SourceClauseCertificate {
    use std::io::Read as _;

    let mut raw = Vec::new();
    xz2::read::XzDecoder::new(compressed).take(8 * 1024 * 1024 + 1).read_to_end(&mut raw).unwrap();
    assert!(raw.len() <= 8 * 1024 * 1024);
    assert_eq!(trust_types::stable_sha256_hex(&raw), digest);
    trust_types::json_depth::from_slice_deep(&raw).unwrap()
}

fn current_retained_source_clause_certificate(
    compressed: &[u8],
    digest: &str,
) -> trust_certify::source_clause_proof::SourceClauseCertificate {
    current_source_clause_certificate(retained_source_clause_certificate(compressed, digest))
}

fn current_source_clause_certificate(
    mut certificate: trust_certify::source_clause_proof::SourceClauseCertificate,
) -> trust_certify::source_clause_proof::SourceClauseCertificate {
    // Retained typed bodies and proof payloads remain immutable fixture inputs.
    // Rebuild only their public projection with today's producer. Each positive
    // caller still replays the exact complete original body group, every callee
    // and every retained proof in the current kernel before publication.
    std::thread::Builder::new()
        .name("source-clause-fixture-producer".into())
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let source = &certificate.source;
            let public_bundle =
                trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
                    &source.function,
                    &source.compiler_contracts,
                    &source.verification_conditions,
                    &source.crate_name,
                    source.stable_crate_id,
                    source.target_pointer_width_bits,
                );
            // Historical captures use struct declaration order in both direct
            // predicate values and embedded predicate text. Only those key
            // representations may change; every other byte must still equal
            // the current typed producer.
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
                    let payload: serde_json::Value =
                        trust_types::json_depth::from_str_deep(&metadata.value).unwrap();
                    metadata.value =
                        serde_json::to_string(&trust_types::canonical_json_value(&payload))
                            .unwrap();
                }
            }
            assert_eq!(
                serde_json::to_vec(&canonical_projection).unwrap(),
                serde_json::to_vec(&public_bundle).unwrap()
            );
            certificate.source.public_bundle = public_bundle;
            certificate
        })
        .unwrap()
        .join()
        .unwrap()
}

fn source_clause_transport()
-> (trust_types::TransportObligationResult, trust_types::obligation_identity::ObligationIdentity) {
    let (checked, transport) = actual_source_clause_fixture();
    source_clause_transport_for(checked.certificate(), transport.clone())
}

fn source_clause_transport_for(
    certificate: &trust_certify::source_clause_proof::SourceClauseCertificate,
    proof: TransportProofEvidence,
) -> (trust_types::TransportObligationResult, trust_types::obligation_identity::ObligationIdentity)
{
    let source = &certificate.source;
    let typed = trust_certify::source_clause_proof::source_clause_input_digest_sha256(
        source,
        &certificate.inferred_returns,
    )
    .unwrap();
    let digest = trust_types::original_vc_snapshot::exact_vc_claim_digest_with_expanded_identity(
        &source.source_vc,
        source.overflow_checks,
        Some(&source.target),
        Some(&typed),
        source.expanded_function_identity.as_ref(),
    )
    .unwrap();
    let snapshot = trust_types::OriginalVcSnapshot::capture_with_expanded_identity(
        &source.source_vc,
        source.overflow_checks,
        &source.target,
        &source.obligation_id,
        &digest,
        Some(&typed),
        source.expanded_function_identity.as_ref(),
    )
    .unwrap();
    let mut row = real_native_body_wp_transport();
    row.obligation_id = Some(source.obligation_id.clone());
    row.claim_digest_sha256 = Some(digest);
    row.original_vc_snapshot = Some(Box::new(snapshot));
    row.kind = source.source_vc.kind.transport_tag();
    row.description = source.source_vc.kind.description();
    row.typed_kind = Some(Box::new(source.source_vc.kind.clone()));
    row.location = Some(source.source_vc.location.clone());
    row.solver = "trust-source-contract".into();
    row.proof_evidence = Some(proof);
    row.native_trust_ir = None;
    let identity = trust_types::obligation_identity::ObligationIdentity {
        key: format!("{}#0000000000000000", source.source_vc.function),
        package: source.crate_name.clone(),
        function_source_sha256: source.source_text_sha256.clone(),
        expanded_function_identity: source.expanded_function_identity.clone(),
    };
    (row, identity)
}

fn rendered_source_clause(
    row: &trust_types::TransportObligationResult,
    identity: &trust_types::obligation_identity::ObligationIdentity,
) -> (trust_types::ObligationReport, crate::types::PublicationBoundary) {
    let result = transport_to_verification_result(
        identity.key.split_once('#').unwrap().0,
        row,
        None,
        Some(identity.clone()),
    );
    let report =
        with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
    let boundary = report.publication_boundary.clone().unwrap();
    let obligation = report.to_trust_report().functions.remove(0).obligations.remove(0);
    (obligation, boundary)
}

#[test]
fn actual_source_clause_compositions_publish_with_retained_callee_proofs() {
    // Exact retained compiler-derived caller/query and callee inputs, original
    // body proofs, and the checked callee graph from the RowSink regression.
    // Compression preserves the original certificate bytes without embedding
    // three copies of multi-megabyte CIC payloads in the test executable.
    let fixtures: [(&str, &[u8], &str); 3] = [
        (
            "correct",
            include_bytes!("fixtures/source_clause_correct.json.xz"),
            "945b7fc72ed281512f3e59618970f4f1bf163ccc1ed657df1c2c4fdc44df36c0",
        ),
        (
            "correct_true",
            include_bytes!("fixtures/source_clause_correct_true.json.xz"),
            "21123d80c6c711c25030c54539ee85323be1e468f67b43964a9541be713e9186",
        ),
        (
            "forwarded_correct",
            include_bytes!("fixtures/source_clause_forwarded_correct.json.xz"),
            "24a6f4cfa005ed163b9835e38ac7660294342780f622ca149d9abddfbced93df",
        ),
    ];
    for (name, compressed, digest) in fixtures {
        let certificate = current_retained_source_clause_certificate(compressed, digest);
        assert_eq!(certificate.inferred_returns.nodes.len(), 2, "{name}");
        let checked = trust_certify::source_clause_proof::replay_source_clause(&certificate)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (row, identity) =
            source_clause_transport_for(&certificate, checked.transport_evidence().unwrap());
        let (obligation, boundary) = rendered_source_clause(&row, &identity);
        assert!(
            matches!(obligation.outcome, ObligationOutcome::Proved { .. }),
            "{name}: {:?}",
            obligation.outcome
        );
        assert_eq!(boundary.published_favorable, 1, "{name}");
        assert_eq!(boundary.withheld_relabelled, 0, "{name}");
        let proof = obligation.proof_evidence.unwrap();
        assert_eq!(proof.strength, ProofStrength::deductive(), "{name}");
        assert_eq!(proof.artifacts, row.proof_evidence.unwrap().artifacts, "{name}");
    }
}

#[test]
fn actual_source_clause_publication_refuses_replay_valid_callee_substitution() {
    let original = current_retained_source_clause_certificate(
        include_bytes!("fixtures/source_clause_correct.json.xz"),
        "945b7fc72ed281512f3e59618970f4f1bf163ccc1ed657df1c2c4fdc44df36c0",
    );
    let checked = trust_certify::source_clause_proof::replay_source_clause(&original).unwrap();
    let (mut row, identity) =
        source_clause_transport_for(&original, checked.transport_evidence().unwrap());
    let mut substituted = original.clone();
    let leaf = substituted
        .inferred_returns
        .nodes
        .iter_mut()
        .find(|node| node.children.is_empty())
        .unwrap();
    assert_eq!(leaf.function.def_path, "call_vc_tables::Site::admits");
    leaf.function.body.blocks[0].stmts.insert(0, trust_types::Statement::Nop);

    // This is still a valid proof, with the same caller and original proof
    // payloads. It answers a different typed question because the callee changed.
    assert_eq!(
        serde_json::to_vec(&original.source).unwrap(),
        serde_json::to_vec(&substituted.source).unwrap()
    );
    assert!(trust_certify::source_clause_proof::replay_source_clause(&substituted).is_ok());
    assert_ne!(
        trust_certify::source_clause_proof::source_clause_input_digest_sha256(
            &original.source,
            &original.inferred_returns,
        )
        .unwrap(),
        trust_certify::source_clause_proof::source_clause_input_digest_sha256(
            &substituted.source,
            &substituted.inferred_returns,
        )
        .unwrap()
    );
    reframe_source_clause(&mut row, &substituted);
    let (obligation, boundary) = rendered_source_clause(&row, &identity);
    assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
    assert!(obligation.proof_evidence.is_none());
    assert_eq!(boundary.published_favorable, 0);
    assert_eq!(boundary.withheld_relabelled, 1);
}

// CLAMP-SOURCE-REPLAY-1 (f2c4e2ccce) compares typed VC payload text through a
// canonical view, so a retained certificate whose public context differs from
// today's producer ONLY in that payload's JSON key order is no longer stale: it
// replays, exactly as trust-certify's twin
// (`retained_typed_payload_key_order_replays_without_rewriting_the_question`)
// now pins. These retained fixtures are that case. A stale context is one the
// producer no longer derives: [`stale_public_contexts`] drifts the retained
// context's typed payload semantically (the very field the canonical view
// rewrites, so it must not forgive more than key order) and, separately, a
// non-payload field. Both must still refuse, and must not publish.

/// The retained certificate with its public context drifted two ways: a
/// semantic change inside the typed VC payload (a boolean literal flipped, or
/// failing that an `and`/`or` swapped), and a changed obligation description.
fn stale_public_contexts(
    certificate: &trust_certify::source_clause_proof::SourceClauseCertificate,
) -> Vec<(&'static str, trust_certify::source_clause_proof::SourceClauseCertificate)> {
    fn drift(node: &mut serde_json::Value, flip_literal: bool) -> bool {
        match node {
            serde_json::Value::Object(map) => {
                if flip_literal
                    && map.get("node").and_then(serde_json::Value::as_str) == Some("bool_literal")
                {
                    if let Some(serde_json::Value::Bool(value)) = map.get_mut("value") {
                        *value = !*value;
                        return true;
                    }
                }
                if !flip_literal
                    && map.get("node").and_then(serde_json::Value::as_str) == Some("binary")
                {
                    let swapped = match map.get("op").and_then(serde_json::Value::as_str) {
                        Some("and") => Some("or"),
                        Some("or") => Some("and"),
                        _ => None,
                    };
                    if let Some(op) = swapped {
                        map.insert("op".into(), op.into());
                        return true;
                    }
                }
                map.values_mut().any(|child| drift(child, flip_literal))
            }
            serde_json::Value::Array(items) => {
                items.iter_mut().any(|child| drift(child, flip_literal))
            }
            _ => false,
        }
    }
    let mut payload = certificate.clone();
    let drifted = payload
        .source
        .public_bundle
        .obligations
        .iter_mut()
        .flat_map(|row| &mut row.metadata)
        .filter(|entry| entry.key == "trust.vc.formula.payload")
        .any(|entry| {
            let mut value: serde_json::Value =
                trust_types::json_depth::from_str_deep(&entry.value).unwrap();
            let changed = drift(&mut value, true) || drift(&mut value, false);
            if changed {
                entry.value =
                    trust_types::json_depth::into_string_owned_on_deep_stack(value).unwrap();
            }
            changed
        });
    assert!(drifted, "the retained context has a typed payload to drift");
    let mut description = certificate.clone();
    description.source.public_bundle.obligations[0].description.push_str(" (stale)");
    vec![("typed payload", payload), ("description", description)]
}

#[test]
fn stale_source_clause_public_context_refuses_on_small_caller_stack() {
    let certificate = retained_source_clause_certificate(
        include_bytes!("fixtures/source_clause_correct.json.xz"),
        "945b7fc72ed281512f3e59618970f4f1bf163ccc1ed657df1c2c4fdc44df36c0",
    );
    let stale = stale_public_contexts(&certificate);
    let (replayed, refused) = std::thread::Builder::new()
        .name("small-source-clause-consumer".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let replayed =
                trust_certify::source_clause_proof::replay_source_clause(&certificate).map(|_| ());
            let refused: Vec<_> = stale
                .iter()
                .map(|(label, stale)| {
                    (
                        *label,
                        trust_certify::source_clause_proof::replay_source_clause(stale).map(|_| ()),
                    )
                })
                .collect();
            (replayed, refused)
        })
        .unwrap()
        .join()
        .expect(
            "native replay must decide a deep retained context without exhausting its caller stack",
        );
    assert_eq!(replayed, Ok(()), "a key-order-only retained context replays");
    for (label, refused) in refused {
        assert_eq!(
            refused,
            Err("complete public semantic context differs from typed producer".to_string()),
            "{label}"
        );
    }
}

#[test]
fn stale_source_clause_json_context_and_transport_refuse_publication() {
    let certificate = retained_actual_source_clause_certificate();
    let expanded: trust_certify::source_clause_proof::SourceClauseCertificate =
        trust_types::json_depth::from_slice_deep(include_bytes!(
            "../../crates/trust-types/tests/fixtures/expanded_source_clause_certificate.json"
        ))
        .unwrap();
    let alternate: trust_certify::source_clause_proof::SourceClauseCertificate =
        trust_types::json_depth::from_slice_deep(include_bytes!(
            "../../crates/trust-types/tests/fixtures/expanded_source_clause_alternate.json"
        ))
        .unwrap();
    for retained in [&certificate, &expanded, &alternate] {
        let name = &retained.source.function.def_path;
        assert!(
            trust_certify::source_clause_proof::replay_source_clause(retained).is_ok(),
            "{name}: a key-order-only retained context replays"
        );
        for (label, stale) in stale_public_contexts(retained) {
            assert_eq!(
                trust_certify::source_clause_proof::replay_source_clause(&stale).unwrap_err(),
                "complete public semantic context differs from typed producer",
                "{name}: {label}"
            );
        }
    }
    let proof: TransportProofEvidence = serde_json::from_str(include_str!(
        "../../crates/trust-types/tests/fixtures/source_clause_transport.json"
    ))
    .unwrap();
    // Control: the same transport, framed around the replayable retained
    // certificate, publishes; so the refusals below are the stale context's.
    let (mut row, identity) = source_clause_transport_for(&certificate, proof.clone());
    reframe_source_clause(&mut row, &certificate);
    let (obligation, boundary) = rendered_source_clause(&row, &identity);
    assert!(
        matches!(obligation.outcome, ObligationOutcome::Proved { .. }),
        "{:?}",
        obligation.outcome
    );
    assert_eq!(boundary.published_favorable, 1);
    for (label, stale) in stale_public_contexts(&certificate) {
        let (mut row, identity) = source_clause_transport_for(&stale, proof.clone());
        reframe_source_clause(&mut row, &stale);
        let (obligation, boundary) = rendered_source_clause(&row, &identity);
        assert!(
            matches!(obligation.outcome, ObligationOutcome::Unknown { .. }),
            "{label}: {:?}",
            obligation.outcome
        );
        assert!(obligation.proof_evidence.is_none(), "{label}");
        assert_eq!(boundary.published_favorable, 0, "{label}");
        assert_eq!(boundary.withheld_relabelled, 1, "{label}");
    }
}

#[test]
fn over_depth_source_clause_inputs_refuse_on_small_caller_stack() {
    type Certificate = trust_certify::source_clause_proof::SourceClauseCertificate;

    fn formula(certificate: &mut Certificate, input: usize) -> &mut trust_types::Formula {
        match input {
            0 => &mut certificate.source.source_vc.formula,
            1 => &mut certificate.source.verification_conditions[0].formula,
            2 => &mut certificate.body_proofs[0].vc.formula,
            3 => &mut certificate.source.compiler_contracts.typed_propositions[0].formula,
            4 => &mut certificate.source.function.postconditions[0],
            5 => &mut certificate.inferred_returns.nodes[0].function.preconditions[0],
            _ => unreachable!(),
        }
    }

    for input in 0..6 {
        let mut certificate = retained_source_clause_certificate(
            include_bytes!("fixtures/source_clause_correct.json.xz"),
            "945b7fc72ed281512f3e59618970f4f1bf163ccc1ed657df1c2c4fdc44df36c0",
        );
        certificate.inferred_returns.nodes[0].function.preconditions =
            vec![trust_types::Formula::Bool(false)];
        let mut deep = trust_types::Formula::Bool(false);
        for _ in 0..4096 {
            deep = trust_types::Formula::Not(Box::new(deep));
        }
        *formula(&mut certificate, input) = deep;
        let (source_refusal, graph_refusal) = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("small-over-depth-source-clause-consumer".into())
                .stack_size(2 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    let source_refusal =
                        trust_certify::source_clause_proof::replay_source_clause(&certificate)
                            .unwrap_err();
                    let graph_refusal = (input == 5).then(|| {
                        trust_certify::inferred_return_proof::replay_inferred_return_graph(
                            &certificate.inferred_returns,
                        )
                        .unwrap_err()
                    });
                    (source_refusal, graph_refusal)
                })
                .unwrap()
                .join()
                .expect("over-depth native replay must refuse before recursive work")
        });
        assert_eq!(
            source_refusal, "source clause formula exceeds replay depth bound",
            "input {input}"
        );
        if let Some(refusal) = graph_refusal {
            assert_eq!(refusal, "inferred return formula exceeds replay depth bound");
        }
        // The malformed caller owns this synthetic tree. Dismantle it
        // iteratively so its derived Drop does not exercise an unrelated stack
        // boundary after the replay API has already refused it correctly.
        let mut deep =
            std::mem::replace(formula(&mut certificate, input), trust_types::Formula::Bool(false));
        while let trust_types::Formula::Not(inner) = deep {
            deep = *inner;
        }
    }
}

fn reframe_source_clause(
    row: &mut trust_types::TransportObligationResult,
    certificate: &trust_certify::source_clause_proof::SourceClauseCertificate,
) {
    let owner = row.obligation_id.as_ref().unwrap();
    let binding = format!("trust-source-clause:{owner}");
    let (bytes, digest) = trust_verifier_api::EvidenceArtifactMaterialization::new_bound(
        trust_verifier_api::EvidenceArtifactKind::ProofCertificate,
        &serde_json::to_vec(certificate).unwrap(),
        &binding,
        owner,
        vec![],
    )
    .unwrap();
    let proof = row.proof_evidence.as_mut().unwrap();
    let artifact = &mut proof.artifacts[0];
    proof.proof_id = Some(format!("source-clause:v1:{}", digest.value));
    artifact.artifact_id = proof.proof_id.clone();
    artifact.digest = Some(trust_types::TransportArtifactDigest {
        algorithm: digest.algorithm,
        value: digest.value.clone(),
    });
    artifact.uri =
        Some(format!("trust-source-contract://{owner}/certificate/sha256/{}", digest.value));
    artifact.materialization = trust_types::TransportArtifactMaterialization::from_exact_bytes(
        bytes.bytes(),
        binding,
        vec![],
    );
}

#[test]
fn actual_source_clause_publication_replays_and_preserves_certificate() {
    let (row, identity) = source_clause_transport();
    let (obligation, boundary) = rendered_source_clause(&row, &identity);
    assert!(
        matches!(obligation.outcome, ObligationOutcome::Proved { .. }),
        "{:?}",
        obligation.outcome
    );
    assert_eq!(boundary.published_favorable, 1);
    assert_eq!(boundary.withheld_relabelled, 0);
    let proof = obligation.proof_evidence.as_ref().unwrap();
    assert_eq!(proof.strength, ProofStrength::deductive());
    assert_eq!(proof.evidence, ProofEvidence::from(ProofStrength::deductive()));
    assert_eq!(proof.artifacts, row.proof_evidence.as_ref().unwrap().artifacts);
    assert!(proof.native_trust_ir.is_none());
    assert_eq!(trust_types::saved_obligation_structural_proof_defect(&obligation, None), None);
    // Structural availability does not restore saved authority.
    let result = transport_to_verification_result(
        "source_clause_fixture::constant_false",
        &row,
        None,
        Some(identity),
    );
    let report =
        with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
    let wire = serde_json::to_vec(&report.to_trust_report()).unwrap();
    let (saved, sanitation, _) =
        trust_types::JsonProofReport::decode_saved_json(&wire, None).unwrap();
    assert_eq!(sanitation.downgraded_proved, 1);
    assert_eq!(sanitation.structural_evidence_defects, 0);
    assert!(matches!(saved.functions[0].obligations[0].outcome, ObligationOutcome::Unknown { .. }));
}

#[test]
fn actual_source_clause_path_backed_certificate_requires_exact_trusted_store() {
    let (mut row, identity) = source_clause_transport();
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let artifact = &mut row.proof_evidence.as_mut().unwrap().artifacts[0];
    let path = format!(".trust-proof-artifacts/sha256/{}", artifact.digest.as_ref().unwrap().value);
    let materialization = artifact.materialization.as_mut().unwrap();
    let bytes = materialization.decoded_bytes().unwrap();
    let absolute = root.join(&path);
    std::fs::create_dir_all(absolute.parent().unwrap()).unwrap();
    std::fs::write(&absolute, bytes).unwrap();
    materialization.materialized_path = Some(path);
    materialization.encoded_bytes.clear();
    let result = transport_to_verification_result(
        "source_clause_fixture::constant_false",
        &row,
        None,
        Some(identity),
    );
    let structured = structured_transport_evidence(&result).unwrap();
    assert!(source_clause::proof_evidence_report(&result, Some(&structured), None).is_none());
    let proof =
        source_clause::proof_evidence_report(&result, Some(&structured), Some(&root)).unwrap();
    assert_eq!(proof.artifacts, row.proof_evidence.as_ref().unwrap().artifacts);
    std::fs::write(absolute, b"changed certificate").unwrap();
    assert!(
        source_clause::proof_evidence_report(&result, Some(&structured), Some(&root)).is_none()
    );
}

#[test]
fn actual_source_clause_publication_refuses_modified_identity_grade_and_group() {
    let (row, identity) = source_clause_transport();
    for mutation in 0..11 {
        let mut row = row.clone();
        let mut identity = identity.clone();
        let mut certificate = actual_source_clause_certificate();
        match mutation {
            0 => identity.function_source_sha256 = Some("0".repeat(64)),
            1 => row.obligation_id.as_mut().unwrap().push('x'),
            2 => row.original_vc_snapshot.as_mut().unwrap().typed_input_digest_sha256 = None,
            3 => row.claim_digest_sha256 = Some("0".repeat(64)),
            4 => {
                let proof = row.proof_evidence.as_mut().unwrap();
                proof.strength.as_mut().unwrap().assurance = AssuranceLevel::Certified;
                proof.evidence.as_mut().unwrap().assurance = AssuranceLevel::Certified;
            }
            5 => {
                let proof = row.proof_evidence.as_mut().unwrap();
                proof.artifacts.push(proof.artifacts[0].clone());
            }
            6 => row.proof_evidence.as_mut().unwrap().request_id = Some("0".into()),
            7 => {
                certificate.body_proofs.clear();
                reframe_source_clause(&mut row, &certificate);
            }
            8 => {
                certificate.body_proofs[0].claim_digest_sha256 = "0".repeat(64);
                reframe_source_clause(&mut row, &certificate);
            }
            9 => {
                certificate.source.function.body.blocks[0]
                    .stmts
                    .insert(0, trust_types::Statement::Nop);
                let source = &mut certificate.source;
                source.public_bundle =
                    trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
                        &source.function,
                        &source.compiler_contracts,
                        &source.verification_conditions,
                        &source.crate_name,
                        source.stable_crate_id,
                        source.target_pointer_width_bits,
                    );
                // A different valid body proof must still not answer this original question.
                assert!(
                    trust_certify::source_clause_proof::replay_source_clause(&certificate).is_ok()
                );
                reframe_source_clause(&mut row, &certificate);
            }
            _ => {
                row.proof_evidence.as_mut().unwrap().artifacts[0]
                    .materialization
                    .as_mut()
                    .unwrap()
                    .encoded_bytes
                    .replace_range(0..2, "00");
            }
        }
        let (obligation, boundary) = rendered_source_clause(&row, &identity);
        assert!(
            matches!(obligation.outcome, ObligationOutcome::Unknown { .. }),
            "mutation {mutation}: {:?}",
            obligation.outcome
        );
        assert!(obligation.proof_evidence.is_none(), "mutation {mutation}");
        assert_eq!(boundary.withheld_relabelled, 1, "mutation {mutation}");
    }
}

#[test]
fn actual_expanded_source_clause_publication_binds_origin_and_strips_saved_authority() {
    let certificate: trust_certify::source_clause_proof::SourceClauseCertificate =
        trust_types::json_depth::from_slice_deep(include_bytes!(
            "../../crates/trust-types/tests/fixtures/expanded_source_clause_certificate.json"
        ))
        .unwrap();
    let certificate = current_source_clause_certificate(certificate);
    let alternate: trust_certify::source_clause_proof::SourceClauseCertificate =
        trust_types::json_depth::from_slice_deep(include_bytes!(
            "../../crates/trust-types/tests/fixtures/expanded_source_clause_alternate.json"
        ))
        .unwrap();
    let alternate = current_source_clause_certificate(alternate);
    let proof = trust_certify::source_clause_proof::replay_source_clause(&certificate).unwrap();
    let alternate_proof =
        trust_certify::source_clause_proof::replay_source_clause(&alternate).unwrap();
    let (row, identity) =
        source_clause_transport_for(&certificate, proof.transport_evidence().unwrap());
    let (published, boundary) = rendered_source_clause(&row, &identity);
    assert!(matches!(published.outcome, ObligationOutcome::Proved { .. }));
    assert_eq!(boundary.published_favorable, 1);
    assert_eq!(published.proof_evidence.as_ref().unwrap().strength, ProofStrength::deductive());
    let (other, other_identity) =
        source_clause_transport_for(&alternate, alternate_proof.transport_evidence().unwrap());
    assert!(matches!(
        rendered_source_clause(&other, &other_identity).0.outcome,
        ObligationOutcome::Proved { .. }
    ));
    let mut transplanted = row.clone();
    reframe_source_clause(&mut transplanted, &alternate);
    assert!(matches!(
        rendered_source_clause(&transplanted, &identity).0.outcome,
        ObligationOutcome::Unknown { .. }
    ));
    for mutation in 0..5 {
        let mut changed = row.clone();
        let mut changed_identity = identity.clone();
        match mutation {
            0 => changed_identity.expanded_function_identity = None,
            1 => changed.original_vc_snapshot.as_mut().unwrap().expanded_function_identity = None,
            2 => changed_identity.function_source_sha256 = Some("f".repeat(64)),
            3 => {
                changed.proof_evidence.as_mut().unwrap().strength.as_mut().unwrap().assurance =
                    AssuranceLevel::Certified
            }
            _ => {
                changed.proof_evidence.as_mut().unwrap().artifacts[0].format =
                    Some("trust.source-clause-body-proof.v1".into())
            }
        }
        assert!(
            matches!(
                rendered_source_clause(&changed, &changed_identity).0.outcome,
                ObligationOutcome::Unknown { .. }
            ),
            "mutation {mutation}"
        );
    }
    let result = transport_to_verification_result(
        &certificate.source.function.def_path,
        &row,
        None,
        Some(identity),
    );
    let report =
        with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
    let (saved, sanitation, _) = trust_types::JsonProofReport::decode_saved_json(
        &serde_json::to_vec(&report.to_trust_report()).unwrap(),
        None,
    )
    .unwrap();
    assert_eq!(sanitation.downgraded_proved, 1);
    assert_eq!(sanitation.structural_evidence_defects, 0);
    assert!(matches!(saved.functions[0].obligations[0].outcome, ObligationOutcome::Unknown { .. }));
}
