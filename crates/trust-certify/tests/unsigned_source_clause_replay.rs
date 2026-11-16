//! Original retained integer body proofs, independent of source publication.
use trust_certify::replay_presented_vc_evidence;
use trust_ir::ProofEvidence;
use trust_types::VerificationCondition;

#[derive(serde::Deserialize)]
struct CapturedSourceRow {
    obligation_id: String,
    proof: trust_types::TransportProofEvidence,
    identity: trust_types::obligation_identity::ObligationIdentity,
    snapshot: trust_types::OriginalVcSnapshot,
    claim_digest_sha256: String,
}

struct ReplayedSourceRow {
    captured: CapturedSourceRow,
    checked: trust_certify::source_clause_proof::CheckedSourceClauseProof,
}

fn source_proofs() -> &'static [ReplayedSourceRow] {
    use std::io::Read;
    use std::sync::OnceLock;

    use trust_certify::source_clause_proof::{
        SourceClauseCertificate, replay_source_clause, source_clause_input_digest_sha256,
    };
    #[derive(serde::Deserialize)]
    struct Capture {
        schema: String,
        rows: Vec<CapturedSourceRow>,
    }
    static PROOFS: OnceLock<Vec<ReplayedSourceRow>> = OnceLock::new();
    PROOFS.get_or_init(|| {
        let compressed = include_bytes!("fixtures/retained-clamp-source-proofs.json.gz");
        assert_eq!(
            trust_types::stable_sha256_hex(compressed),
            "d3c041807e4301a0278878b8880b29d1eac7661dae52bfeb39464373a2d3d54f"
        );
        let mut raw = Vec::new();
        flate2::read::GzDecoder::new(&compressed[..]).read_to_end(&mut raw).unwrap();
        assert_eq!(raw.len(), 3_295_411);
        assert_eq!(
            trust_types::stable_sha256_hex(&raw),
            "9e80b4deebb1a5a303879b8998413f573d3f3134b59b65bd8ae9c32b7de1a742"
        );
        let capture: Capture = trust_types::json_depth::from_slice_deep(&raw).unwrap();
        assert_eq!(capture.schema, "trust.test.captured-source-clauses.v1");
        assert_eq!(capture.rows.len(), 8);
        capture
            .rows
            .into_iter()
            .map(|captured| {
                // Decode the original envelope through the shared publication
                // boundary, then independently check the complete typed input
                // and its retained body proofs. A saved Proved bit is never used.
                let payload = trust_types::source_clause_certificate_payload(
                    &captured.proof,
                    Some(&captured.obligation_id),
                    Some(&captured.identity),
                    Some(&captured.claim_digest_sha256),
                    Some(&captured.snapshot),
                    None,
                )
                .unwrap();
                let certificate: SourceClauseCertificate =
                    trust_types::json_depth::from_slice_deep(&payload).unwrap();
                assert_eq!(
                    source_clause_input_digest_sha256(
                        &certificate.source,
                        &certificate.inferred_returns,
                    ),
                    captured.snapshot.typed_input_digest_sha256
                );
                let checked = replay_source_clause(&certificate)
                    .unwrap_or_else(|error| panic!("{}: {error}", captured.obligation_id));
                assert_eq!(checked.proof_strength(), trust_types::ProofStrength::deductive());
                ReplayedSourceRow { captured, checked }
            })
            .collect()
    })
}

#[test]
fn actual_clamp_source_certificates_replay_all_eight_original_questions() {
    let mut actual: Vec<_> =
        source_proofs().iter().map(|row| row.captured.obligation_id.as_str()).collect();
    actual.sort_unstable();
    assert_eq!(
        actual,
        [
            "obligation:trust_budget__process_ceiling_mb:postcondition:0",
            "obligation:trust_budget__process_ceiling_mb:postcondition:1",
            "obligation:trust_intbound__clamp_to_max:postcondition:0",
            "obligation:trust_intbound__clamp_to_max:postcondition:1",
            "obligation:trust_intbound__clamp_width:postcondition:0",
            "obligation:trust_intbound__clamp_width:postcondition:1",
            "obligation:trust_widthconv__join_width:postcondition:0",
            "obligation:trust_widthconv__join_width:postcondition:1",
        ]
    );
    for row in source_proofs() {
        let certificate = row.checked.certificate();
        assert!(!certificate.body_proofs.is_empty());
        assert_eq!(certificate.source.obligation_id, row.captured.obligation_id);
        assert_eq!(row.checked.proof_strength(), trust_types::ProofStrength::deductive());
    }
}

#[test]
fn actual_clamp_source_certificates_refuse_missing_rows_changed_contracts_and_evidence() {
    use trust_certify::source_clause_proof::replay_source_clause;
    for row in source_proofs() {
        for mutation in 0..12 {
            let mut changed = row.checked.certificate().clone();
            match mutation {
                0 => {
                    changed.body_proofs.pop().unwrap();
                }
                1 => {
                    changed.source.verification_conditions.remove(changed.body_proofs[0].vc_index);
                }
                2 => {
                    let index = changed.source.source_contract_index;
                    changed
                        .source
                        .compiler_contracts
                        .typed_propositions
                        .iter_mut()
                        .find(|proposition| proposition.source_contract_index == index)
                        .unwrap()
                        .formula = trust_types::Formula::Bool(true);
                }
                3 => changed.source.source_vc.formula = trust_types::Formula::Bool(true),
                4 => changed.body_proofs[0].claim_digest_sha256 = "0".repeat(64),
                5 => {
                    let ProofEvidence::CleanCic { lineage, .. } =
                        &mut changed.body_proofs[0].evidence
                    else {
                        panic!("retained body proof must be CleanCic")
                    };
                    lineage.bytes[0] ^= 1;
                }
                6..=8 => {
                    let payload = changed
                        .source
                        .public_bundle
                        .obligations
                        .iter_mut()
                        .flat_map(|row| &mut row.metadata)
                        .find(|entry| entry.key == "trust.vc.formula.payload")
                        .unwrap();
                    let mut value: serde_json::Value =
                        serde_json::from_str(&payload.value).unwrap();
                    if mutation == 6 {
                        value.as_object_mut().unwrap().insert("unexpected".into(), true.into());
                        payload.value = serde_json::to_string(&value).unwrap();
                    } else if mutation == 7 {
                        payload.value =
                            format!("{{\"root\":{},{}", value["root"], &payload.value[1..]);
                    } else {
                        value["root"] = serde_json::json!({"sort":"bool", "kind":{"node":"bool_literal", "value":true}});
                        payload.value = serde_json::to_string(&value).unwrap();
                    }
                }
                9 => {
                    let row = changed
                        .source
                        .public_bundle
                        .obligations
                        .iter_mut()
                        .find(|row| {
                            row.metadata.iter().any(|entry| entry.key == "trust.vc.formula.payload")
                        })
                        .unwrap();
                    let duplicate = row
                        .metadata
                        .iter()
                        .find(|entry| entry.key == "trust.vc.formula.payload")
                        .unwrap()
                        .clone();
                    row.metadata.push(duplicate);
                }
                10 => {
                    changed
                        .source
                        .public_bundle
                        .obligations
                        .iter_mut()
                        .flat_map(|row| &mut row.metadata)
                        .find(|entry| entry.key == "trust.vc.formula.schema")
                        .unwrap()
                        .value = "unknown.v1".into();
                }
                11 => changed.source.public_bundle.obligations.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(
                replay_source_clause(&changed).is_err(),
                "{} accepted mutation {mutation}",
                row.captured.obligation_id,
            );
        }
    }
}

#[test]
fn actual_valid_clamp_proofs_cannot_move_to_another_source_identity_or_clause() {
    for row in source_proofs() {
        // Every donor has already independently replayed above. In particular,
        // these controls do not reject merely because the donor proof is invalid.
        let donor = source_proofs()
            .iter()
            .find(|donor| {
                donor.captured.identity.expanded_function_identity
                    != row.captured.identity.expanded_function_identity
            })
            .unwrap();
        assert!(
            trust_types::source_clause_certificate_payload(
                &row.captured.proof,
                Some(&row.captured.obligation_id),
                Some(&donor.captured.identity),
                Some(&row.captured.claim_digest_sha256),
                Some(&row.captured.snapshot),
                None,
            )
            .is_err()
        );
        let same_function_other_clause = source_proofs()
            .iter()
            .find(|other| {
                other.captured.identity.expanded_function_identity
                    == row.captured.identity.expanded_function_identity
                    && other.captured.obligation_id != row.captured.obligation_id
            })
            .unwrap();
        assert!(
            trust_types::source_clause_certificate_payload(
                &row.captured.proof,
                Some(&same_function_other_clause.captured.obligation_id),
                Some(&same_function_other_clause.captured.identity),
                Some(&same_function_other_clause.captured.claim_digest_sha256),
                Some(&same_function_other_clause.captured.snapshot),
                None,
            )
            .is_err()
        );
    }
}

fn body_proofs() -> Vec<(VerificationCondition, ProofEvidence)> {
    let capture: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/retained-clamp-body-proofs.json")).unwrap();
    capture["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let raw = row["original_vc_json"].as_str().unwrap();
            assert_eq!(trust_types::stable_sha256_hex(raw.as_bytes()), row["payload_sha256"]);
            (
                serde_json::from_str(raw).unwrap(),
                serde_json::from_value(row["evidence"].clone()).unwrap(),
            )
        })
        .collect()
}

#[test]
fn retained_clamp_body_proofs_replay_without_new_search() {
    let proofs = body_proofs();
    assert_eq!(proofs.len(), 8);
    for (vc, proof) in &proofs {
        assert!(replay_presented_vc_evidence(vc, proof), "{} {:?}", vc.function, vc.location);
    }
}

#[test]
fn retained_clamp_body_proofs_refuse_changed_question_and_lineage() {
    for (vc, proof) in body_proofs() {
        let mut changed = vc.clone();
        changed.formula = trust_types::Formula::Bool(false);
        assert!(!replay_presented_vc_evidence(&changed, &proof));
        let mut changed = proof;
        let ProofEvidence::CleanCic { lineage, .. } = &mut changed else { panic!("expected CIC") };
        lineage.bytes[0] ^= 1;
        assert!(!replay_presented_vc_evidence(&vc, &changed));
    }
}
