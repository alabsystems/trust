//! Real compiler-query/extractor input; proof facts are minted once and reused.
use std::sync::OnceLock;

use trust_certify::source_clause_proof::{
    SourceClauseCertificate, replay_source_clause, source_clause_input_digest_sha256,
};

fn captured_scalar_certificate() -> SourceClauseCertificate {
    use trust_certify::source_clause_proof::{SCHEMA, SourceBodyProof, SourceClauseInput};
    let mut source: SourceClauseInput =
        serde_json::from_str(include_str!("fixtures/provider-source-clause-input-11627.json"))
            .unwrap();
    let canonical = trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
        &source.function,
        &source.compiler_contracts,
        &source.verification_conditions,
        &source.crate_name,
        source.stable_crate_id,
        source.target_pointer_width_bits,
    );
    // Reconstruct the query sidecar only when its predicates and all original
    // constructor metadata equal the actual native capture. Routing additions
    // remain comparison data, never source or proof authority.
    for expected in &canonical.contracts {
        if !expected.contract_id.starts_with("trust-contract:") {
            continue;
        }
        let actual = source
            .public_bundle
            .contracts
            .iter()
            .find(|actual| actual.contract_id == expected.contract_id)
            .unwrap();
        assert!(trust_source_contract::public_contract_preserves_source(expected, actual));
    }
    source.public_bundle = canonical;
    assert_eq!(source.function.preconditions.len(), 2, "authored Requires and exact type range");
    assert!(source.function.body.blocks.iter().all(|block| {
        !matches!(
            block.terminator,
            trust_types::Terminator::Call { .. } | trust_types::Terminator::TailCall { .. }
        )
    }));
    let vc = source.verification_conditions[0].clone();
    let evidence = trust_certify::certify_vc(&vc).expect("the captured body goal's own proof");
    assert!(trust_certify::replay_presented_vc_evidence(&vc, &evidence));
    assert!(trust_certify::reference_certificate_for(&evidence).is_some());
    let identity = trust_source_contract::verifier_vc_content_identity_with_crate_name(
        &source.function,
        0,
        &vc,
        &source.crate_name,
    );
    let body = SourceBodyProof {
        vc_index: 0,
        public_obligation_id: identity.obligation_id,
        claim_digest_sha256: trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(
            &vc,
            source.overflow_checks,
            Some(&source.target),
        )
        .unwrap(),
        vc,
        evidence,
    };
    SourceClauseCertificate {
        schema: SCHEMA.into(),
        source,
        body_proofs: vec![body],
        inferred_returns: trust_certify::inferred_return_proof::InferredReturnProofGraph {
            nodes: vec![],
        },
    }
}

#[test]
fn captured_audited_scalar_requires_body_has_complete_source_certificate() {
    let certificate = captured_scalar_certificate();
    let checked =
        replay_source_clause(&certificate).expect("complete conditional source/body certificate");
    assert_eq!(checked.proof_strength(), trust_types::ProofStrength::deductive());
}

#[test]
fn captured_scalar_correspondence_binds_every_premise_and_original_body_row() {
    let certificate = captured_scalar_certificate();
    let source = &certificate.source;
    let relation = |source: &trust_certify::source_clause_proof::SourceClauseInput| {
        trust_source_contract::exact_ensures_body_group(
            &source.function,
            &source.compiler_contracts,
            source.source_contract_index,
            &source.verification_conditions,
            source.target_pointer_width_bits,
            None,
        )
    };
    assert_eq!(relation(source).unwrap().body_indices(), &[0]);
    for mutation in 0..11 {
        let mut changed = source.clone();
        match mutation {
            0 => changed.function.preconditions.pop().map(|_| ()).unwrap(),
            1 => changed.function.preconditions.push(trust_types::Formula::Bool(false)),
            2 => {
                changed.compiler_contracts.typed_propositions.remove(0);
            }
            3 => {
                let proposition = changed.compiler_contracts.typed_propositions[0].clone();
                changed.compiler_contracts.typed_propositions.push(proposition);
            }
            4 => {
                changed.compiler_contracts.typed_propositions[0].variable_domains[0].domain =
                    trust_types::CompilerContractValueDomain::MachineInt { width: 8, signed: false }
            }
            5 => {
                changed.verification_conditions.remove(0);
            }
            6 => changed.verification_conditions.push(changed.verification_conditions[0].clone()),
            7 => changed.verification_conditions[0].formula = trust_types::Formula::Bool(false),
            8 => changed.source_contract_index = 0, // a Requires cannot acquire Ensures proof credit
            9 => {
                changed.function.body.blocks[0].terminator =
                    trust_types::Terminator::Goto(trust_types::BlockId(0))
            }
            10 => {
                changed.function.body.return_ty = trust_types::Ty::Int { width: 32, signed: true }
            }
            _ => unreachable!(),
        }
        assert!(relation(&changed).is_none(), "premise/body mutation {mutation}");
    }
    // The correspondence is not proof: an empty/mismatched proof group and
    // a different presented kernel payload still fail checked source replay.
    let mut missing = certificate.clone();
    missing.body_proofs.clear();
    assert!(replay_source_clause(&missing).is_err());
    let mut wrong = certificate.clone();
    wrong.body_proofs[0].evidence = fixture().body_proofs[0].evidence.clone();
    assert!(replay_source_clause(&wrong).is_err());
}

#[test]
fn captured_scalar_correspondence_rejects_memory_and_opaque_operands() {
    use trust_types::{Operand, Projection, Rvalue, Statement};
    let certificate = captured_scalar_certificate();
    for mutation in 0..3 {
        let mut source = certificate.source.clone();
        if mutation == 2 {
            source.function.body.blocks[1].terminator =
                source.function.body.blocks[0].terminator.clone();
        } else {
            let Statement::Assign { rvalue, .. } = &mut source.function.body.blocks[0].stmts[0]
            else {
                panic!("captured arithmetic assignment")
            };
            let Rvalue::CheckedBinaryOp(_, operand, _) = rvalue else {
                panic!("captured checked arithmetic")
            };
            if mutation == 0 {
                let Operand::Copy(place) = operand else { panic!("captured argument") };
                place.projections.push(Projection::Deref);
            } else {
                *operand = Operand::Symbolic(trust_types::Formula::Int(1));
            }
        }
        assert!(
            trust_source_contract::exact_ensures_body_group(
                &source.function,
                &source.compiler_contracts,
                source.source_contract_index,
                &source.verification_conditions,
                source.target_pointer_width_bits,
                None,
            )
            .is_none(),
            "effect/control mutation {mutation}"
        );
    }
}

fn fixture() -> &'static SourceClauseCertificate {
    static FIXTURE: OnceLock<SourceClauseCertificate> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        // Retain the once-checked body proof. This suite exercises replay,
        // not repeated proof search for an unchanged source input.
        let mut certificate = retained_fixture();
        let input: serde_json::Value =
            serde_json::from_str(include_str!("fixtures/source-clause-actual-input.json")).unwrap();
        assert_eq!(serde_json::to_value(&certificate.source.function).unwrap(), input["function"]);
        assert_eq!(
            serde_json::to_value(&certificate.source.compiler_contracts).unwrap(),
            input["compiler_contracts"]
        );
        let source = &certificate.source;
        let current = trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
            &source.function,
            &source.compiler_contracts,
            &source.verification_conditions,
            &source.crate_name,
            source.stable_crate_id,
            source.target_pointer_width_bits,
        );
        // Keep the capture immutable. Only key order in direct predicate values
        // and embedded predicate text changed. Every other byte must still
        // equal the current typed producer before full replay accepts it.
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
                    serde_json::to_string(&trust_types::canonical_json_value(&payload)).unwrap();
            }
        }
        assert_eq!(
            serde_json::to_vec(&canonical_projection).unwrap(),
            serde_json::to_vec(&current).unwrap()
        );
        certificate.source.public_bundle = current;
        certificate
    })
}

fn retained_fixture() -> SourceClauseCertificate {
    serde_json::from_slice(include_bytes!("fixtures/source-clause-actual-certificate.json"))
        .unwrap()
}

#[test]
fn retained_typed_payload_key_order_replays_without_rewriting_the_question() {
    let certificate = retained_fixture();
    let original = serde_json::to_vec(&certificate).unwrap();
    let checked = replay_source_clause(&certificate).unwrap();
    assert_eq!(serde_json::to_vec(checked.certificate()).unwrap(), original);
    assert_eq!(checked.proof_strength(), trust_types::ProofStrength::deductive());
}

#[test]
fn actual_query_source_proof_replays_and_reuses_checked_body_fact() {
    let certificate = fixture();
    let checked = replay_source_clause(certificate).unwrap();
    assert_eq!(checked.proof_strength(), trust_types::ProofStrength::deductive());
    assert_eq!(replay_source_clause(certificate).unwrap().digest(), checked.digest());
    if let Some(dir) = std::env::var_os("TRUST_SOURCE_CLAUSE_ARTIFACT_DIR") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let write = |name, bytes: Vec<u8>| {
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(dir.join(name))
                .unwrap();
            f.write_all(&bytes).unwrap();
        };
        write("certificate.json", serde_json::to_vec_pretty(certificate).unwrap());
        write(
            "transport-proof.json",
            serde_json::to_vec_pretty(&checked.transport_evidence().unwrap()).unwrap(),
        );
    }
}

#[test]
fn source_proof_rejects_changed_claim_body_certificate_group_and_context() {
    let mut mutants = Vec::new();
    let mut c = fixture().clone();
    c.source.source_vc.formula = trust_types::Formula::Bool(true);
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.source_contract_index = 1;
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.compiler_contracts.typed_propositions[0].formula = trust_types::Formula::Bool(true);
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.function.postconditions[0] = trust_types::Formula::Bool(true);
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.function.body.blocks.clear();
    mutants.push(c);
    let mut c = fixture().clone();
    c.body_proofs.clear();
    mutants.push(c);
    let mut c = fixture().clone();
    c.body_proofs.push(c.body_proofs[0].clone());
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.verification_conditions.clear();
    mutants.push(c);
    let mut c = fixture().clone();
    c.body_proofs[0].claim_digest_sha256 = "a".repeat(64);
    mutants.push(c);
    let mut c = fixture().clone();
    c.body_proofs[0].public_obligation_id.push_str("-other");
    mutants.push(c);
    let mut c = fixture().clone();
    if let trust_ir::ProofEvidence::CleanCic { lineage, .. } = &mut c.body_proofs[0].evidence {
        lineage.bytes[0] ^= 1;
    } else {
        panic!("not CleanCic")
    };
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.public_bundle.metadata.push(trust_verifier_api::MetadataEntry {
        key: "test.assumption".into(),
        value: "false".into(),
    });
    mutants.push(c);
    let mut c = fixture().clone();
    c.source.public_bundle.obligations.push(c.source.public_bundle.obligations[0].clone());
    mutants.push(c);
    for (index, c) in mutants.iter().enumerate() {
        assert!(replay_source_clause(c).is_err(), "mutant {index}");
    }
}

#[test]
fn source_question_digest_uses_canonical_public_predicate_values() {
    let original = fixture();
    let digest =
        source_clause_input_digest_sha256(&original.source, &original.inferred_returns).unwrap();
    let mut consumer = original.clone();
    let mut predicates = 0;
    for contract in &mut consumer.source.public_bundle.contracts {
        if let trust_verifier_api::ContractPredicate::TrustIr { value, .. } =
            &mut contract.predicate
        {
            // Model the sorted-map representation of the same source question
            // in a consumer compiled without serde_json/preserve_order.
            trust_types::canonicalize_json_in_place(value);
            predicates += 1;
        }
    }
    assert!(predicates > 0, "exercise the actual captured source predicate");
    assert_eq!(consumer.source.public_bundle, original.source.public_bundle);
    assert_eq!(
        source_clause_input_digest_sha256(&consumer.source, &consumer.inferred_returns).unwrap(),
        digest,
        "the current producer's typed question must survive the consumer's map representation"
    );
}

#[test]
fn original_input_identity_binds_typed_bodies_but_not_replacement_proofs() {
    let original = fixture();
    let digest =
        source_clause_input_digest_sha256(&original.source, &original.inferred_returns).unwrap();
    let decoded: SourceClauseCertificate =
        serde_json::from_slice(&serde_json::to_vec(original).unwrap()).unwrap();
    assert_eq!(
        source_clause_input_digest_sha256(&decoded.source, &decoded.inferred_returns),
        Some(digest.clone())
    );
    let mut changed = original.clone();
    changed.body_proofs.clear();
    assert_eq!(
        source_clause_input_digest_sha256(&changed.source, &changed.inferred_returns),
        Some(digest.clone()),
        "proof payloads do not change the original typed question"
    );
    changed.source.function.body.blocks.clear();
    assert_ne!(
        source_clause_input_digest_sha256(&changed.source, &changed.inferred_returns),
        Some(digest.clone())
    );
    let graph: trust_certify::inferred_return_proof::InferredReturnProofGraph =
        serde_json::from_slice(include_bytes!("fixtures/inferred-return-actual-proof-graph.json"))
            .unwrap();
    let graph_digest = source_clause_input_digest_sha256(&original.source, &graph).unwrap();
    let mut changed_graph = graph.clone();
    changed_graph.nodes[0].evidence.clear();
    assert_eq!(
        source_clause_input_digest_sha256(&original.source, &changed_graph),
        Some(graph_digest.clone())
    );
    changed_graph.nodes[0].function.body.blocks.clear();
    assert_ne!(
        source_clause_input_digest_sha256(&original.source, &changed_graph),
        Some(graph_digest)
    );
}

/// Regression for EW18-REDS-1(4)(d): a real current-context certificate must
/// not escape the original function's exhausted count merely by replaying on
/// the native large-stack worker. The unchanged positive performs full current
/// VC regeneration and kernel replay before the exhausted-budget refusal.
#[test]
fn actual_query_replay_respects_the_original_function_budget() {
    use trust_types::determinism::StopCause;
    use trust_types::verify_budget::{VerifyBudgetGuard, exhausted_readonly, exhaustion_cause};

    let certificate = fixture();
    let positive = replay_source_clause(certificate)
        .expect("unchanged real proof replays with the current kernel");
    assert_eq!(positive.proof_strength(), trust_types::ProofStrength::deductive());
    let _budget = VerifyBudgetGuard::install(None, 0);
    let result = replay_source_clause(certificate);
    assert!(result.is_err(), "large-stack replay escaped the original function's spent budget");
    assert!(result.unwrap_err().contains("function verification budget"));
    assert!(exhausted_readonly());
    assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
}

#[test]
fn actual_query_replay_keeps_the_original_expired_deadline() {
    use std::time::{Duration, Instant};

    use trust_types::determinism::StopCause;
    use trust_types::verify_budget::{
        VerifyBudgetGuard, WALL_POLL_INTERVAL, current_deadline, exhaustion_cause,
    };

    let certificate = fixture();
    replay_source_clause(certificate).expect("unchanged real proof has a current-kernel replay");
    let original = Instant::now() - Duration::from_millis(1);
    // The first regeneration poll reads this already-expired clock, so a small
    // fixture cannot accidentally avoid the amortized clock observation.
    let _budget = VerifyBudgetGuard::install(Some(original), WALL_POLL_INTERVAL);
    let result = replay_source_clause(certificate);
    assert!(result.is_err(), "large-stack replay renewed or lost the original expired deadline");
    assert!(result.unwrap_err().contains("function verification budget"));
    assert_eq!(current_deadline(), Some(original));
    assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
}
