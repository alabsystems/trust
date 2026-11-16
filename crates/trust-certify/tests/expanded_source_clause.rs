//! Real macro-expanded typed inputs captured by the compiler callback. This
//! exercises the Trusted translation/replay boundary; it is not a release or
//! a claim that serialized provenance authenticates itself.
use serde::Deserialize;
use trust_certify::source_clause_proof::*;
use trust_types::expanded_function_identity::*;
use trust_types::*;

#[derive(Deserialize)]
struct Captured {
    origin: Origin,
    function: VerifiableFunction,
    compiler_contracts: CompilerContractBundle,
}
#[derive(Deserialize)]
struct Origin {
    function_path: String,
    function_def_path_hash: [u64; 2],
    macro_path: String,
    macro_def_path_hash: [u64; 2],
    definition_span: SourceSpan,
    definition_text: String,
    invocation_span: SourceSpan,
    invocation_text: String,
}
fn certificate(bytes: &[u8]) -> SourceClauseCertificate {
    let captured: Captured = trust_types::json_depth::from_slice_deep(bytes).unwrap();
    let function = captured.function;
    let contracts = captured.compiler_contracts;
    let origin = captured.origin;
    let identity = ExpandedFunctionIdentity {
        schema: EXPANDED_FUNCTION_IDENTITY_SCHEMA.into(),
        function_path: origin.function_path,
        function_def_path_hash: origin.function_def_path_hash,
        macro_path: origin.macro_path,
        macro_def_path_hash: origin.macro_def_path_hash,
        definition: ExpansionSourceFragment::from_exact_snippet(
            origin.definition_span,
            &origin.definition_text,
        )
        .unwrap(),
        invocation: ExpansionSourceFragment::from_exact_snippet(
            origin.invocation_span,
            &origin.invocation_text,
        )
        .unwrap(),
        typed_input_sha256: expanded_typed_input_digest(&function, &contracts).unwrap(),
    };
    assert!(identity.matches_input(&function, &contracts));
    let vcs = trust_vcgen::generate_vcs(&function);
    let source_vc = trust_source_contract::boolean_ensures_source_marker(&function, 0).unwrap();
    let public_bundle =
        trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
            &function,
            &contracts,
            &vcs,
            "expanded_fixture",
            identity.function_def_path_hash[0],
            Some(64),
        );
    let source_bundle =
        trust_source_contract::contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &contracts,
            "expanded_fixture",
            identity.function_def_path_hash[0],
            Some(64),
        );
    assert_eq!(source_bundle.obligations.len(), 1);
    let obligation_id = source_bundle.obligations[0].obligation_id.clone();
    let group = trust_source_contract::exact_boolean_ensures_body_group(
        &function,
        &contracts,
        0,
        &vcs,
        Some(64),
    )
    .unwrap();
    let target = "aarch64-apple-darwin;ptr64".to_string();
    let body_proofs = group
        .body_indices()
        .iter()
        .map(|&index| {
            let vc = &vcs[index];
            SourceBodyProof {
                vc_index: index,
                public_obligation_id:
                    trust_source_contract::verifier_vc_content_identity_with_crate_name(
                        &function,
                        index,
                        vc,
                        "expanded_fixture",
                    )
                    .obligation_id,
                claim_digest_sha256: original_vc_snapshot::exact_vc_claim_digest_sha256(
                    vc,
                    true,
                    Some(&target),
                )
                .unwrap(),
                evidence: trust_certify::certify_vc(vc)
                    .expect("actual constant-false body must be independently certified"),
                vc: vc.clone(),
            }
        })
        .collect();
    SourceClauseCertificate {
        schema: EXPANDED_SCHEMA.into(),
        source: SourceClauseInput {
            function,
            compiler_contracts: contracts,
            public_bundle,
            obligation_id,
            source_contract_index: 0,
            stable_crate_id: identity.function_def_path_hash[0],
            crate_name: "expanded_fixture".into(),
            target_pointer_width_bits: Some(64),
            source_text_sha256: None,
            expanded_function_identity: Some(identity),
            source_vc,
            verification_conditions: vcs,
            overflow_checks: true,
            target,
        },
        body_proofs,
        inferred_returns: Default::default(),
    }
}
fn outer(
    c: &SourceClauseCertificate,
) -> (obligation_identity::ObligationIdentity, OriginalVcSnapshot) {
    let source = &c.source;
    let typed = source_clause_input_digest_sha256(source, &c.inferred_returns).unwrap();
    let expanded = source.expanded_function_identity.as_ref();
    let claim = original_vc_snapshot::exact_vc_claim_digest_with_expanded_identity(
        &source.source_vc,
        true,
        Some(&source.target),
        Some(&typed),
        expanded,
    )
    .unwrap();
    let snapshot = OriginalVcSnapshot::capture_with_expanded_identity(
        &source.source_vc,
        true,
        &source.target,
        &source.obligation_id,
        &claim,
        Some(&typed),
        expanded,
    )
    .unwrap();
    (
        obligation_identity::ObligationIdentity {
            key: format!("{}#0000000000000000", source.function.def_path),
            package: source.crate_name.clone(),
            function_source_sha256: None,
            expanded_function_identity: expanded.cloned(),
        },
        snapshot,
    )
}
fn check(
    c: &SourceClauseCertificate,
    identity: &obligation_identity::ObligationIdentity,
    snapshot: &OriginalVcSnapshot,
) -> bool {
    let proof = replay_source_clause(c).unwrap().transport_evidence().unwrap();
    let result = source_clause_certificate_payload(
        &proof,
        Some(&snapshot.obligation_id),
        Some(identity),
        Some(&snapshot.claim_digest_sha256),
        Some(snapshot),
        None,
    );
    if let Err(error) = &result {
        eprintln!("publication refusal: {error}");
    }
    result.is_ok()
}
#[test]
fn actual_macro_source_certificate_binds_both_live_outer_identities() {
    let c = certificate(include_bytes!("../../trust-types/tests/fixtures/expanded_base.json"));
    let (identity, snapshot) = outer(&c);
    assert!(check(&c, &identity, &snapshot));
    if let Some(directory) = std::env::var_os("TRUST_EXPANDED_FIXTURE_OUT") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("certificate.json"), serde_json::to_vec_pretty(&c).unwrap())
            .unwrap();
        std::fs::write(
            directory.join("proof.json"),
            serde_json::to_vec_pretty(
                &replay_source_clause(&c).unwrap().transport_evidence().unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
    }
    assert_eq!(snapshot.schema, original_vc_snapshot::EXPANDED_ORIGINAL_VC_SNAPSHOT_SCHEMA);
    let mut other = identity.clone();
    other.expanded_function_identity = None;
    assert!(!check(&c, &other, &snapshot));
    let mut other = snapshot.clone();
    other.expanded_function_identity = None;
    assert!(!check(&c, &identity, &other));
    let mut wrong = c.clone();
    wrong.schema = SCHEMA.into();
    assert!(replay_source_clause(&wrong).is_err());
    let mut wrong = c.clone();
    wrong.source.source_text_sha256 = Some("1".repeat(64));
    assert!(replay_source_clause(&wrong).is_err());
    let mut wrong = c.clone();
    wrong.source.stable_crate_id += 1;
    assert!(replay_source_clause(&wrong).is_err());
    let mut wrong = c.clone();
    wrong.source.expanded_function_identity.as_mut().unwrap().typed_input_sha256 = "0".repeat(64);
    assert!(replay_source_clause(&wrong).is_err());
}
#[test]
fn actual_valid_alternate_macro_expansion_cannot_answer_original_source_question() {
    let a = certificate(include_bytes!("../../trust-types/tests/fixtures/expanded_base.json"));
    let b =
        certificate(include_bytes!("../../trust-types/tests/fixtures/expanded_equivalent.json"));
    // Both programs return false and have their own independently checked body
    // proofs; rejection must come from the externally bound original question.
    assert!(replay_source_clause(&a).is_ok());
    assert!(replay_source_clause(&b).is_ok());
    let (ia, sa) = outer(&a);
    let (ib, sb) = outer(&b);
    assert_ne!(sa.typed_input_digest_sha256, sb.typed_input_digest_sha256);
    assert!(check(&a, &ia, &sa));
    assert!(check(&b, &ib, &sb));
    if let Some(directory) = std::env::var_os("TRUST_EXPANDED_FIXTURE_OUT") {
        std::fs::write(
            std::path::PathBuf::from(directory).join("alternate-certificate.json"),
            serde_json::to_vec_pretty(&b).unwrap(),
        )
        .unwrap();
    }
    assert!(!check(&b, &ia, &sa));
    assert!(!check(&a, &ib, &sb));
}

#[test]
fn actual_macro_wrong_body_or_contract_refuses_body_certificate() {
    for bytes in [
        &include_bytes!("../../trust-types/tests/fixtures/expanded_body_change.json")[..],
        &include_bytes!("../../trust-types/tests/fixtures/expanded_arguments.json")[..],
        &include_bytes!("../../trust-types/tests/fixtures/expanded_contract.json")[..],
    ] {
        let captured: Captured = trust_types::json_depth::from_slice_deep(bytes).unwrap();
        let vcs = trust_vcgen::generate_vcs(&captured.function);
        let group = trust_source_contract::exact_boolean_ensures_body_group(
            &captured.function,
            &captured.compiler_contracts,
            0,
            &vcs,
            Some(64),
        )
        .unwrap();
        assert!(
            group
                .body_indices()
                .iter()
                .any(|&index| trust_certify::certify_vc(&vcs[index]).is_none())
        );
    }
}
