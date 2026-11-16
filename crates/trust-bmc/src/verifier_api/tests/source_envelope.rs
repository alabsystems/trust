//! The canonical source-only record is metadata, never proof authority.

use super::*;

/// Exercise the production bridge over existing compiler-captured bodies,
/// rather than recreating the consumer's expected JSON in this test.
fn bridge_source_record() -> (
    TrustObligation,
    trust_ir::ProofId,
    trust_ir::ProofObligationSourceIdentity,
    trust_ir::ProofFormula,
) {
    // This real caller/callee pair takes the resolved-call arm and mints the
    // whole-function panic carrier. A per-site arithmetic check instead emits
    // a predicate formula, which is a different consumer contract.
    let functions: [trust_types::VerifiableFunction; 2] = [
        include_str!("../../../../trust-ir-bridge/src/testdata/fp11/mixed_always_panics.json"),
        include_str!("../../../../trust-ir-bridge/src/testdata/fp11/leaf_div.json"),
    ]
    .map(|raw| serde_json::from_str(raw).expect("the checked-in compiler body must decode"));
    let module = trust_ir_bridge::lower_mir_compat_functions_to_trust_ir(
        "source_envelope_fixture",
        &functions,
    )
    .expect("the real bridge must lower the checked-in caller/callee pair");
    let proof = module
        .proof_obligations
        .iter()
        .find(|proof| {
            proof
                .source
                .as_ref()
                .is_some_and(|source| source.source_id.starts_with("mir-assertions:"))
        })
        .expect("the bridge emits the whole-function assertion source record");
    let source = proof.source.as_ref().expect("the producer preserves source identity");
    let range = source.range.expect("the captured body has an exact source range");
    let mut public = obligation(ObligationKind::Assertion, &source.source_id);
    public.source = SourceLocation {
        file: Some(module.file_name(range.file).expect("source file is interned").to_owned()),
        line: Some(range.start_line),
        column: Some(range.start_col),
        end_line: Some(range.end_line),
        end_column: Some(range.end_col),
    };
    (
        public,
        proof.id,
        source.clone(),
        proof.formula.as_ref().expect("the producer retains the source formula").clone(),
    )
}

#[test]
fn source_envelope_accepts_actual_bridge_four_field_record() {
    let (public, proof_id, source, formula) = bridge_source_record();
    let record: serde_json::Value = serde_json::from_str(&formula.payload).unwrap();
    let mut keys = record.as_object().unwrap().keys().map(String::as_str).collect::<Vec<_>>();
    keys.sort_unstable();
    assert_eq!(keys, ["assertion_id", "native_assertion_id", "source_id", "span"]);
    assert_eq!(formula.schema, trust_ir_bridge::TRUST_OBLIGATION_SOURCE_SCHEMA);
    assert!(formula.bindings.is_empty());
    assert!(formula.smtlib.is_none() && formula.sort.is_none());
    validate_native_trust_ir_public_formula_binding(&public, proof_id, &source, &formula)
        .expect("the actual closed producer record must be readable by MC");
}

#[test]
fn source_envelope_rejects_extra_and_duplicate_fields() {
    let (public, proof_id, source, original) = bridge_source_record();
    let mut extra: serde_json::Value = serde_json::from_str(&original.payload).unwrap();
    extra["public_obligation_id"] = serde_json::json!(public.obligation_id);
    let duplicate = format!(
        "{},\"source_id\":{}}}",
        original.payload.strip_suffix('}').unwrap(),
        serde_json::to_string(&source.source_id).unwrap()
    );
    // The duplicate has the SAME value. Parsing it into a Value would hide the
    // duplicate; canonical byte equality must still reject the original wire.
    for payload in [extra.to_string(), duplicate] {
        let mut formula = original.clone();
        formula.payload = payload;
        let reason =
            validate_native_trust_ir_public_formula_binding(&public, proof_id, &source, &formula)
                .expect_err("extra or duplicate fields are not a canonical source envelope");
        assert!(reason.contains("exact canonical public source envelope"), "{reason}");
    }
}

#[test]
fn source_envelope_rejects_changed_source_assertion_number_and_span() {
    let (public, proof_id, source, original) = bridge_source_record();
    let record: serde_json::Value = serde_json::from_str(&original.payload).unwrap();
    let mut changed_source = record.clone();
    changed_source["source_id"] = serde_json::json!("other-source");
    let mut changed_assertion = record.clone();
    changed_assertion["assertion_id"] = serde_json::json!("trust-assertion:other-source");
    let mut changed_number = record.clone();
    changed_number["native_assertion_id"] =
        serde_json::json!(record["native_assertion_id"].as_u64().unwrap().wrapping_add(1));
    let mut changed_span = record.clone();
    changed_span["span"]["col_end"] =
        serde_json::json!(record["span"]["col_end"].as_u64().unwrap().wrapping_add(1));
    let mut missing_number = record;
    missing_number.as_object_mut().unwrap().remove("native_assertion_id");
    for (name, payload) in [
        ("source", changed_source),
        ("assertion", changed_assertion),
        ("numeric assertion", changed_number),
        ("span", changed_span),
        ("missing numeric assertion", missing_number),
    ] {
        let mut formula = original.clone();
        formula.payload = payload.to_string();
        let reason =
            validate_native_trust_ir_public_formula_binding(&public, proof_id, &source, &formula)
                .expect_err(name);
        assert!(reason.contains("exact canonical public source envelope"), "{name}: {reason}");
    }
}

#[test]
fn source_envelope_rejects_schema_smtlib_sort_and_fail_closed_marker_changes() {
    let (public, proof_id, source, original) = bridge_source_record();
    let mut schema = original.clone();
    schema.schema.push_str("-other");
    let mut smtlib = original.clone();
    smtlib.smtlib = Some("true".to_owned());
    let mut sort = original.clone();
    sort.sort = Some("Bool".to_owned());
    let mut marker = original.clone();
    let mut payload: serde_json::Value = serde_json::from_str(&marker.payload).unwrap();
    payload["predicate_parse_failed"] = serde_json::json!("unparseable-contract-predicate");
    marker.payload = payload.to_string();
    for formula in [schema, smtlib, sort, marker] {
        let reason =
            validate_native_trust_ir_public_formula_binding(&public, proof_id, &source, &formula)
                .expect_err("noncanonical source metadata cannot gain formula authority");
        assert!(reason.contains("exact canonical public source envelope"), "{reason}");
    }
}

#[test]
fn source_envelope_preserves_independent_public_compiler_and_replay_joins() {
    type Mutation = fn(&mut trust_ir::NativeVerificationBundle);
    let cases: &[(&str, Mutation, &str)] = &[
        (
            "embedded public id",
            |native| {
                native.module.proof_obligations[0]
                    .source
                    .as_mut()
                    .unwrap()
                    .public
                    .as_mut()
                    .unwrap()
                    .obligation_id
                    .push_str("-other");
            },
            "embeds public obligation id",
        ),
        (
            "compiler public id",
            |native| {
                native.compiler_facts.obligation_sources[0].public_obligation_id.push_str("-other");
            },
            "compiler facts bind public id",
        ),
        (
            "embedded source",
            |native| {
                native.module.proof_obligations[0]
                    .source
                    .as_mut()
                    .unwrap()
                    .source_id
                    .push_str("-other");
            },
            "source/assertion identity",
        ),
        (
            "embedded assertion",
            |native| {
                native.module.proof_obligations[0]
                    .source
                    .as_mut()
                    .unwrap()
                    .assertion_id
                    .push_str("-other");
            },
            "source/assertion identity",
        ),
        (
            "embedded span",
            |native| {
                native.module.proof_obligations[0]
                    .source
                    .as_mut()
                    .unwrap()
                    .range
                    .as_mut()
                    .unwrap()
                    .end_col += 1;
            },
            "embedded source range",
        ),
        (
            "compiler numeric assertion",
            |native| {
                let source = &mut native.compiler_facts.obligation_sources[0];
                source.assertion_id = Some(trust_ir::NativeAssertionId::new(
                    source.assertion_id.unwrap().index().wrapping_add(1),
                ));
            },
            "compiler-fact assertion",
        ),
        (
            "compiler span",
            |native| {
                native.compiler_facts.obligation_sources[0].span.as_mut().unwrap().col += 1;
            },
            "compiler-fact span",
        ),
        (
            "compiler function",
            |native| {
                native.compiler_facts.obligation_sources[0].function =
                    Some(trust_ir::FuncId::new(u32::MAX));
            },
            "function projection disagrees",
        ),
        (
            "replay formula",
            |native| {
                let trust_ir::NativeVerificationRequest::TrustMc(request) = &mut native.requests[0]
                else {
                    panic!("fixture is a TrustMC request")
                };
                request.provenance.replay_context.atoms[0].formula.payload.push(' ');
            },
            "assertion replay atom",
        ),
    ];
    let public = compiler_style_safe_public_bundle();
    let native =
        bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &public);
    validate_compiler_style_public_claim_for_test(&public, &native, 0)
        .expect("the canonical source-only full claim binds before mutation");
    for &(name, mutate, expected) in cases {
        let mut changed = native.clone();
        mutate(&mut changed);
        let reason =
            validate_compiler_style_public_claim_for_test(&public, &changed, 0).expect_err(name);
        assert!(reason.contains(expected), "{name}: expected {expected}, got {reason}");
    }
}

#[test]
fn native_public_identity_matches_shared_validator_and_legacy_refusals() {
    use trust_verifier_api::native_contract_claim::validate_native_public_obligation_identity;

    let public = compiler_style_safe_public_bundle();
    let native =
        bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &public);
    let obligation = &public.obligations[0];
    let digest = public.canonical_obligation_semantic_digest_sha256(obligation).unwrap();
    validate_compiler_style_public_claim_for_test(&public, &native, 0).unwrap();

    // Keep the retired predicate only as a differential test oracle. The
    // production adapter now delegates this identity boundary to the API.
    let legacy_accepts = |proof: &trust_ir::ProofObligation| {
        proof.source.as_ref().and_then(|source| source.public.as_ref()).is_some_and(|id| {
            id.obligation_id == obligation.obligation_id
                && id.semantic_digest.algorithm == trust_ir::ProofDigestAlgorithm::Sha256
                && !id.semantic_digest.is_zero()
                && id.semantic_digest.to_string() == format!("sha256:{digest}")
        })
    };
    let original = &native.module.proof_obligations[0];
    assert!(legacy_accepts(original));
    validate_native_public_obligation_identity(original, &obligation.obligation_id, &digest)
        .unwrap();
    for (mutation, expected) in [
        (0, "missing its embedded source identity"),
        (1, "missing its atomic public-obligation identity"),
        (2, "embeds public obligation id"),
        (3, "embedded public semantic digest"),
        (4, "embedded public semantic digest"),
        (5, "embedded public semantic digest"),
    ] {
        let mut changed = native.clone();
        let proof = &mut changed.module.proof_obligations[0];
        match mutation {
            0 => proof.source = None,
            1 => proof.source.as_mut().unwrap().public = None,
            _ => {
                let id = proof.source.as_mut().unwrap().public.as_mut().unwrap();
                match mutation {
                    2 => id.obligation_id.push_str("-other"),
                    3 => id.semantic_digest = trust_ir::ProofDigest::sha256([0; 32]),
                    4 => id.semantic_digest = trust_ir::ProofDigest::sha256([37; 32]),
                    5 => {
                        id.semantic_digest.algorithm =
                            trust_ir::ProofDigestAlgorithm::TrustIrStableV1
                    }
                    _ => unreachable!(),
                }
            }
        }
        let shared =
            validate_native_public_obligation_identity(proof, &obligation.obligation_id, &digest);
        assert_eq!(shared.is_ok(), legacy_accepts(proof), "mutation {mutation}");
        assert!(shared.is_err(), "mutation {mutation}");
        let reason = validate_compiler_style_public_claim_for_test(&public, &changed, 0)
            .expect_err("an invalid native/public identity must remain refused");
        assert!(reason.contains(expected), "mutation {mutation}: {reason}");
    }
}
