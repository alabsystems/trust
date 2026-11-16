#![cfg(feature = "native-trust-ir-claims")]

use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::{ProofDigest, ProofFormula, PublicObligationIdentity};
use trust_verifier_api::native_contract_claim::{
    validate_native_public_contract_claim, validate_native_public_source_projection,
};
use trust_verifier_api::*;

fn identity(bundle: &TrustContractBundle) -> PublicObligationIdentity {
    let digest =
        bundle.canonical_obligation_semantic_digest_sha256(&bundle.obligations[0]).unwrap();
    PublicObligationIdentity {
        obligation_id: bundle.obligations[0].obligation_id.clone(),
        semantic_digest: ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        })),
    }
}

fn native_proof(
    identity: Option<&PublicObligationIdentity>,
    formula: Option<&ProofFormula>,
    obligation: &TrustObligation,
) -> trust_ir::ProofObligation {
    let id = obligation
        .contract_id
        .as_deref()
        .or(obligation.proof_item_id.as_deref())
        .unwrap_or(&obligation.obligation_id);
    let mut source =
        trust_ir::ProofObligationSourceIdentity::new(id, format!("trust-assertion:{id}"));
    source.public = identity.cloned();
    let mut proof = trust_ir::ProofObligation::new(
        trust_ir::ProofId::new(0),
        trust_ir::ObligationKind::Postcondition,
        trust_ir::ProofStatus::Pending,
        "original public clause",
    )
    .with_source(source);
    proof.formula = formula.cloned();
    proof
}

fn validate_claim(
    identity: Option<&PublicObligationIdentity>,
    formula: Option<&ProofFormula>,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<(), String> {
    validate_native_public_contract_claim(
        &trust_ir::Module::new("source-less"),
        &native_proof(identity, formula, obligation),
        bundle,
        obligation,
    )
}

fn fixture() -> (TrustContractBundle, ProofFormula) {
    let mut bundle = TrustContractBundle::empty(
        "raw-claim",
        BundleSubject::Function { crate_name: "test".into(), path: "identity".into() },
    );
    let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", "(r : bool) == (x : bool)");
    formula.bindings = vec![
        (
            "x".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
        ),
        (
            "r".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::ResultSlot { index: 0 } },
        ),
    ];
    bundle.contracts.push(TrustContract {
        contract_id: "post".into(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::CanonicalJson {
            schema: formula.schema.clone(),
            value: formula.payload.clone().into(),
        },
        source: SourceLocation::default(),
        metadata: vec![MetadataEntry {
            key: TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
            value: serde_json::to_string(&formula.bindings).unwrap(),
        }],
    });
    bundle.obligations.push(TrustObligation {
        obligation_id: "obligation:identity:post".into(),
        kind: ObligationKind::Postcondition,
        contract_id: Some("post".into()),
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "identity returns its argument".into(),
        required_strength: None,
        summary_facts: vec![],
        metadata: vec![],
    });
    (bundle, formula)
}

#[test]
fn exact_original_clause_binds_without_body_vc_metadata() {
    let (bundle, formula) = fixture();
    let original = bundle.clone();
    validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
        .unwrap();
    assert_eq!(bundle, original);
}

#[test]
fn changed_identity_formula_binding_and_rendering_are_rejected() {
    let (bundle, formula) = fixture();
    let mut wrong_id = identity(&bundle);
    wrong_id.obligation_id.push_str("-other");
    assert!(
        validate_claim(Some(&wrong_id), Some(&formula), &bundle, &bundle.obligations[0]).is_err()
    );
    let mut wrong_digest = identity(&bundle);
    wrong_digest.semantic_digest = ProofDigest::sha256([7; 32]);
    assert!(
        validate_claim(Some(&wrong_digest), Some(&formula), &bundle, &bundle.obligations[0])
            .is_err()
    );
    for mode in 0..5 {
        let mut changed = formula.clone();
        match mode {
            0 => changed.payload = "(r : bool) != (x : bool)".into(),
            1 => changed.schema.push_str("-other"),
            2 => changed.bindings[0].1.place = ClausePlace::Param { index: 1 },
            3 => changed.smtlib = Some("true".into()),
            _ => changed.sort = Some("Bool".into()),
        }
        assert!(
            validate_claim(
                Some(&identity(&bundle)),
                Some(&changed),
                &bundle,
                &bundle.obligations[0]
            )
            .is_err(),
            "mutation {mode}"
        );
    }
}

#[test]
fn rehashed_changed_contract_and_ambiguous_map_still_refuse() {
    let (mut bundle, formula) = fixture();
    bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: formula.schema.clone(),
        value: "(r : bool) != (x : bool)".into(),
    };
    assert!(
        validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
            .is_err()
    );
    let (mut bundle, formula) = fixture();
    let good_identity = identity(&bundle);
    let duplicate = bundle.contracts[0].metadata[0].clone();
    bundle.contracts[0].metadata.push(duplicate);
    assert!(
        validate_claim(Some(&good_identity), Some(&formula), &bundle, &bundle.obligations[0])
            .is_err()
    );
}

fn typed_fixture() -> (TrustContractBundle, ProofFormula) {
    let (mut bundle, mut formula) = fixture();
    let predicate = TrustSpecPredicate::new(
        TrustSpecExpr::binary(
            TrustSpecBinaryOp::Eq,
            TrustSpecExpr::result(TrustSpecSort::Bool),
            TrustSpecExpr::variable("x", TrustSpecSort::Bool),
        ),
        vec![TrustSpecVariable {
            name: "x".into(),
            sort: TrustSpecSort::Bool,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        }],
    );
    formula.schema = trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.into();
    formula.payload=trust_verifier_api::trust_spec_native_formula::trust_spec_predicate_to_trust_formula_payload(&predicate).unwrap();
    formula.bindings[1].0 = "result".into();
    bundle.contracts[0].predicate = predicate.into_contract_predicate().unwrap();
    bundle.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    (bundle, formula)
}

#[test]
fn original_trust_spec_uses_the_shared_strict_converter() {
    let (bundle, formula) = typed_fixture();
    validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
        .unwrap();
}

fn typed_scalar_binding_fixture(
    public_sort: TrustSpecSort,
    carrier: ClauseSort,
) -> (TrustContractBundle, ProofFormula) {
    let (mut bundle, mut formula) = typed_fixture();
    let predicate = TrustSpecPredicate::new(
        TrustSpecExpr::binary(
            TrustSpecBinaryOp::Eq,
            TrustSpecExpr::result(public_sort),
            TrustSpecExpr::variable("x", public_sort),
        ),
        vec![TrustSpecVariable {
            name: "x".into(),
            sort: public_sort,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        }],
    );
    formula.payload = trust_verifier_api::trust_spec_native_formula::
        trust_spec_predicate_to_trust_formula_payload(&predicate).unwrap();
    for (_, binding) in &mut formula.bindings {
        binding.sort = carrier.clone();
    }
    bundle.contracts[0].predicate = predicate.into_contract_predicate().unwrap();
    bundle.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    (bundle, formula)
}

#[test]
fn typed_claim_rejects_scalar_domain_substitution_even_after_both_maps_and_public_rehash() {
    let mut accepted = Vec::new();
    for (public_sort, good_carrier, changed_carrier) in [
        (TrustSpecSort::Bool, ClauseSort::Bool, ClauseSort::Int),
        (TrustSpecSort::Bool, ClauseSort::Bool, ClauseSort::BitVec(8)),
        (TrustSpecSort::Bool, ClauseSort::Bool, ClauseSort::BitVec(32)),
        (TrustSpecSort::Bool, ClauseSort::Bool, ClauseSort::BitVec(64)),
        (TrustSpecSort::Int, ClauseSort::BitVec(8), ClauseSort::Bool),
    ] {
        let (original, formula) = typed_scalar_binding_fixture(public_sort, good_carrier);
        // Correspondence controls only: these do not manufacture native body
        // admission or claim that the helper's old acceptance was a compiler proof.
        validate_claim(
            Some(&identity(&original)),
            Some(&formula),
            &original,
            &original.obligations[0],
        )
        .unwrap();
        for selected in [&[0][..], &[1][..], &[0, 1][..]] {
            let mut bundle = original.clone();
            let mut changed = formula.clone();
            for &index in selected {
                changed.bindings[index].1.sort = changed_carrier.clone();
            }
            // Mutate both allegedly exact maps, then recompute the real public
            // semantic digest. Map equality and a fresh digest cannot justify
            // interpreting the original Bool/Int claim at another scalar domain.
            bundle.contracts[0].metadata[0].value =
                serde_json::to_string(&changed.bindings).unwrap();
            if validate_claim(
                Some(&identity(&bundle)),
                Some(&changed),
                &bundle,
                &bundle.obligations[0],
            )
            .is_ok()
            {
                accepted.push(format!(
                    "public {public_sort:?}, substituted {changed_carrier:?}, bindings {selected:?}"
                ));
            }
        }
    }
    assert!(accepted.is_empty(), "accepted scalar substitutions: {accepted:?}");
}

#[test]
fn typed_claim_preserves_original_boolean_and_explicit_integer_carriers() {
    for (public_sort, carrier) in [
        (TrustSpecSort::Bool, ClauseSort::Bool),
        (TrustSpecSort::Int, ClauseSort::Int),
        (TrustSpecSort::Int, ClauseSort::BitVec(8)),
        (TrustSpecSort::Int, ClauseSort::BitVec(32)),
        (TrustSpecSort::Int, ClauseSort::BitVec(64)),
    ] {
        let (bundle, formula) = typed_scalar_binding_fixture(public_sort, carrier);
        let original_bundle = bundle.clone();
        let original_formula = formula.clone();
        validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
            .unwrap();
        // The exact width/place remains explicit in both original maps. Only
        // the owning native validator/binder can authenticate that carrier
        // against an actual body; this shared check grants no width or proof.
        assert_eq!(bundle, original_bundle);
        assert_eq!(formula, original_formula);
    }
}

#[test]
fn typed_result_placeholder_rejects_place_substitution_after_both_maps_and_public_rehash() {
    let (original, formula) = typed_fixture();
    let mut accepted = Vec::new();
    for place in [
        ClausePlace::Param { index: 0 },
        ClausePlace::Param { index: 1 },
        ClausePlace::ResultSlot { index: 1 },
    ] {
        let mut bundle = original.clone();
        let mut changed = formula.clone();
        changed.bindings.iter_mut().find(|(name, _)| name == "result").unwrap().1.place = place;
        bundle.contracts[0].metadata[0].value = serde_json::to_string(&changed.bindings).unwrap();
        if validate_claim(Some(&identity(&bundle)), Some(&changed), &bundle, &bundle.obligations[0])
            .is_ok()
        {
            accepted.push(place);
        }
    }
    assert!(accepted.is_empty(), "accepted original Result substitutions: {accepted:?}");
}

#[test]
fn a_parameter_named_result_is_not_a_result_placeholder() {
    let (mut bundle, mut formula) = typed_fixture();
    let predicate = TrustSpecPredicate::new(
        TrustSpecExpr::binary(
            TrustSpecBinaryOp::Eq,
            TrustSpecExpr::variable("result", TrustSpecSort::Bool),
            TrustSpecExpr::variable("result", TrustSpecSort::Bool),
        ),
        vec![TrustSpecVariable {
            name: "result".into(),
            sort: TrustSpecSort::Bool,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        }],
    );
    formula.payload = trust_verifier_api::trust_spec_native_formula::
        trust_spec_predicate_to_trust_formula_payload(&predicate).unwrap();
    formula.bindings = vec![(
        "result".into(),
        ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
    )];
    bundle.contracts[0].predicate = predicate.into_contract_predicate().unwrap();
    bundle.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
        .unwrap();
}

#[test]
fn typed_public_claim_accepts_reordered_raw_object_keys_without_changing_inputs() {
    let (bundle, mut formula) = typed_fixture();
    let public = identity(&bundle);
    // Exercise both sorted maps and the insertion order of the compiler's
    // serde_json/preserve_order build, including nested binding/body objects.
    for payload in [
        r#"{"schema":"trust_wp.trust-formula.v1","variables":[{"sort":"bool","name":"x"}],"result":{"sort":"bool","name":"result"},"body":{"op":"eq","rhs":{"var":"x"},"lhs":{"result":true}}}"#,
        r#"{ "body": { "lhs": { "result": true }, "op": "eq", "rhs": { "var": "x" } }, "result": { "name": "result", "sort": "bool" }, "schema": "trust_wp.trust-formula.v1", "variables": [{ "name": "x", "sort": "bool" }] }"#,
    ] {
        formula.payload = payload.into();
        let original = formula.clone();
        validate_claim(Some(&public), Some(&formula), &bundle, &bundle.obligations[0]).unwrap();
        assert_eq!(formula, original);
    }
}

#[test]
fn typed_public_claim_rejects_duplicate_raw_keys_at_every_level() {
    let (bundle, formula) = typed_fixture();
    for (original, duplicate) in [
        ("\"body\":", "\"body\":{\"bool\":false},\"body\":"),
        ("\"op\":\"eq\"", "\"op\":\"ne\",\"op\":\"eq\""),
        ("\"name\":\"x\"", "\"name\":\"other\",\"name\":\"x\""),
        ("\"result\":true", "\"result\":false,\"result\":true"),
    ] {
        let mut changed = formula.clone();
        changed.payload = formula.payload.replacen(original, duplicate, 1);
        assert_ne!(changed.payload, formula.payload, "mutation must apply");
        let error = validate_claim(
            Some(&identity(&bundle)),
            Some(&changed),
            &bundle,
            &bundle.obligations[0],
        )
        .unwrap_err();
        assert!(error.contains("duplicate"), "{error}");
    }
}

fn json_formula_fixture() -> (TrustContractBundle, ProofFormula) {
    let (mut bundle, formula) = typed_fixture();
    bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: formula.schema.clone(),
        value: serde_json::from_str(&formula.payload).unwrap(),
    };
    (bundle, formula)
}

#[test]
fn json_public_claim_keeps_object_order_irrelevant_and_input_bytes_intact() {
    let (bundle, mut formula) = json_formula_fixture();
    let original_bundle = bundle.clone();
    for payload in [
        formula.payload.clone(),
        r#"{ "variables": [{ "sort": "bool", "name": "x" }], "schema": "trust_wp.trust-formula.v1", "result": { "sort": "bool", "name": "result" }, "body": { "rhs": { "var": "x" }, "op": "eq", "lhs": { "result": true } } }"#.into(),
    ] {
        formula.payload = payload;
        let original_formula = formula.clone();
        validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
            .unwrap();
        assert_eq!(formula, original_formula);
        assert_eq!(bundle, original_bundle);
    }
    formula.payload = formula.payload.replace("\"eq\"", "\"ne\"");
    assert!(
        validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
            .is_err()
    );
}

#[test]
fn json_public_claim_rejects_duplicate_raw_keys_at_every_level() {
    let (bundle, formula) = json_formula_fixture();
    for (original, duplicate) in [
        ("\"body\":", "\"body\":{\"bool\":false},\"body\":"),
        ("\"op\":\"eq\"", "\"op\":\"ne\",\"op\":\"eq\""),
        ("\"name\":\"x\"", "\"name\":\"other\",\"name\":\"x\""),
        ("\"result\":true", "\"result\":false,\"result\":true"),
    ] {
        let mut changed = formula.clone();
        changed.payload = formula.payload.replacen(original, duplicate, 1);
        assert_ne!(changed.payload, formula.payload, "mutation must apply");
        let error = validate_claim(
            Some(&identity(&bundle)),
            Some(&changed),
            &bundle,
            &bundle.obligations[0],
        )
        .unwrap_err();
        assert!(error.contains("duplicate"), "{error}");
    }
}

#[test]
fn typed_public_claim_rejects_changed_predicates_and_unsupported_raw_fragments() {
    let (bundle, formula) = typed_fixture();
    for (original, replacement) in [
        ("\"eq\"", "\"ne\""),
        ("\"eq\"", "\"add\""),
        ("\"sort\":\"bool\"", "\"sort\":\"int\""),
        ("\"schema\":", "\"unknown\":true,\"schema\":"),
    ] {
        let mut changed = formula.clone();
        changed.payload = formula.payload.replacen(original, replacement, 1);
        assert_ne!(changed.payload, formula.payload, "mutation must apply");
        assert!(
            validate_claim(
                Some(&identity(&bundle)),
                Some(&changed),
                &bundle,
                &bundle.obligations[0],
            )
            .is_err()
        );
    }
    let mut changed = bundle.clone();
    let ContractPredicate::TrustIr { value, .. } = &mut changed.contracts[0].predicate else {
        panic!("typed public fixture must use canonical JSON");
    };
    let mut predicate: TrustSpecPredicate = serde_json::from_value(value.clone()).unwrap();
    let TrustSpecExprKind::Binary { op, .. } = &mut predicate.root.kind else {
        panic!("fixture must have a binary predicate");
    };
    *op = TrustSpecBinaryOp::Ne;
    changed.contracts[0].predicate = predicate.into_contract_predicate().unwrap();
    assert!(
        validate_claim(
            Some(&identity(&changed)),
            Some(&formula),
            &changed,
            &changed.obligations[0],
        )
        .is_err()
    );
}

#[test]
fn direct_mc_and_unknown_contracts_are_not_raw_source_candidates() {
    use trust_verifier_api::native_contract_claim::has_raw_source_postcondition_contract;
    let (mut bundle, formula) = fixture();
    assert!(has_raw_source_postcondition_contract(&bundle, &bundle.obligations[0]));
    for schema in ["trust-mc.typed-chc-obligation.v1", "unknown.encoding.v1"] {
        bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
            schema: schema.into(),
            value: serde_json::json!({}),
        };
        assert!(!has_raw_source_postcondition_contract(&bundle, &bundle.obligations[0]));
    }
    bundle.contracts[0].predicate = ContractPredicate::MathIr {
        schema: "trust-mc.typed-chc-obligation.v1".into(),
        value: serde_json::json!({}),
    };
    assert!(!has_raw_source_postcondition_contract(&bundle, &bundle.obligations[0]));
    bundle.contracts[0].predicate =
        ContractPredicate::CanonicalJson { schema: formula.schema, value: formula.payload.into() };
    bundle.obligations[0].kind = ObligationKind::Precondition;
    assert!(!has_raw_source_postcondition_contract(&bundle, &bundle.obligations[0]));
}

#[test]
fn duplicate_binding_names_are_not_an_exact_raw_claim() {
    let (mut bundle, mut formula) = fixture();
    formula.bindings.push(formula.bindings[0].clone());
    bundle.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    assert!(
        validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
            .is_err()
    );
}

#[test]
fn raw_codec_discriminator_is_shared_with_claim_validation() {
    use trust_verifier_api::native_contract_claim::{
        has_raw_source_postcondition_contract, is_supported_raw_source_contract_schema,
    };
    for schema in [
        TRUST_SPEC_PREDICATE_SCHEMA_VERSION,
        trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        "trust-wp.pure-expr.v1",
        "trust-types.Formula@1",
    ] {
        assert!(is_supported_raw_source_contract_schema(schema));
    }
    for schema in ["trust-mc.typed-chc-obligation.v1", "unknown.encoding.v1"] {
        let (mut bundle, mut formula) = fixture();
        formula.schema = schema.into();
        bundle.contracts[0].predicate = ContractPredicate::CanonicalJson {
            schema: schema.into(),
            value: formula.payload.clone().into(),
        };
        assert!(!is_supported_raw_source_contract_schema(schema));
        assert!(!has_raw_source_postcondition_contract(&bundle, &bundle.obligations[0]));
        assert!(
            validate_claim(
                Some(&identity(&bundle)),
                Some(&formula),
                &bundle,
                &bundle.obligations[0],
            )
            .unwrap_err()
            .contains("unsupported source-contract codec")
        );
    }
}

#[test]
fn distinct_binding_names_can_share_a_place() {
    let (mut bundle, mut formula) = fixture();
    formula.bindings.push(("x_alias".into(), formula.bindings[0].1.clone()));
    bundle.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    validate_claim(Some(&identity(&bundle)), Some(&formula), &bundle, &bundle.obligations[0])
        .unwrap();
}

#[test]
fn complete_source_projection_is_required_even_after_public_rehash() {
    let (mut bundle, formula) = fixture();
    let mut module = trust_ir::Module::new("source-binding");
    let file = module.intern_file("unicode/λ.rs").unwrap();
    bundle.obligations[0].source = SourceLocation {
        file: Some("unicode/λ.rs".into()),
        line: Some(10),
        column: Some(2),
        end_line: Some(12),
        end_column: Some(40),
    };
    let mut proof = native_proof(Some(&identity(&bundle)), Some(&formula), &bundle.obligations[0]);
    proof.source.as_mut().unwrap().range = Some(trust_ir::ProofObligationSourceRange {
        file,
        start_line: 10,
        start_col: 2,
        end_line: 12,
        end_col: 40,
    });
    validate_native_public_contract_claim(&module, &proof, &bundle, &bundle.obligations[0])
        .unwrap();
    for mutation in 0..11 {
        let mut changed = proof.clone();
        let source = changed.source.as_mut().unwrap();
        match mutation {
            0 => source.source_id.push_str("-other"),
            1 => source.assertion_id.push_str("-other"),
            2 => source.range.as_mut().unwrap().file = file + 1,
            3 => source.range.as_mut().unwrap().start_line += 1,
            4 => source.range.as_mut().unwrap().start_col += 1,
            5 => source.range.as_mut().unwrap().end_line += 1,
            6 => source.range.as_mut().unwrap().end_col += 1,
            7 => source.range = None,
            8 => source.public = None,
            9 => changed.source = None,
            _ => changed.formula = None,
        }
        assert!(
            validate_native_public_contract_claim(
                &module,
                &changed,
                &bundle,
                &bundle.obligations[0]
            )
            .is_err(),
            "mutation {mutation}"
        );
    }
    for mutation in 0..6 {
        let mut changed = bundle.clone();
        let source = &mut changed.obligations[0].source;
        match mutation {
            0 => source.file = None,
            1 => source.file = Some("unicode/other.rs".into()),
            2 => source.line = Some(11),
            3 => source.column = Some(3),
            4 => source.end_line = Some(13),
            _ => source.end_column = Some(41),
        }
        let mut unchanged_native = proof.clone();
        unchanged_native.source.as_mut().unwrap().public = Some(identity(&changed));
        assert!(
            validate_native_public_contract_claim(
                &module,
                &unchanged_native,
                &changed,
                &changed.obligations[0]
            )
            .is_err(),
            "rehashed public mutation {mutation}"
        );
    }
}

#[test]
fn source_projection_preserves_contract_proof_item_and_obligation_precedence() {
    let (bundle, _) = fixture();
    let module = trust_ir::Module::new("source-less");
    for mode in 0..3 {
        let mut obligation = bundle.obligations[0].clone();
        obligation.proof_item_id = Some("proof-item".into());
        if mode >= 1 {
            obligation.contract_id = None;
        }
        if mode == 2 {
            obligation.proof_item_id = None;
        }
        let mut proof = native_proof(None, None, &obligation);
        validate_native_public_source_projection(&module, &proof, &obligation).unwrap();
        proof.source.as_mut().unwrap().source_id.push_str("-other");
        assert!(validate_native_public_source_projection(&module, &proof, &obligation).is_err());
    }
}

#[test]
fn source_projection_preserves_optional_coordinate_defaults_and_missing_range_refusal() {
    let (mut bundle, _) = fixture();
    let mut module = trust_ir::Module::new("defaults");
    let file = module.intern_file("defaults.rs").unwrap();
    let mut proof = native_proof(None, None, &bundle.obligations[0]);
    validate_native_public_source_projection(&module, &proof, &bundle.obligations[0]).unwrap();
    bundle.obligations[0].source.file = Some("defaults.rs".into());
    assert!(
        validate_native_public_source_projection(&module, &proof, &bundle.obligations[0]).is_err()
    );
    for coordinates in [None, Some((4, 6))] {
        let (line, column) = coordinates.unwrap_or_default();
        bundle.obligations[0].source.line = coordinates.map(|v| v.0);
        bundle.obligations[0].source.column = coordinates.map(|v| v.1);
        proof.source.as_mut().unwrap().range = Some(trust_ir::ProofObligationSourceRange {
            file,
            start_line: line,
            start_col: column,
            end_line: line,
            end_col: column,
        });
        validate_native_public_source_projection(&module, &proof, &bundle.obligations[0]).unwrap();
    }
    bundle.obligations[0].source.file = None;
    assert!(
        validate_native_public_source_projection(&module, &proof, &bundle.obligations[0]).is_err()
    );
}

#[test]
fn shared_native_public_identity_preserves_the_exact_claim_boundary() {
    use trust_verifier_api::native_contract_claim::{
        NativePublicIdentityError as Error, validate_native_public_obligation_identity as check,
    };
    let (bundle, formula) = fixture();
    let obligation = &bundle.obligations[0];
    let expected = bundle.canonical_obligation_semantic_digest_sha256(obligation).unwrap();
    let public = identity(&bundle);
    let original = native_proof(Some(&public), Some(&formula), obligation);
    assert_eq!(check(&original, &obligation.obligation_id, &expected), Ok(()));
    let mut missing = original.clone();
    missing.source = None;
    assert_eq!(check(&missing, &obligation.obligation_id, &expected), Err(Error::MissingSource));
    let mut missing = original.clone();
    missing.source.as_mut().unwrap().public = None;
    assert_eq!(
        check(&missing, &obligation.obligation_id, &expected),
        Err(Error::MissingPublicIdentity)
    );
    let mut moved = original.clone();
    moved.source.as_mut().unwrap().public.as_mut().unwrap().obligation_id.push('x');
    assert!(matches!(
        check(&moved, &obligation.obligation_id, &expected),
        Err(Error::ObligationIdMismatch { .. })
    ));
    for digest in [
        ProofDigest::sha256([0; 32]),
        ProofDigest::sha256([3; 32]),
        ProofDigest {
            algorithm: trust_ir::ProofDigestAlgorithm::TrustIrStableV1,
            bytes: public.semantic_digest.bytes,
        },
    ] {
        let mut changed = original.clone();
        changed.source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest = digest;
        assert!(matches!(
            check(&changed, &obligation.obligation_id, &expected),
            Err(Error::SemanticDigestMismatch { .. })
        ));
        assert!(
            validate_claim(
                changed.source.as_ref().unwrap().public.as_ref(),
                Some(&formula),
                &bundle,
                obligation
            )
            .is_err()
        );
    }
    for malformed in ["", "sha256:abc", &"A".repeat(64), &"f".repeat(63)] {
        assert_eq!(
            check(&original, &obligation.obligation_id, malformed),
            Err(Error::InvalidExpectedSemanticDigest)
        );
    }
}

fn program_binding_fixture() -> (trust_ir::Module, TrustContractBundle, ProofFormula) {
    let (mut bundle, formula) = fixture();
    let module = trust_ir::Module::new("original-program");
    let digest = module.stable_digest().to_string();
    let hex = digest.strip_prefix("sha256:").unwrap();
    let public_id = bundle.obligations[0].obligation_id.clone();
    bundle.obligations[0].metadata.extend([
        MetadataEntry {
            key: "trust.trust_ir.native.trust_ir_module_digest".into(),
            value: hex.into(),
        },
        MetadataEntry {
            key: "trust.trust_ir.native.proof_unit.v1".into(),
            value: serde_json::json!({
                "schema_version":"trust.trust_ir.native-proof-unit.v1",
                "public_obligation_id":public_id,
                "proof_obligation_id":0,
                "trust_ir_module_digest":{"algorithm":"sha256","value":hex},
                // Request configuration is a separate strategy identity. This
                // history is not permission to change the original program.
                "request_digest":{"algorithm":"sha256","value":"a".repeat(64)},
            })
            .to_string(),
        },
    ]);
    bundle.obligations[0].metadata.push(
        ObligationContext::new(
            ObligationProducer::CompilerMirExtract,
            ObligationOrigin::Contract {
                contract_id: "post".into(),
                contract_kind: ContractKind::Ensures,
                contract_index: 0,
                predicate_schema: Some(formula.schema.clone()),
            },
        )
        .to_metadata_entry()
        .unwrap(),
    );
    (module, bundle, formula)
}

fn validate_program_binding(
    module: &trust_ir::Module,
    bundle: &TrustContractBundle,
    formula: &ProofFormula,
) -> Result<(), String> {
    let obligation = &bundle.obligations[0];
    // Check transport correspondence directly before deriving a logical
    // identity: duplicate metadata is itself a canonical-digest refusal.
    trust_verifier_api::native_contract_claim::validate_native_public_module_binding(
        module,
        &native_proof(None, Some(formula), obligation),
        obligation,
    )?;
    validate_native_public_contract_claim(
        module,
        &native_proof(Some(&identity(bundle)), Some(formula), obligation),
        bundle,
        obligation,
    )
}

#[test]
fn original_public_program_binding_survives_current_request_planning() {
    let (module, mut bundle, formula) = program_binding_fixture();
    let original_identity = identity(&bundle);
    validate_program_binding(&module, &bundle, &formula).unwrap();
    let unit = &mut bundle.obligations[0].metadata[1].value;
    let mut value: serde_json::Value = serde_json::from_str(unit).unwrap();
    value["request_digest"]["value"] = "b".repeat(64).into();
    *unit = value.to_string();
    assert_eq!(identity(&bundle), original_identity);
    validate_program_binding(&module, &bundle, &formula).unwrap();
    let changed = trust_ir::Module::new("different-program");
    assert!(validate_program_binding(&changed, &bundle, &formula).is_err());
}

#[test]
fn each_original_public_program_binding_rejects_a_different_module() {
    let (module, bundle, formula) = program_binding_fixture();
    for retained in 0..2 {
        let mut only = bundle.clone();
        only.obligations[0].metadata = vec![only.obligations[0].metadata[retained].clone()];
        validate_program_binding(&module, &only, &formula).unwrap();
        assert!(
            validate_program_binding(&trust_ir::Module::new("different-program"), &only, &formula,)
                .is_err()
        );
    }
}

#[test]
fn conflicting_duplicate_and_noncanonical_public_program_bindings_refuse() {
    let (module, bundle, formula) = program_binding_fixture();
    for index in 0..2 {
        let mut duplicate = bundle.clone();
        let entry = duplicate.obligations[0].metadata[index].clone();
        duplicate.obligations[0].metadata.push(entry);
        assert!(validate_program_binding(&module, &duplicate, &formula).is_err());
    }
    for value in ["0".repeat(64), "A".repeat(64), "sha256:bad".into(), " bad ".into()] {
        let mut changed = bundle.clone();
        changed.obligations[0].metadata[0].value = value;
        assert!(validate_program_binding(&module, &changed, &formula).is_err());
    }
    for mutation in 0..4 {
        let mut changed = bundle.clone();
        let encoded = &mut changed.obligations[0].metadata[1].value;
        let mut unit: serde_json::Value = serde_json::from_str(encoded).unwrap();
        match mutation {
            0 => unit["trust_ir_module_digest"]["value"] = "0".repeat(64).into(),
            1 => unit["trust_ir_module_digest"]["algorithm"] = "sha512".into(),
            2 => unit["schema_version"] = "future-proof-unit".into(),
            _ => {
                unit.as_object_mut().unwrap().remove("trust_ir_module_digest");
            }
        }
        *encoded = unit.to_string();
        assert!(validate_program_binding(&module, &changed, &formula).is_err());
    }
    let mut duplicate_json = bundle;
    let encoded = &mut duplicate_json.obligations[0].metadata[1].value;
    *encoded =
        encoded.replacen("{", "{\"schema_version\":\"trust.trust_ir.native-proof-unit.v1\",", 1);
    assert!(validate_program_binding(&module, &duplicate_json, &formula).is_err());
}

#[test]
fn compiler_origin_context_requires_both_program_carriers() {
    let (module, bundle, formula) = program_binding_fixture();
    let expected_identity = identity(&bundle);
    for removed in 0..3 {
        let mut changed = bundle.clone();
        changed.obligations[0].metadata.retain(|entry| match entry.key.as_str() {
            "trust.trust_ir.native.trust_ir_module_digest" => removed == 1,
            "trust.trust_ir.native.proof_unit.v1" => removed == 0,
            _ => true,
        });
        assert_eq!(identity(&changed), expected_identity);
        assert!(validate_program_binding(&module, &changed, &formula).is_err());
    }
}

#[test]
fn compiler_program_binding_context_is_unique_and_uses_the_existing_strict_decoder() {
    let (module, bundle, formula) = program_binding_fixture();
    for mutation in 0..4 {
        let mut changed = bundle.clone();
        match mutation {
            0 => {
                let context = changed.obligations[0].metadata[2].clone();
                changed.obligations[0].metadata.push(context);
            }
            1 => {
                let encoded = &mut changed.obligations[0].metadata[2].value;
                *encoded = encoded.replacen("{", "{\"producer\":\"compiler_mir_extract\",", 1);
            }
            2 => changed.obligations[0].metadata[2].value = "{}".into(),
            _ => {
                let encoded = &mut changed.obligations[0].metadata[2].value;
                let mut context: serde_json::Value = serde_json::from_str(encoded).unwrap();
                context["schema_version"] = "future-context".into();
                *encoded = context.to_string();
            }
        }
        let proof = native_proof(Some(&identity(&bundle)), Some(&formula), &bundle.obligations[0]);
        assert!(
            trust_verifier_api::native_contract_claim::validate_native_public_module_binding(
                &module,
                &proof,
                &changed.obligations[0],
            )
            .is_err()
        );
    }
}

#[test]
fn proof_unit_program_constraint_cannot_name_another_obligation() {
    let (module, bundle, formula) = program_binding_fixture();
    for mutation in 0..2 {
        let mut changed = bundle.clone();
        let encoded = &mut changed.obligations[0].metadata[1].value;
        let mut unit: serde_json::Value = serde_json::from_str(encoded).unwrap();
        if mutation == 0 {
            unit["public_obligation_id"] = "another-public-obligation".into();
        } else {
            unit["proof_obligation_id"] = 1.into();
        }
        *encoded = unit.to_string();
        assert_eq!(identity(&changed), identity(&bundle));
        assert!(validate_program_binding(&module, &changed, &formula).is_err());
    }
}
