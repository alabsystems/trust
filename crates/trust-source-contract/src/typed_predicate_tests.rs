//! Query-only predicate projection: semantic parity and provenance refusal.

use trust_types::{
    CompilerContractProposition, CompilerContractValueDomain as Domain,
    CompilerContractVariableDomain as Variable,
};

use super::*;

fn query(text: &str, domain: Domain) -> CompilerContractBundle {
    let contract = Contract {
        kind: TrustTypesContractKind::Ensures,
        span: SourceSpan::default(),
        body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{text}"),
    };
    let parsed = trust_types::parse_spec_expr(text).unwrap();
    let mut names: Vec<_> = parsed.free_variables().into_iter().collect();
    names.sort();
    let variable_domains: Vec<_> =
        names.into_iter().map(|name| Variable { name, domain }).collect();
    let formula =
        trust_types::compiler_contract_formula_with_domains(&parsed, &variable_domains).unwrap();
    let proposition = CompilerContractProposition {
        source_contract_index: 0,
        kind: contract.kind,
        body: contract.body.clone(),
        formula,
        variable_domains,
    };
    CompilerContractBundle::new(vec![contract]).with_typed_propositions(vec![proposition])
}

fn signature() -> VerifiableFunction {
    VerifiableFunction {
        name: "query_only".into(),
        def_path: "predicate_test::query_only".into(),
        span: SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: Ty::u32(), name: None },
                trust_types::LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
#[allow(deprecated)]
fn query_only_projection_matches_catalog_bytes_for_supported_and_refused_clauses() {
    for text in [
        "result >= 0",
        "result + 1 > result",
        "(x % 2 == 0 && result == 0) || (x % 2 == 1 && result == 3988292384)",
        "x / 2 == 0",
    ] {
        let query = query(text, Domain::MachineInt { width: 32, signed: false });
        let (predicate, refusal, lowering) = compiler_typed_contract_predicate(&query, 0).unwrap();
        let public = contract_bundle_to_verifier_api(&signature(), &query);
        assert_eq!(public.contracts.len(), 1, "{text}");
        let contract = &public.contracts[0];
        assert_eq!(
            serde_json::to_vec(&predicate).unwrap(),
            serde_json::to_vec(&contract.predicate).unwrap(),
            "{text}"
        );
        let metadata = |key: &str| {
            contract
                .metadata
                .iter()
                .find(|entry| entry.key == key)
                .map(|entry| entry.value.as_str())
        };
        assert_eq!(metadata("trust.contract.lowering"), Some(lowering), "{text}");
        assert_eq!(metadata("trust.contract.unsupported_reason"), refusal.as_deref(), "{text}");
    }
}

#[test]
fn query_only_machine_arithmetic_keeps_the_declared_width() {
    let query = query("result + 1 > result", Domain::MachineInt { width: 32, signed: false });
    let (predicate, refusal, lowering) = compiler_typed_contract_predicate(&query, 0).unwrap();
    assert!(refusal.is_none());
    assert_eq!(lowering, "typed_proposition_machine_width");
    let predicate = TrustSpecPredicate::from_contract_predicate(&predicate).unwrap().unwrap();
    assert!(!predicate.variables.is_empty());
    assert!(
        predicate
            .variables
            .iter()
            .all(|variable| { matches!(variable.sort, TrustSpecSort::BitVec { width: 32 }) })
    );
}

#[test]
fn query_only_undefined_division_keeps_the_existing_visible_refusal() {
    let query = query("x / 2 == 0", Domain::MachineInt { width: 32, signed: false });
    let (predicate, refusal, lowering) = compiler_typed_contract_predicate(&query, 0).unwrap();
    assert!(matches!(predicate, ContractPredicate::Unsupported { .. }));
    assert!(refusal.is_some());
    assert_eq!(lowering, UNMODELED_CONTRACT_ARITHMETIC_LOWERING);
}

#[test]
fn query_only_projection_rejects_missing_duplicate_and_stale_typed_provenance() {
    let original = query("x <= result", Domain::MachineInt { width: 32, signed: false });
    assert!(compiler_typed_contract_predicate(&original, 0).is_some());
    assert!(compiler_typed_contract_predicate(&original, 1).is_none());
    for mutation in ["missing", "duplicate", "kind", "body", "formula", "index", "untyped"] {
        let mut changed = original.clone();
        match mutation {
            "missing" => changed.typed_propositions.clear(),
            "duplicate" => changed.typed_propositions.push(changed.typed_propositions[0].clone()),
            "kind" => changed.typed_propositions[0].kind = TrustTypesContractKind::Requires,
            "body" => changed.typed_propositions[0].body.push_str(" && false"),
            "formula" => changed.typed_propositions[0].formula = Formula::Bool(true),
            "index" => changed.typed_propositions[0].source_contract_index = 1,
            "untyped" => {
                changed.contracts[0].body = "true".into();
                changed.typed_propositions[0].body = "true".into();
                changed.typed_propositions[0].formula = Formula::Bool(true);
            }
            _ => unreachable!(),
        }
        assert!(compiler_typed_contract_predicate(&changed, 0).is_none(), "{mutation}");
    }
}

#[test]
#[allow(deprecated)]
fn query_only_projection_preserves_explicit_compiler_refusals() {
    let mut query = query("x <= result", Domain::MachineInt { width: 32, signed: false });
    query.contracts[0].body =
        format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}retained-query-refusal");
    query.typed_propositions[0].body = query.contracts[0].body.clone();
    assert!(query.typed_proposition(0, &query.contracts[0]).is_none());
    assert!(compiler_typed_contract_predicate(&query, 0).is_none());
    let public = contract_bundle_to_verifier_api(&signature(), &query);
    assert_eq!(public.contracts.len(), 1);
    assert!(matches!(&public.contracts[0].predicate,
        ContractPredicate::Unsupported { reason } if reason.contains("retained-query-refusal")));
    assert_eq!(public.obligations.len(), 1);
}
