//! Source-binding regression using the producer's actual native opaque input.

use super::*;

fn actual_decline_input() -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>)
{
    decline_input(include_str!("../../trust-vcgen/testdata/native-opaque-return-call-e560.json"))
}

fn decline_input(
    capture: &str,
) -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let function: VerifiableFunction =
        serde_json::from_str(capture).expect("actual native compiler function");
    let contract = &function.contracts[0];
    let proposition = trust_types::CompilerContractProposition {
        source_contract_index: 0,
        kind: contract.kind,
        body: contract.body.clone(),
        formula: function.postconditions[0].clone(),
        variable_domains: ["_0", "x"]
            .into_iter()
            .map(|name| trust_types::CompilerContractVariableDomain {
                name: name.into(),
                domain: trust_types::CompilerContractValueDomain::MachineInt {
                    width: 8,
                    signed: false,
                },
            })
            .collect(),
    };
    let contracts = CompilerContractBundle::new(function.contracts.clone())
        .with_typed_propositions(vec![proposition]);
    assert!(contracts.typed_proposition(0, &contracts.contracts[0]).is_some());
    let vcs = trust_vcgen::generate_vcs(&function);
    assert_eq!(vcs.iter().filter(|vc| vc.kind.declined_contract_body().is_some()).count(), 1);
    (function, contracts, vcs)
}

#[test]
fn native_owned_discharge_retains_exact_current_source_decline_transport() {
    let (function, contracts, _) = decline_input(include_str!(
        "../../trust-vcgen/testdata/native-opaque-return-call-53c.json"
    ));
    let (mut vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&function);
    assert!(
        discharged.iter().all(|(vc, _)| vc.kind.declined_contract_body().is_none()),
        "a source decline is never discharged as a proof"
    );
    vcs.extend(discharged.into_iter().map(|(vc, _)| vc));
    let declines =
        vcs.iter().filter(|vc| vc.kind.declined_contract_body().is_some()).collect::<Vec<_>>();
    assert_eq!(declines.len(), 1);
    let row = declines[0];
    assert_eq!(row.formula, Formula::Bool(true));
    assert!(row.kernel_authority_refusal().is_some());
    let bundle = function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &contracts,
        &vcs,
        "n4_runtime_blackbox_monitor",
        0x1234,
        Some(64),
    );
    let obligation = bundle
        .obligations
        .iter()
        .find(|obligation| {
            matches!(&obligation.kind, ObligationKind::Custom { namespace, name }
            if namespace == "trust.vc" && name == "declined_contract_body")
        })
        .expect("production discharge retains the complete non-proving source question");
    assert_eq!(obligation.contract_id.as_deref(), Some(bundle.contracts[0].contract_id.as_str()));
    assert_eq!(
        obligation
            .metadata
            .iter()
            .filter(|entry| entry.key == SOURCE_BODY_DECLINE_METADATA_KEY)
            .count(),
        1
    );
    let context = FunctionContext {
        crate_name: "n4_runtime_blackbox_monitor".into(),
        path: function.def_path.clone(),
    };
    assert!(source_body_decline_metadata_matches_contract(
        &function,
        &contracts,
        row,
        &context,
        &bundle.contracts[0],
        obligation,
    ));
    // Keep the consumer strict. The producer repair does not accept the old
    // wrapped payload or turn a malformed sentinel into source correspondence.
    for formula in [
        Formula::Bool(false),
        Formula::And(vec![function.preconditions[0].clone(), Formula::Bool(true)]),
    ] {
        let mut changed = row.clone();
        changed.formula = formula;
        assert!(validated_source_body_decline(&function, &contracts, &changed).is_none());
    }
    assert!(
        verifier_api_source_clause_body_formula_metadata(
            &function,
            &contracts,
            &vcs,
            "n4_runtime_blackbox_monitor",
            Some(64),
        )
        .is_empty(),
        "the retained refusal must not become a source body proof"
    );
}

#[test]
fn native_body_decline_preserves_complete_typed_source_claim() {
    let (function, contracts, vcs) = actual_decline_input();
    let bundle = function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &contracts,
        &vcs,
        "n4_runtime_blackbox_monitor",
        0x1234,
        Some(64),
    );
    let declined = bundle
        .obligations
        .iter()
        .find(|obligation| {
            matches!(&obligation.kind, ObligationKind::Custom { namespace, name }
            if namespace == "trust.vc" && name == "declined_contract_body")
        })
        .expect("one explicit non-proving body decline");
    assert_eq!(
        declined.contract_id.as_deref(),
        Some(bundle.contracts[0].contract_id.as_str()),
        "the actual refusal must retain the canonical authored clause identity"
    );
    assert_eq!(
        declined
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY)
            .count(),
        1
    );
    let payload = declined
        .metadata
        .iter()
        .find(|entry| entry.key == "trust.vc.source_body_decline.v1")
        .expect("complete typed source question, not diagnostic text");
    let payload: serde_json::Value = serde_json::from_str(&payload.value).unwrap();
    assert_eq!(
        payload["proposition"],
        serde_json::to_value(&contracts.typed_propositions[0]).unwrap()
    );
    assert_eq!(payload["source_digest"], verifier_source_digest(&function));
    assert_eq!(payload["contract_id"], bundle.contracts[0].contract_id);
    assert_eq!(payload["source"], serde_json::to_value(&contracts.contracts[0].span).unwrap());
    let context = FunctionContext {
        crate_name: "n4_runtime_blackbox_monitor".into(),
        path: function.def_path.clone(),
    };
    let row = vcs.iter().find(|vc| vc.kind.declined_contract_body().is_some()).unwrap();
    let matches = |obligation: &TrustObligation| {
        source_body_decline_metadata_matches_contract(
            &function,
            &contracts,
            row,
            &context,
            &bundle.contracts[0],
            obligation,
        )
    };
    assert!(matches(declined));
    for key in [
        "trust.contract.lowering",
        SOURCE_BODY_DECLINE_METADATA_KEY,
        TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY,
        TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY,
        TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
        TRUST_SOURCE_DIGEST_METADATA_KEY,
        TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
    ] {
        let mut changed = declined.clone();
        changed.metadata.iter_mut().find(|entry| entry.key == key).unwrap().value.push('x');
        assert!(!matches(&changed), "altered {key}");
        let mut missing = declined.clone();
        missing.metadata.retain(|entry| entry.key != key);
        assert!(!matches(&missing), "missing {key}");
        let mut duplicate = declined.clone();
        duplicate
            .metadata
            .push(duplicate.metadata.iter().find(|entry| entry.key == key).unwrap().clone());
        assert!(!matches(&duplicate), "duplicate {key}");
    }
    assert!(
        verifier_api_source_clause_body_formula_metadata(
            &function,
            &contracts,
            &vcs,
            "n4_runtime_blackbox_monitor",
            Some(64)
        )
        .is_empty(),
        "a decline must not become an ordinary body-proof query"
    );
}

#[test]
fn native_body_decline_rejects_missing_ambiguous_or_changed_source() {
    let (function, contracts, vcs) = actual_decline_input();
    let row = vcs.iter().find(|row| row.kind.declined_contract_body().is_some()).unwrap();
    assert!(validated_source_body_decline(&function, &contracts, row).is_some());
    for change in ["index", "predicate", "metadata", "query", "function"] {
        let mut changed = row.clone();
        match change {
            "index" => {
                let VcKind::DeclinedContractBody(value) = &mut changed.kind else { unreachable!() };
                value.source_contract_index = 1;
            }
            "predicate" => {
                let VcKind::DeclinedContractBody(value) = &mut changed.kind else { unreachable!() };
                value.source_predicate = Formula::Bool(false);
            }
            "metadata" => changed.contract_metadata.as_mut().unwrap().source_contract_index = None,
            "query" => changed.formula = Formula::Bool(false),
            "function" => changed.function = "foreign_function".into(),
            _ => unreachable!(),
        }
        assert!(
            validated_source_body_decline(&function, &contracts, &changed).is_none(),
            "{change}"
        );
    }
    for change in ["missing", "duplicate", "domains", "source"] {
        let mut changed = contracts.clone();
        match change {
            "missing" => changed.typed_propositions.clear(),
            "duplicate" => changed.typed_propositions.push(changed.typed_propositions[0].clone()),
            "domains" => {
                changed.typed_propositions[0].variable_domains[0].domain =
                    trust_types::CompilerContractValueDomain::MachineInt {
                        width: 16,
                        signed: false,
                    }
            }
            "source" => changed.contracts[0].span.line_start += 1,
            _ => unreachable!(),
        }
        assert!(validated_source_body_decline(&function, &changed, row).is_none(), "{change}");
    }
}

#[test]
fn native_body_decline_prevents_partial_source_formula_even_if_omitted() {
    let (mut function, contracts, _) = actual_decline_input();
    // A constructed mixed-path control uses the actual captured opaque call,
    // with one additional ordinary return. It is not a new compiler capture.
    let mut call = function.body.blocks[0].clone();
    call.id = trust_types::BlockId(2);
    let Terminator::Call { target, .. } = &mut call.terminator else { panic!() };
    *target = Some(trust_types::BlockId(3));
    function.body.arg_count = 2;
    function.body.locals.push(trust_types::LocalDecl {
        index: 2,
        ty: Ty::Int { width: 8, signed: false },
        name: Some("choose".into()),
    });
    let ordinary = trust_types::BasicBlock {
        id: trust_types::BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: function.span.clone(),
        }],
        terminator: Terminator::Return,
    };
    function.body.blocks = vec![
        trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, trust_types::BlockId(1))],
                otherwise: trust_types::BlockId(2),
                exhaustive_enum_unreachable: false,
                span: function.span.clone(),
            },
        },
        ordinary.clone(),
        call,
        trust_types::BasicBlock {
            id: trust_types::BlockId(3),
            stmts: vec![],
            terminator: Terminator::Return,
        },
    ];
    let rows = trust_vcgen::generate_vcs(&function);
    assert!(rows.iter().any(|vc| vc.kind == VcKind::Postcondition));
    assert!(rows.iter().any(|vc| vc.kind.declined_contract_body().is_some()));
    let check = |function: &VerifiableFunction, rows: &[VerificationCondition]| {
        verifier_api_source_clause_body_formula_metadata(
            function,
            &contracts,
            rows,
            "n4_runtime_blackbox_monitor",
            Some(64),
        )
    };
    assert!(check(&function, &rows).is_empty(), "all fresh returns belong to the clause");
    let omitted = rows
        .into_iter()
        .filter(|vc| vc.kind.declined_contract_body().is_none())
        .collect::<Vec<_>>();
    assert!(check(&function, &omitted).is_empty(), "omission cannot manufacture completeness");

    let mut pure = function.clone();
    pure.body.blocks = vec![trust_types::BasicBlock { id: trust_types::BlockId(0), ..ordinary }];
    let pure_rows = trust_vcgen::generate_vcs(&pure);
    assert!(!check(&pure, &pure_rows).is_empty(), "ordinary complete body still binds");
}
