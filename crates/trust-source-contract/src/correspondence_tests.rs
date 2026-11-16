use trust_types::{
    CompilerContractProposition, CompilerContractValueDomain, CompilerContractVariableDomain,
};

use super::*;

fn input(name: &str) -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let bytes = match name {
        "correct" => include_str!("../tests/fixtures/correct.json"),
        "correct_true" => include_str!("../tests/fixtures/correct_true.json"),
        "forwarded_correct" => include_str!("../tests/fixtures/forwarded_correct.json"),
        "wrong" => include_str!("../tests/fixtures/wrong.json"),
        _ => panic!("unknown fixture"),
    };
    let function: VerifiableFunction = serde_json::from_str(bytes).unwrap();
    // This is explicitly a query-shaped test fixture, not a claim that the old
    // diagnostic exporter retained the actual compiler query bytes.
    let propositions = function
        .contracts
        .iter()
        .enumerate()
        .map(|(index, contract)| {
            let body = contract.body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap();
            let parsed = trust_types::parse_spec_expr(body).unwrap();
            let domains = vec![CompilerContractVariableDomain {
                name: "_0".into(),
                domain: CompilerContractValueDomain::Bool,
            }];
            let formula =
                trust_types::compiler_contract_formula_with_domains(&parsed, &domains).unwrap();
            CompilerContractProposition {
                source_contract_index: index,
                kind: contract.kind,
                body: contract.body.clone(),
                formula,
                variable_domains: domains,
            }
        })
        .collect();
    let query = CompilerContractBundle::new(function.contracts.clone())
        .with_typed_propositions(propositions);
    let frames: serde_json::Value = serde_json::from_str(include_str!(
        "../../../targo-trust/src/fixtures/native_wp_selfuse_transport.json"
    ))
    .unwrap();
    let frame =
        frames.as_array().unwrap().iter().find(|f| f["function"] == function.def_path).unwrap();
    let vcs = frame["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|r| {
            let snapshot = r["original_vc_snapshot"]["original_vc_json"].as_str()?;
            Some(serde_json::from_str(snapshot).unwrap())
        })
        .collect();
    (function, query, vcs)
}

#[test]
fn real_selfuse_without_callee_derivations_refuses_correspondence() {
    for name in ["correct", "correct_true", "forwarded_correct", "wrong"] {
        let (function, query, vcs) = input(name);
        assert!(
            exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).is_none(),
            "{name}: bare function must not import its missing inferred-callee model"
        );
    }
}

#[test]
fn exact_source_group_checks_query_body_and_complete_membership() {
    let (mut function, query, _) = input("correct");
    // Explicit constructed pure-body control, distinct from the real call
    // fixture above. The shared generator owns its executable semantics.
    function.body.locals.truncate(1);
    function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(false))),
            span: function.span.clone(),
        }],
        terminator: Terminator::Return,
    }];
    let (vcs, _) = trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
    let group = exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).unwrap();
    assert_eq!(group.body_indices(), &[0]);
    assert_eq!(group.source_contract_index(), 0);
    assert_eq!(
        exact_ensures_body_group(&function, &query, 0, &vcs, Some(64), None)
            .unwrap()
            .body_indices(),
        group.body_indices()
    );
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &[], Some(64)).is_none());
    let mut duplicate = vcs.clone();
    duplicate.push(vcs[0].clone());
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &duplicate, Some(64)).is_none());
    let mut changed = function.clone();
    changed.postconditions[0] = Formula::Bool(true);
    assert!(exact_boolean_ensures_body_group(&changed, &query, 0, &vcs, Some(64)).is_none());
    let mut changed = query.clone();
    changed.typed_propositions[0].formula = Formula::Bool(true);
    assert!(exact_boolean_ensures_body_group(&function, &changed, 0, &vcs, Some(64)).is_none());
    assert!(exact_boolean_ensures_body_group(&function, &query, 1, &vcs, Some(64)).is_none());
    let mut changed = vcs.clone();
    changed[0].formula = Formula::Bool(false);
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &changed, Some(64)).is_none());
    let mut changed = function.clone();
    changed.body.blocks.clear();
    assert!(exact_boolean_ensures_body_group(&changed, &query, 0, &vcs, Some(64)).is_none());
}

fn unsigned_select_input(
    name: &str,
) -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let text = match name {
        "clamp_width" => include_str!("../tests/fixtures/retained-clamp-width.json"),
        "clamp_to_max" => include_str!("../tests/fixtures/retained-clamp-to-max.json"),
        "process_ceiling_mb" => include_str!("../tests/fixtures/retained-process-ceiling-mb.json"),
        "join_width" => include_str!("../tests/fixtures/retained-join-width.json"),
        _ => panic!("unknown retained select"),
    };
    let capture: serde_json::Value = serde_json::from_str(text).unwrap();
    let raw = capture["original_function_json"].as_str().unwrap();
    assert_eq!(stable_sha256_hex(raw.as_bytes()), capture["function_sha256"]);
    let function: VerifiableFunction = serde_json::from_str(raw).unwrap();
    // The original exporter retained the body/VCs, not the typed compiler
    // query or source identity. Reconstruct only the query-shaped sidecar via
    // the shared parser; this fixture cannot authorize source publication.
    let query = unsigned_select_query(&function);
    let vcs = capture["body_vcs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let raw = row["original_vc_json"].as_str().unwrap();
            assert_eq!(stable_sha256_hex(raw.as_bytes()), row["payload_sha256"]);
            serde_json::from_str(raw).unwrap()
        })
        .collect();
    (function, query, vcs)
}

pub(super) fn unsigned_select_query(function: &VerifiableFunction) -> CompilerContractBundle {
    let propositions = function
        .contracts
        .iter()
        .enumerate()
        .map(|(index, contract)| {
            let parsed = trust_types::parse_spec_expr(
                contract.body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap(),
            )
            .unwrap();
            let mut names: Vec<_> = parsed.free_variables().into_iter().collect();
            names.sort();
            let variable_domains = names
                .into_iter()
                .map(|name| {
                    let ty = if name == "_0" {
                        &function.body.return_ty
                    } else {
                        &function
                            .body
                            .locals
                            .iter()
                            .find(|local| {
                                local.index > 0
                                    && local.index <= function.body.arg_count
                                    && trust_vcgen::local_var_name(function, local) == name
                            })
                            .unwrap()
                            .ty
                    };
                    let Ty::Int { width, signed } = ty else { panic!("expected integer") };
                    CompilerContractVariableDomain {
                        name,
                        domain: CompilerContractValueDomain::MachineInt {
                            width: *width,
                            signed: *signed,
                        },
                    }
                })
                .collect::<Vec<_>>();
            CompilerContractProposition {
                source_contract_index: index,
                kind: contract.kind,
                body: contract.body.clone(),
                formula: trust_types::compiler_contract_formula_with_domains(
                    &parsed,
                    &variable_domains,
                )
                .unwrap(),
                variable_domains,
            }
        })
        .collect();
    CompilerContractBundle::new(function.contracts.clone()).with_typed_propositions(propositions)
}

#[test]
fn retained_unsigned_selects_bind_every_original_body_clause() {
    for name in ["clamp_width", "clamp_to_max", "process_ceiling_mb", "join_width"] {
        let (function, query, vcs) = unsigned_select_input(name);
        assert!(
            trust_types::admissible_body::recognize_unsigned_ordered_select(&function).is_some()
        );
        assert_eq!(vcs.len(), 4);
        for index in 0..2 {
            let group =
                exact_unsigned_select_ensures_body_group(&function, &query, index, &vcs, Some(64))
                    .unwrap_or_else(|| panic!("{name} clause {index} failed exact correspondence"));
            assert_eq!(group.source_contract_index(), index);
            assert_eq!(group.body_indices().len(), 2);
            assert_eq!(
                exact_ensures_body_group(&function, &query, index, &vcs, Some(64), None)
                    .unwrap()
                    .body_indices(),
                group.body_indices(),
            );
            assert_eq!(
                exact_ensures_body_group(&function, &query, index, &vcs, Some(64), Some(&[]))
                    .unwrap()
                    .body_indices(),
                group.body_indices(),
                "an empty call context contributes no assumptions to the original select"
            );
            assert!(
                exact_boolean_ensures_body_group(&function, &query, index, &vcs, Some(64))
                    .is_none()
            );
        }
    }
}

#[test]
fn retained_non_clamp_selects_refuse_changed_body_query_or_incomplete_groups() {
    for name in ["process_ceiling_mb", "join_width"] {
        let (function, query, vcs) = unsigned_select_input(name);
        let refuses = |function: &VerifiableFunction,
                       query: &CompilerContractBundle,
                       vcs: &[VerificationCondition]| {
            exact_ensures_body_group(function, query, 0, vcs, Some(64), None).is_none()
        };
        for removed in 0..vcs.len() {
            let mut incomplete = vcs.clone();
            incomplete.remove(removed);
            assert!(refuses(&function, &query, &incomplete), "{name}: missing row {removed}");
        }
        let mut changed = function.clone();
        let width = match function.body.return_ty {
            Ty::Int { width, signed: false } => width,
            _ => panic!("not an unsigned select"),
        };
        let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[1].stmts[0] else {
            panic!("missing first return arm")
        };
        *rvalue = Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(
            u128::from(trust_intbound::unsigned_max(width)),
            width,
        )));
        assert!(refuses(&changed, &query, &vcs), "{name}: old proofs cannot answer another body");

        let mut changed = function.clone();
        changed.contracts[0].body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == 0");
        let changed_query = unsigned_select_query(&changed);
        changed.postconditions =
            changed_query.typed_propositions.iter().map(|p| p.formula.clone()).collect();
        assert!(
            refuses(&changed, &changed_query, &vcs),
            "{name}: old proofs cannot answer another query"
        );

        let mut changed = function.clone();
        changed.preconditions.push(Formula::Bool(false));
        assert!(refuses(&changed, &query, &vcs), "{name}: no vacuous narrowed input domain");
    }
}

#[test]
fn unsigned_select_cannot_transfer_changed_contract_body_or_partial_vcs() {
    let (function, query, vcs) = unsigned_select_input("clamp_width");
    let check = |f, q, v: &[VerificationCondition]| {
        exact_unsigned_select_ensures_body_group(f, q, 0, v, Some(64)).is_none()
    };
    for removed in 0..vcs.len() {
        let mut partial = vcs.clone();
        partial.remove(removed);
        assert!(check(&function, &query, &partial), "missing body VC {removed}");
    }
    let mut duplicate = vcs.clone();
    duplicate.push(vcs[0].clone());
    assert!(check(&function, &query, &duplicate));
    let mut changed = function.clone();
    changed.contracts[0].body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result >= 64");
    let changed_query = unsigned_select_query(&changed);
    changed.postconditions =
        changed_query.typed_propositions.iter().map(|p| p.formula.clone()).collect();
    assert!(check(&changed, &changed_query, &vcs), "old VCs cannot bind a new clause");
    let mut changed = function.clone();
    let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[1].stmts[0] else { panic!() };
    *rvalue = Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(65, 32)));
    assert!(check(&changed, &query, &vcs), "old VCs cannot bind a changed return");
    let mut changed = vcs.clone();
    changed[0].formula = Formula::Bool(false);
    assert!(check(&function, &query, &changed));
}

#[test]
fn unsigned_select_refuses_narrowed_assumptions_width_drift_and_overflow() {
    let (function, query, vcs) = unsigned_select_input("clamp_width");
    let check = |f: &VerifiableFunction, q: &CompilerContractBundle| {
        exact_unsigned_select_ensures_body_group(f, q, 0, &vcs, Some(64)).is_none()
    };
    let mut changed = function.clone();
    changed.preconditions.push(Formula::Bool(false));
    assert!(check(&changed, &query), "caller assumptions are not type facts");
    let mut changed = function.clone();
    let Formula::And(parts) = &mut changed.preconditions[0] else { panic!() };
    let Formula::Le(_, max) = &mut parts[1] else { panic!() };
    *max = Box::new(Formula::Int(63));
    assert!(check(&changed, &query), "a narrower range must not rule out real inputs");
    for domain in [
        CompilerContractValueDomain::MathematicalInt,
        CompilerContractValueDomain::PointerSizedInt { width: 32, signed: false },
    ] {
        let mut changed_query = query.clone();
        changed_query.typed_propositions[0].variable_domains[0].domain = domain;
        assert!(check(&function, &changed_query));
    }
    let mut changed = function.clone();
    changed.body.locals[1].ty = Ty::u64();
    assert!(check(&changed, &query));
    let mut changed = function.clone();
    let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[1].stmts[0] else { panic!() };
    // This is still a correctly typed u32 return, but overflows at u32::MAX.
    *rvalue = Rvalue::BinaryOp(
        trust_types::BinOp::Add,
        Operand::Copy(Place::local(1)),
        Operand::Constant(trust_types::ConstValue::Uint(1, 32)),
    );
    assert!(check(&changed, &query), "arithmetic/overflow bodies are outside the select fragment");
    let mut changed = function.clone();
    changed.contracts[0].body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result + 1 > result");
    let changed_query = unsigned_select_query(&changed);
    changed.postconditions =
        changed_query.typed_propositions.iter().map(|p| p.formula.clone()).collect();
    assert!(check(&changed, &changed_query), "wrapping arithmetic must not inherit Int ordering");
    let mut changed = function.clone();
    let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[1].stmts[0] else { panic!() };
    *rvalue = Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(1_u128 << 32, 32)));
    assert!(check(&changed, &query), "out-of-width literal is not a u32 return");
}

pub(super) fn boolean_input()
-> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let (mut function, _, _) = input("correct");
    function.body.arg_count = 1;
    function.body.locals.truncate(1);
    function.body.locals.push(trust_types::LocalDecl {
        index: 1,
        ty: Ty::Bool,
        name: Some("input".into()),
    });
    function.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: function.span.clone(),
        }],
        terminator: Terminator::Return,
    }];
    function.spec.ensures = vec!["result == input".into()];
    function.contracts[0].body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == input");
    let domains = vec![
        CompilerContractVariableDomain {
            name: "_0".into(),
            domain: CompilerContractValueDomain::Bool,
        },
        CompilerContractVariableDomain {
            name: "input".into(),
            domain: CompilerContractValueDomain::Bool,
        },
    ];
    let formula = trust_types::compiler_contract_formula_with_domains(
        &trust_types::parse_spec_expr("result == input").unwrap(),
        &domains,
    )
    .unwrap();
    function.postconditions = vec![formula.clone()];
    let query =
        CompilerContractBundle::new(function.contracts.clone()).with_typed_propositions(vec![
            CompilerContractProposition {
                source_contract_index: 0,
                kind: function.contracts[0].kind,
                body: function.contracts[0].body.clone(),
                formula,
                variable_domains: domains,
            },
        ]);
    let (vcs, _) = trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
    (function, query, vcs)
}

#[test]
fn boolean_formal_correspondence_binds_original_input_and_full_body_group() {
    let (function, query, vcs) = boolean_input();
    let group = exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).unwrap();
    assert_eq!(group.body_indices(), &[0]);
    let mut wrong = function.clone();
    let Statement::Assign { rvalue, .. } = &mut wrong.body.blocks[0].stmts[0] else { panic!() };
    *rvalue = Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(false)));
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = query.clone();
    wrong.typed_propositions[0].variable_domains[1].name = "other".into();
    assert!(exact_boolean_ensures_body_group(&function, &wrong, 0, &vcs, Some(64)).is_none());
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &[], Some(64)).is_none());
}

#[test]
fn boolean_formal_correspondence_refuses_forged_indices_domains_and_premises() {
    let (function, query, vcs) = boolean_input();
    let refuses = |function: &VerifiableFunction| {
        exact_boolean_ensures_body_group(function, &query, 0, &vcs, Some(64)).is_none()
    };
    let mut wrong = function.clone();
    wrong.body.locals[1].index = 2;
    assert!(refuses(&wrong));
    let mut wrong = function.clone();
    wrong.body.locals[1].name = Some("_0".into());
    assert!(refuses(&wrong));
    let mut wrong = function.clone();
    wrong.body.locals[1].name = None;
    assert!(refuses(&wrong));
    for ty in [
        Ty::Int { width: 64, signed: false },
        Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) },
    ] {
        let mut wrong = function.clone();
        wrong.body.locals[1].ty = ty;
        assert!(refuses(&wrong));
    }
    let mut wrong = function.clone();
    wrong.preconditions.push(Formula::Bool(false));
    assert!(refuses(&wrong));
    let mut wrong = function.clone();
    wrong.spec.requires.push("false".into());
    assert!(refuses(&wrong));
    let mut wrong = function.clone();
    wrong.body.arg_count = usize::MAX;
    assert!(refuses(&wrong));
}
