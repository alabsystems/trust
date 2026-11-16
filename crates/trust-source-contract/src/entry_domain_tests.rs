//! Constructed typed/query controls, not retained compiler-query captures.
use trust_types::{
    BasicBlock, BinOp, BlockId, CompilerContractProposition, CompilerContractValueDomain as Domain,
    CompilerContractVariableDomain as Variable, ConstValue, LocalDecl, VariantDef,
};

use super::*;

fn bind(
    mut function: VerifiableFunction,
    text: &str,
    domains: Vec<Variable>,
) -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    function.spec.ensures = vec![text.into()];
    function.contracts[0].body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{text}");
    let formula = trust_types::compiler_contract_formula_with_domains(
        &trust_types::parse_spec_expr(text).unwrap(),
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

fn scalar(
    width: u32,
    signed: bool,
) -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let (mut function, _, _) = super::correspondence_tests::boolean_input();
    function.body.arg_count = 2;
    function.body.locals[1].name = Some("have".into());
    function.body.locals[1].ty = Ty::Int { width, signed };
    function.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Int { width, signed },
        name: Some("need".into()),
    });
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Ge,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        span: function.span.clone(),
    };
    let (min, max) = if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    };
    function.preconditions = ["have", "need"]
        .into_iter()
        .map(|name| {
            Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var(name.into(), Sort::Int)),
                    Box::new(Formula::Int(min)),
                ),
                Formula::Le(
                    Box::new(Formula::Var(name.into(), Sort::Int)),
                    Box::new(Formula::Int(max)),
                ),
            ])
        })
        .collect();
    bind(
        function,
        "result == (have >= need)",
        vec![
            Variable { name: "_0".into(), domain: Domain::Bool },
            Variable { name: "have".into(), domain: Domain::MachineInt { width, signed } },
            Variable { name: "need".into(), domain: Domain::MachineInt { width, signed } },
        ],
    )
}

#[test]
fn scalar_boolean_entry_uses_full_original_machine_domains() {
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            let (function, query, vcs) = scalar(width, signed);
            assert!(
                exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).is_some(),
                "{width}/{signed}"
            );
            let mut wrong = function.clone();
            wrong.preconditions.push(Formula::Bool(false));
            assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
            let mut wrong = function.clone();
            wrong.preconditions.remove(0);
            assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
            let mut wrong = function.clone();
            let Formula::And(parts) = &mut wrong.preconditions[0] else { panic!() };
            parts[1] = Formula::Bool(false);
            assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
            let mut wrong = query.clone();
            wrong.typed_propositions[0].variable_domains[1].domain =
                Domain::MachineInt { width, signed: !signed };
            assert!(
                exact_boolean_ensures_body_group(&function, &wrong, 0, &vcs, Some(64)).is_none()
            );
        }
    }
}

fn nominal() -> (VerifiableFunction, CompilerContractBundle, Vec<VerificationCondition>) {
    let (mut function, _, _) = super::correspondence_tests::boolean_input();
    let mut ty = Ty::adt_enum(
        "original::Nominal",
        vec![
            VariantDef { name: "Negative".into(), discriminant: -7, fields: vec![] },
            VariantDef { name: "Positive".into(), discriminant: 42, fields: vec![] },
        ],
    );
    let Ty::Adt { fields, adt_kind, .. } = &mut ty else { panic!() };
    *fields = vec![("__tag".into(), Ty::Int { width: 8, signed: true })].into();
    *adt_kind = Some(trust_types::AdtKind::Enum);
    function.body.locals[1].ty = ty;
    function.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Int { width: 8, signed: true },
        name: None,
    });
    function.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: function.span.clone(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(249, BlockId(1)), (42, BlockId(1))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: function.span.clone(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                span: function.span.clone(),
            }],
            terminator: Terminator::Return,
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
    ];
    function.preconditions = vec![Formula::Or(
        [-7, 42]
            .into_iter()
            .map(|tag| {
                Formula::Eq(
                    Box::new(Formula::Var("_2".into(), Sort::Int)),
                    Box::new(Formula::Int(tag)),
                )
            })
            .collect(),
    )];
    bind(function, "result", vec![Variable { name: "_0".into(), domain: Domain::Bool }])
}

#[test]
fn nominal_entry_preserves_exact_signed_tags_and_never_scalarizes_enum_formal() {
    let (function, query, vcs) = nominal();
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).is_some());
    let mut wrong = function.clone();
    let Formula::Or(tags) = &mut wrong.preconditions[0] else { panic!() };
    tags.remove(0);
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    let Ty::Adt { adt_kind, .. } = &mut wrong.body.locals[1].ty else { panic!() };
    *adt_kind = None;
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = query.clone();
    wrong.typed_propositions[0].variable_domains.push(Variable {
        name: "input".into(),
        domain: Domain::MachineInt { width: 8, signed: true },
    });
    assert!(exact_boolean_ensures_body_group(&function, &wrong, 0, &vcs, Some(64)).is_none());
}

#[test]
fn nominal_payload_descriptor_and_unknown_call_cannot_forge_entry_premises() {
    let (mut function, query, _) = nominal();
    let Ty::Adt { fields, variants, .. } = &mut function.body.locals[1].ty else { panic!() };
    variants.make_mut()[1].fields.push(("depth".into(), Ty::Int { width: 64, signed: false }));
    fields.make_mut().push(("__v1_depth".into(), Ty::Int { width: 64, signed: false }));
    let (vcs, _) = trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).is_some());
    let mut wrong = function.clone();
    let Ty::Adt { fields, .. } = &mut wrong.body.locals[1].ty else { panic!() };
    fields.make_mut()[1].0 = "__v0_depth".into();
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    let Ty::Adt { fields, .. } = &mut wrong.body.locals[1].ty else { panic!() };
    fields.make_mut()[0].1 = Ty::Int { width: 8, signed: false };
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    wrong.body.locals[2].ty = Ty::Int { width: 8, signed: false };
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    wrong.body.locals[2].name = Some("_0".into());
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    wrong.preconditions.push(Formula::Bool(false));
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
    let mut wrong = function.clone();
    wrong.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: wrong.span.clone(),
    });
    assert!(exact_boolean_ensures_body_group(&wrong, &query, 0, &vcs, Some(64)).is_none());
}

#[test]
fn nominal_entry_refuses_unprovided_original_callee_identity() {
    let (mut function, query, vcs) = nominal();
    let original: VerifiableFunction =
        serde_json::from_str(include_str!("../tests/fixtures/correct.json")).unwrap();
    let mut call = original
        .body
        .blocks
        .iter()
        .find_map(|block| {
            matches!(block.terminator, Terminator::Call { .. }).then(|| block.terminator.clone())
        })
        .unwrap();
    let Terminator::Call { args, dest, target, .. } = &mut call else { panic!() };
    *args = vec![Operand::Copy(Place::local(1))];
    *dest = Place::local(0);
    *target = Some(BlockId(1));
    function.body.blocks[0].terminator = call;
    assert!(exact_boolean_ensures_body_group(&function, &query, 0, &vcs, Some(64)).is_none());
}

#[test]
fn every_nominal_formal_has_independent_nonaliasing_source_identity() {
    let (mut function, _, _) = nominal();
    function.body.arg_count = 2;
    function.body.locals[1].name = Some("left".into());
    function.body.locals[2] =
        LocalDecl { index: 2, ty: function.body.locals[1].ty.clone(), name: Some("right".into()) };
    function.body.blocks = vec![function.body.blocks[1].clone()];
    function.body.blocks[0].id = BlockId(0);
    function.preconditions.clear();
    let domains = trust_vcgen::boolean_source_entry_domains(&function, None).unwrap();
    assert_eq!(domains.len(), 1, "neither nominal input becomes a scalar domain");
    let mut wrong = function.clone();
    wrong.body.locals[1].name = Some("_0".into());
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
    let mut wrong = function.clone();
    wrong.body.locals[1].name = Some("right".into());
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
    let mut wrong = function.clone();
    wrong.body.locals[2].ty = Ty::Bool;
    wrong.body.locals[2].name = Some("left".into());
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
    let (mut wrong, _, _) = nominal();
    wrong.body.locals[2].name = Some("input".into());
    let Formula::Or(tags) = &mut wrong.preconditions[0] else { panic!() };
    for tag in tags {
        let Formula::Eq(variable, _) = tag else { panic!() };
        **variable = Formula::Var("input".into(), Sort::Int);
    }
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
}

#[test]
fn retained_original_enum_method_has_exact_entry_premise_carrier() {
    let capture: serde_json::Value =
        serde_json::from_str(include_str!("../tests/fixtures/actual-inferred-source-group.json"))
            .unwrap();
    let function: VerifiableFunction =
        serde_json::from_value(capture["callee"]["function"].clone()).unwrap();
    assert_eq!(function.def_path, "call_vc_tables::Site::admits");
    let domains = trust_vcgen::boolean_source_entry_domains(&function, None).unwrap();
    assert_eq!(domains.len(), 1);
    assert_eq!(function.preconditions.len(), 3, "all original repeated tag reads participate");
    let mut wrong = function.clone();
    wrong.preconditions.pop();
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
    let mut wrong = function.clone();
    wrong.preconditions.push(Formula::Bool(false));
    assert!(trust_vcgen::boolean_source_entry_domains(&wrong, None).is_none());
}

#[test]
fn original_five_law_helper_entry_domains_keep_real_callee_custody() {
    let inputs = [
        include_str!("../tests/fixtures/law-entry/coverage_supports.json"),
        include_str!("../tests/fixtures/law-entry/license_admits_body.json"),
        include_str!("../tests/fixtures/law-entry/visibility_contradicts_linkage.json"),
        include_str!("../tests/fixtures/law-entry/evidence_admits_kind.json"),
        include_str!("../tests/fixtures/law-entry/proof_ref_kind_is_ambiguous.json"),
    ];
    let callee: VerifiableFunction =
        serde_json::from_str(include_str!("../tests/fixtures/law-entry/is_module_local.json"))
            .unwrap();
    let candidate = trust_vcgen::infer_return_candidate(&callee).unwrap();
    for raw in inputs {
        let function: VerifiableFunction = serde_json::from_str(raw).unwrap();
        // Candidate-only structural inputs, never substitutes for the original
        // callee's independently checked certificate DAG.
        let identity = function.body.blocks.iter().find_map(|block| match block.terminator {
            Terminator::Call { callee_identity, .. } => callee_identity,
            _ => None,
        });
        let calls: Vec<_> = identity
            .into_iter()
            .map(|identity| trust_vcgen::InferredReturnCall::new(identity, &candidate).unwrap())
            .collect();
        let domains = trust_vcgen::boolean_source_entry_domains(&function, Some(&calls))
            .unwrap_or_else(|| panic!("{}", function.def_path));
        assert_eq!(domains.len(), 1, "all original formals remain nominal");
        let mut wrong = function.clone();
        wrong.preconditions.push(Formula::Bool(false));
        assert!(trust_vcgen::boolean_source_entry_domains(&wrong, Some(&calls)).is_none());
        if let Some(identity) = identity {
            assert!(trust_vcgen::boolean_source_entry_domains(&function, None).is_none());
            let mut wrong = identity;
            wrong.def_index ^= 1;
            let foreign = trust_vcgen::InferredReturnCall::new(wrong, &candidate).unwrap();
            assert!(
                trust_vcgen::boolean_source_entry_domains(&function, Some(&[foreign])).is_none()
            );
        }
    }
}

#[test]
fn original_scalar_and_nominal_laws_bind_complete_source_groups() {
    for (wrapper_raw, helper_raw, scalar) in [
        (
            include_str!("../tests/fixtures/law-entry/coverage_unwind_is_magnitude_order.json"),
            include_str!("../tests/fixtures/law-entry/coverage_supports.json"),
            true,
        ),
        (
            include_str!("../tests/fixtures/law-entry/evidence_clean_cic_unconstrained.json"),
            include_str!("../tests/fixtures/law-entry/evidence_admits_kind.json"),
            false,
        ),
        (
            include_str!(
                "../tests/fixtures/law-entry/license_gated_admitted_under_any_policy.json"
            ),
            include_str!("../tests/fixtures/law-entry/license_admits_body.json"),
            false,
        ),
        (
            include_str!("../tests/fixtures/law-entry/visibility_external_never_contradicts.json"),
            include_str!("../tests/fixtures/law-entry/visibility_contradicts_linkage.json"),
            false,
        ),
        (
            include_str!("../tests/fixtures/law-entry/ambiguous_precondition.json"),
            include_str!("../tests/fixtures/law-entry/proof_ref_kind_is_ambiguous.json"),
            false,
        ),
    ] {
        let function: VerifiableFunction = serde_json::from_str(wrapper_raw).unwrap();
        let helper: VerifiableFunction = serde_json::from_str(helper_raw).unwrap();
        let identity = function
            .body
            .blocks
            .iter()
            .find_map(|block| match block.terminator {
                Terminator::Call { callee_identity, .. } => callee_identity,
                _ => None,
            })
            .unwrap();
        let method_identity = helper.body.blocks.iter().find_map(|block| match block.terminator {
            Terminator::Call { callee_identity, .. } => callee_identity,
            _ => None,
        });
        let candidate = if let Some(method_identity) = method_identity {
            let method: VerifiableFunction = serde_json::from_str(include_str!(
                "../tests/fixtures/law-entry/is_module_local.json"
            ))
            .unwrap();
            let leaf = trust_vcgen::infer_return_candidate(&method).unwrap();
            let method_call = trust_vcgen::InferredReturnCall::new(method_identity, &leaf).unwrap();
            trust_vcgen::infer_return_candidate_with_calls_rows(
                &helper,
                &[method_call],
                &mut trust_types::vc_context::VcContext::new(),
            )
            .unwrap()
        } else {
            trust_vcgen::infer_return_candidate(&helper).unwrap()
        };

        let calls = [trust_vcgen::InferredReturnCall::new(identity, &candidate).unwrap()];
        // Explicit constructed query sidecar, NOT an original compiler-query
        // capture and NOT source proof authority. The original function/body,
        // authored clause bytes, and generated postconditions stay unchanged.
        let mut domains = vec![Variable { name: "_0".into(), domain: Domain::Bool }];
        if scalar {
            for name in ["have", "need"] {
                domains.push(Variable {
                    name: name.into(),
                    domain: Domain::MachineInt { width: 64, signed: false },
                });
            }
        }
        let contract = &function.contracts[0];
        let formula = trust_types::compiler_contract_formula_with_domains(
            &trust_types::parse_spec_expr(
                contract.body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap(),
            )
            .unwrap(),
            &domains,
        )
        .unwrap();
        assert_eq!(formula, function.postconditions[0]);
        let query = CompilerContractBundle::new(function.contracts.clone())
            .with_typed_propositions(vec![CompilerContractProposition {
                source_contract_index: 0,
                kind: contract.kind,
                body: contract.body.clone(),
                formula,
                variable_domains: domains,
            }]);
        let (vcs, _) =
            trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
                &function, &calls,
            )
            .unwrap();
        assert!(!vcs.is_empty());
        assert!(
            exact_boolean_ensures_body_group_with_inferred_calls(
                &function,
                &query,
                0,
                &vcs,
                Some(64),
                &calls
            )
            .is_some(),
            "{}",
            function.def_path
        );
        assert!(
            exact_boolean_ensures_body_group_with_inferred_calls(
                &function,
                &query,
                0,
                &vcs[1..],
                Some(64),
                &calls
            )
            .is_none()
        );
        let mut wrong = function.clone();
        let name = wrong.body.blocks[0]
            .stmts
            .iter_mut()
            .find_map(|statement| match statement {
                Statement::Assign {
                    rvalue: Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
                    ..
                } => Some(name),
                _ => None,
            })
            .unwrap();
        *name = "lookalike::WrongNominal".into();
        assert!(
            exact_boolean_ensures_body_group_with_inferred_calls(
                &wrong,
                &query,
                0,
                &vcs,
                Some(64),
                &calls
            )
            .is_none()
        );
        let mut wrong = function.clone();
        let Terminator::Call { args, .. } = &mut wrong.body.blocks[0].terminator else { panic!() };
        if args.len() > 1 {
            args.swap(0, 1);
        } else {
            args.clear();
        }
        assert!(
            exact_boolean_ensures_body_group_with_inferred_calls(
                &wrong,
                &query,
                0,
                &vcs,
                Some(64),
                &calls
            )
            .is_none()
        );
    }
}
