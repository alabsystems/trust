//! Constructed typed inputs exercise the shared source/call relation. These
//! are correspondence tests, not retained compiler artifacts or proof claims.
use trust_types::{
    BasicBlock, BlockId, CalleeIdentity, CompilerContractProposition,
    CompilerContractValueDomain as Domain, CompilerContractVariableDomain as Variable,
};

use super::*;

fn identity() -> CalleeIdentity {
    CalleeIdentity { stable_crate_id: 29, def_index: 7, substs_digest: [13, 17] }
}

fn input(
    width: u32,
) -> (VerifiableFunction, CompilerContractBundle, trust_vcgen::InferredReturnCall) {
    let (mut caller, _, _) = super::correspondence_tests::boolean_input();
    let ty = Ty::Int { width, signed: false };
    caller.body.return_ty = ty.clone();
    caller.body.locals[0].ty = ty.clone();
    caller.body.locals[1].ty = ty;
    let domain = Domain::MachineInt { width, signed: false };
    let variables =
        vec![Variable { name: "_0".into(), domain }, Variable { name: "input".into(), domain }];
    let formula = trust_types::compiler_contract_formula_with_domains(
        &trust_types::parse_spec_expr("result == input").unwrap(),
        &variables,
    )
    .unwrap();
    caller.postconditions = vec![formula.clone()];
    caller.preconditions = vec![Formula::And(vec![
        Formula::Ge(Box::new(Formula::Var("input".into(), Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(i128::from(trust_intbound::unsigned_max(width)))),
        ),
    ])];
    let query =
        CompilerContractBundle::new(caller.contracts.clone()).with_typed_propositions(vec![
            CompilerContractProposition {
                source_contract_index: 0,
                kind: caller.contracts[0].kind,
                body: caller.contracts[0].body.clone(),
                formula,
                variable_domains: variables,
            },
        ]);
    let mut callee = caller.clone();
    callee.name = "identity".into();
    callee.def_path = "unsigned_calls::identity".into();
    callee.contracts.clear();
    callee.postconditions.clear();
    callee.spec = Default::default();
    let candidate = trust_vcgen::infer_return_candidate(&callee).unwrap();
    let call = trust_vcgen::InferredReturnCall::new(identity(), &candidate).unwrap();
    caller.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: callee.def_path,
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: caller.span.clone(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: trust_types::UnwindEdge::Unreachable,
                callee_identity: Some(identity()),
                callee_key: None,
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    (caller, query, call)
}

#[test]
fn unsigned_call_source_group_binds_exact_typed_callee_and_original_rows() {
    for width in [8, 16, 32, 64] {
        let (function, query, call) = input(width);
        let (raw, augmented) =
            trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
                &function,
                std::slice::from_ref(&call),
            )
            .unwrap();
        assert!(!raw.is_empty());
        for rows in [&raw, &augmented] {
            let group = exact_ensures_body_group(
                &function,
                &query,
                0,
                rows,
                Some(64),
                Some(std::slice::from_ref(&call)),
            )
            .expect("typed unsigned call must retain exact source correspondence");
            assert_eq!(group.body_indices().len(), rows.len());
        }
        assert!(exact_ensures_body_group(&function, &query, 0, &raw, Some(64), None).is_none());
        assert!(
            exact_ensures_body_group(&function, &query, 0, &raw, Some(64), Some(&[])).is_none()
        );
        for missing in 0..raw.len() {
            let mut rows = raw.clone();
            rows.remove(missing);
            assert!(
                exact_ensures_body_group(
                    &function,
                    &query,
                    0,
                    &rows,
                    Some(64),
                    Some(std::slice::from_ref(&call)),
                )
                .is_none()
            );
        }
    }
}

#[test]
fn unsigned_call_source_group_refuses_changed_identity_type_premises_and_query() {
    let (function, query, call) = input(32);
    let (rows, _) = trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
        &function,
        std::slice::from_ref(&call),
    )
    .unwrap();
    // Prove the control before testing refusals: a blanket rejection cannot
    // satisfy this test.
    assert!(
        exact_ensures_body_group(
            &function,
            &query,
            0,
            &rows,
            Some(64),
            Some(std::slice::from_ref(&call)),
        )
        .is_some()
    );
    for mutation in 0..7 {
        let mut changed = function.clone();
        match mutation {
            0 => {
                let Terminator::Call { callee_identity, .. } =
                    &mut changed.body.blocks[0].terminator
                else {
                    panic!()
                };
                callee_identity.as_mut().unwrap().substs_digest[0] ^= 1;
            }
            1 => changed.body.locals[0].ty = Ty::Int { width: 64, signed: false },
            2 => changed.body.locals[1].ty = Ty::Int { width: 32, signed: true },
            3 => changed.preconditions.push(Formula::Bool(false)),
            4 => changed.preconditions.clear(),
            5 => changed.postconditions[0] = Formula::Bool(true),
            6 => changed.body.blocks[1].stmts.push(Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(0, 32))),
                span: changed.span.clone(),
            }),
            _ => unreachable!(),
        }
        assert!(
            exact_ensures_body_group(
                &changed,
                &query,
                0,
                &rows,
                Some(64),
                Some(std::slice::from_ref(&call)),
            )
            .is_none(),
            "accepted mutation {mutation}"
        );
    }
    let mut changed = query.clone();
    changed.typed_propositions[0].variable_domains[0].domain =
        Domain::MachineInt { width: 64, signed: false };
    assert!(
        exact_ensures_body_group(
            &function,
            &changed,
            0,
            &rows,
            Some(64),
            Some(std::slice::from_ref(&call)),
        )
        .is_none()
    );
}

#[test]
fn unsigned_call_source_group_requires_every_authored_clause() {
    let (mut function, mut query, call) = input(32);
    let mut contract = function.contracts[0].clone();
    contract.body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result <= input");
    let mut proposition = query.typed_propositions[0].clone();
    proposition.source_contract_index = 1;
    proposition.body = contract.body.clone();
    proposition.formula = trust_types::compiler_contract_formula_with_domains(
        &trust_types::parse_spec_expr("result <= input").unwrap(),
        &proposition.variable_domains,
    )
    .unwrap();
    function.postconditions.push(proposition.formula.clone());
    function.spec.ensures.push("result <= input".into());
    function.contracts.push(contract.clone());
    query.contracts.push(contract);
    query.typed_propositions.push(proposition);
    let (rows, _) = trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
        &function,
        std::slice::from_ref(&call),
    )
    .unwrap();
    assert_eq!(rows.len(), 2);
    for index in 0..2 {
        let group = exact_ensures_body_group(
            &function,
            &query,
            index,
            &rows,
            Some(64),
            Some(std::slice::from_ref(&call)),
        )
        .unwrap();
        assert_eq!(group.body_indices().len(), 1);
        let only_selected = vec![rows[group.body_indices()[0]].clone()];
        assert!(
            exact_ensures_body_group(
                &function,
                &query,
                index,
                &only_selected,
                Some(64),
                Some(std::slice::from_ref(&call)),
            )
            .is_none(),
            "an unselected authored clause cannot disappear"
        );
    }
    let mut duplicate = rows.clone();
    duplicate.push(rows[0].clone());
    assert!(
        exact_ensures_body_group(
            &function,
            &query,
            0,
            &duplicate,
            Some(64),
            Some(std::slice::from_ref(&call)),
        )
        .is_none()
    );
    query.typed_propositions[1].formula = Formula::Bool(true);
    assert!(
        exact_ensures_body_group(
            &function,
            &query,
            0,
            &rows,
            Some(64),
            Some(std::slice::from_ref(&call)),
        )
        .is_none(),
        "an unselected authored clause cannot change"
    );
}

#[test]
fn retained_toolchain_width_wrappers_bind_the_original_typed_helpers() {
    for (caller_bytes, caller_sha, callee_bytes, callee_sha) in [
        (
            &include_bytes!("../tests/fixtures/unsigned-calls/width_is_supported.json")[..],
            "4cdc6a7f9a975fc85ccf6b5c2bab6a486d10a9d144b97fa8fa410ceb3385b55a",
            &include_bytes!("../tests/fixtures/unsigned-calls/raw_width_is_supported.json")[..],
            "a76d61d07e43d5ee12a3bc4f1b74c7c5d885dbefef9318640725ce2cf0e900d5",
        ),
        (
            &include_bytes!("../tests/fixtures/unsigned-calls/width_supported.json")[..],
            "a85f4b4f2a12e05c1f58ce39d0853c4fd21abfad96e14a0e6b18cec6af4b8142",
            &include_bytes!("../tests/fixtures/unsigned-calls/raw_width_supported.json")[..],
            "a3533e502b0ba240e0c8af81278e2ed55104aca35d2ed768d9bec5e8ea595367",
        ),
    ] {
        assert_eq!(stable_sha256_hex(caller_bytes), caller_sha);
        assert_eq!(stable_sha256_hex(callee_bytes), callee_sha);
        let function: VerifiableFunction = serde_json::from_slice(caller_bytes).unwrap();
        let callee: VerifiableFunction = serde_json::from_slice(callee_bytes).unwrap();
        let identity = function
            .body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator {
                Terminator::Call { callee_identity, .. } => *callee_identity,
                _ => None,
            })
            .unwrap();
        let inferred = trust_vcgen::infer_return_candidate(&callee).unwrap();
        let call = trust_vcgen::InferredReturnCall::new(identity, &inferred).unwrap();
        // The original exporter retained typed bodies, not the compiler query.
        // Reconstruct this sidecar with the same test helper as other retained
        // integer controls; this is not source-publication authority.
        let query = super::correspondence_tests::unsigned_select_query(&function);
        let (raw, augmented) =
            trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
                &function,
                std::slice::from_ref(&call),
            )
            .unwrap();
        for rows in [&raw, &augmented] {
            let group = exact_ensures_body_group(
                &function,
                &query,
                0,
                rows,
                Some(64),
                Some(std::slice::from_ref(&call)),
            )
            .unwrap_or_else(|| panic!("{} failed correspondence", function.def_path));
            assert!(!group.body_indices().is_empty());
            assert_eq!(group.body_indices().len(), rows.len());
        }
        assert!(exact_ensures_body_group(&function, &query, 0, &raw, Some(64), None).is_none());
    }
}
