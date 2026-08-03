use trust_types::UnwindEdge;
use std::path::PathBuf;

use trust_types::{
    AggregateKind, CallableDefPathHash, CallableKind, ClosureCallKind, Operand, Place, Sort,
    SourceSpan, VcKind, VerificationResult,
};

use super::*;

/// Build the midpoint function MIR.
pub fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn fixture_dir() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest).join("../trust-integration-tests/fixtures/real_mir")
}

fn load_fixture(name: &str) -> VerifiableFunction {
    let path = fixture_dir().join(format!("{name}.json"));
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse fixture {}: {e}", path.display()))
}

fn assert_malformed_body_fails_closed(func: &VerifiableFunction) {
    assert!(
        try_generate_vcs(func).is_err(),
        "fallible VC generation must reject malformed public MIR"
    );
    let vcs = generate_vcs(func);
    assert_eq!(vcs.len(), 1, "malformed MIR must replace every proof-capable row");
    assert!(
        matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr"
        ),
        "infallible VC generation must expose one fail-closed UnsupportedMir row: {vcs:?}"
    );
    assert_eq!(vcs[0].formula, Formula::Bool(true));

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(func);
    assert!(solver_vcs.is_empty());
    assert_eq!(preclassified.len(), 1);
    assert!(matches!(&preclassified[0].1, VerificationResult::Unknown { .. }));

    let summaries = SummaryDatabase::new();
    let (solver_vcs, preclassified) = generate_vcs_with_discharge_and_summaries(func, &summaries);
    assert!(solver_vcs.is_empty());
    assert_eq!(preclassified.len(), 1);
    assert!(matches!(&preclassified[0].1, VerificationResult::Unknown { .. }));

    assert_eq!(generate_callsite_precondition_vcs(func, &summaries).len(), 1);
    assert_eq!(generate_callsite_precondition_vcs_attributed(func, &summaries).len(), 1);
    assert_eq!(generate_full_assert_refutation_vcs(func).len(), 1);

    let loop_rows = regenerate_loop_decreases_with_invariant_feedback_vcs(func, &[]);
    assert_eq!(loop_rows.len(), 1);
    assert!(matches!(
        &loop_rows[0].kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr"
    ));
    assert!(
        regenerate_loop_decreases_with_invariant_feedback_production_variants(func, &[]).is_none()
    );
    assert!(regenerate_loop_contract_production_variants(func, &[]).is_none());
    assert!(regenerate_recursion_decreases_production_variants(func).is_none());
}

#[test]
fn public_vcgen_rejects_reordered_and_sparse_local_declarations() {
    let mut reordered = midpoint_function();
    reordered.body.locals.swap(1, 2);
    assert_malformed_body_fails_closed(&reordered);

    let mut sparse = midpoint_function();
    sparse.body.locals[2].index = 7;
    assert_malformed_body_fails_closed(&sparse);
}

#[test]
fn public_vcgen_rejects_reordered_and_sparse_basic_blocks() {
    let mut reordered = midpoint_function();
    reordered.body.blocks.swap(0, 1);
    assert_malformed_body_fails_closed(&reordered);

    let mut sparse = midpoint_function();
    sparse.body.blocks[1].id = BlockId(7);
    assert_malformed_body_fails_closed(&sparse);
}

#[test]
fn public_vcgen_rejects_invalid_argument_and_reference_indices() {
    let mut invalid_arg_count = midpoint_function();
    invalid_arg_count.body.arg_count = invalid_arg_count.body.locals.len();
    assert_malformed_body_fails_closed(&invalid_arg_count);

    let mut invalid_local = midpoint_function();
    let Statement::Assign { rvalue, .. } = &mut invalid_local.body.blocks[0].stmts[0] else {
        unreachable!()
    };
    *rvalue = Rvalue::Use(Operand::Copy(Place::local(99)));
    assert!(matches!(
        validate_function(&invalid_local),
        Err(VcgenError::InvalidLocal { index: 99, .. })
    ));
    assert_malformed_body_fails_closed(&invalid_local);

    let mut invalid_target = midpoint_function();
    let Terminator::Assert { target, .. } = &mut invalid_target.body.blocks[0].terminator else {
        unreachable!()
    };
    *target = BlockId(99);
    assert!(matches!(validate_function(&invalid_target), Err(VcgenError::InvalidBlock { .. })));
    assert_malformed_body_fails_closed(&invalid_target);
}

#[test]
fn public_vcgen_rejects_return_type_drift_and_duplicate_switch_cases() {
    let mut wrong_return_type = midpoint_function();
    wrong_return_type.body.return_ty = Ty::u8();
    assert_malformed_body_fails_closed(&wrong_return_type);

    let mut duplicate_switch_case = midpoint_function();
    duplicate_switch_case.body.blocks[0].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(1)),
        targets: vec![(0, BlockId(1)), (0, BlockId(1))],
        otherwise: BlockId(1),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    assert_malformed_body_fails_closed(&duplicate_switch_case);
}

#[test]
fn test_operand_to_formula_preserves_symbolic_operand() {
    let func = midpoint_function();
    let symbolic = Formula::var_owned("__trust_symbolic_operand".to_string(), Sort::Int);

    assert_eq!(operand_to_formula(&func, &Operand::Symbolic(symbolic.clone())), symbolic);
}

#[test]
fn test_generate_vcs_consumes_trust_symbolic_formula_payload() {
    let symbolic_payload =
        Formula::var_owned("trust_symbolic.formula".to_string(), Sort::BitVec(64));
    let symbolic_divisor = Formula::BvAdd(
        Box::new(symbolic_payload.clone()),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let func = VerifiableFunction {
        name: "symbolic_payload_divisor".to_string(),
        def_path: "test::symbolic_payload_divisor".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x0".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("result".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Symbolic(symbolic_divisor.clone()),
                    ),
                    span: SourceSpan::binary_address(0x4000),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let div_vc = generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("symbolic divisor should emit a DivisionByZero VC");
    let expected_formula =
        Formula::Eq(Box::new(symbolic_divisor), Box::new(Formula::BitVec { value: 0, width: 64 }));

    assert_eq!(
        div_vc.formula, expected_formula,
        "trust_symbolic.formula payloads must be consumed structurally, not lowered to Undef"
    );
    assert!(
        formula_contains(&div_vc.formula, &|formula| formula == &symbolic_payload),
        "proof consumers must still see the preserved trust_symbolic.formula payload: {:?}",
        div_vc.formula
    );
}

#[test]
fn test_symbolic_formula_consumer_record_carries_content_digest_status() {
    let symbolic_payload =
        Formula::var_owned("trust_symbolic.formula".to_string(), Sort::BitVec(64));
    let formula = Formula::BvAdd(
        Box::new(symbolic_payload.clone()),
        Box::new(Formula::BitVec { value: 7, width: 64 }),
        64,
    );
    let expected_content = serde_json::to_string(&formula).expect("Formula JSON should serialize");
    let expected_digest = trust_types::stable_sha256_hex(expected_content.as_bytes());

    let record = symbolic_formula::consume_symbolic_formula(&formula)
        .expect("typed trust_symbolic.formula should be consumed");

    assert_eq!(record.schema, symbolic_formula::SYMBOLIC_FORMULA_SCHEMA);
    assert_eq!(record.status, symbolic_formula::SymbolicFormulaConsumerStatus::Consumed);
    assert_eq!(record.content, expected_content);
    assert_eq!(record.digest, expected_digest);
    assert_eq!(record.sort, Sort::BitVec(64));
    assert_eq!(record.smtlib_sort, "(_ BitVec 64)");
    assert!(
        record.diagnostic("bb0 stmt0 rhs").contains("trust_symbolic.formula=consumed"),
        "accepted consumer diagnostic must carry consumed status: {record:?}"
    );
}

#[test]
fn test_symbolic_formula_consumer_rejects_unknown_schema_with_blocker_record() {
    let formula = Formula::var_owned("trust_symbolic.formula".to_string(), Sort::BitVec(64));

    let rejection = symbolic_formula::consume_symbolic_formula_with_schema(
        "trust-types.Formula@future",
        &formula,
    )
    .expect_err("unknown symbolic formula schema must be rejected");
    let diagnostic = rejection.diagnostic("bb0 stmt0 rhs");

    assert_eq!(rejection.unsupported_vc_kind(), "TrustSymbolicFormulaNotProofConsumed");
    assert!(diagnostic.contains("formula.schema_error=unknown-schema"));
    assert!(diagnostic.contains("proof-grade=false"));
    assert!(diagnostic.contains("formula.sha256="));
    assert!(
        diagnostic.contains("rejecting instead of Undef"),
        "unknown schema must block proof-grade without an Undef fallback: {diagnostic}"
    );
}

#[test]
fn test_generate_vcs_threads_symbolic_aggregate_fields() {
    let symbolic_payload =
        Formula::var_owned("trust_symbolic.aggregate.field0".to_string(), Sort::BitVec(64));
    let symbolic_field = Formula::BvAdd(
        Box::new(symbolic_payload.clone()),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let field_place = Place::field(1, 0);
    let func = VerifiableFunction {
        name: "symbolic_aggregate_divisor".to_string(),
        def_path: "test::symbolic_aggregate_divisor".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                    name: Some("agg".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("numerator".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Symbolic(symbolic_field.clone()),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::binary_address(0x4100),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(field_place.clone()),
                        ),
                        span: SourceSpan::binary_address(0x4104),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let div_vc = generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("aggregate field divisor should emit a DivisionByZero VC");
    let field_formula = operand_to_formula(&func, &Operand::Copy(field_place));
    let expected_field_def = Formula::Eq(Box::new(field_formula), Box::new(symbolic_field.clone()));

    assert!(
        formula_contains(&strip_versions(&div_vc.formula), &|formula| formula
            == &expected_field_def),
        "trust_symbolic.aggregate field definitions must be preserved in VC dataflow: {:?}",
        div_vc.formula
    );
    assert!(
        formula_contains(&div_vc.formula, &|formula| formula == &symbolic_payload),
        "aggregate payload must not be silently ignored or replaced by an unconstrained field: {:?}",
        div_vc.formula
    );

    let field_sorts = trust_types::collect_free_var_decls(&div_vc.formula)
        .into_iter()
        .filter_map(|(name, sort)| (vbase(&name) == "agg.0").then_some(sort))
        .collect::<Vec<_>>();
    assert_eq!(
        field_sorts,
        vec![Sort::BitVec(64)],
        "aggregate field variables fed by symbolic payloads must keep the payload sort: {:?}",
        div_vc.formula
    );
    assert!(
        formula_contains(&div_vc.formula, &|formula| {
            matches!(formula, Formula::BitVec { value: 0, width: 64 })
        }),
        "bitvector aggregate fields must compare against a bitvector zero, not Int(0): {:?}",
        div_vc.formula
    );
}

#[test]
fn test_generate_vcs_threads_closure_capture_fields_without_unsupported_mir() {
    let symbolic_payload =
        Formula::var_owned("trust_symbolic.closure.capture0".to_string(), Sort::BitVec(64));
    let symbolic_capture = Formula::BvAdd(
        Box::new(symbolic_payload.clone()),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let capture_place = Place::field(1, 0);
    let func = VerifiableFunction {
        name: "closure_capture_divisor".to_string(),
        def_path: "test::closure_capture_divisor".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Closure {
                        name: "test::closure".to_string(),
                        upvars: vec![Ty::u64()],
                        call: None,
                    },
                    name: Some("closure_env".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("numerator".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Closure {
                                name: "test::closure".to_string(),
                                captures: vec![Ty::u64()],
                                call_kind: ClosureCallKind::FnOnce,
                            },
                            vec![Operand::Symbolic(symbolic_capture.clone())],
                        ),
                        span: SourceSpan::binary_address(0x4200),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(capture_place.clone()),
                        ),
                        span: SourceSpan::binary_address(0x4204),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "AggregateKind::Closure"
        )),
        "well-formed closure construction should not be classified unsupported: {vcs:?}"
    );

    let div_vc = vcs
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("closure capture divisor should emit a DivisionByZero VC");
    let capture_formula = operand_to_formula(&func, &Operand::Copy(capture_place));
    let expected_capture_def =
        Formula::Eq(Box::new(capture_formula), Box::new(symbolic_capture.clone()));

    assert!(
        formula_contains(&strip_versions(&div_vc.formula), &|formula| formula
            == &expected_capture_def),
        "closure capture field definitions must be preserved in VC dataflow: {:?}",
        div_vc.formula
    );
    assert!(
        formula_contains(&div_vc.formula, &|formula| formula == &symbolic_payload),
        "closure capture symbolic payload must not be replaced by an unconstrained field: {:?}",
        div_vc.formula
    );
}

#[test]
fn test_generate_vcs_blocks_unconsumed_symbolic_formula_schema_without_undef() {
    let symbolic_formula = Formula::var_owned(
        "trust_symbolic.formula.array".to_string(),
        Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
    );
    let func = VerifiableFunction {
        name: "symbolic_formula_array_schema_blocked".to_string(),
        def_path: "test::symbolic_formula_array_schema_blocked".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("dst".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Symbolic(symbolic_formula)),
                    span: SourceSpan::binary_address(0x4210),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let blocker = generate_vcs(&func)
        .into_iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "TrustSymbolicFormulaNotProofConsumed"
                        && detail.contains("unsupported-top-level-sort")
            )
        })
        .expect("unsupported symbolic formula schema must emit a proof-grade blocker");
    let VcKind::UnsupportedMir { detail, .. } = &blocker.kind else {
        unreachable!("filtered to UnsupportedMir")
    };

    assert_eq!(blocker.formula, Formula::Bool(true));
    assert!(detail.contains("trust_symbolic.formula=not-consumed"));
    assert!(detail.contains("formula.schema=trust-types.Formula@1"));
    assert!(detail.contains("formula.sha256="));
    assert!(detail.contains("proof-grade=false"));
    assert!(
        !detail.contains("Undef") || detail.contains("rejecting instead of Undef"),
        "symbolic formula blocker must not degrade to Undef-only diagnostics: {detail}"
    );
}

#[test]
fn test_operand_ty_infers_symbolic_formula_sort() {
    let func = midpoint_function();

    assert_eq!(
        operand_ty(&func, &Operand::Symbolic(Formula::var_owned("flag".to_string(), Sort::Bool))),
        Some(Ty::Bool)
    );
    assert_eq!(
        operand_ty(
            &func,
            &Operand::Symbolic(Formula::var_owned("word".to_string(), Sort::BitVec(32)))
        ),
        Some(Ty::Int { width: 32, signed: false })
    );
    assert_eq!(
        operand_ty(
            &func,
            &Operand::Symbolic(Formula::Eq(
                Box::new(Formula::var_owned("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        ),
        Some(Ty::Bool)
    );
}

#[test]
fn test_generate_vcs_fails_closed_on_symbolic_formula_missing_sort_metadata() {
    let malformed_formula = Formula::Select(
        Box::new(Formula::Var("not_array".to_string(), Sort::Int)),
        Box::new(Formula::Int(0)),
    );
    let func = VerifiableFunction {
        name: "malformed_symbolic_sort".to_string(),
        def_path: "test::malformed_symbolic_sort".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("dst".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Symbolic(malformed_formula)),
                    span: SourceSpan::binary_address(0x4200),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "TrustSymbolicFormulaSortMissing"
                    && detail.contains("strict SMT sort metadata")
                    && detail.contains("select")
        )),
        "symbolic formulas without strict sort metadata must fail closed: {vcs:?}"
    );
}

#[test]
fn test_symbolic_aggregate_with_recoverable_sorts_is_not_spuriously_fail_closed() {
    let func = VerifiableFunction {
        name: "missing_aggregate_field_sort".to_string(),
        def_path: "test::missing_aggregate_field_sort".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u64()]), name: Some("agg".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![
                            Operand::Symbolic(Formula::Var("field0".to_string(), Sort::BitVec(64))),
                            Operand::Symbolic(Formula::Var("field1".to_string(), Sort::BitVec(64))),
                        ],
                    ),
                    span: SourceSpan::binary_address(0x4300),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // The symbolic operands declare concrete SMT sorts (BitVec(64)), so the
    // strict `place_sort` path (`symbolic_assignment_sort_for_place` first)
    // RECOVERS each field's sort and the aggregate is well-formed — no
    // `TrustSymbolicAggregateFieldSortMissing` marker is emitted. The fail-closed
    // check (generate.rs) still fires when a sort is genuinely unrecoverable; the
    // precision fix only suppresses the marker where a well-formed VC is
    // producible, never turning an unmodelable place into a false proof.
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. }
                if kind == "TrustSymbolicAggregateFieldSortMissing"
        )),
        "symbolic aggregate whose field sorts ARE recoverable must not spuriously fail closed: {vcs:?}"
    );
}

#[test]
fn test_generate_vcs_midpoint() {
    let func = midpoint_function();
    let vcs = generate_vcs(&func);

    // `generate_vcs` emits safety VCs (overflow, divzero) so that
    // callers which invoke it directly (e.g., `real_ay_verification`,
    // `m5_e2e_loop`) receive real SMT formulas. The midpoint body has one
    // `CheckedBinaryOp(Add)` + `Assert(Overflow(Add))` pair in bb0 and a
    // constant-divisor `Div(_, 2)` in bb1. The constant divisor is skipped,
    // so we expect exactly one `ArithmeticOverflow` VC.
    let overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(
        overflow_vcs.len(),
        1,
        "midpoint has one CheckedBinaryOp(Add) → one overflow VC, got {}",
        overflow_vcs.len()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "constant divisor `2` must not produce a DivisionByZero VC"
    );
}

fn unsupported_mir_function() -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: "opaque_term".to_string(),
        def_path: "test::opaque_term".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Opaque {
                        kind: "UnsupportedValidMirTerminator".to_string(),
                        targets: vec![BlockId(1), BlockId(2)],
                        span: span.clone(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn malformed_atomic_metadata_opaque_function() -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: "malformed_atomic_metadata".to_string(),
        def_path: "test::malformed_atomic_metadata".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Opaque {
                        kind: "Call::core::sync::atomic::atomic::atomic_load::UnsupportedAtomicMetadata(load ordering argument is missing or not a concrete Ordering discriminant)"
                            .to_string(),
                        targets: vec![BlockId(1)],
                        span: span.clone(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_unsupported_mir_vc_fails_closed_for_direct_callers() {
    let vcs = generate_vcs(&unsupported_mir_function());

    let unsupported = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. }))
        .expect("opaque TrustIr terminator must emit UnsupportedMir VC");

    assert_eq!(unsupported.formula, Formula::Bool(true));
}

#[test]
fn test_unsupported_mir_is_preclassified_unknown_before_solver() {
    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&unsupported_mir_function());

    assert!(
        solver_vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "UnsupportedMir VCs must not be sent to solvers as ordinary proof obligations"
    );
    assert!(preclassified.iter().any(|(vc, result)| {
        matches!(vc.kind, VcKind::UnsupportedMir { .. })
            && matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
    }));
}

#[test]
fn test_malformed_atomic_metadata_opaque_is_unknown_not_passed() {
    let func = malformed_atomic_metadata_opaque_function();
    let vcs = generate_vcs(&func);

    let unsupported = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. }
                    if kind.contains("UnsupportedAtomicMetadata")
                        && kind.contains("atomic_load")
            )
        })
        .expect("malformed atomic lowering must remain an UnsupportedMir obligation");

    assert_eq!(
        unsupported.formula,
        Formula::Bool(true),
        "direct callers must see a fail-closed satisfiable violation formula"
    );

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        solver_vcs.is_empty(),
        "malformed atomic metadata must not become an ordinary solver candidate: {solver_vcs:#?}"
    );
    assert!(
        preclassified
            .iter()
            .all(|(_, result)| !matches!(result, VerificationResult::Proved { .. })),
        "malformed atomic metadata must not be reported as Proved: {preclassified:#?}"
    );
    assert!(
        preclassified.iter().any(|(vc, result)| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind.contains("UnsupportedAtomicMetadata")
                        && detail.contains("bb0 targets")
            ) && matches!(
                result,
                VerificationResult::Unknown { reason, .. }
                    if reason.contains("unsupported MIR")
                        && reason.contains("UnsupportedAtomicMetadata")
            )
        }),
        "malformed atomic metadata must be preclassified to Unknown: {preclassified:#?}"
    );
}

fn assert_unsupported_mir_unknown(func: VerifiableFunction) {
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| {
            matches!(vc.kind, VcKind::UnsupportedMir { .. }) && vc.formula == Formula::Bool(true)
        }),
        "unsupported TrustIr must emit a satisfiable fail-closed UnsupportedMir VC"
    );

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        solver_vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "UnsupportedMir VCs must be preclassified before solver dispatch"
    );
    assert!(preclassified.iter().any(|(vc, result)| {
        matches!(vc.kind, VcKind::UnsupportedMir { .. })
            && matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
    }));
}

fn unsupported_cast_function(name: &str, from_ty: Ty, to_ty: Ty) -> VerifiableFunction {
    let span = SourceSpan::default();
    let return_ty = to_ty.clone();
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: to_ty.clone(), name: None },
                LocalDecl { index: 1, ty: from_ty, name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to_ty),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unsupported_checked_op_function(op: BinOp) -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: "unsupported_checked_op".to_string(),
        def_path: "test::unsupported_checked_op".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("shift".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(op),
                        target: BlockId(1),
                        span,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_unsupported_checked_binary_op_fails_closed() {
    // Checked shifts are modeled as `ShiftOverflow` VCs. Keep this fail-closed
    // test on a checked op whose overflow semantics are intentionally unsupported.
    let func = unsupported_checked_op_function(BinOp::BitAnd);
    let vcs = generate_vcs(&func);
    let unsupported = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "Rvalue::CheckedBinaryOp" && detail.contains("checked BitAnd")
            )
        })
        .expect("unsupported checked op overflow semantics must emit UnsupportedMir VC");
    assert_eq!(unsupported.formula, Formula::Bool(true));

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        solver_vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "UnsupportedMir checked-op VCs must be preclassified before solver dispatch"
    );
    assert!(preclassified.iter().any(|(vc, result)| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::CheckedBinaryOp")
            && matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
    }));
}

#[test]
fn test_unsupported_mir_statement_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_stmt".to_string(),
        def_path: "test::unsupported_stmt".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Unsupported {
                    kind: "StatementKind::Intrinsic".to_string(),
                    detail: "copy_nonoverlapping requires memory semantics".to_string(),
                    operands: vec![],
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_assume_intrinsic_statement_is_metadata_noop() {
    let func = VerifiableFunction {
        name: "assume_intrinsic_stmt".to_string(),
        def_path: "test::assume_intrinsic_stmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("assumption".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Intrinsic {
                    name: "assume".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "single-bool assume intrinsic is metadata for vcgen and must not block launch"
    );
}

#[test]
fn test_unknown_intrinsic_statement_fails_closed() {
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unknown_intrinsic_stmt".to_string(),
        def_path: "test::unknown_intrinsic_stmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("arg".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Intrinsic {
                    name: "unknown_intrinsic".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_assume_intrinsic_non_bool_condition_fails_closed() {
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "bad_assume_intrinsic_stmt".to_string(),
        def_path: "test::bad_assume_intrinsic_stmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("arg".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Intrinsic {
                    name: "assume".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_unsupported_mir_rvalue_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_rvalue".to_string(),
        def_path: "test::unsupported_rvalue".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Unsupported {
                        kind: "Rvalue::SyntheticUnsupported".to_string(),
                        detail: "synthetic rvalue has no modeled semantics".to_string(),
                        operands: vec![],
                    },
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_ptr_offset_rvalue_fails_closed() {
    // Trust: W2 inc-0 — `Rvalue::PtrOffset` (the modeled MIR `BinOp::Offset`) is
    // pointer arithmetic (`ptr + count * size_of::<T>()`), UB when out-of-bounds.
    // Its faithful in-bounds obligation is the intrinsic lane's
    // `ptr_offset_bounds_vc`, which lives over the reflected slice-relative index
    // in trust-clean, NOT on this direct VC lane. Until that resolves, the lane
    // must fail CLOSED — emit a satisfiable `UnsupportedMir` VC that preclassifies
    // to Unknown — so no function containing an un-discharged offset can vacuously
    // certify. This is exactly the discipline the `Unsupported` marker carried
    // before, now keyed to a distinguishable variant.
    let span = SourceSpan::default();
    let raw = trust_types::Ty::RawPtr { mutable: true, pointee: Box::new(trust_types::Ty::i32()) };
    let func = VerifiableFunction {
        name: "ptr_offset".to_string(),
        def_path: "test::ptr_offset".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: raw.clone(), name: None },
                LocalDecl { index: 1, ty: raw.clone(), name: Some("p".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::PtrOffset {
                        ptr: Operand::Copy(Place::local(1)),
                        count: Operand::Constant(trust_types::ConstValue::Uint(1, 64)),
                    },
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: raw,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Generic fail-closed contract: an UnsupportedMir VC is emitted AND
    // preclassified to Unknown before any solver dispatch (never proved).
    assert_unsupported_mir_unknown(func.clone());

    // And specifically keyed to the PtrOffset marker — the obligation is not
    // swallowed by the collect-unsupported wildcard (i.e. not vacuously safe).
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::PtrOffset"
        )),
        "PtrOffset must emit its own UnsupportedMir obligation: {vcs:#?}"
    );
}

#[test]
fn test_thread_local_ref_rvalue_uses_sealed_address_model() {
    let span = SourceSpan::default();
    let reference_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::usize()) };
    let func = VerifiableFunction {
        name: "thread_local_ref".to_string(),
        def_path: "test::thread_local_ref".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: reference_ty.clone(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Unsupported {
                        kind: "Rvalue::ThreadLocalRef".to_string(),
                        detail: "thread-local reference to test::TLS".to_string(),
                        operands: vec![],
                    },
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: reference_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "the exact ThreadLocalRef marker uses the sealed TLS-address model, not UnsupportedMir: {vcs:#?}"
    );

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        solver_vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. }))
            && preclassified.iter().all(|(vc, _)| {
                !matches!(vc.kind, VcKind::UnsupportedMir { .. })
            }),
        "ThreadLocalRef must not reappear as a preclassified unsupported row: solver={solver_vcs:#?}, preclassified={preclassified:#?}"
    );

    let mut raw_pointer_destination = func.clone();
    let raw_pointer_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::usize()) };
    raw_pointer_destination.body.locals[0].ty = raw_pointer_ty.clone();
    raw_pointer_destination.body.return_ty = raw_pointer_ty;
    let raw_pointer_vcs = generate_vcs(&raw_pointer_destination);
    assert!(
        raw_pointer_vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "the exact raw-pointer ThreadLocalRef marker must use the sealed address model: {raw_pointer_vcs:#?}"
    );

    let mut marker_with_operand = func.clone();
    let Statement::Assign { rvalue, .. } =
        &mut marker_with_operand.body.blocks[0].stmts[0]
    else {
        panic!("ThreadLocalRef fixture assignment disappeared");
    };
    let Rvalue::Unsupported { operands, .. } = rvalue else {
        panic!("ThreadLocalRef fixture marker disappeared");
    };
    operands.push(Operand::Copy(Place::local(0)));
    let malformed_vcs = generate_vcs(&marker_with_operand);
    assert!(
        malformed_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
        )),
        "a ThreadLocalRef marker with operands must fail closed: {malformed_vcs:#?}"
    );

    let mut scalar_destination = func.clone();
    scalar_destination.body.locals[0].ty = Ty::i32();
    scalar_destination.body.return_ty = Ty::i32();
    let malformed_vcs = generate_vcs(&scalar_destination);
    assert!(
        malformed_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
        )),
        "a ThreadLocalRef marker with a scalar destination must fail closed: {malformed_vcs:#?}"
    );

    for fat_pointee in [
        Ty::Slice { elem: Box::new(Ty::u8()) },
        Ty::Str,
        Ty::SymArray {
            elem: Box::new(Ty::u8()),
            len_sym: trust_types::ConstLen { index: 0, name: "N".into() },
        },
        Ty::Dynamic { trait_name: "test::Trait".into() },
    ] {
        for fat_destination in [
            Ty::Ref { mutable: false, inner: Box::new(fat_pointee.clone()) },
            Ty::RawPtr { mutable: false, pointee: Box::new(fat_pointee.clone()) },
        ] {
            let mut fat_pointer_destination = func.clone();
            fat_pointer_destination.body.locals[0].ty = fat_destination.clone();
            fat_pointer_destination.body.return_ty = fat_destination;
            let malformed_vcs = generate_vcs(&fat_pointer_destination);
            assert!(
                malformed_vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
                )),
                "a fat-pointer ThreadLocalRef destination must fail closed: {malformed_vcs:#?}"
            );
        }
    }

    let mut malformed_detail = func.clone();
    let Statement::Assign { rvalue, .. } = &mut malformed_detail.body.blocks[0].stmts[0] else {
        panic!("ThreadLocalRef fixture assignment disappeared");
    };
    let Rvalue::Unsupported { detail, .. } = rvalue else {
        panic!("ThreadLocalRef fixture marker disappeared");
    };
    *detail = "unbound TLS marker".to_string();
    let malformed_vcs = generate_vcs(&malformed_detail);
    assert!(
        malformed_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
        )),
        "a ThreadLocalRef marker without a compiler-shaped symbol must fail closed: {malformed_vcs:#?}"
    );
}

#[test]
fn symbolic_array_pointer_remains_thin_outside_tls_native_model() {
    let pointee = Ty::SymArray {
        elem: Box::new(Ty::u8()),
        len_sym: trust_types::ConstLen { index: 0, name: "N".into() },
    };
    for pointer in [
        Ty::Ref { mutable: false, inner: Box::new(pointee.clone()) },
        Ty::RawPtr { mutable: false, pointee: Box::new(pointee.clone()) },
    ] {
        assert!(
            crate::is_thin_pointer_ty(&pointer),
            "a pointer to sized [T; N] must remain thin in the general layout classifier"
        );
    }
}

#[test]
fn test_ptr_to_int_cast_is_modeled_not_fail_closed() {
    // pointer->int `as` casts are now ACCEPTED, not refused as UnsupportedMir. Exposing
    // a pointer's address yields an arbitrary integer: the dest is left UNCONSTRAINED (no
    // value-fact), so any derived null/alignment obligation stays soundly caught and
    // nothing is falsely proved. Accepting it stops this one cast from poisoning the whole
    // function's obligations (e.g. its arithmetic-overflow safety VCs) into Unsupported.
    let vcs = generate_vcs(&unsupported_cast_function(
        "ptr_to_int_cast",
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) },
        Ty::usize(),
    ));
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast" && detail.contains("unsupported cast")
        )),
        "ptr->int cast must be modeled as unconstrained, not a fail-closed UnsupportedMir VC: {vcs:?}"
    );
}

#[test]
fn test_float_to_int_cast_is_modeled_not_fail_closed() {
    // float `as` casts are now modeled as an unconstrained fresh value, not
    // refused as UnsupportedMir — sound (the value is never asserted, so
    // float-value-dependent obligations stay `unknown`, never falsely proved),
    // and it stops a float cast from wedging the whole function at Unsupported.
    // A genuinely-unsupported cast (ptr->int, above) still fails closed.
    let vcs = generate_vcs(&unsupported_cast_function(
        "float_to_int_cast",
        Ty::Float { width: 64 },
        Ty::i32(),
    ));
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast" && detail.contains("unsupported cast")
        )),
        "float->int cast must be modeled as unconstrained, not a fail-closed UnsupportedMir VC: {vcs:?}"
    );
}

#[test]
fn test_unsupported_mir_operand_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_operand".to_string(),
        def_path: "test::unsupported_operand".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Unsupported {
                        kind: "ConstValue::Ty".to_string(),
                        detail: "unsupported constant kind".to_string(),
                    }),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_unsupported_type_in_local_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_local_ty".to_string(),
        def_path: "test::unsupported_local_ty".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Unsupported {
                        kind: "TyKind::Alias".to_string(),
                        detail: "alias type was not normalized".to_string(),
                    },
                    name: Some("x".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_unsupported_type_in_projection_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_projection_ty".to_string(),
        def_path: "test::unsupported_projection_ty".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 0,
                        projections: vec![trust_types::Projection::OpaqueCast(Ty::Unsupported {
                            kind: "TyKind::Opaque".to_string(),
                            detail: "opaque type was not normalized".to_string(),
                        })],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_project_ty_array_subslice_preserves_fixed_length() {
    let source_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 6 };

    assert_eq!(
        project_ty(
            source_ty,
            &trust_types::Projection::Subslice { from: 1, to: 4, from_end: false },
        ),
        Some(Ty::Array { elem: Box::new(Ty::i32()), len: 3 })
    );
}

#[test]
fn test_project_ty_slice_subslice_preserves_slice_metadata_shape() {
    let source_ty = Ty::Slice { elem: Box::new(Ty::u8()) };

    assert_eq!(
        project_ty(
            source_ty.clone(),
            &trust_types::Projection::Subslice { from: 1, to: 2, from_end: true },
        ),
        Some(source_ty)
    );
}

fn tagged_adt_with_field(field_name: &str, field_ty: Ty) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Tagged".to_string(),
        fields: vec![(field_name.to_string(), field_ty), ("payload".to_string(), Ty::i32())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn set_discriminant_function(name: &str, local_ty: Ty, variant_index: usize) -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: local_ty, name: Some("e".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::SetDiscriminant { place: Place::local(1), variant_index }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_set_discriminant_on_explicit_tagged_adt_is_modeled() {
    let func = set_discriminant_function(
        "tagged_set_discriminant",
        tagged_adt_with_field("tag", Ty::u32()),
        2,
    );

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "StatementKind::SetDiscriminant"
            )
        }),
        "simple tagged ADT SetDiscriminant must not block vcgen"
    );

    let defs = crate::generate::set_discriminant_definitions(&func, &Place::local(1), 2)
        .expect("explicit tagged ADT should produce discriminant definitions");
    assert!(defs.contains(&Formula::Eq(
        Box::new(Formula::Var("e.0".to_string(), Sort::Int)),
        Box::new(Formula::Int(2)),
    )));
    assert!(defs.contains(&Formula::Eq(
        Box::new(Formula::Var(crate::discriminant_formula_var_name("e"), Sort::Int)),
        Box::new(Formula::Int(2)),
    )));
}

#[test]
fn generated_discriminant_definition_cannot_alias_source_scalar() {
    let mut func = set_discriminant_function(
        "tagged_discriminant_namespace",
        tagged_adt_with_field("tag", Ty::u32()),
        1,
    );
    // `discr_e` is a legal source binding and was the old generated spelling.
    func.body.locals.push(LocalDecl { index: 2, ty: Ty::i32(), name: Some("discr_e".into()) });
    func.body.arg_count = 2;

    let mut conjuncts = crate::generate::set_discriminant_definitions(&func, &Place::local(1), 1)
        .expect("explicit tagged ADT should produce discriminant definitions");
    conjuncts.push(Formula::Eq(
        Box::new(Formula::Var(crate::place_to_var_name(&func, &Place::local(2)), Sort::Int)),
        Box::new(Formula::Int(0)),
    ));
    let vars = Formula::And(conjuncts).free_variables();

    assert!(vars.contains("discr_e"));
    assert!(vars.contains(&crate::discriminant_formula_var_name("e")));
    assert_ne!(crate::discriminant_formula_var_name("e"), "discr_e");
}

#[test]
fn test_set_discriminant_without_explicit_tag_fails_closed() {
    let func = set_discriminant_function(
        "untagged_set_discriminant",
        Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Untagged".to_string(),
            fields: vec![("payload".to_string(), Ty::i32())],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, },
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "StatementKind::SetDiscriminant"
                    && detail.contains("no explicit discriminant/tag field")
        )
    }));
}

#[test]
fn test_set_discriminant_bool_tag_out_of_range_fails_closed() {
    let func = set_discriminant_function(
        "bool_tag_set_discriminant",
        tagged_adt_with_field("discriminant", Ty::Bool),
        2,
    );

    let vcs = generate_vcs(&func);
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "StatementKind::SetDiscriminant"
                    && detail.contains("does not fit bool")
        )
    }));
}

#[test]
fn test_deinit_stale_internal_compatibility_variant_fails_closed() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "deinit_stale_internal".to_string(),
        def_path: "test::deinit_stale_internal".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Deinit { place: Place::local(0) }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "Statement::Deinit"
                    && detail.contains("not present in current rustc StatementKind")
        )
    }));
    assert_unsupported_mir_unknown(func);
}

#[test]
fn test_safe_retag_statement_is_metadata_noop() {
    let func = VerifiableFunction {
        name: "safe_retag_stmt".to_string(),
        def_path: "test::safe_retag_stmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) },
                    name: Some("x".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Retag { place: Place::local(1) }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "retag without raw-pointer unsafe surface is metadata for vcgen"
    );
}

#[test]
fn test_retag_with_raw_pointer_surface_fails_closed() {
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "raw_retag_stmt".to_string(),
        def_path: "test::raw_retag_stmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) },
                    name: Some("p".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Retag { place: Place::local(1) }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_sparse_local_type_resolution_uses_decl_index() {
    let func = VerifiableFunction {
        name: "sparse_locals".to_string(),
        def_path: "test::sparse_locals".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert_eq!(operand_ty(&func, &Operand::Copy(Place::local(2))), Some(Ty::Bool));
}

#[test]
fn test_unsupported_mir_aggregate_kind_fails_closed() {
    let span = SourceSpan::default();
    assert_unsupported_mir_unknown(VerifiableFunction {
        name: "unsupported_aggregate".to_string(),
        def_path: "test::unsupported_aggregate".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "UnionLike".to_string(),
                            variant: 0,
                            active_field: Some(1),
                            args: None,
                        },
                        vec![Operand::Constant(ConstValue::Int(7))],
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    });
}

#[test]
fn test_closure_aggregate_mismatched_capture_count_fails_closed() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "bad_closure_aggregate".to_string(),
        def_path: "test::bad_closure_aggregate".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Closure {
                        name: "test::closure".to_string(),
                        upvars: vec![Ty::u64()],
                        call: None,
                    },
                    name: Some("closure_env".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure {
                            name: "test::closure".to_string(),
                            captures: vec![Ty::u64()],
                            call_kind: ClosureCallKind::FnOnce,
                        },
                        vec![],
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(
        generate_vcs(&func).iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AggregateKind::Closure" && detail.contains("capture count")
        )),
        "malformed closure construction must fail closed"
    );
}

// Trust: M6 rung 7 probes — the closure-extraction gap fix (`trust-mir-extract`
// convert.rs, `AggregateKind::Closure` capture conversion now shares the
// enclosing body's `typing_env` with local-decl conversion) only widens
// ACCEPTANCE of closure aggregates whose declared capture types genuinely
// match their operand types. These three probes pin the safety boundary that
// widening must not cross: (1) a genuine capture TYPE mismatch (not just a
// count mismatch) still fails closed, (2) a write through a captured `&mut`
// upvar is still an ordinary tracked write (never silently exempted), and (3)
// the closure's declared `name` has no power to bypass the mismatch check —
// a "wrong body" claim cannot talk its way past capture/operand consistency.

#[test]
fn test_closure_aggregate_mismatched_capture_type_fails_closed() {
    // Same shape as `test_closure_aggregate_mismatched_capture_count_fails_closed`
    // (count matches: 1 capture, 1 operand) but the declared capture type
    // (`u64`) does not match the operand's actual resolved type (`Bool`) — the
    // exact failure MODE this fix's `convert.rs` change eliminates when both
    // sides are extracted consistently, but which must still be caught and
    // rejected when they are genuinely, honestly different types (e.g. a real
    // extraction bug, not a `typing_env` artifact).
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "bad_closure_aggregate_type".to_string(),
        def_path: "test::bad_closure_aggregate_type".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Closure {
                        name: "test::closure".to_string(),
                        upvars: vec![Ty::u64()],
                        call: None,
                    },
                    name: Some("closure_env".into()),
                },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("wrong_ty_capture".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure {
                            name: "test::closure".to_string(),
                            captures: vec![Ty::u64()],
                            call_kind: ClosureCallKind::FnOnce,
                        },
                        vec![Operand::Copy(Place::local(2))],
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(
        generate_vcs(&func).iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AggregateKind::Closure" && detail.contains("capture 0 type")
        )),
        "a genuine capture/operand TYPE mismatch (not merely a count mismatch) must fail closed"
    );
}

#[test]
fn test_closure_capture_by_mut_ref_write_through_upvar_is_a_captured_write() {
    // Models the inlined body of a capture-light `FnMut` closure over `&mut
    // i32` — `_2: i32 = 5; _3: &mut i32 = &mut _2; _4 = Closure { captures:
    // [_3] }; *_4.0 = _1;` (the last statement is the write an inlined `|x|
    // *captured = x` body compiles to: `Field(0)` selects the closure's first
    // upvar, `Deref` writes through it). Two things must both hold: the
    // closure aggregate itself is accepted (capture types match — this fix's
    // own widened-acceptance path), AND the write through the
    // Field-then-Deref projection into the closure env is classified
    // `WriteEffect::Captured` by the EXHAUSTIVE `Statement::write_effect`
    // oracle the version/staleness pass relies on for soundness — i.e.
    // nothing about accepting the closure aggregate construction exempts a
    // later write through its captured mutable upvar from ordinary tracked-write
    // semantics. A silently-untracked write here would let a stale fact about
    // `_2`'s pre-capture value survive past a real mutation — the "upvar
    // mutation" false-accept this probe rules out.
    let span = SourceSpan::default();
    let mut_ref_ty = Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) };
    let func = VerifiableFunction {
        name: "mutate_through_captured_upvar".to_string(),
        def_path: "test::mutate_through_captured_upvar".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("captured".into()) },
                LocalDecl { index: 3, ty: mut_ref_ty.clone(), name: None },
                LocalDecl {
                    index: 4,
                    ty: Ty::Closure {
                        name: "test::closure".to_string(),
                        upvars: vec![mut_ref_ty.clone()],
                        call: None,
                    },
                    name: Some("closure_env".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Closure {
                                name: "test::closure".to_string(),
                                captures: vec![mut_ref_ty],
                                call_kind: ClosureCallKind::FnMut,
                            },
                            vec![Operand::Move(Place::local(3))],
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place {
                            local: 4,
                            projections: vec![Projection::Field(0), Projection::Deref],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "AggregateKind::Closure")
        ),
        "a capture-light &mut-upvar FnMut closure aggregate must be accepted: {vcs:?}"
    );
    let write_through_upvar = &func.body.blocks[0].stmts[3];
    assert_eq!(
        write_through_upvar.write_effect(),
        trust_types::WriteEffect::Captured,
        "a write through a closure-captured &mut upvar's Field-then-Deref projection \
         must be an ordinary tracked write, never silently exempted"
    );
}

#[test]
fn test_closure_aggregate_capture_check_ignores_declared_name() {
    // The closure's declared `name` (its claimed body def_path) must have NO
    // power over the accept/reject decision: a "wrong body" claim cannot talk
    // its way past the capture/operand consistency check by any choice of
    // name (garbage, empty, or a real-looking but unrelated def_path) —
    // consistent with `unsupported_aggregate_kind`'s current architecture,
    // where `name` is threaded into the diagnostic message only and never
    // consulted by `closure_aggregate_support_error`'s own comparison. This is
    // the current, narrow answer to "wrong-body-claim must be rejected": there
    // is no name-keyed lookup yet for a wrong claim to exploit, and this test
    // pins that a future change cannot accidentally start trusting `name` as a
    // bypass without a corresponding, deliberate safety review.
    let make_func = |name: &str, captures: Vec<Ty>, operands: Vec<Operand>| VerifiableFunction {
        name: "probe".to_string(),
        def_path: "test::probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Closure { name: name.to_string(), upvars: vec![Ty::u64()], call: None },
                    name: Some("closure_env".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("capture".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure {
                            name: name.to_string(),
                            captures,
                            call_kind: ClosureCallKind::FnOnce,
                        },
                        operands,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let is_closure_unsupported = |vcs: &[VerificationCondition]| {
        vcs.iter()
            .any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "AggregateKind::Closure"))
    };

    // A garbage/empty name does not let a genuinely mismatched capture type
    // sneak past the check — still rejected.
    for bogus_name in ["", "not::a::real::path", "<garbage>::{closure#99}"] {
        let mismatched =
            make_func(bogus_name, vec![Ty::u64()], vec![Operand::Copy(Place::local(0))]);
        assert!(
            is_closure_unsupported(&generate_vcs(&mismatched)),
            "name {bogus_name:?} must not bypass a genuine capture/operand type mismatch"
        );
    }

    // Symmetrically, a garbage name does not cause a FALSE reject when the
    // capture types genuinely match — `name` is inert on the accept path too.
    let matched =
        make_func("<garbage>::{closure#99}", vec![Ty::u64()], vec![Operand::Copy(Place::local(2))]);
    assert!(
        !is_closure_unsupported(&generate_vcs(&matched)),
        "a bogus name must not cause a false reject of an otherwise-consistent closure aggregate"
    );
}

#[test]
fn test_thin_raw_ptr_aggregate_does_not_emit_unsupported_mir() {
    let span = SourceSpan::default();
    let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) };
    let func = VerifiableFunction {
        name: "thin_raw_ptr_aggregate".to_string(),
        def_path: "test::thin_raw_ptr_aggregate".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: ptr_ty.clone(), name: Some("data".into()) },
                LocalDecl { index: 2, ty: ptr_ty.clone(), name: Some("out".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::RawPtr { pointee_ty: Ty::i32(), mutable: false },
                        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Unit)],
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "thin raw pointer aggregate with unit metadata is modeled as the data pointer"
    );
}

#[test]
fn test_fat_raw_ptr_aggregate_fails_closed() {
    let span = SourceSpan::default();
    let data_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let slice_ptr_ty =
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let func = VerifiableFunction {
        name: "fat_raw_ptr_aggregate".to_string(),
        def_path: "test::fat_raw_ptr_aggregate".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: slice_ptr_ty, name: Some("out".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                            mutable: false,
                        },
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(4, 64)),
                        ],
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AggregateKind::RawPtr" && detail.contains("fat-pointer metadata")
        )
    }));
}

#[test]
fn test_float_bits_zero_divisor_emits_no_obligation() {
    // Trust §9: float division is TOTAL/defined (`a / 0.0` → ±inf/NaN, never
    // traps). It is not a safety violation, so — like an int→int cast — it emits
    // NO obligation. (Was: asserted a `FloatDivisionByZero` VC, which rejected
    // valid Rust.)
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "float_bits_divzero".to_string(),
        def_path: "test::float_bits_divzero".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: None },
                LocalDecl { index: 1, ty: Ty::Float { width: 32 }, name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::FloatBits { bits: 0, width: 32 }),
                    ),
                    span,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Float { width: 32 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero)),
        "float division is defined (±inf/NaN) — no FloatDivisionByZero obligation \
         may be emitted; got {:?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "and it must not fall back to integer DivisionByZero either"
    );
}

#[test]
fn test_generate_vcs_skips_rustc_const_false_divzero_assert() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: None },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Move(Place::field(4, 0))),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Constant(ConstValue::Uint(2, 64)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(5)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(2),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Move(Place::local(3)),
                            Operand::Constant(ConstValue::Uint(2, 64)),
                        ),
                        span,
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "rustc's constant-false `2 == 0` divzero assert must not produce a VC: {vcs:?}"
    );
}

#[test]
fn test_const_false_divzero_assert_does_not_suppress_variable_divisor_in_target() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "mixed_divisors".to_string(),
        def_path: "test::mixed_divisors".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Constant(ConstValue::Uint(2, 64)),
                            Operand::Constant(ConstValue::Uint(0, 64)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(3)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(
        div_vcs.len(),
        1,
        "const-false `2 == 0` assert must not suppress real target-block `x / y` VC: {vcs:?}"
    );
}

#[test]
fn test_division_vc_uses_only_prior_same_block_defs() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "reassigned_divisor".to_string(),
        def_path: "test::reassigned_divisor".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("variable divisor should emit a DivisionByZero VC");

    assert!(
        contains_var_eq_int_formula(&div_vc.formula, "y", 0),
        "div VC must retain the divisor-zero witness, got {:?}",
        div_vc.formula
    );
    assert!(
        !contains_var_eq_int_formula(&div_vc.formula, "y", 1),
        "later same-block assignment must not contradict an earlier div VC: {:?}",
        div_vc.formula
    );
}

#[test]
fn test_division_vc_kills_overwritten_prior_same_block_defs() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "overwritten_divisor".to_string(),
        def_path: "test::overwritten_divisor".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("input".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("d".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("variable divisor should emit a DivisionByZero VC");

    assert!(
        contains_var_eq_int_formula(&div_vc.formula, "d", 0),
        "div VC must retain the divisor-zero witness, got {:?}",
        div_vc.formula
    );
    assert!(
        !contains_var_eq_int_formula(&div_vc.formula, "d", 1),
        "overwritten prior assignment must not contradict a later div VC: {:?}",
        div_vc.formula
    );
}

#[test]
fn test_const_false_assert_skip_does_not_use_stale_condition_assignment() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "stale_condition".to_string(),
        def_path: "test::stale_condition".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("y".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Constant(ConstValue::Uint(2, 64)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(0)),
                            ),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span.clone(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "latest nonconstant condition assignment must keep the assert VC live: {vcs:?}"
    );
}

#[test]
fn test_const_false_assert_skip_respects_copied_condition_time() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "copied_condition_time".to_string(),
        def_path: "test::copied_condition_time".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span.clone(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "source-local reassignment after copying the condition must not suppress the assert VC: {vcs:?}"
    );
}

#[test]
fn test_division_vc_carries_same_block_defs_for_temp_divisor() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "div_with_temp".to_string(),
        def_path: "test::div_with_temp".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("tmp".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("temp divisor should still emit a DivisionByZero VC");

    assert!(
        contains_eq_int_formula(&div_vc.formula, 1),
        "same-block temp definitions must be conjoined into the Div VC, got {:?}",
        div_vc.formula
    );
}

#[test]
fn test_narrowing_temp_cast_is_defined_no_overflow_vc() {
    // Drop-in (owner decision 2026-07-06): `tmp = 300; ret = tmp as u8` — a
    // truncating cast of a constant — is DEFINED (`300 as u8 == 44`), so it emits NO
    // CastOverflow obligation and compiles. (Previously this asserted the cast VC
    // carried the `tmp == 300` block-def; that VC no longer exists.)
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "cast_with_temp".to_string(),
        def_path: "test::cast_with_temp".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("tmp".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(300))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u8()),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })),
        "`tmp as u8` is a defined truncating cast and must NOT emit a CastOverflow \
         obligation, got {vcs:?}"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })),
        "a defined truncating cast must not fail closed as unsupported, got {vcs:?}"
    );
}

fn contains_eq_int_formula(f: &Formula, value: i128) -> bool {
    match f {
        Formula::Eq(lhs, rhs) => matches!(
            (&**lhs, &**rhs),
            (Formula::Var(_, _), Formula::Int(v)) | (Formula::Int(v), Formula::Var(_, _))
                if *v == value
        ),
        Formula::And(clauses) | Formula::Or(clauses) => {
            clauses.iter().any(|clause| contains_eq_int_formula(clause, value))
        }
        Formula::Not(inner) => contains_eq_int_formula(inner, value),
        Formula::Implies(lhs, rhs) => {
            contains_eq_int_formula(lhs, value) || contains_eq_int_formula(rhs, value)
        }
        _ => false,
    }
}

/// The base place name of a (possibly S2c-versioned) variable: `y#s0_1` → `y`.
/// The `#token` is a consistent-renaming encoding detail; dataflow-presence tests
/// assert the fact exists, not which program-point version carries it.
fn vbase(var: &str) -> &str {
    var.split('#').next().unwrap_or(var)
}

/// Strip every `#token` version suffix from a formula's variable names, so
/// structural/equality assertions test semantic dataflow content rather than the
/// S2c versioning encoding.
fn strip_versions(f: &Formula) -> Formula {
    f.clone().map(&mut |node| match node {
        Formula::Var(name, sort) if name.contains('#') => {
            Formula::Var(vbase(&name).to_string(), sort)
        }
        other => other,
    })
}

fn contains_var_eq_int_formula(f: &Formula, name: &str, value: i128) -> bool {
    match f {
        Formula::Eq(lhs, rhs) => matches!(
            (&**lhs, &**rhs),
            (Formula::Var(var, _), Formula::Int(v)) | (Formula::Int(v), Formula::Var(var, _))
                if vbase(var) == name && *v == value
        ),
        Formula::And(clauses) | Formula::Or(clauses) => {
            clauses.iter().any(|clause| contains_var_eq_int_formula(clause, name, value))
        }
        Formula::Not(inner) => contains_var_eq_int_formula(inner, name, value),
        Formula::Implies(lhs, rhs) => {
            contains_var_eq_int_formula(lhs, name, value)
                || contains_var_eq_int_formula(rhs, name, value)
        }
        _ => false,
    }
}

#[test]
fn test_operand_ty_resolution() {
    let func = midpoint_function();

    assert_eq!(operand_ty(&func, &Operand::Copy(Place::local(1))), Some(Ty::usize()));
    assert_eq!(operand_ty(&func, &Operand::Copy(Place::field(3, 1))), Some(Ty::Bool));
    assert_eq!(operand_ty(&func, &Operand::Copy(Place::field(3, 0))), Some(Ty::usize()));
    assert_eq!(
        operand_ty(&func, &Operand::Constant(ConstValue::Uint(2, 64))),
        Some(Ty::Int { width: 64, signed: false })
    );
}

#[test]
fn test_place_to_var_name() {
    let func = midpoint_function();

    assert_eq!(place_to_var_name(&func, &Place::local(1)), "a");
    assert_eq!(place_to_var_name(&func, &Place::local(2)), "b");
    assert_eq!(place_to_var_name(&func, &Place::local(0)), "_0");
    assert_eq!(place_to_var_name(&func, &Place::field(3, 1)), "_3.1");
}

#[test]
fn test_place_to_var_name_resolves_unique_explicit_indices_in_sparse_reordered_tables() {
    // `place_to_var_name` is a public standalone helper, so it must resolve the
    // Trust-IR local ID rather than accidentally treating it as a Vec offset.
    // Proof entry points reject this non-canonical table, but direct consumers
    // still need collision-safe, deterministic names.
    let mut func = midpoint_function();
    func.body.locals.swap(1, 2);
    func.body
        .locals
        .iter_mut()
        .find(|decl| decl.index == 2)
        .expect("local 2")
        .index = 7;

    assert_eq!(place_to_var_name(&func, &Place::local(1)), "a");
    assert_eq!(place_to_var_name(&func, &Place::local(7)), "b");
    assert_eq!(place_to_var_name(&func, &Place::local(2)), "_2");
}

// Trust: Tests for verification level filtering.

/// Helper: build a VC with the given kind and function name.
fn make_vc(kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "test_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn test_filter_vcs_by_level_l0_keeps_only_safety() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L0Safety);
    assert_eq!(filtered.len(), 2, "L0 should keep only safety VCs");
    assert_eq!(filtered[0].kind.proof_level(), ProofLevel::L0Safety);
    assert_eq!(filtered[1].kind.proof_level(), ProofLevel::L0Safety);
}

#[test]
fn test_filter_vcs_by_level_l1_keeps_safety_and_functional() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::Precondition { callee: "foo".to_string() }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L1Functional);
    assert_eq!(filtered.len(), 3, "L1 should keep safety + functional VCs");
    for vc in &filtered {
        assert!(vc.kind.proof_level() <= ProofLevel::L1Functional, "all VCs should be at most L1");
    }
}

#[test]
fn test_filter_vcs_by_level_l2_keeps_all() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::Temporal { property: "liveness".to_string(), machine: None }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L2Domain);
    assert_eq!(filtered.len(), 4, "L2 should keep all VCs");
}

#[test]
fn test_filter_vcs_by_level_empty_input() {
    let filtered = filter_vcs_by_level(vec![], ProofLevel::L0Safety);
    assert!(filtered.is_empty(), "filtering empty vec should return empty vec");
}

#[test]
fn test_proof_level_ordering() {
    assert!(ProofLevel::L0Safety < ProofLevel::L1Functional);
    assert!(ProofLevel::L1Functional < ProofLevel::L2Domain);
    assert!(ProofLevel::L0Safety < ProofLevel::L2Domain);
}

// Guard condition extraction and VC threading tests.

/// Build a function with SwitchInt branching into blocks with arithmetic.
///
/// ```
/// fn guarded_div(flag: bool, x: u32, y: u32) -> u32 {
///     if flag {        // SwitchInt on _1 (flag)
///         x / y        // bb1: div by zero VC should have guard: flag == 1
///     } else {
///         0            // bb2: no VCs
///     }
/// }
/// ```
fn guarded_div_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "guarded_div".to_string(),
        def_path: "test::guarded_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_guarded_div_vc_has_guard_assumption() {
    // DivisionByZero VCs are again emitted by `generate_vcs`.
    // `guarded_div_function` has a `Div(a, b)` with a variable divisor `b`,
    // so exactly one DivisionByZero VC is expected.
    let func = guarded_div_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

#[test]
fn test_discover_clauses_reports_switch_int() {
    let func = guarded_div_function();
    let clauses = discover_clauses(&func);

    assert_eq!(clauses.len(), 2, "SwitchInt with 1 target + otherwise = 2 clauses");
    assert!(clauses.iter().any(|c| matches!(c.target, ClauseTarget::Block(BlockId(1)))
        && matches!(&c.guard, GuardCondition::SwitchIntMatch { value: 1, .. })));
    assert!(clauses.iter().any(|c| matches!(c.target, ClauseTarget::Block(BlockId(2)))
        && matches!(&c.guard, GuardCondition::SwitchIntOtherwise { .. })));
}

#[test]
fn test_build_path_map_shows_accumulated_guards() {
    let func = guarded_div_function();
    let path_map = build_path_map(&func);

    assert_eq!(path_map.len(), 3, "3 blocks should all be reachable");

    let bb0 = path_map.iter().find(|e| e.block == BlockId(0)).expect("bb0");
    assert!(bb0.guards.is_empty(), "entry block has no guards");

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1);
    assert!(matches!(&bb1.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 1);
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntOtherwise { .. }));
}

#[test]
fn test_discovered_clauses_json_serialization() {
    let func = guarded_div_function();
    let clauses = discover_clauses(&func);

    let json = serde_json::to_string(&clauses).expect("serialize clauses");
    let round: Vec<DiscoveredClause> = serde_json::from_str(&json).expect("deserialize clauses");
    assert_eq!(round.len(), clauses.len());
}

#[test]
fn test_path_map_json_serialization() {
    let func = guarded_div_function();
    let path_map = build_path_map(&func);

    let json = serde_json::to_string(&path_map).expect("serialize path map");
    let round: Vec<PathMapEntry> = serde_json::from_str(&json).expect("deserialize path map");
    assert_eq!(round.len(), path_map.len());
}

#[test]
fn test_midpoint_bb1_guarded_by_assert() {
    let func = midpoint_function();
    let path_map = build_path_map(&func);

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1, "bb1 should have 1 guard from the Assert");
    assert!(matches!(&bb1.guards[0], GuardCondition::AssertHolds { expected: false, .. }));
}

/// Build a function with nested guards (SwitchInt -> Assert -> block with VCs).
fn nested_guard_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "nested".to_string(),
        def_path: "test::nested".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("check".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(4)),
                        expected: true,
                        msg: AssertMessage::Custom("check must hold".into()),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 4,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_nested_guards_accumulate() {
    let func = nested_guard_function();
    let path_map = build_path_map(&func);

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 2, "bb2 should have 2 accumulated guards");
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));
    assert!(matches!(&bb2.guards[1], GuardCondition::AssertHolds { expected: true, .. }));
}

#[test]
fn test_nested_guards_in_vc_formula() {
    // DivisionByZero VCs are again emitted by `generate_vcs`.
    // `nested_guard_function` has one `Div(x, y)` with a variable divisor,
    // so exactly one DivisionByZero VC is expected.
    let func = nested_guard_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

/// Build a function with 3-way match (enum variant SwitchInt).
fn match_exhaustive_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "match_fn".to_string(),
        def_path: "test::match_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "Status".into(),
                        fields: vec![("discriminant".into(), Ty::u32())],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("status".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_match_exhaustive_guards() {
    let func = match_exhaustive_function();
    let clauses = discover_clauses(&func);

    assert_eq!(clauses.len(), 3);

    let path_map = build_path_map(&func);

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1);
    assert!(matches!(&bb1.guards[0], GuardCondition::SwitchIntMatch { value: 0, .. }));

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 1);
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));

    let bb3 = path_map.iter().find(|e| e.block == BlockId(3)).expect("bb3");
    assert_eq!(bb3.guards.len(), 1);
    assert!(matches!(
        &bb3.guards[0],
        GuardCondition::SwitchIntOtherwise { excluded_values, .. }
            if excluded_values == &vec![0, 1]
    ));
}

#[test]
fn test_match_div_vc_has_variant_guard() {
    // DivisionByZero VCs are again emitted by `generate_vcs`.
    // `match_exhaustive_function` has one `Div(x, y)` with a variable divisor
    // guarded by a SwitchInt match arm, so exactly one DivisionByZero VC is
    // expected.
    let func = match_exhaustive_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

// -----------------------------------------------------------------------
// Comprehensive arithmetic VC coverage tests
// -----------------------------------------------------------------------

/// Helper: build a function with a single BinOp on two variable operands.
fn make_binop_func(op: BinOp, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: format!("arith_{op:?}"),
        def_path: format!("test::arith_{op:?}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// The canonical pipeline emits direct safety VCs for operations callers still
// send to trust_vcgen. Assert-guarded checked integer operations use rustc
// Assert terminators; direct integer Add/Sub/Mul still emits solver-facing
// overflow obligations here.

#[test]
fn test_vc_coverage_add_emits_overflow_vc() {
    let func = make_binop_func(BinOp::Add, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "direct Add must emit an ArithmeticOverflow VC"
    );
}

#[test]
fn test_vc_coverage_sub_emits_overflow_vc() {
    let func = make_binop_func(BinOp::Sub, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "direct Sub must emit an ArithmeticOverflow VC"
    );
}

#[test]
fn test_vc_coverage_mul_emits_overflow_vc() {
    let func = make_binop_func(BinOp::Mul, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "direct Mul must emit an ArithmeticOverflow VC"
    );
}

#[test]
fn test_vc_coverage_div_no_divzero_vc() {
    // DivisionByZero VCs are emitted again for `Div(_, var)`.
    let func = make_binop_func(BinOp::Div, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "Div(_, var) must emit DivisionByZero VC"
    );
}

#[test]
fn test_vc_coverage_rem_no_remzero_vc() {
    // RemainderByZero VCs are emitted again for `Rem(_, var)`.
    let func = make_binop_func(BinOp::Rem, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "Rem(_, var) must emit RemainderByZero VC"
    );
}

#[test]
fn test_vc_coverage_signed_div_generates_overflow_vc() {
    // Signed `Div(_, var)` emits DivisionByZero plus the
    // `i32::MIN / -1` ArithmeticOverflow obligation.
    let func = make_binop_func(BinOp::Div, Ty::i32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "signed Div(_, var) must emit DivisionByZero VC"
    );
    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }))
        .collect();
    assert!(
        overflow_vcs.len() == 1,
        "signed Div(_, var) must emit exactly one ArithmeticOverflow VC, got {}",
        overflow_vcs.len()
    );
}

#[test]
fn test_vc_coverage_signed_rem_generates_overflow_vc() {
    // Signed `Rem(_, var)` emits RemainderByZero plus the
    // `i32::MIN % -1` ArithmeticOverflow obligation.
    let func = make_binop_func(BinOp::Rem, Ty::i32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "signed Rem(_, var) must emit RemainderByZero VC"
    );
    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Rem, .. }))
        .collect();
    assert!(
        overflow_vcs.len() == 1,
        "signed Rem(_, var) must emit exactly one ArithmeticOverflow VC, got {}",
        overflow_vcs.len()
    );
}

#[test]
fn test_vc_coverage_shl_generates_shift_overflow_vc() {
    let func = make_binop_func(BinOp::Shl, Ty::u32());
    let vcs = generate_vcs(&func);
    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .collect();
    assert!(
        shift_vcs.len() == 1,
        "Shl(_, var) must emit exactly one ShiftOverflow VC, got {}",
        shift_vcs.len()
    );
}

#[test]
fn test_vc_coverage_shr_generates_shift_overflow_vc() {
    let func = make_binop_func(BinOp::Shr, Ty::u32());
    let vcs = generate_vcs(&func);
    let shift_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shr, .. }))
        .collect();
    assert!(
        shift_vcs.len() == 1,
        "Shr(_, var) must emit exactly one ShiftOverflow VC, got {}",
        shift_vcs.len()
    );
}
/// `fn f(x: <value_ty>, n: <amt_ty|literal k>) { x <<|>> n }` — the width-edge
/// shift fixture: the shifted VALUE and the AMOUNT deliberately have different
/// types (Rust allows any integer amount type), so the emitted `amount >= W`
/// threshold must come from the VALUE's width, at full 128-bit fidelity.
fn make_shift_func(op: BinOp, value_ty: Ty, amount: ShiftAmount) -> VerifiableFunction {
    let (amt_operand, locals, arg_count) = match amount {
        ShiftAmount::Var(amt_ty) => (
            Operand::Copy(Place::local(2)),
            vec![
                LocalDecl { index: 0, ty: value_ty.clone(), name: None },
                LocalDecl { index: 1, ty: value_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: amt_ty, name: Some("n".into()) },
            ],
            2,
        ),
        ShiftAmount::Lit(k) => (
            Operand::Constant(ConstValue::Uint(k, 32)),
            vec![
                LocalDecl { index: 0, ty: value_ty.clone(), name: None },
                LocalDecl { index: 1, ty: value_ty.clone(), name: Some("x".into()) },
            ],
            1,
        ),
    };
    VerifiableFunction {
        name: format!("shift_{op:?}"),
        def_path: format!("test::shift_{op:?}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(op, Operand::Copy(Place::local(1)), amt_operand),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty: value_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

enum ShiftAmount {
    Var(Ty),
    Lit(u128),
}

/// True if `formula` contains `Ge(lhs, Int(bound))` for the given predicate on `lhs`.
fn formula_has_ge_with_bound(
    formula: &Formula,
    lhs_pred: impl Fn(&Formula) -> bool,
    bound: i128,
) -> bool {
    let mut found = false;
    formula.visit(&mut |sub| {
        if let Formula::Ge(l, r) = sub
            && lhs_pred(l)
            && matches!(r.as_ref(), Formula::Int(b) if *b == bound)
        {
            found = true;
        }
    });
    found
}

/// Trust: 128-BIT SHIFT VC WIDTH — a 128-bit shifted VALUE with a NARROWER
/// (u8) amount type emits the full, untruncated `n >= 128` threshold (the
/// amount-type-vs-operand-width mismatch edge: the bound literal 128 does not
/// even fit the amount's own u8 sort, and must NOT be clamped to it), and
/// never the fabricated-i64 `n >= 64`.
#[test]
fn test_shift_overflow_u128_value_narrow_amount_emits_threshold_128() {
    let is_n =
        |f: &Formula| matches!(f, Formula::Var(name, _) if name.split('#').next() == Some("n"));
    let func = make_shift_func(
        BinOp::Shl,
        Ty::Int { width: 128, signed: false },
        ShiftAmount::Var(Ty::Int { width: 8, signed: false }),
    );
    let vcs = generate_vcs(&func);
    let shift = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .expect("u128 << n must emit a ShiftOverflow VC");
    assert!(
        formula_has_ge_with_bound(&shift.formula, is_n, 128),
        "the u128 shift bound must be `n >= 128`; got {:?}",
        shift.formula
    );
    assert!(
        !formula_has_ge_with_bound(&shift.formula, is_n, 64),
        "the u128 shift bound must not be a truncated/fabricated `n >= 64`; got {:?}",
        shift.formula
    );
    // The VC kind carries the honest 128-bit operand type (a variable, not a
    // width-less constant — no fabrication on this path).
    let VcKind::ShiftOverflow { operand_ty, shift_ty, .. } = &shift.kind else { unreachable!() };
    assert_eq!(operand_ty, &Ty::Int { width: 128, signed: false });
    assert_eq!(shift_ty, &Ty::Int { width: 8, signed: false });
}

/// Trust: 128-BIT SHIFT VC WIDTH — an i128 value with a SIGNED amount emits the
/// full disjunction `Or([n < 0, n >= 128])` (negative amounts are UB too).
#[test]
fn test_shift_overflow_i128_value_signed_amount_emits_or_core_at_128() {
    let is_n =
        |f: &Formula| matches!(f, Formula::Var(name, _) if name.split('#').next() == Some("n"));
    let func = make_shift_func(
        BinOp::Shl,
        Ty::Int { width: 128, signed: true },
        ShiftAmount::Var(Ty::Int { width: 32, signed: true }),
    );
    let vcs = generate_vcs(&func);
    let shift = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .expect("i128 << n must emit a ShiftOverflow VC");
    let mut has_or_core = false;
    shift.formula.visit(&mut |sub| {
        if let Formula::Or(v) = sub
            && v.iter().any(|x| {
                matches!(x, Formula::Lt(l, r)
                if is_n(l) && matches!(r.as_ref(), Formula::Int(0)))
            })
            && v.iter().any(|x| {
                matches!(x, Formula::Ge(l, r)
                if is_n(l) && matches!(r.as_ref(), Formula::Int(128)))
            })
        {
            has_or_core = true;
        }
    });
    assert!(
        has_or_core,
        "signed-amount i128 shift must emit `Or([n < 0, n >= 128])`; got {:?}",
        shift.formula
    );
}

/// Trust: 128-BIT SHIFT VC WIDTH — LITERAL amounts at the 127/128/129 boundary
/// on a u128 value each emit the closed core `Ge(Int(k), Int(128))`: 127 is the
/// last safe amount (refutable core), 128/129 are real UB (satisfiable core) —
/// the emitter must state the honest condition for all three, never truncate
/// the threshold or drop the VC.
#[test]
fn test_shift_overflow_u128_literal_amounts_at_the_128_boundary() {
    for k in [127u128, 128, 129] {
        let func =
            make_shift_func(BinOp::Shr, Ty::Int { width: 128, signed: false }, ShiftAmount::Lit(k));
        let vcs = generate_vcs(&func);
        let shift = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
            .unwrap_or_else(|| panic!("u128 >> {k} must emit a ShiftOverflow VC"));
        assert!(
            formula_has_ge_with_bound(
                &shift.formula,
                |l| matches!(l, Formula::Int(v) if *v == i128::try_from(k).unwrap()),
                128,
            ),
            "u128 >> {k} must emit the closed core `Ge(Int({k}), Int(128))`; got {:?}",
            shift.formula
        );
    }
}

#[test]
fn test_vc_coverage_neg_generates_negation_overflow() {
    // Build a function with UnaryOp::Neg on a signed variable
    let func = VerifiableFunction {
        name: "arith_neg".to_string(),
        def_path: "test::arith_neg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })),
        "Neg on signed integers must generate NegationOverflow VC"
    );
}

#[test]
fn test_vc_coverage_bitwise_ops_no_vcs() {
    // BitAnd, BitOr, BitXor should NOT generate any arithmetic VCs
    for op in [BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        let arith_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::ArithmeticOverflow { .. }
                        | VcKind::DivisionByZero
                        | VcKind::RemainderByZero
                        | VcKind::ShiftOverflow { .. }
                        | VcKind::NegationOverflow { .. }
                )
            })
            .collect();
        assert!(
            arith_vcs.is_empty(),
            "Bitwise op {op:?} should not generate any arithmetic VCs, got {}",
            arith_vcs.len()
        );
    }
}

#[test]
fn test_vc_coverage_comparison_ops_no_vcs() {
    // Eq, Ne, Lt, Le, Gt, Ge should NOT generate any arithmetic VCs
    for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        let arith_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::ArithmeticOverflow { .. }
                        | VcKind::DivisionByZero
                        | VcKind::RemainderByZero
                        | VcKind::ShiftOverflow { .. }
                        | VcKind::NegationOverflow { .. }
                )
            })
            .collect();
        assert!(
            arith_vcs.is_empty(),
            "Comparison op {op:?} should not generate any arithmetic VCs, got {}",
            arith_vcs.len()
        );
    }
}

// Trust: Tests for #409 (operand wildcard) and #406 (float constants).

#[test]
fn test_operand_to_formula_float_produces_bitvec_constant() {
    // #406: Float constants should lower to their IEEE-754 bit pattern.
    let func = midpoint_function();
    let float_op = Operand::Constant(ConstValue::Float(3.125));
    let formula = operand_to_formula(&func, &float_op);
    match formula {
        Formula::BitVec { value, width } => {
            assert_eq!(width, 64, "float constants should lower to 64-bit bitvectors");
            assert_eq!(
                value,
                i128::from(3.125f64.to_bits()),
                "float constants should preserve their IEEE-754 bit pattern"
            );
        }
        other => panic!("expected Formula::BitVec for float constant, got: {other:?}"),
    }
}

#[test]
fn test_operand_ty_float_constant() {
    // #406: Float constant type should resolve to Float, not Unit.
    let func = midpoint_function();
    let float_op = Operand::Constant(ConstValue::Float(2.875));
    let ty = operand_ty(&func, &float_op);
    assert_eq!(ty, Some(Ty::Float { width: 64 }), "float constant should have Float type");
}

#[test]
fn test_operand_to_formula_unit_not_true() {
    // #409: Unit operand should produce Formula::Int(0), NOT Formula::Bool(true).
    // This validates that the wildcard fallback returning Bool(true) is gone.
    let func = midpoint_function();
    let unit_op = Operand::Constant(ConstValue::Unit);
    let formula = operand_to_formula(&func, &unit_op);
    assert_eq!(formula, Formula::Int(0), "Unit operand should produce Int(0), not Bool(true)");
}

#[test]
fn test_generate_vcs_with_discharge_returns_split() {
    //, #428: Verify that generate_vcs_with_discharge produces
    // both solver VCs and discharged results without panicking.
    let func = midpoint_function();
    let (solver_vcs, discharged) = generate_vcs_with_discharge(&func);

    // Total should equal what generate_vcs returns.
    let all_vcs = generate_vcs(&func);
    assert_eq!(
        solver_vcs.len() + discharged.len(),
        all_vcs.len(),
        "discharge split must preserve total VC count"
    );

    // All discharged results should be Proved.
    for (_vc, result) in &discharged {
        assert!(result.is_proved(), "discharged VCs must be Proved");
    }
}

// -----------------------------------------------------------------------
// VC generator integrity tests
// -----------------------------------------------------------------------

#[test]
fn test_float_div_by_variable_emits_no_obligation_through_pipeline() {
    // Trust §9: `a / b` on f64 with a variable divisor is defined for every b
    // (b == 0.0 → ±inf/NaN, never a trap), so the pipeline emits NO
    // division-by-zero obligation — neither float nor integer. (Was: asserted
    // one `FloatDivisionByZero` VC comparing the divisor magnitude bits.)
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_div_pipeline".to_string(),
        def_path: "test::float_div_pipeline".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero)),
        "float Div by a variable is defined — no FloatDivisionByZero obligation; \
         got {:?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "float Div must not fall back to integer DivisionByZero either"
    );
}

#[test]
fn test_float_add_generates_overflow_vc_through_pipeline() {
    // Float overflow gets a solver-facing witness obligation in the canonical pipeline.
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_add_pipeline".to_string(),
        def_path: "test::float_add_pipeline".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let float_overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::FloatOverflowToInfinity {
                    op: BinOp::Add,
                    operand_ty: Ty::Float { width: 64 }
                }
            )
        })
        .collect();
    assert!(
        float_overflow_vcs.len() == 1,
        "plain float Add must emit exactly one FloatOverflowToInfinity VC, got {}",
        float_overflow_vcs.len()
    );
    assert!(
        !matches!(float_overflow_vcs[0].formula, Formula::Bool(false)),
        "FloatOverflowToInfinity VC must carry a real witness formula"
    );
}

fn formula_contains(formula: &Formula, predicate: &impl Fn(&Formula) -> bool) -> bool {
    if predicate(formula) {
        return true;
    }
    formula.children().into_iter().any(|child| formula_contains(child, predicate))
}

fn is_float_zero_magnitude_check_for_var(formula: &Formula, name: &str) -> bool {
    matches!(
        formula,
        Formula::Eq(lhs, rhs)
            if matches!(
                &**lhs,
                Formula::BvExtract { inner, high: 62, low: 0 }
                    if matches!(&**inner, Formula::Var(var, Sort::BitVec(64)) if vbase(var) == name)
            )
                && matches!(&**rhs, Formula::BitVec { value: 0, width: 63 })
    )
}

fn is_float_gt_const_guard_for_var(formula: &Formula, name: &str) -> bool {
    matches!(
        formula,
        Formula::BvULt(lhs, rhs, 63)
            if matches!(
                &**lhs,
                Formula::BvExtract { inner, high: 62, low: 0 }
                    if matches!(&**inner, Formula::BitVec { width: 64, .. })
            )
                && matches!(
                    &**rhs,
                    Formula::BvExtract { inner, high: 62, low: 0 }
                        if matches!(&**inner, Formula::Var(var, Sort::BitVec(64)) if var == name)
                )
    )
}

/// The IEEE-754 ordering guard `FpGt(FpFromBits(Var(name)), FpFromBits(const))`
/// that the safe-path SwitchInt discriminant `name = abs.abs() > LIMIT` lowers to.
/// `name` is the abs-result temp (`abs_a`/`abs_b`), NOT the arithmetic operand.
fn is_fp_gt_const_guard_for_var(formula: &Formula, name: &str) -> bool {
    matches!(
        formula,
        Formula::FpGt(lhs, rhs)
            if matches!(
                &**lhs,
                Formula::FpFromBits { bits, .. }
                    if matches!(&**bits, Formula::Var(var, Sort::BitVec(64)) if vbase(var) == name)
            )
                && matches!(
                    &**rhs,
                    Formula::FpFromBits { bits, .. } if matches!(&**bits, Formula::BitVec { .. })
                )
    )
}

#[test]
fn test_float_div_guarded_or_not_emits_no_obligation() {
    // Trust §9: float division is defined regardless of guarding — a
    // `if y != 0.0 { x / y }` shape emits NO division-by-zero obligation, just
    // like the unguarded case, because `x / 0.0` is itself defined (±inf/NaN).
    // (Was `test_float_div_safe_path_threads_zero_guard_definition`, which
    // asserted the guard threaded into a now-unemitted FloatDivisionByZero VC.)
    let span = SourceSpan::default();
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_divide_safe".to_string(),
        def_path: "test::float_divide_safe".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("is_zero".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Float(0.0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(0.0))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter()
            .any(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero | VcKind::DivisionByZero)),
        "guarded or not, float division emits no division-by-zero obligation; got {:?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
    let _ = is_float_zero_magnitude_check_for_var; // retained: still used by float-overflow tests
}

#[test]
fn test_float_overflow_safe_path_generates_guarded_obligation() {
    let span = SourceSpan::default();
    let ty = Ty::Float { width: 64 };
    let safe_limit = ConstValue::Float(1.0e300);
    let func = VerifiableFunction {
        name: "float_add_safe".to_string(),
        def_path: "test::float_add_safe".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("a_too_large".into()) },
                LocalDecl { index: 4, ty: ty.clone(), name: Some("abs_a".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("b_too_large".into()) },
                LocalDecl { index: 6, ty: ty.clone(), name: Some("abs_b".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(safe_limit.clone()),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(6),
                        target: Some(BlockId(3)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(6)),
                            Operand::Constant(safe_limit),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(5))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(0.0))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. }))
        .expect("guarded float Add should generate a FloatOverflowToInfinity VC");

    // soundness (round-9): the float-overflow VC must model the REAL IEEE
    // overflow condition over the operands, NOT the program's own range-check
    // booleans. Previously the violation was `Or([a_too_large, b_too_large])` (the
    // program's discriminants); conjoined with the safe-path guard
    // `¬a_too_large ∧ ¬b_too_large` that made the VC a tautological contradiction,
    // always Proved regardless of whether the guard was correct (a self-referential
    // false-PROVE). The violation is now the semantic witness (same-sign ∧ both
    // magnitudes > MAX/2 ∧ both finite), so on a path whose (unmodeled, round-8)
    // float guards do not constrain the operands the VC is satisfiable ->
    // Failed/Unknown (fail-closed), never falsely Proved.
    assert!(
        !formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Or(disjuncts)
                if disjuncts.iter().any(|i| matches!(i, Formula::Var(name, Sort::Bool) if name == "a_too_large"))
                    && disjuncts.iter().any(|i| matches!(i, Formula::Var(name, Sort::Bool) if name == "b_too_large"))
        )),
        "overflow violation must NOT be the self-referential `Or([a_too_large, b_too_large])`, got {:?}",
        vc.formula
    );
    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::BvULt(_, rhs, _)
                if matches!(&**rhs, Formula::BvExtract { inner, high: 62, low: 0 }
                    if matches!(&**inner, Formula::Var(name, Sort::BitVec(64)) if name == "a"))
        )),
        "overflow VC should carry the real magnitude-threshold witness over operand `a`, got {:?}",
        vc.formula
    );
    // The safe-path SwitchInt guard is still threaded, now as the IEEE-754
    // ordering form `¬FpGt(abs_a, LIMIT) ∧ ¬FpGt(abs_b, LIMIT)` (the boolean
    // discriminants `a_too_large`/`b_too_large` resolve to their defining float
    // comparison `abs > LIMIT` via `bool_condition_definition`/`fp_compare`). This
    // is a guard PRESENCE assertion: the path is threaded so the reachable safe
    // path is preserved on the obligation.
    //
    // SOUNDNESS (the load-bearing property): this guard does NOT constrain the
    // arithmetic OPERANDS the witness ranges over. The witness is stated over the
    // raw bits of `a`/`b` (asserted above), while the guard is over `abs_a`/`abs_b`
    // — the `f64::abs()` result temps — which are FREE here (no fact ties
    // `abs_x == |x|`; `build_fp_abs_facts` is SSA-gated and skips parameter args,
    // fail-closed). So the solver may satisfy `¬FpGt(abs_a, LIMIT)` with `abs_a`
    // small while INDEPENDENTLY choosing a huge `a` that meets the witness: the VC
    // stays satisfiable -> Failed/Unknown (fail-closed), never the tautological
    // contradiction `(¬p ∧ ¬q) ∧ (p ∨ q)` of the old self-referential false-PROVE.
    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::And(conj)
                if conj.iter().any(|i| matches!(i, Formula::Not(v) if is_fp_gt_const_guard_for_var(v, "abs_a")))
                    && conj.iter().any(|i| matches!(i, Formula::Not(v) if is_fp_gt_const_guard_for_var(v, "abs_b")))
        )),
        "overflow VC should carry the safe-path float-ordering guard `¬FpGt(abs_a, LIMIT) ∧ ¬FpGt(abs_b, LIMIT)`, got {:?}",
        vc.formula
    );
    // Soundness: the threaded guard must be over the abs-result temps, NOT over the
    // arithmetic operands `a`/`b` — a guard over `a`/`b` would (with the witness
    // over the same `a`/`b`) re-create the self-referential contradiction.
    assert!(
        !formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::FpGt(lhs, _)
                if matches!(&**lhs, Formula::FpFromBits { bits, .. }
                    if matches!(&**bits, Formula::Var(name, Sort::BitVec(64)) if vbase(name) == "a" || vbase(name) == "b"))
        )),
        "the path guard must constrain the abs temps, never the witness operands `a`/`b` (would be self-referential), got {:?}",
        vc.formula
    );
    // The OLD round-8 bitvector-magnitude stand-in (`BvULt` over sign-dropped
    // magnitude bits) must NOT be how the guard is modeled — float ordering is now
    // the IEEE `fp.*` theory, not the magnitude hack.
    assert!(
        !formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Not(inner) if is_float_gt_const_guard_for_var(inner, "abs_a")
        )),
        "stale round-8 bitvector-magnitude `>` guard must NOT be modeled, got {:?}",
        vc.formula
    );
}

#[test]
fn test_float_overflow_join_does_not_use_first_path_guard_shortcut() {
    let span = SourceSpan::default();
    let ty = Ty::Float { width: 64 };
    let safe_limit = ConstValue::Float(1.0e300);
    let func = VerifiableFunction {
        name: "float_add_mixed_join".to_string(),
        def_path: "test::float_add_mixed_join".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("a_too_large".into()) },
                LocalDecl { index: 4, ty: ty.clone(), name: Some("abs_a".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("b_too_large".into()) },
                LocalDecl { index: 6, ty: ty.clone(), name: Some("abs_b".into()) },
                LocalDecl { index: 7, ty: Ty::Bool, name: Some("shortcut".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(7)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(safe_limit.clone()),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(6),
                        target: Some(BlockId(4)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(6)),
                            Operand::Constant(safe_limit),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(5))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. }))
        .expect("float Add should generate a FloatOverflowToInfinity VC");

    assert!(
        !formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Or(disjuncts)
                if disjuncts.len() == 2
                    && disjuncts.iter().any(|item| matches!(item, Formula::Var(name, Sort::Bool) if name == "a_too_large"))
                    && disjuncts.iter().any(|item| matches!(item, Formula::Var(name, Sort::Bool) if name == "b_too_large"))
        )),
        "mixed-path joins must not use a guard shortcut derived from only one incoming path: {:?}",
        vc.formula
    );
}

#[test]
fn test_begin_panic_call_generates_guarded_assertion_vc() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "panic_assertion".to_string(),
        def_path: "test::panic_assertion".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::rt::begin_panic::<&str>".to_string(),
                        args: vec![],
                        dest: Place::local(3),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("begin_panic")))
        .expect("begin_panic should generate an Assertion VC");

    assert!(
        formula_contains(&assert_vc.formula, &|node| matches!(
            node,
            Formula::Not(inner)
                if matches!(&**inner, Formula::Var(name, Sort::Bool) if name == "ok")
                    || matches!(
                        &**inner,
                        Formula::Ge(lhs, rhs)
                            if matches!(&**lhs, Formula::Var(name, Sort::Int) if name == "x")
                                && matches!(&**rhs, Formula::Int(0))
                    )
        )),
        "Assertion VC should be guarded by the false branch reaching begin_panic, got {:?}",
        assert_vc.formula
    );
}

/// Trust (T9 contract-panic): fixture — a guarded panic call whose (optional)
/// const-str message operand is `msg`. Shape mirrors
/// `test_begin_panic_call_generates_guarded_assertion_vc`.
fn contract_panic_fixture(def_path: &str, msg: Option<&str>) -> VerifiableFunction {
    let span = SourceSpan::default();
    let args = msg
        .map(|m| vec![Operand::Constant(ConstValue::Str { bytes: m.as_bytes().to_vec() })])
        .unwrap_or_default();
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
        def_path: def_path.to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::panicking::panic_fmt".to_string(),
                        args,
                        dest: Place::local(3),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn nested_query_forcing_restores_false_caller_after_true_callee() {
    let caller = VcgenContext::for_function("test::caller");
    let callee =
        VcgenContext::for_function("test::callee").with_single_writer(true).with_backing(true);

    with_vcgen_context(&caller, || {
        assert!(!single_writer_hint_for("test::caller"));
        assert!(!backing_hint_for("test::caller"));
        with_vcgen_context(&callee, || {
            assert!(single_writer_hint_for("test::callee"));
            assert!(backing_hint_for("test::callee"));
            assert!(!single_writer_hint_for("test::caller"));
            assert!(!backing_hint_for("test::caller"));
        });
        assert!(!single_writer_hint_for("test::caller"));
        assert!(!backing_hint_for("test::caller"));
    });

    assert!(!single_writer_hint_for("test::caller"));
    assert!(!backing_hint_for("test::caller"));
}

#[test]
fn nested_query_forcing_restores_true_caller_after_false_callee() {
    let caller =
        VcgenContext::for_function("test::caller").with_single_writer(true).with_backing(true);
    let callee = VcgenContext::for_function("test::callee");

    with_vcgen_context(&caller, || {
        assert!(single_writer_hint_for("test::caller"));
        assert!(backing_hint_for("test::caller"));
        with_vcgen_context(&callee, || {
            assert!(!single_writer_hint_for("test::callee"));
            assert!(!backing_hint_for("test::callee"));
            assert!(!single_writer_hint_for("test::caller"));
            assert!(!backing_hint_for("test::caller"));
        });
        assert!(single_writer_hint_for("test::caller"));
        assert!(backing_hint_for("test::caller"));
    });
}

#[test]
fn vcgen_context_rejects_single_writer_and_backing_owner_mismatch() {
    let context =
        VcgenContext::for_function("test::owner").with_single_writer(true).with_backing(true);

    with_vcgen_context(&context, || {
        assert!(single_writer_hint_for("test::owner"));
        assert!(backing_hint_for("test::owner"));
        assert!(!single_writer_hint_for("test::different_function"));
        assert!(!backing_hint_for("test::different_function"));
    });
}

#[test]
fn nested_query_forcing_restores_contract_panic_owner_and_payloads() {
    let caller = VcgenContext::for_function("test::caller")
        .with_contract_panic_annotations(vec!["caller payload".into()]);
    let callee = VcgenContext::for_function("test::callee")
        .with_contract_panic_annotations(vec!["callee payload".into()]);

    with_vcgen_context(&caller, || {
        assert_eq!(
            contract_panic_annotations_for("test::caller"),
            vec!["caller payload".to_string()]
        );
        with_vcgen_context(&callee, || {
            assert!(contract_panic_annotations_for("test::caller").is_empty());
            assert_eq!(
                contract_panic_annotations_for("test::callee"),
                vec!["callee payload".to_string()]
            );
        });
        assert_eq!(
            contract_panic_annotations_for("test::caller"),
            vec!["caller payload".to_string()]
        );
    });
}

#[test]
fn vcgen_context_restores_after_unwind() {
    let context = VcgenContext::for_function("test::panics")
        .with_single_writer(true)
        .with_backing(true)
        .with_contract_panic_annotations(vec!["payload".into()]);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_vcgen_context(&context, || panic!("synthetic nested query panic"));
    }));
    assert!(result.is_err());
    assert!(!single_writer_hint_for("test::panics"));
    assert!(!backing_hint_for("test::panics"));
    assert!(contract_panic_annotations_for("test::panics").is_empty());
}

fn callee_summary_fixture(marker: i128, certified: &str) -> CalleeSummaryContext {
    const CALLEE: &str = "test::helper";

    let mut certified_backing_structs = trust_types::fx::FxHashSet::default();
    certified_backing_structs.insert(certified.to_string());
    let mut return_bounds = trust_types::fx::FxHashMap::default();
    return_bounds.insert(CALLEE.to_string(), marker);
    let mut return_lower_bounds = trust_types::fx::FxHashMap::default();
    return_lower_bounds.insert(CALLEE.to_string(), -marker);
    let mut return_const_sets = trust_types::fx::FxHashMap::default();
    return_const_sets.insert(CALLEE.to_string(), vec![marker]);
    let mut return_disc_summaries = trust_types::fx::FxHashMap::default();
    return_disc_summaries.insert(
        CALLEE.to_string(),
        ReturnDiscSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["value".into()],
            cases: ReturnDiscCases::Unconditional { tag: marker },
        },
    );
    let mut setter_summaries = trust_types::fx::FxHashMap::default();
    setter_summaries.insert(
        CALLEE.to_string(),
        SetterSummary {
            param_count: 2,
            ptr_param: 1,
            pointee: (64, true),
            src: SetterSrc::Const(marker),
        },
    );
    let mut return_bool_preds = trust_types::fx::FxHashMap::default();
    return_bool_preds.insert(
        CALLEE.to_string(),
        ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["value".into()],
            pred_param: 1,
            pred_field: None,
            kind: ReturnBoolPredKind::Iff,
            pred_tag: marker,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );

    CalleeSummaryContext::default()
        .with_certified_backing_structs(certified_backing_structs)
        .with_return_bounds(return_bounds)
        .with_return_lower_bounds(return_lower_bounds)
        .with_return_const_sets(return_const_sets)
        .with_return_disc_summaries(return_disc_summaries)
        .with_setter_summaries(setter_summaries)
        .with_return_bool_preds(return_bool_preds)
}

fn assert_callee_summary_marker(marker: i128) {
    const CALLEE: &str = "test::helper";
    assert_eq!(callee_return_upper_bound(CALLEE), Some(marker));
    assert_eq!(callee_return_lower_bound(CALLEE), Some(-marker));
    assert_eq!(callee_return_const_set(CALLEE), Some(vec![marker]));
    assert!(matches!(
        callee_return_disc_summary(CALLEE),
        Some(ReturnDiscSummary {
            cases: ReturnDiscCases::Unconditional { tag },
            ..
        }) if tag == marker
    ));
    assert!(matches!(
        callee_setter_summary(CALLEE),
        Some(SetterSummary { src: SetterSrc::Const(value), .. }) if value == marker
    ));
    assert_eq!(callee_return_bool_pred(CALLEE).unwrap().pred_tag, marker);
}

fn assert_no_callee_summaries() {
    const CALLEE: &str = "test::helper";
    assert!(!is_backing_struct_certified("CallerBacking"));
    assert!(!is_backing_struct_certified("NestedBacking"));
    assert!(callee_return_upper_bound(CALLEE).is_none());
    assert!(callee_return_lower_bound(CALLEE).is_none());
    assert!(callee_return_const_set(CALLEE).is_none());
    assert!(callee_return_disc_summary(CALLEE).is_none());
    assert!(callee_setter_summary(CALLEE).is_none());
    assert!(callee_return_bool_pred(CALLEE).is_none());
}

#[test]
fn callee_summary_context_restores_nested_default_and_unwound_callers() {
    assert_no_callee_summaries();
    let caller = VcgenContext::for_function("test::caller")
        .with_callee_summaries(callee_summary_fixture(1, "CallerBacking"));

    with_vcgen_context(&caller, || {
        assert!(is_backing_struct_certified("CallerBacking"));
        assert_callee_summary_marker(1);

        let nested = VcgenContext::for_function("test::nested")
            .with_callee_summaries(callee_summary_fixture(2, "NestedBacking"));
        with_vcgen_context(&nested, || {
            assert!(!is_backing_struct_certified("CallerBacking"));
            assert!(is_backing_struct_certified("NestedBacking"));
            assert_callee_summary_marker(2);
        });
        assert!(is_backing_struct_certified("CallerBacking"));
        assert_callee_summary_marker(1);

        let default = VcgenContext::for_function("test::legacy-default");
        with_vcgen_context(&default, assert_no_callee_summaries);
        assert_callee_summary_marker(1);

        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let nested = VcgenContext::for_function("test::panicking-nested")
                .with_callee_summaries(callee_summary_fixture(3, "NestedBacking"));
            with_vcgen_context(&nested, || {
                assert_callee_summary_marker(3);
                panic!("exercise callee-summary scope unwinding");
            });
        }));
        assert!(unwind.is_err());
        assert_callee_summary_marker(1);
    });

    assert_no_callee_summaries();
}

#[test]
fn vcgen_context_guard_removes_only_its_owned_frame() {
    let outer = VcgenContext::for_function("test::outer")
        .with_callee_summaries(callee_summary_fixture(1, "CallerBacking"));
    let inner = VcgenContext::for_function("test::inner")
        .with_callee_summaries(callee_summary_fixture(2, "NestedBacking"));
    let outer_scope = enter_vcgen_context(&outer);
    let inner_scope = enter_vcgen_context(&inner);

    drop(outer_scope);
    assert_callee_summary_marker(2);
    drop(inner_scope);
    assert_no_callee_summaries();
}

#[test]
fn mismatched_function_context_cannot_lend_callee_summary_authority() {
    let mismatched = VcgenContext::for_function("test::other")
        .with_callee_summaries(callee_summary_fixture(9, "NestedBacking"));
    with_function_vcgen_context("test::target", &mismatched, assert_no_callee_summaries);
    assert_no_callee_summaries();
}

#[test]
fn legacy_generation_entry_does_not_inherit_ambient_contract_policy() {
    let func = contract_panic_fixture("test::ambient", Some("ArrayVec overflow: capacity is 8"));
    let ambient = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".into()]);

    with_vcgen_context(&ambient, || {
        let vcs = generate_vcs(&func);
        let assert_vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:"))
            })
            .expect("guarded panic call should generate an Assertion VC");
        let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
        assert!(
            !message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
            "legacy generation must install fail-closed policy, not inherit ambient context"
        );
        assert_eq!(
            contract_panic_annotations_for(&func.def_path),
            vec!["capacity is".to_string()],
            "the outer frame must still be restored after legacy generation"
        );
    });
}

#[test]
fn contract_panic_annotation_stamps_matching_panic_call_vc() {
    // Annotation payload is a substring of the panic call's const-str message
    // → the panic-call Assertion VC message carries the MATCHED marker. The VC
    // is otherwise the same obligation (still solved normally).
    let func =
        contract_panic_fixture("test::annotated_push", Some("ArrayVec overflow: capacity is 8"));
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".to_string()]);
    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("guarded panic call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "message-matched annotated panic must carry the contract-panic marker: {message}"
    );
}

#[test]
fn contract_panic_annotation_leaves_non_matching_message_unstamped() {
    // The payload does NOT occur in the panic message → no marker (the row
    // stays a plain refutable panic obligation; nothing to reclassify).
    let func = contract_panic_fixture("test::annotated_wrong_msg", Some("some other bug"));
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".to_string()]);
    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("guarded panic call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        !message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "a non-matching message must never be stamped: {message}"
    );
}

#[test]
fn contract_panic_annotation_is_pinned_to_its_function() {
    // The thread-local hint is keyed by def_path: a payload registered for a
    // DIFFERENT function must never stamp this one (no stale cross-function
    // reclassification channel).
    let func =
        contract_panic_fixture("test::unannotated_fn", Some("ArrayVec overflow: capacity is 8"));
    let context = VcgenContext::for_function("test::some_other_fn")
        .with_contract_panic_annotations(vec!["capacity is".into()]);
    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("guarded panic call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        !message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "another function's payload must never stamp this VC: {message}"
    );
}

#[test]
fn contract_panic_unused_annotation_mints_failed_refutation_vc() {
    // A function with NO matching panic call + a contract_panic annotation →
    // the refute lane mints an always-SAT (`Bool(true)`) Assertion VC carrying
    // the UNUSED marker, which lands as a guaranteed FAILED row (annotation on
    // panic-free code is an ERROR).
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "panic_free".to_string(),
        def_path: "test::panic_free".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".to_string()]);
    let vcs = generate_full_assert_refutation_vcs_with_context(&func, &context);
    let unused = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message }
                    if message.contains(trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
            )
        })
        .expect("an unused contract_panic annotation must mint the unused-marker VC");
    assert!(
        matches!(unused.formula, Formula::Bool(true)),
        "the unused-annotation VC must be always-SAT (guaranteed FAILED in the refute lane): {:?}",
        unused.formula
    );
}

#[test]
fn contract_panic_used_annotation_mints_no_unused_vc() {
    // The usage check is SYNTACTIC: a panic call whose const-str message
    // contains the payload counts as used, whatever the lanes later decide
    // about its reachability.
    let func =
        contract_panic_fixture("test::annotated_used", Some("ArrayVec overflow: capacity is 8"));
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".to_string()]);
    let vcs = generate_full_assert_refutation_vcs_with_context(&func, &context);
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message }
                if message.contains(trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
        )),
        "a message-matched annotation is used — no unused-annotation VC may be minted"
    );
}

#[test]
fn contract_panic_inlined_panic_fmt_arguments_from_str_counts_as_used_and_stamps() {
    // Edition-2021 post-inline lowering of `panic!("static str")`:
    //   _5 = fmt::Arguments::from_str("…"); panic_fmt(move _5)
    // The const message sits one call BEHIND the panic entry. Both the
    // unused-annotation check and the site matcher must harvest it through the
    // one-level `Arguments::from_str` chase (`panic_call_const_str_messages`):
    // the annotation counts as USED (no unused-marker VC) and the panic-call
    // VC is stamped with the matched marker.
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "inlined_panic_fmt".to_string(),
        def_path: "test::inlined_panic_fmt".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
                LocalDecl { index: 4, ty: Ty::Unit, name: None },
                LocalDecl { index: 5, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::fmt::Arguments::<'a>::from_str".to_string(),
                        args: vec![Operand::Constant(ConstValue::Str {
                            bytes: b"ArrayVec overflow: capacity is 8".to_vec(),
                        })],
                        dest: Place::local(5),
                        target: Some(BlockId(2)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::rt::panic_fmt".to_string(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(3),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["capacity is".to_string()]);

    // USED: no unused-annotation marker VC.
    let refute_vcs = generate_full_assert_refutation_vcs_with_context(&func, &context);
    assert!(
        !refute_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message }
                if message.contains(trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
        )),
        "an annotation matched through the Arguments::from_str chase is USED"
    );

    // STAMPED: the panic-call VC carries the matched marker.
    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("the panic_fmt call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "the from_str-carried static message must stamp the matched marker: {message}"
    );
}

/// Trust (T7 contract-panic through panic_fmt): fixture — the REAL
/// post-lowering shape of a guarded FORMATTED `panic!("prefix {}", x)` on this
/// toolchain (see the unoptimized-MIR probe in the T7 report):
///   _5 = const b"\x07prefix \xc0\x00";               // the fmt TEMPLATE bytes
///   _4 = fmt::Arguments::<'_>::new::<10, 1>(move _5, copy _6);
///   panic_fmt(move _4)
/// The literal pieces live ONLY in the template constant; the runtime value
/// (`x`) is never in it.
fn contract_panic_formatted_fixture(def_path: &str, template: &[u8]) -> VerifiableFunction {
    let span = SourceSpan::default();
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
        def_path: def_path.to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
                LocalDecl { index: 4, ty: Ty::Unit, name: None },
                LocalDecl { index: 5, ty: Ty::Unit, name: None },
                LocalDecl { index: 6, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    // The template constant sits one bare-local `Use` def
                    // behind the ctor arg — exactly the real MIR shape.
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Str {
                            bytes: template.to_vec(),
                        })),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::fmt::Arguments::<'_>::new::<10, 1>".to_string(),
                        args: vec![Operand::Move(Place::local(5)), Operand::Copy(Place::local(6))],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::panicking::panic_fmt".to_string(),
                        args: vec![Operand::Move(Place::local(4))],
                        dest: Place::local(3),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn contract_panic_formatted_template_literal_piece_matches_and_counts_used() {
    // T7 pin (task shape): `panic!("prefix {}", x)` with
    // `message_contains = "prefix"` MUST match — the literal piece is
    // decoded out of the fmt template through the `Arguments::new` chase.
    let func = contract_panic_formatted_fixture("test::t7_formatted_match", b"\x07prefix \xc0\x00");
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["prefix".to_string()]);

    // STAMPED: the panic-call VC carries the matched marker.
    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("the panic_fmt call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "a template literal piece must stamp the matched marker: {message}"
    );

    // USED (same harvest, unused-annotation semantics preserved): no
    // unused-marker VC.
    let refute_vcs = generate_full_assert_refutation_vcs_with_context(&func, &context);
    assert!(
        !refute_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message }
                if message.contains(trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
        )),
        "an annotation matched through the template chase is USED"
    );
}

#[test]
fn contract_panic_formatted_runtime_only_text_still_never_matches() {
    // T7 pin (task shape): `message_contains` text that only occurs in the
    // RUNTIME value (never in a literal piece) must NOT match — the runtime
    // value is not in the template, so the harvest cannot contain it. The
    // annotation is then also (correctly) UNUSED.
    let func =
        contract_panic_formatted_fixture("test::t7_formatted_runtime_only", b"\x07prefix \xc0\x00");
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_contract_panic_annotations(vec!["42".to_string()]);

    let vcs = generate_vcs_with_context(&func, &context);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call:")))
        .expect("the panic_fmt call should generate an Assertion VC");
    let VcKind::Assertion { message } = &assert_vc.kind else { unreachable!() };
    assert!(
        !message.contains(trust_types::assumption::CONTRACT_PANIC_VC_MARKER),
        "runtime-value-only text must never stamp the marker: {message}"
    );

    let refute_vcs = generate_full_assert_refutation_vcs_with_context(&func, &context);
    assert!(
        refute_vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message }
                if message.contains(trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
        )),
        "an annotation matching only runtime text must mint the unused-annotation VC"
    );
}

#[test]
fn fmt_template_decoder_walks_pieces_placeholders_and_fails_closed() {
    use crate::generate::fmt_template_literal_pieces as decode;
    // Single piece + default placeholder (the probe's real template).
    assert_eq!(decode(b"\x07prefix \xc0\x00").as_deref(), Some("prefix "));
    // Two pieces around placeholders; arg_index field (head bit 3 -> 2 bytes)
    // and a default placeholder both skip cleanly; pieces CONCATENATE.
    assert_eq!(
        decode(b"\x09expected \xc8\x00\x00\x05 got \xc0\x00").as_deref(),
        Some("expected  got ")
    );
    // Long-piece encoding (0x80 + u16 LE length).
    assert_eq!(decode(b"\x80\x03\x00abc\x00").as_deref(), Some("abc"));
    // Placeholder with ALL option fields (flags 4B + width 2B + precision 2B
    // + arg_index 2B = 10 bytes) skips exactly.
    assert_eq!(
        decode(b"\xcf\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x02hi\x00").as_deref(),
        Some("hi")
    );
    // Fail-closed: truncated piece, truncated placeholder fields, invalid
    // part-start byte, bytes after the end marker, non-UTF-8 piece, empty.
    assert_eq!(decode(b"\x07pre"), None);
    assert_eq!(decode(b"\xc8\x00"), None);
    assert_eq!(decode(b"\x81\x00"), None);
    assert_eq!(decode(b"\x00\x00"), None);
    assert_eq!(decode(b"\x02\xff\xfe\x00"), None);
    assert_eq!(decode(b""), None);
}

#[test]
fn arguments_template_new_recognizer_excludes_sibling_ctors() {
    use crate::generate::is_arguments_template_new_call as is_new;
    // The turbofished real spelling and the bare synthetic spelling match.
    assert!(is_new("core::fmt::Arguments::<'_>::new::<10, 1>"));
    assert!(is_new("std::fmt::Arguments::new"));
    // Sibling ctors have their own arm / are not Arguments at all.
    assert!(!is_new("std::fmt::Arguments::<'a>::from_str"));
    assert!(!is_new("core::fmt::Arguments::<'_>::new_const::<1>"));
    assert!(!is_new("core::fmt::rt::Argument::<'_>::new_display::<usize>"));
    // Name-boundary hygiene: `renew` is not `::new`; non-Arguments `new` is out.
    assert!(!is_new("my::Arguments::renew"));
    assert!(!is_new("alloc::vec::Vec::<u8>::new"));
}

/// Trust (T5 float intervals): fixture — `r = <clamp_callee>(x, lo, hi);
/// m = 0.2126 * r; s = m + m; return s` (the aterm-types WCAG-luminance shape,
/// lib.rs:291). `lo`/`hi` are the given operands so tests can flip them from
/// literals to symbolic/void bounds.
fn float_clamp_weighted_sum_fixture(
    clamp_callee: &str,
    lo: Operand,
    hi: Operand,
) -> VerifiableFunction {
    let span = SourceSpan::default();
    let f64_ty = Ty::Float { width: 64 };
    VerifiableFunction {
        name: "clamp_weighted_sum".to_string(),
        def_path: "test::clamp_weighted_sum".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: f64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: f64_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: f64_ty.clone(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: f64_ty.clone(), name: Some("m".into()) },
                LocalDecl { index: 4, ty: f64_ty.clone(), name: Some("s".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: clamp_callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1)), lo, hi],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Mul,
                                Operand::Constant(ConstValue::FloatBits {
                                    bits: 0.2126f64.to_bits() as u128,
                                    width: 64,
                                }),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: f64_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn f64_lit(v: f64) -> Operand {
    Operand::Constant(ConstValue::FloatBits { bits: v.to_bits() as u128, width: 64 })
}

fn float_overflow_vcs(func: &VerifiableFunction) -> Vec<VcKind> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { .. }))
        .map(|vc| vc.kind)
        .collect()
}

#[test]
fn float_clamped_weighted_sum_discharges_overflow_vcs() {
    // T5 pin (aterm-types lib.rs:291 shape): operands clamped to literal
    // [0.0, 1.0] make both the const-weight Mul and the downstream Add
    // provably overflow-free — no FloatOverflowToInfinity VC is minted.
    let func = float_clamp_weighted_sum_fixture(
        "core::f64::<impl f64>::clamp",
        f64_lit(0.0),
        f64_lit(1.0),
    );
    let vcs = float_overflow_vcs(&func);
    assert!(vcs.is_empty(), "clamp-bounded weighted sum must discharge, got {vcs:?}");
}

#[test]
fn float_add_with_small_literal_operand_discharges_overflow_vc() {
    // T5 pin (aterm-types lib.rs:265 shape, `lighter + 0.05`): ONE small
    // literal operand suffices for the Add discharge (the witness needs BOTH
    // magnitudes above f64::MAX/2).
    let span = SourceSpan::default();
    let f64_ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "add_small_literal".to_string(),
        def_path: "test::add_small_literal".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: f64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: f64_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: f64_ty.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            f64_lit(0.05),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: f64_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = float_overflow_vcs(&func);
    assert!(vcs.is_empty(), "x + 0.05 must discharge its overflow VC, got {vcs:?}");
}

#[test]
fn float_clamp_discharge_fails_closed_on_every_weak_gate() {
    // Symbolic bounds prove nothing.
    let symbolic = float_clamp_weighted_sum_fixture(
        "core::f64::<impl f64>::clamp",
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(1)),
    );
    assert!(
        !float_overflow_vcs(&symbolic).is_empty(),
        "symbolic clamp bounds must keep the overflow VCs"
    );
    // A user-defined `clamp` has arbitrary semantics — never matched.
    let user = float_clamp_weighted_sum_fixture("mymod::clamp", f64_lit(0.0), f64_lit(1.0));
    assert!(!float_overflow_vcs(&user).is_empty(), "a non-std clamp must keep the overflow VCs");
    // `lo > hi` panics at runtime instead of bounding — no fact.
    let inverted = float_clamp_weighted_sum_fixture(
        "core::f64::<impl f64>::clamp",
        f64_lit(1.0),
        f64_lit(0.0),
    );
    assert!(
        !float_overflow_vcs(&inverted).is_empty(),
        "an inverted-bounds clamp must keep the overflow VCs"
    );
    // Huge literal bounds stay above the discharge margin.
    let huge = float_clamp_weighted_sum_fixture(
        "core::f64::<impl f64>::clamp",
        f64_lit(0.0),
        f64_lit(1.0e308),
    );
    assert!(
        !float_overflow_vcs(&huge).is_empty(),
        "a near-MAX clamp bound must keep the overflow VCs (margin respected)"
    );
    // NaN bounds panic at runtime — no fact.
    let nan = float_clamp_weighted_sum_fixture(
        "core::f64::<impl f64>::clamp",
        f64_lit(0.0),
        f64_lit(f64::NAN),
    );
    assert!(!float_overflow_vcs(&nan).is_empty(), "NaN clamp bounds must keep the overflow VCs");
}

#[test]
fn test_unreachable_display_call_generates_guarded_unreachable_vc() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "panic_unreachable".to_string(),
        def_path: "test::panic_unreachable".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::panicking::unreachable_display::<&str>".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let unreach_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Unreachable))
        .expect("unreachable_display should generate an Unreachable VC");

    assert!(
        matches!(
            &unreach_vc.formula,
            Formula::And(clauses)
                if clauses.iter().any(|clause| matches!(
                    clause,
                    Formula::Var(name, Sort::Bool) if name == "flag"
                ))
        ),
        "Unreachable VC should be guarded by the true branch reaching unreachable_display, got {:?}",
        unreach_vc.formula
    );
}

/// Build a function modelling an enum `match` whose `otherwise` arm is a bare
/// `Terminator::Unreachable`, with the enum's valid discriminant set attached
/// as a function precondition — exactly what `trust-mir-extract`'s
/// `enum_discriminant_range_preconditions` emits for a match on an enum value.
///
/// `covered_tags` are the discriminant values the `SwitchInt` explicitly
/// branches on (the match arms); `valid_tags` is the enum's full discriminant
/// set, surfaced as the precondition `discr == t0 OR discr == t1 OR ...`.
fn enum_discriminant_match_function(
    covered_tags: &[u128],
    valid_tags: &[i128],
) -> VerifiableFunction {
    let span = SourceSpan::default();
    // The discriminant temp is local _2 (name: None → var name "_2"), so the
    // SwitchInt otherwise-guard and the precondition both reference `_2`.
    let discr = Operand::Move(Place::local(2));

    let arm_blocks: Vec<(u128, BlockId)> =
        covered_tags.iter().enumerate().map(|(i, &tag)| (tag, BlockId(1 + i))).collect();
    let unreachable_block_id = BlockId(1 + covered_tags.len());

    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr,
            targets: arm_blocks.clone(),
            otherwise: unreachable_block_id,
            exhaustive_enum_unreachable: false,
            span: span.clone(),
        },
    }];
    for (_, arm) in &arm_blocks {
        blocks.push(BasicBlock { id: *arm, stmts: vec![], terminator: Terminator::Return });
    }
    blocks.push(BasicBlock {
        id: unreachable_block_id,
        stmts: vec![],
        terminator: Terminator::Unreachable,
    });

    // Precondition: `discr ∈ valid_tags`, encoded as a disjunction of equalities
    // — the always-true enum-range invariant carried by the authoritative tag set.
    let precondition = Formula::Or(
        valid_tags
            .iter()
            .map(|&t| {
                Formula::Eq(Box::new(Formula::var("_2", Sort::Int)), Box::new(Formula::Int(t)))
            })
            .collect(),
    );

    VerifiableFunction {
        name: "enum_discriminant_match".to_string(),
        def_path: "test::enum_discriminant_match".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![precondition],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Finite-model SAT check for the discriminant-range Unreachable VCs above.
/// Brute-forces every variable over a small integer domain; the VC is SAT iff
/// some assignment makes it true (i.e. the "unreachable" block is reachable).
/// Panics on any formula node the discriminant encoding shouldn't produce, so
/// the test fails loudly if the VC shape drifts rather than silently passing.
fn discriminant_vc_is_sat(formula: &Formula) -> bool {
    fn collect_vars(f: &Formula, out: &mut std::collections::BTreeSet<String>) {
        if let Some(name) = f.var_name() {
            out.insert(name.to_string());
            return;
        }
        match f {
            Formula::Not(a) | Formula::Neg(a) => collect_vars(a, out),
            Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| collect_vars(x, out)),
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b) => {
                collect_vars(a, out);
                collect_vars(b, out);
            }
            Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => {}
            other => panic!("discriminant VC: unexpected node while collecting vars: {other:?}"),
        }
    }

    fn eval_int(f: &Formula, env: &std::collections::BTreeMap<String, i128>) -> i128 {
        if let Some(name) = f.var_name() {
            return *env.get(name).expect("var bound in env");
        }
        match f {
            Formula::Int(n) => *n,
            Formula::UInt(n) => i128::try_from(*n).expect("uint fits i128 in test"),
            Formula::Neg(a) => -eval_int(a, env),
            Formula::Add(a, b) => eval_int(a, env) + eval_int(b, env),
            Formula::Sub(a, b) => eval_int(a, env) - eval_int(b, env),
            Formula::Mul(a, b) => eval_int(a, env) * eval_int(b, env),
            other => panic!("discriminant VC: unexpected node in integer position: {other:?}"),
        }
    }

    fn eval_bool(f: &Formula, env: &std::collections::BTreeMap<String, i128>) -> bool {
        match f {
            Formula::Bool(b) => *b,
            // A boolean-sorted variable: nonzero means true.
            Formula::Var(_, _) | Formula::SymVar(_, _) => {
                *env.get(f.var_name().expect("var")).expect("var bound in env") != 0
            }
            Formula::Not(a) => !eval_bool(a, env),
            Formula::And(xs) => xs.iter().all(|x| eval_bool(x, env)),
            Formula::Or(xs) => xs.iter().any(|x| eval_bool(x, env)),
            Formula::Implies(a, b) => !eval_bool(a, env) || eval_bool(b, env),
            Formula::Eq(a, b) => eval_int(a, env) == eval_int(b, env),
            Formula::Lt(a, b) => eval_int(a, env) < eval_int(b, env),
            Formula::Le(a, b) => eval_int(a, env) <= eval_int(b, env),
            Formula::Gt(a, b) => eval_int(a, env) > eval_int(b, env),
            Formula::Ge(a, b) => eval_int(a, env) >= eval_int(b, env),
            other => panic!("discriminant VC: unexpected node in boolean position: {other:?}"),
        }
    }

    let mut names = std::collections::BTreeSet::new();
    collect_vars(formula, &mut names);
    let names: Vec<String> = names.into_iter().collect();
    let domain: Vec<i128> = (-3..=6).collect();
    let total = domain.len().checked_pow(names.len() as u32).expect("small domain");
    for mut idx in 0..total {
        let mut env = std::collections::BTreeMap::new();
        for name in &names {
            env.insert(name.clone(), domain[idx % domain.len()]);
            idx /= domain.len();
        }
        if eval_bool(formula, &env) {
            return true;
        }
    }
    false
}

#[test]
fn exhaustive_enum_match_unreachable_vc_is_unsat_under_discriminant_precondition() {
    // Exhaustive: arms cover every valid tag {0,1,2}. The precondition
    // `discr ∈ {0,1,2}` conjoined with the otherwise-guard `discr ∉ {0,1,2}`
    // is UNSAT, so the otherwise-`Unreachable` VC proves — the exhaustive match
    // no longer degrades to a runtime check.
    let func = enum_discriminant_match_function(&[0, 1, 2], &[0, 1, 2]);
    let vcs = generate_vcs(&func);
    let unreach = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Unreachable))
        .expect("exhaustive match otherwise->Unreachable should generate an Unreachable VC");
    assert!(
        !discriminant_vc_is_sat(&unreach.formula),
        "exhaustive match: precondition discr∈{{0,1,2}} AND otherwise-guard discr∉{{0,1,2}} must \
         be UNSAT (proved unreachable), got SAT: {:?}",
        unreach.formula
    );
}

#[test]
fn partial_enum_match_unreachable_vc_stays_sat_without_full_coverage() {
    // Partial: arms cover only {0} of the valid tags {0,1,2}. discr=1 or discr=2
    // satisfies BOTH the precondition and the otherwise-guard, so the VC stays
    // SAT and is NOT proved. This is the soundness floor: proving it would mask
    // a genuinely reachable obligation (e.g. an inlined `unreachable_unchecked`).
    let func = enum_discriminant_match_function(&[0], &[0, 1, 2]);
    let vcs = generate_vcs(&func);
    let unreach = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Unreachable))
        .expect("partial match otherwise->Unreachable should generate an Unreachable VC");
    assert!(
        discriminant_vc_is_sat(&unreach.formula),
        "partial match: an uncovered-but-valid tag (1 or 2) reaches the otherwise arm, so the VC \
         must stay SAT (NOT proved); proving it would be unsound. got UNSAT: {:?}",
        unreach.formula
    );
}

/// Models a *nested* enum match (`match o { Some(Ok(x)) ... }` over
/// `Option<Result<_, _>>`): an outer `SwitchInt` on `_3` whose `Some` arm leads
/// to an inner `SwitchInt` on `_2`, with BOTH `otherwise` edges flowing to one
/// shared `Terminator::Unreachable` sink. This is the CFG shape that
/// `trust-mir-extract`'s `enum_discriminant_range_preconditions` must now cover:
/// `_2` is the INNER enum's discriminant, read through `[Downcast,Field]`
/// projections, so its range precondition uses the INNER enum's tag set.
///
/// `inner_valid` is the inner enum's full discriminant set; `inner_covered` the
/// inner arms the match branches on. With `include_inner_precondition`, the
/// always-true `_2 ∈ inner_valid` invariant is attached (what the fix emits); the
/// outer `_3 ∈ {0,1}` invariant is always attached.
fn nested_enum_discriminant_match_function(
    inner_valid: &[i128],
    inner_covered: &[u128],
    include_inner_precondition: bool,
) -> VerifiableFunction {
    let span = SourceSpan::default();
    // Block layout: bb0 outer switch; bb1 None-arm return; bb2 inner switch;
    // bb3.. inner-arm returns; final block the shared Unreachable sink.
    let inner_arm0 = 3usize;
    let unreachable_block_id = BlockId(inner_arm0 + inner_covered.len());

    let inner_targets: Vec<(u128, BlockId)> =
        inner_covered.iter().enumerate().map(|(i, &t)| (t, BlockId(inner_arm0 + i))).collect();

    let mut blocks = vec![
        // bb0: outer Option switch — 0 (None) -> bb1 ret, 1 (Some) -> bb2 inner,
        // otherwise -> shared Unreachable.
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                otherwise: unreachable_block_id,
                exhaustive_enum_unreachable: false,
                span: span.clone(),
            },
        },
        // bb1: None arm.
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        // bb2: inner enum switch sharing the SAME Unreachable otherwise.
        BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(2)),
                targets: inner_targets,
                otherwise: unreachable_block_id,
                exhaustive_enum_unreachable: false,
                span: span.clone(),
            },
        },
    ];
    for (i, _) in inner_covered.iter().enumerate() {
        blocks.push(BasicBlock {
            id: BlockId(inner_arm0 + i),
            stmts: vec![],
            terminator: Terminator::Return,
        });
    }
    blocks.push(BasicBlock {
        id: unreachable_block_id,
        stmts: vec![],
        terminator: Terminator::Unreachable,
    });

    let outer_precondition = Formula::Or(vec![
        Formula::Eq(Box::new(Formula::var("_3", Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Eq(Box::new(Formula::var("_3", Sort::Int)), Box::new(Formula::Int(1))),
    ]);
    let mut preconditions = vec![outer_precondition];
    if include_inner_precondition {
        preconditions.push(Formula::Or(
            inner_valid
                .iter()
                .map(|&t| {
                    Formula::Eq(Box::new(Formula::var("_2", Sort::Int)), Box::new(Formula::Int(t)))
                })
                .collect(),
        ));
    }

    VerifiableFunction {
        name: "nested_enum_discriminant_match".to_string(),
        def_path: "test::nested_enum_discriminant_match".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions,
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn nested_enum_match_shared_unreachable_proves_under_both_range_preconditions() {
    // PRECISION: the inner `Result` is 2-variant {0,1}, fully covered. With
    // BOTH `_3 ∈ {0,1}` and `_2 ∈ {0,1}` attached, every path reaching the shared
    // Unreachable sink is UNSAT: the outer otherwise needs `_3 ∉ {0,1}`, the inner
    // otherwise needs `_3 == 1 ∧ _2 ∉ {0,1}` — both contradicted. So every
    // Unreachable VC proves, exactly turning `Some(Ok(x))`-style false-FAILs into
    // proofs. The inner precondition is what the two-downcast `Place::ty` fix emits.
    let func = nested_enum_discriminant_match_function(&[0, 1], &[0, 1], true);
    let vcs = generate_vcs(&func);
    let unreach: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert!(!unreach.is_empty(), "nested match should generate an Unreachable VC");
    for vc in &unreach {
        assert!(
            !discriminant_vc_is_sat(&vc.formula),
            "nested exhaustive match: shared Unreachable must be UNSAT (proved) under both \
             discriminant-range preconditions, got SAT: {:?}",
            vc.formula
        );
    }
}

#[test]
fn nested_enum_match_inner_precondition_is_load_bearing() {
    // NECESSITY: drop the inner `_2 ∈ {0,1}` precondition (the pre-fix
    // behavior, where the inner discriminant read through `[Downcast,Field]` got
    // no range fact). The inner otherwise path `_3 == 1 ∧ _2 ∉ {0,1}` is then SAT
    // (e.g. _3=1, _2=5), so the shared Unreachable stays SAT — the precise
    // reproduction of the `safe_param_nested` false-FAIL this fix removes.
    let func = nested_enum_discriminant_match_function(&[0, 1], &[0, 1], false);
    let vcs = generate_vcs(&func);
    let unreach: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert!(!unreach.is_empty(), "nested match should generate an Unreachable VC");
    assert!(
        unreach.iter().any(|vc| discriminant_vc_is_sat(&vc.formula)),
        "without the inner range precondition the inner otherwise is reachable, so some \
         Unreachable VC must stay SAT (the false-FAIL); got all UNSAT"
    );
}

#[test]
fn nested_enum_match_partial_inner_uses_inner_tag_set_not_outer() {
    // SOUNDNESS: the inner enum is 3-variant {0,1,2} but only {0,1} are
    // covered — the otherwise sink is GENUINELY reachable for inner tag 2. The
    // correct precondition is the INNER enum's full set `_2 ∈ {0,1,2}`, under
    // which `_3 == 1 ∧ _2 ∉ {0,1}` is SAT at _2=2 → stays NOT-proved. Had the fix
    // wrongly leaked the OUTER Option's smaller set `_2 ∈ {0,1}`, this would
    // collapse to UNSAT — a false-PROVE of a reachable block. Pinning SAT here
    // guards `place_enum_tags` against resolving the outer enum's tags.
    let func = nested_enum_discriminant_match_function(&[0, 1, 2], &[0, 1], true);
    let vcs = generate_vcs(&func);
    let unreach: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert!(!unreach.is_empty(), "nested match should generate an Unreachable VC");
    assert!(
        unreach.iter().any(|vc| discriminant_vc_is_sat(&vc.formula)),
        "partial inner match: inner tag 2 reaches the otherwise sink, so with the inner enum's \
         full tag set {{0,1,2}} the VC must stay SAT (NOT proved); UNSAT would mean the outer \
         enum's smaller tag set leaked in — a false-PROVE"
    );
}

#[test]
fn test_cmp_binop_produces_no_arithmetic_vcs() {
    // #361: BinOp::Cmp (three-way comparison) is always safe — no VCs.
    let func = make_binop_func(BinOp::Cmp, Ty::i32());
    let vcs = generate_vcs(&func);
    let arith_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::ArithmeticOverflow { .. }
                    | VcKind::DivisionByZero
                    | VcKind::RemainderByZero
                    | VcKind::ShiftOverflow { .. }
                    | VcKind::NegationOverflow { .. }
            )
        })
        .collect();
    assert!(
        arith_vcs.is_empty(),
        "BinOp::Cmp should not generate any arithmetic VCs, got {}",
        arith_vcs.len()
    );
}

#[test]
fn test_integer_ops_produce_no_float_vcs() {
    // #361: Integer operations must NOT produce float VCs.
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(
                vc.kind,
                VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. }
            )),
            "integer op {op:?} must not produce float VCs"
        );
    }
}

#[test]
fn test_operand_to_formula_unknown_const_does_not_panic() {
    // #361: Unknown ConstValue variants should produce a symbolic variable,
    // not panic. We test this by verifying the fallback path works for
    // known variants that previously used unreachable!.
    let func = midpoint_function();

    // All known variants should still work correctly
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Bool(true))),
        Formula::Bool(true)
    );
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Int(42))),
        Formula::Int(42)
    );
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Uint(7, 32))),
        Formula::Int(7)
    );
    assert_eq!(operand_to_formula(&func, &Operand::Constant(ConstValue::Unit)), Formula::Int(0));
    let first = operand_to_formula(
        &func,
        &Operand::Constant(ConstValue::CallableItem {
            def_path: "fixture::first".to_string(),
            kind: CallableKind::FnDef,
            def_path_hash: CallableDefPathHash::new(1, 1),
        }),
    );
    let second = operand_to_formula(
        &func,
        &Operand::Constant(ConstValue::CallableItem {
            def_path: "fixture::second".to_string(),
            kind: CallableKind::FnDef,
            def_path_hash: CallableDefPathHash::new(1, 2),
        }),
    );
    assert_ne!(first, second, "distinct callable identities must not alias one formula term");
    assert!(matches!(first, Formula::Var(_, Sort::Int)));
    assert!(matches!(second, Formula::Var(_, Sort::Int)));
}

#[test]
fn test_float_ops_integer_isolation() {
    // Integer Div emits a DivisionByZero VC but never produces
    // a float-typed VC. This test guards the integer/float isolation.
    let func = make_binop_func(BinOp::Div, Ty::i32());
    let vcs = generate_vcs(&func);
    let float_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. })
        })
        .collect();
    assert!(float_vcs.is_empty(), "integer Div must not produce float VCs, got {float_vcs:?}");
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "integer Div(_, var) must emit DivisionByZero VC"
    );
}

// -----------------------------------------------------------------------
// Atomic ordering legality VCs in generate_vcs() pipeline
// -----------------------------------------------------------------------

/// Build a function with a Call terminator carrying an illegal atomic load
/// using Release ordering (violates L1: loads cannot release).
fn atomic_load_release_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "atomic_load_release".to_string(),
        def_path: "test::atomic_load_release".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("target".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::intrinsics::atomic_load_release".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(1),
                        dest: Some(Place::local(0)),
                        op_kind: AtomicOpKind::Load,
                        ordering: AtomicOrdering::Release, // L1 violation
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_atomic_legality_load_release_generates_vc() {
    // #609: Load with Release ordering violates L1.
    let func = atomic_load_release_function();
    let vcs = generate_vcs(&func);

    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert_eq!(
        ordering_vcs.len(),
        1,
        "load with Release ordering should produce exactly 1 InsufficientOrdering VC, got {}",
        ordering_vcs.len(),
    );
    assert_eq!(ordering_vcs[0].function, "atomic_load_release");
}

#[test]
fn test_atomic_legality_no_atomics_no_new_vcs() {
    // #609: Functions without atomic operations should produce no ordering VCs.
    let func = midpoint_function();
    let vcs = generate_vcs(&func);

    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert!(
        ordering_vcs.is_empty(),
        "non-atomic function should produce no InsufficientOrdering VCs"
    );
}

#[test]
fn test_atomic_legality_legal_load_no_vc() {
    // #609: Load with Acquire ordering is legal — no InsufficientOrdering VC.
    let func = VerifiableFunction {
        name: "atomic_load_acquire".to_string(),
        def_path: "test::atomic_load_acquire".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("target".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::intrinsics::atomic_load_acquire".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(1),
                        dest: Some(Place::local(0)),
                        op_kind: AtomicOpKind::Load,
                        ordering: AtomicOrdering::Acquire, // legal
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert!(ordering_vcs.is_empty(), "legal atomic load should produce no ordering VCs");
}

// -----------------------------------------------------------------------
// Assert-passed semantic guard propagation across blocks
// -----------------------------------------------------------------------

/// Build a 3-block safe midpoint: `lo + (hi - lo) / 2`
///
/// ```text
/// bb0: _3 = CheckedSub(hi, lo); Assert(!_3.1, overflow) -> bb1
/// bb1: _4 = _3.0; _5 = Div(_4, 2); goto bb2
/// bb2: _6 = CheckedAdd(lo, _5); Assert(!_6.1, overflow) -> bb3
/// bb3: return _6.0
/// ```
///
/// The Assert in bb0 passing means `hi >= lo` (unsigned no-overflow on sub).
/// The Assert in bb2 checking CheckedAdd(lo, _5) should benefit from the
/// semantic guard: knowing `hi >= lo` constrains `_5 = (hi - lo) / 2` and
/// makes the Add overflow impossible.
fn safe_midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_midpoint".to_string(),
        def_path: "test::safe_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) }, // _1
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) }, // _2
                // _3: (usize, bool) from CheckedSub
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4: sub result
                LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5: _4 / 2
                // _6: (usize, bool) from CheckedAdd
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 7, ty: Ty::usize(), name: None }, // _7: add result
            ],
            blocks: vec![
                // bb0: _3 = CheckedSub(hi, lo); assert(!_3.1) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(2)), // hi
                            Operand::Copy(Place::local(1)), // lo
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _4 = _3.0; _5 = _4 / 2; goto bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                // bb2: _6 = CheckedAdd(lo, _5); assert(!_6.1) -> bb3
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)), // lo
                            Operand::Copy(Place::local(5)), // (hi - lo) / 2
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(6, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb3: _7 = _6.0; _0 = _7; return
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(6, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(7))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a CFG with a join block whose successor must be reprocessed after
/// the join's path assumptions are weakened.
fn semantic_guard_join_reenqueue_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "semantic_guard_join_reenqueue".to_string(),
        def_path: "test::semantic_guard_join_reenqueue".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) }, // _1
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) }, // _2
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) }, // _3
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("tmp".into()) }, // _4
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("joined".into()) }, // _5
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_safe_midpoint_sub_guard_propagates_to_add() {
    // `generate_vcs` emits ArithmeticOverflow VCs again.
    // `safe_midpoint_function` has two `CheckedBinaryOp` + `Assert(Overflow)`
    // pairs (a Sub in bb0 and an Add in bb2), so exactly two overflow VCs
    // are expected. The second VC's formula should incorporate the semantic
    // guard from bb0's passing Assert (i.e., `hi >= lo`) via
    // `build_semantic_guard_map`.
    let func = safe_midpoint_function();
    let vcs = generate_vcs(&func);

    let overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(
        overflow_vcs.len(),
        2,
        "safe_midpoint has two CheckedBinaryOp overflow pairs, got {}",
        overflow_vcs.len()
    );

    // The Add overflow VC (bb2) must contain the Sub's semantic guard —
    // specifically a `Le` formula from the `hi >= lo` range constraint.
    let add_overflow_formula = overflow_vcs
        .iter()
        .find_map(|vc| match &vc.kind {
            VcKind::ArithmeticOverflow { op: BinOp::Add, .. } => Some(&vc.formula),
            _ => None,
        })
        .expect("expected an Add overflow VC");
    assert!(
        contains_le_formula(add_overflow_formula),
        "Add overflow VC must carry the propagated Sub semantic guard (Le node), got {add_overflow_formula:?}"
    );
}

/// Recursively check if a formula contains a `Formula::Le` node.
fn contains_le_formula(f: &Formula) -> bool {
    match f {
        Formula::Le(_, _) => true,
        Formula::And(clauses) => clauses.iter().any(contains_le_formula),
        Formula::Or(clauses) => clauses.iter().any(contains_le_formula),
        Formula::Not(inner) => contains_le_formula(inner),
        Formula::Implies(lhs, rhs) => contains_le_formula(lhs) || contains_le_formula(rhs),
        _ => false,
    }
}

#[test]
fn test_safe_midpoint_semantic_guard_map_populated() {
    // #621: Verify build_semantic_guard_map finds the Sub's semantic guard
    // and propagates it to bb1 and bb2.
    let func = safe_midpoint_function();
    let guard_map = build_semantic_guard_map(&func);

    // bb0 has the CheckedSub + Assert pattern.
    // bb1 is the assert-passed target, so it should have the semantic guard.
    // bb2 is reached from bb1 via Goto, so the guard propagates there too.
    assert!(
        guard_map.contains_key(&BlockId(1)),
        "bb1 (assert-passed target) should have semantic guards"
    );
    assert!(
        guard_map.contains_key(&BlockId(2)),
        "bb2 (reachable from bb1) should have semantic guards from bb0's assert"
    );

    // bb1 gets 4 from bb0: range constraint, result definition (_3.0 = hi - lo),
    // lhs input range (hi in [0, max]), rhs input range (lo in [0, max])
    // bb2 gets 4 from bb0 + 2 dataflow defs from bb1 (_4 = _3.0, _5 = _4 / 2) = 6
    let bb1_guards = guard_map.get(&BlockId(1)).unwrap();
    let bb2_guards = guard_map.get(&BlockId(2)).unwrap();
    assert_eq!(bb1_guards.len(), 4, "bb1 should have 4 assumptions from bb0. Got: {bb1_guards:?}");
    assert_eq!(
        bb2_guards.len(),
        6,
        "bb2 should have 6 assumptions: bb0's 4 + bb1's 2 defs. Got: {bb2_guards:?}"
    );
}

#[test]
fn test_safe_midpoint_sub_vc_has_no_semantic_guard() {
    // #621: The Sub overflow VC (in bb0) should NOT have semantic guards,
    // since it's the entry block and no prior asserts have passed.
    let func = safe_midpoint_function();
    let guard_map = build_semantic_guard_map(&func);

    // bb0 is the entry block — no semantic guards should be accumulated.
    assert!(!guard_map.contains_key(&BlockId(0)), "entry block bb0 should have no semantic guards");
}

#[test]
fn test_semantic_guard_map_reenqueues_successors_after_join_weakening() {
    let func = semantic_guard_join_reenqueue_function();
    let guard_map = build_semantic_guard_map(&func);

    assert_eq!(
        guard_map.get(&BlockId(3)),
        Some(&vec![Formula::Bool(true)]),
        "join block should weaken to Bool(true) after seeing conflicting incoming defs"
    );

    assert_eq!(
        guard_map.get(&BlockId(4)),
        Some(&vec![Formula::Bool(true)]),
        "successor should be revisited and weakened instead of retaining the first path's stronger defs"
    );
}

#[test]
fn test_atomic_legality_fence_relaxed_generates_vc() {
    // #609: Fence with Relaxed ordering violates L5.
    let func = VerifiableFunction {
        name: "relaxed_fence".to_string(),
        def_path: "test::relaxed_fence".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::intrinsics::atomic_fence_relaxed".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(0),
                        dest: None,
                        op_kind: AtomicOpKind::Fence,
                        ordering: AtomicOrdering::Relaxed, // L5 violation
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert_eq!(
        ordering_vcs.len(),
        1,
        "fence with Relaxed ordering should produce exactly 1 InsufficientOrdering VC"
    );
}

// -----------------------------------------------------------------------
// Real MIR fixture tests
// -----------------------------------------------------------------------

#[test]
fn test_real_mir_generate_vcs_safe_divide() {
    // DivisionByZero VCs are emitted again. `safe_divide` divides
    // by a variable parameter, so `generate_vcs` must produce at least one
    // DivisionByZero VC.
    let func = load_fixture("test_functions__safe_divide");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "safe_divide(var, var) must emit DivisionByZero VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_checked_add() {
    // CheckedAdd should deserialize from a real MIR fixture and run through vcgen.
    let func = load_fixture("test_functions__checked_add");
    let vcs = generate_vcs(&func);
    let _ = vcs;
}

#[test]
fn test_real_mir_generate_vcs_sum_to_loop() {
    // sum_to exercises CheckedBinaryOp asserts. `generate_vcs`
    // must emit at least one ArithmeticOverflow VC for the loop body.
    let func = load_fixture("test_functions__sum_to");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "sum_to loop must emit at least one ArithmeticOverflow VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_increment() {
    // ArithmeticOverflow VCs are emitted again. `increment` has
    // at least one CheckedBinaryOp + Assert(Overflow) pair, so at least one
    // ArithmeticOverflow VC is expected.
    let func = load_fixture("test_functions__increment");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "increment must emit at least one ArithmeticOverflow VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_wrapping_mul() {
    let func = load_fixture("test_functions__wrapping_mul");
    let vcs = generate_vcs(&func);
    let _ = vcs;
}

#[test]
fn test_real_mir_generate_vcs_all_fixtures() {
    let dir = fixture_dir();
    let mut count = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let json = std::fs::read_to_string(&path).unwrap();
        if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&json) {
            let _vcs = generate_vcs(&func);
            count += 1;
        }
    }
    assert!(count >= 10, "expected at least 10 fixtures, found {count}");
}

// a one-block function from raw locals + statements, for naming tests.
fn single_block_func(locals: Vec<LocalDecl>, stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "t".to_string(),
        def_path: "test::t".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn arr_literal_const_index_read_name_matches_aggregate_write_name() {
    // `let a = [1,2,3,4]; a[0] + a[1]` lowers the element reads as
    // dynamic `Index(local)` projections whose index local is a separate
    // constant temp. The read name must converge on the same `[c;min=N]` name
    // the array-aggregate element *write* uses, or the literal's values never
    // reach the overflow VC and the (safe) add false-fails.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
            LocalDecl { index: 4, ty: Ty::u32(), name: None },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Constant(ConstValue::Uint(1, 32)),
                        Operand::Constant(ConstValue::Uint(2, 32)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                        Operand::Constant(ConstValue::Uint(4, 32)),
                    ],
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
        ],
    );

    let read_place = Place { local: 1, projections: vec![Projection::Index(5)] };
    let write_place = aggregate_field_place(&Place::local(1), &AggregateKind::Array, 0, 4)
        .expect("array aggregate field place");

    assert_eq!(place_to_var_name(&func, &read_place), "a[0;min=4]");
    assert_eq!(place_to_var_name(&func, &write_place), "a[0;min=4]");
    assert_eq!(
        place_to_var_name(&func, &read_place),
        place_to_var_name(&func, &write_place),
        "const-index read must share the aggregate write's variable name"
    );

    assert_eq!(index_local_const(&func, 5), Some(0));
    assert!(array_local_index_naming_stable(&func, 1));
}

#[test]
fn arr_const_index_store_keeps_stable_naming() {
    // a CONST-index element store keeps stable naming. Its place name
    // `a[0;min=2]` converges with the array literal and with const-index reads, so
    // the store correctly overrides the literal under last-write-wins (seen_dests
    // within a block, extend_killing_redefs across blocks) — no stale-literal
    // contradiction, hence no false-PROVE. Contrast
    // arr_variable_index_store_suppresses_stable_naming, where a runtime index
    // forces the opaque fallback.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 2 };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Constant(ConstValue::Uint(0, 32)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ],
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            // a[_5] = 99 — a CONST-index element store (_5 == 0).
            Statement::Assign {
                place: Place { local: 1, projections: vec![Projection::Index(5)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(99, 32))),
                span: SourceSpan::default(),
            },
        ],
    );

    assert!(array_local_index_naming_stable(&func, 1));
    let read_place = Place { local: 1, projections: vec![Projection::Index(5)] };
    assert_eq!(place_to_var_name(&func, &read_place), "a[0;min=2]");
}

#[test]
fn arr_variable_index_store_suppresses_stable_naming() {
    // soundness anchor: a VARIABLE-index store could write ANY element,
    // so it must NOT be modeled as overriding a single element's literal — doing so
    // would leave the other elements' stale literals live and risk a false-PROVE.
    // Naming falls back to the opaque `[_i]` form (the whole array reads as free → a
    // sound false-FAIL) even for a const-index read, and the predicate returns false.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 2 };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
            LocalDecl { index: 7, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Constant(ConstValue::Uint(0, 32)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ],
                ),
                span: SourceSpan::default(),
            },
            // _5 = 0 — a constant read index.
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            // _7 = copy _0 — a non-constant (runtime) index.
            Statement::Assign {
                place: Place::local(7),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(0))),
                span: SourceSpan::default(),
            },
            // a[_7] = 99 — a VARIABLE-index element store.
            Statement::Assign {
                place: Place { local: 1, projections: vec![Projection::Index(7)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(99, 32))),
                span: SourceSpan::default(),
            },
        ],
    );

    assert!(!array_local_index_naming_stable(&func, 1));
    // Even the const-index read (_5 == 0) is destabilized by the variable write.
    let read_place = Place { local: 1, projections: vec![Projection::Index(5)] };
    assert_eq!(place_to_var_name(&func, &read_place), "a[_5]");
}

#[test]
fn arr_mut_borrow_suppresses_const_index_rename() {
    // soundness guard: a `&mut` of the array could mutate it through
    // the reference, so the const-index rename must be suppressed.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 2 };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
            LocalDecl { index: 6, ty: Ty::u32(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Constant(ConstValue::Uint(0, 32)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ],
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(6),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            },
        ],
    );

    assert!(!array_local_index_naming_stable(&func, 1));
    let read_place = Place { local: 1, projections: vec![Projection::Index(5)] };
    assert_eq!(place_to_var_name(&func, &read_place), "a[_5]");
}

#[test]
fn index_local_const_rejects_conflicting_and_nonconst_assignments() {
    // two differing constants (loop induction variable analog) or a
    // non-constant assignment must not resolve to a single known index.
    let conflicting = single_block_func(
        vec![LocalDecl { index: 5, ty: Ty::usize(), name: None }],
        vec![
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
                span: SourceSpan::default(),
            },
        ],
    );
    assert_eq!(index_local_const(&conflicting, 5), None);

    let nonconst = single_block_func(
        vec![
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("p".into()) },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
        ],
        vec![Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        }],
    );
    assert_eq!(index_local_const(&nonconst, 5), None);
}

#[test]
fn place_ty_resolves_nested_enum_variant_payload() {
    // `lower_enum_adt` flattens `Option<T>` to fields
    // `[__tag, __v1_0: T]` (variant 1 = Some, field 0). A MIR enum-payload read
    // is variant-relative — `[Downcast(1), Field(0)]` means "Some's field 0",
    // which must resolve to `T`, NOT the flat field 0 (`__tag`). Without this the
    // inner payload of `Option<Option<u32>>` resolves to the tag's Int and a
    // discriminant read on it false-fails as InvalidDiscriminant (nested_opt).
    let tag = || Ty::Int { width: 64, signed: true };
    let inner_opt = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Option".into(),
        fields: vec![("__tag".into(), tag()), ("__v1_0".into(), Ty::u32())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let outer_opt = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Option".into(),
        fields: vec![("__tag".into(), tag()), ("__v1_0".into(), inner_opt.clone())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: outer_opt.clone(), name: Some("o".into()) },
        ],
        vec![],
    );

    // Whole local is the outer enum.
    assert_eq!(place_ty(&func, &Place::local(1)), Some(outer_opt));

    // Some(_) payload of the OUTER enum is the inner Option (an Adt), not __tag.
    let inner_payload =
        Place { local: 1, projections: vec![Projection::Downcast(1), Projection::Field(0)] };
    assert_eq!(place_ty(&func, &inner_payload), Some(inner_opt));

    // Some(Some(_)) doubly-nested payload is the u32 value.
    let deep_payload = Place {
        local: 1,
        projections: vec![
            Projection::Downcast(1),
            Projection::Field(0),
            Projection::Downcast(1),
            Projection::Field(0),
        ],
    };
    assert_eq!(place_ty(&func, &deep_payload), Some(Ty::u32()));

    // verifier-perf equivalence: `place_ty_cow` MUST resolve byte-identically to the
    // owned `place_ty` for every projection shape — it is the same borrowed walk, only
    // the materialization is deferred. (`.into_owned()` reconstructs the owned result.)
    for place in [&Place::local(1), &inner_payload, &deep_payload] {
        assert_eq!(
            crate::place_ty_cow(&func, place).map(std::borrow::Cow::into_owned),
            place_ty(&func, place),
            "place_ty_cow must equal place_ty for {place:?}",
        );
    }
}

#[test]
fn operand_ty_cow_is_byte_identical_to_operand_ty() {
    // The borrowed `operand_ty_cow` / `place_ty_cow` are pure efficiency: for the
    // BARE FULL-VALUE read of a fat-ADT local (`Move(whole_local)` — the proof-combinator
    // family's case) the cow walk BORROWS the multi-MB declared root, while `operand_ty`
    // deep-clones it; the RESOLVED type must be byte-identical either way. This locks in
    // that VC-IDENTICAL property (a regression here would change a verdict).
    let fat = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Expr".into(),
        fields: vec![
            (
                "kind".into(),
                Ty::Adt { adt_kind: None, layout: None, 
                    variants: Vec::new(),
                    name: "ExprKind".into(),
                    fields: vec![("x".into(), Ty::u32())],
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
            ),
            ("flag".into(), Ty::Bool),
        ],
        disc_index_safe: false, faithful_enum_repr: None, enum_layout: None, };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fat.clone(), name: Some("e".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![],
    );

    // Bare full-value reads (the fat root) and a field projection and scalars.
    let cases = [
        Operand::Copy(Place::local(1)),             // whole fat Expr
        Operand::Move(Place::local(1)),             // whole fat Expr (move)
        Operand::Copy(Place::field(1, 1)),          // Expr.flag : Bool
        Operand::Copy(Place::local(2)),             // usize scalar
        Operand::Copy(Place::local(3)),             // bool scalar
        Operand::Constant(ConstValue::Uint(7, 32)), // constant
        Operand::Constant(ConstValue::Bool(true)),  // constant
    ];
    for op in &cases {
        assert_eq!(
            crate::operand_ty_cow(&func, op).map(std::borrow::Cow::into_owned),
            operand_ty(&func, op),
            "operand_ty_cow must equal operand_ty for {op:?}",
        );
    }
    // The whole-fat-Expr read resolves to the fat root unchanged (not a degraded leaf).
    assert_eq!(
        crate::operand_ty_cow(&func, &Operand::Move(Place::local(1)))
            .map(std::borrow::Cow::into_owned),
        Some(fat),
        "a bare full-value read must resolve to the exact declared type",
    );
}

#[test]
fn deref_of_reborrowed_payload_converges_to_referent_name() {
    // `match o { Some(v) if *v < 100 => *v + 1 }` on `o: &Option<u32>`
    // lowers the guard through a re-borrow round-trip (`_4 = &_3; _9 = *_4`) so
    // the guard reads `*_9` while the arithmetic reads `*_3`. Both alias the same
    // payload `((*o) as Some).0`; the deref names must converge on that referent
    // or the guard cannot constrain the overflow VC (a Goal-1 false-fail).
    let opt = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Option".into(),
        fields: vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v1_0".into(), Ty::u32()),
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let opt_ref = Ty::Ref { mutable: false, inner: Box::new(opt) };
    let payload = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Downcast(1), Projection::Field(0)],
    };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: opt_ref, name: Some("o".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                name: Some("v".into()),
            },
            LocalDecl { index: 4, ty: Ty::u32(), name: None },
            LocalDecl { index: 9, ty: Ty::u32(), name: None },
        ],
        vec![
            // _3 = &((*o) as Some).0
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Ref { mutable: false, place: payload.clone() },
                span: SourceSpan::default(),
            },
            // _4 = &_3
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(3) },
                span: SourceSpan::default(),
            },
            // _9 = *_4
            Statement::Assign {
                place: Place::local(9),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 4,
                    projections: vec![Projection::Deref],
                })),
                span: SourceSpan::default(),
            },
        ],
    );

    let canonical = place_to_var_name(&func, &payload);
    let via_v = place_to_var_name(&func, &Place { local: 3, projections: vec![Projection::Deref] });
    let via_reborrow =
        place_to_var_name(&func, &Place { local: 9, projections: vec![Projection::Deref] });

    assert_eq!(canonical, "o*@1.0");
    assert_eq!(via_v, canonical, "*v (arithmetic) must name the referent payload");
    assert_eq!(via_reborrow, canonical, "*(reborrow) (guard) must name the referent payload");
}

#[test]
fn deref_of_reassigned_reference_is_not_canonicalized() {
    // soundness guard: a reference local with more than one definition
    // has an ambiguous referent, so its deref must NOT be canonicalized (doing so
    // could merge distinct storage and mask a real bug). The name stays `r*`.
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                name: Some("r".into()),
            },
        ],
        vec![
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                span: SourceSpan::default(),
            },
        ],
    );
    let name = place_to_var_name(&func, &Place { local: 3, projections: vec![Projection::Deref] });
    assert_eq!(name, "r*", "ambiguous (twice-defined) reference must not canonicalize");
}

#[test]
fn place_ty_struct_field_without_downcast_stays_flat() {
    // regression guard: a struct field access has no Downcast, so
    // `Field(i)` must keep its flat lookup into the struct's fields.
    let s = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "S".into(),
        fields: vec![("x".into(), Ty::u32()), ("y".into(), Ty::Bool)],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: s, name: Some("s".into()) },
        ],
        vec![],
    );
    let f0 = Place { local: 1, projections: vec![Projection::Field(0)] };
    let f1 = Place { local: 1, projections: vec![Projection::Field(1)] };
    assert_eq!(place_ty(&func, &f0), Some(Ty::u32()));
    assert_eq!(place_ty(&func, &f1), Some(Ty::Bool));
}

#[test]
fn deref_shared_array_ref_const_index_converges() {
    // `a[2]` on `a: &[u32; 4]` lowers as `(*a)[idx]` with a separate
    // constant index temp per use, so the guard reads `(*a)[_4]` and the arithmetic
    // reads `(*a)[_7]`. Both name element 2 of the same (shared, hence immutable)
    // array and must converge on `a*[2;min=4]`, or the guard cannot constrain the
    // overflow VC — a Goal-1 false-fail.
    let arr = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let aref = Ty::Ref { mutable: false, inner: Box::new(arr) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: aref, name: Some("a".into()) },
            LocalDecl { index: 4, ty: Ty::usize(), name: None },
            LocalDecl { index: 7, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(7),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
                span: SourceSpan::default(),
            },
        ],
    );
    let guard = Place { local: 1, projections: vec![Projection::Deref, Projection::Index(4)] };
    let arith = Place { local: 1, projections: vec![Projection::Deref, Projection::Index(7)] };
    assert_eq!(place_to_var_name(&func, &guard), "a*[2;min=4]");
    assert_eq!(place_to_var_name(&func, &arith), "a*[2;min=4]");
}

#[test]
fn deref_shared_slice_ref_const_index_converges() {
    // `s[0]` on `s: &[u32]` lowers as `(*s)[idx]`. A shared slice
    // reference cannot mutate its pointee, so two constant-index reads observe the
    // same element and must converge on `s*[0;slice]`.
    let slice = Ty::Slice { elem: Box::new(Ty::u32()) };
    let sref = Ty::Ref { mutable: false, inner: Box::new(slice) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: sref, name: Some("s".into()) },
            LocalDecl { index: 5, ty: Ty::usize(), name: None },
            LocalDecl { index: 9, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(9),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
        ],
    );
    let guard = Place { local: 1, projections: vec![Projection::Deref, Projection::Index(5)] };
    let arith = Place { local: 1, projections: vec![Projection::Deref, Projection::Index(9)] };
    assert_eq!(place_to_var_name(&func, &guard), "s*[0;slice]");
    assert_eq!(place_to_var_name(&func, &arith), "s*[0;slice]");
}

#[test]
fn deref_mut_array_ref_const_index_does_not_converge() {
    // soundness guard: a *mutable* reference may have its pointee written
    // between reads, so `(*m)[c]` must NOT collapse to a const-index name (doing so
    // could merge a pre-write read with a post-write read and mask a real overflow).
    let arr = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let mref = Ty::Ref { mutable: true, inner: Box::new(arr) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: mref, name: Some("m".into()) },
            LocalDecl { index: 4, ty: Ty::usize(), name: None },
        ],
        vec![Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
            span: SourceSpan::default(),
        }],
    );
    let p = Place { local: 1, projections: vec![Projection::Deref, Projection::Index(4)] };
    assert_eq!(place_to_var_name(&func, &p), "m*[_4]");
}

#[test]
fn double_deref_through_param_ref_converges() {
    // `**r` on `r: &&u32` lowers each use as `_a = *r; *_a`, with a fresh
    // intermediate reference per use (`_6 = *r` for the guard, `_7 = *r` for the
    // arithmetic). Both `*_6` and `*_7` equal `**r` and must converge on `r**`, or
    // the guard cannot constrain the overflow VC — a Goal-1 false-fail.
    let u32ref = Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) };
    let rref = Ty::Ref { mutable: false, inner: Box::new(u32ref.clone()) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: rref, name: Some("r".into()) },
            LocalDecl { index: 6, ty: u32ref.clone(), name: None },
            LocalDecl { index: 7, ty: u32ref, name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(6),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Deref],
                })),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(7),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Deref],
                })),
                span: SourceSpan::default(),
            },
        ],
    );
    let guard = Place { local: 6, projections: vec![Projection::Deref] };
    let arith = Place { local: 7, projections: vec![Projection::Deref] };
    assert_eq!(place_to_var_name(&func, &guard), "r**");
    assert_eq!(place_to_var_name(&func, &arith), "r**");
}

#[test]
fn deref_shared_nested_array_ref_const_index_converges() {
    // (generalized): `(*a)[1][2]` on `a: &[[u32; 8]; 8]` lowers with a
    // fresh constant index temp at *each* dimension per use, so the guard reads
    // `(*a)[_4][_6]` and the arithmetic reads `(*a)[_9][_11]`. Every index is a
    // shared-ref-rooted constant, so all four name the same element and the two
    // reads must converge on `a*[1;min=8][2;min=8]`. The deeper (pos 2) segment is
    // the case the original pos==1-only Shape B missed — it requires walking the
    // prefix `[Deref, Index(const)]` and proving each step is immutable.
    let inner = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let outer = Ty::Array { elem: Box::new(inner), len: 8 };
    let aref = Ty::Ref { mutable: false, inner: Box::new(outer) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: aref, name: Some("a".into()) },
            LocalDecl { index: 4, ty: Ty::usize(), name: None },
            LocalDecl { index: 6, ty: Ty::usize(), name: None },
            LocalDecl { index: 9, ty: Ty::usize(), name: None },
            LocalDecl { index: 11, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(6),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(9),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(11),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
                span: SourceSpan::default(),
            },
        ],
    );
    let guard = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(4), Projection::Index(6)],
    };
    let arith = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(9), Projection::Index(11)],
    };
    assert_eq!(place_to_var_name(&func, &guard), "a*[1;min=8][2;min=8]");
    assert_eq!(place_to_var_name(&func, &arith), "a*[1;min=8][2;min=8]");
}

#[test]
fn deref_shared_struct_field_array_const_index_converges() {
    // (generalized): `(*b).data[0]` on `b: &Buf { data: [u32; 4] }` lowers
    // as `(*b).0[_i]` with a fresh constant index temp per use, so the guard reads
    // `(*b).0[_4]` and the arithmetic reads `(*b).0[_7]`. The array sits behind a
    // shared-ref Deref then a struct Field — both immutable navigation steps — so the
    // two reads must converge on `b*.0[0;min=4]`. Field-in-prefix is the second case
    // the pos==1-only Shape B missed.
    let arr = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let buf = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Buf".to_string(),
        fields: vec![("data".to_string(), arr)],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let bref = Ty::Ref { mutable: false, inner: Box::new(buf) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: bref, name: Some("b".into()) },
            LocalDecl { index: 4, ty: Ty::usize(), name: None },
            LocalDecl { index: 7, ty: Ty::usize(), name: None },
        ],
        vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(7),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                span: SourceSpan::default(),
            },
        ],
    );
    let guard = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(0), Projection::Index(4)],
    };
    let arith = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(0), Projection::Index(7)],
    };
    assert_eq!(place_to_var_name(&func, &guard), "b*.0[0;min=4]");
    assert_eq!(place_to_var_name(&func, &arith), "b*.0[0;min=4]");
}

#[test]
fn deref_shared_array_nonconst_prefix_index_does_not_converge() {
    // soundness guard: a *non-constant* index anywhere in the prefix makes
    // the path itself unstable across reads (the temp need not hold the same value),
    // so a deeper constant index must NOT collapse to a `[c;min=N]` name. Here the
    // outer index `_4` is a runtime value (never assigned a constant), so `(*a)[_4][2]`
    // must stay fully opaque — `a*[_4][_6]` — keeping the VC unconstrained (fails
    // closed) rather than wrongly equating two reads at possibly-different outer rows.
    let inner = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let outer = Ty::Array { elem: Box::new(inner), len: 8 };
    let aref = Ty::Ref { mutable: false, inner: Box::new(outer) };
    let func = single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: aref, name: Some("a".into()) },
            // _4 is a dynamic outer index: declared but never assigned a constant.
            LocalDecl { index: 4, ty: Ty::usize(), name: None },
            LocalDecl { index: 6, ty: Ty::usize(), name: None },
        ],
        vec![Statement::Assign {
            place: Place::local(6),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 64))),
            span: SourceSpan::default(),
        }],
    );
    let p = Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(4), Projection::Index(6)],
    };
    assert_eq!(place_to_var_name(&func, &p), "a*[_4][_6]");
}

// minimal `safe_struct_payload`-shaped function. Local 1 "s" is the enum
// arg; `_3` "p" is the moved-out payload (`_3 = move (_1 as v0).0`); `_4` "p" is the
// guard's reborrow (`_4 = &(_1 as v0).0`). `extra` lets a test inject a mutation
// that must defeat the value-alias fold. Types are irrelevant to naming, so all
// locals are u32.
fn struct_payload_alias_fn(extra: Vec<Statement>) -> VerifiableFunction {
    let payload =
        || Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let mut stmts = vec![
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref { mutable: false, place: payload() },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Move(payload())),
            span: SourceSpan::default(),
        },
    ];
    stmts.extend(extra);
    single_block_func(
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("s".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl { index: 5, ty: Ty::u32(), name: None },
        ],
        stmts,
    )
}

#[test]
fn struct_payload_moved_base_local_field_converges_with_guard_reborrow() {
    // `match s { Shape::P(p) if p.x < 100 => p.x + 1, _ => 0 }`. The guard
    // reads the payload field through a reborrow (`(*_4).0`) and the overflow reads
    // it through the moved base local (`_3.0`). Both must canonicalize to the source
    // field name `s@0.0.0`, or the guard never constrains the overflow VC.
    let func = struct_payload_alias_fn(vec![]);
    let source = Place {
        local: 1,
        projections: vec![Projection::Downcast(0), Projection::Field(0), Projection::Field(0)],
    };
    let source_name = place_to_var_name(&func, &source);
    assert_eq!(source_name, "s@0.0.0");

    let overflow_operand = Place { local: 3, projections: vec![Projection::Field(0)] };
    assert_eq!(place_to_var_name(&func, &overflow_operand), source_name);

    let guard_operand =
        Place { local: 4, projections: vec![Projection::Deref, Projection::Field(0)] };
    assert_eq!(place_to_var_name(&func, &guard_operand), source_name);
}

#[test]
fn struct_payload_fold_blocked_by_mut_borrow_of_source() {
    // Soundness: a `&mut` of the source enum could mutate the payload after the move,
    // so `_3.0` must keep its opaque name rather than aliasing a possibly-stale
    // source field. Fail-closed to a false-fail, never a false-prove. The opaque name is
    // the unique per-local `_3.0`: locals 3 and 4 BOTH carry source name "p", so the
    // name-collision disambiguation (place_to_var_name) drops the ambiguous "p" — which
    // also closes a latent `_3.0`/`_4.0` fact leak.
    let func = struct_payload_alias_fn(vec![Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
        span: SourceSpan::default(),
    }]);
    let overflow_operand = Place { local: 3, projections: vec![Projection::Field(0)] };
    assert_eq!(place_to_var_name(&func, &overflow_operand), "_3.0");
}

#[test]
fn struct_payload_fold_blocked_by_projected_store_to_source() {
    // Soundness: a store through the source (`_1.1 = …`) mutates it in place, so the
    // moved-out `_3` may differ from the live source field. Refuse the rebase.
    let func = struct_payload_alias_fn(vec![Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Field(1)] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    }]);
    let overflow_operand = Place { local: 3, projections: vec![Projection::Field(0)] };
    // `_3.0`: locals 3 and 4 share source name "p", so the name-collision
    // disambiguation uses the unique per-local name (see the mut-borrow test above).
    assert_eq!(place_to_var_name(&func, &overflow_operand), "_3.0");
}

#[test]
fn struct_payload_fold_blocked_by_second_def_of_alias() {
    // Soundness: a second whole-store to `_3` means it no longer uniquely holds the
    // moved payload; `unique_whole_local_def` returns None and the fold is refused.
    let func = struct_payload_alias_fn(vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    }]);
    let overflow_operand = Place { local: 3, projections: vec![Projection::Field(0)] };
    // `_3.0`: locals 3 and 4 share source name "p", so the name-collision
    // disambiguation uses the unique per-local name (see the mut-borrow test above).
    assert_eq!(place_to_var_name(&func, &overflow_operand), "_3.0");
}

// =====================================================================
// Trust: McCarthy array-theory channel for straight-line variable-index
// array code. Eligibility, version naming, no-join detection, and a
// VC-shape check that an eligible array read emits a `Select`-based
// formula (never a `[c;min=len]` free var).
// =====================================================================

/// A no-join function with a `[u32;N]` array param (`local 1`), a non-constant
/// index param (`local 2`), and the given body statements. `local 0` is the
/// return, `local 3` a u32 temp. Single block => no join.
fn array_param_fn(arr_len: u64, stmts: Vec<Statement>) -> VerifiableFunction {
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: arr_len };
    VerifiableFunction {
        name: "arr".to_string(),
        def_path: "test::arr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// A variable-index element store `a[i] = w`.
fn variable_index_store() -> Statement {
    Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Index(2)] },
        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
        span: SourceSpan::default(),
    }
}

#[test]
fn array_theory_local_some_for_param_with_variable_index_store_no_join() {
    // `[u32;8]` param, single block (no join), a variable-index store => eligible.
    let func = array_param_fn(8, vec![variable_index_store()]);
    let model = array_theory_local(&func, 1).expect("eligible array-theory local");
    assert_eq!(model.len, Some(8));
    assert_eq!(model.elem_sort, Sort::Int);
    // Disjoint from the scalar `[c;min=len]` channel by construction.
    assert!(!array_local_index_naming_stable(&func, 1));
}

#[test]
fn array_theory_local_none_for_reassigned_index_local() {
    // Hole 2 (index staleness): the store index local `i` (a param) is reassigned
    // in the body, so a store `Store(v,i,w)` and a later read `Select(v,i)` at the
    // same SMT name would conflate the store-time and read-time index (ROW1 fires
    // spuriously) -> false-PROVE. The channel must disengage. `a[i]=w; i = 3`.
    let reassign_i = Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 64))),
        span: SourceSpan::default(),
    };
    let func = array_param_fn(8, vec![variable_index_store(), reassign_i]);
    assert!(!index_local_stable(&func, 2), "a reassigned param index is not stable");
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn array_theory_local_none_for_index_reassigned_via_call_dest() {
    // Hole 2 via a Terminator::Call: the index local `i` (param, local 2) is
    // reassigned by `i = f()` (a Call whose dest is local 2). A Statement::Assign
    // -only scan misses this, so the index must be checked against Call dests too
    // -- else `a[i]=w; i=f(); a[i]` false-PROVES.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let func = VerifiableFunction {
        name: "arr_idx_call".to_string(),
        def_path: "test::arr_idx_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![variable_index_store()],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "reidx".to_string(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(2), // i = reidx(i)
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(!index_local_stable(&func, 2), "index reassigned via Call dest is not stable");
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn array_theory_local_none_for_whole_array_call_reseat() {
    // Variant 3: a whole-array Call dest (`a = fresh()`) reseats the array to an
    // unmodeled value, invalidating the McCarthy version chain seeded before the
    // call. `array_local_escapes` must flag it (whole-local Call dest).
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let func = VerifiableFunction {
        name: "arr_reseat".to_string(),
        def_path: "test::arr_reseat".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![variable_index_store()],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "fresh".to_string(),
                        args: vec![],
                        dest: Place::local(1), // a = fresh()  (whole-array reseat)
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(array_local_escapes(&func, 1), "whole-array Call reseat must escape");
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn v2_widening_bv_source_declines_reassigned_operand() {
    // Cross-feature audit false-PROVE: `let w = x as i64; w = big; w*w`. The mul
    // operand `w` must only be narrowed to its cast SOURCE width when the cast is
    // its UNIQUE reaching definition. A later reassignment (`w = big`) makes the
    // real value full-range i64, so narrowing it would structurally pin the
    // operand to [-2^31, 2^31-1] and vacuously prove `big*big` no-overflow.
    // locals: 0=ret(i64), 1=x(i32 param), 2=big(i64 param), 3=w(i64).
    let mk = |reassign: bool| {
        let mut stmts = vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i64()),
            span: SourceSpan::default(),
        }];
        if reassign {
            stmts.push(Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            });
        }
        VerifiableFunction {
            name: "wmul".to_string(),
            def_path: "test::wmul".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i64(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i64(), name: Some("big".into()) },
                    LocalDecl { index: 3, ty: Ty::i64(), name: Some("w".into()) },
                ],
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
                arg_count: 2,
                return_ty: Ty::i64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };
    let op = Operand::Copy(Place::local(3));
    // Single-def widening: narrows to source width 32, signed (the true positive).
    assert_eq!(crate::generate::v2_widening_bv_source(&mk(false), &op, 64), Some((32, true)));
    // Reassigned: MUST decline so the operand stays full-width (sound false-FAIL).
    assert_eq!(crate::generate::v2_widening_bv_source(&mk(true), &op, 64), None);
}

#[test]
fn v2_widening_bv_source_declines_call_and_binop_reassign() {
    // Convergence-audit hardening: the widening cast operand must ALSO decline
    // when reassigned via a `Terminator::Call` dest (`w = f()`) or a `BinaryOp`
    // (`w = w + 1`), not only a plain `Use`. `index_local_stable` counts both as a
    // second whole-local definition, so `v2_widening_bv_source` returns None and
    // the operand stays full-width (sound). locals: 0=ret(i64), 1=x(i32 param),
    // 2=w(i64).
    let cast_w = || Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i64()),
        span: SourceSpan::default(),
    };
    let func = |stmts: Vec<Statement>, term: Terminator| VerifiableFunction {
        name: "wmul2".to_string(),
        def_path: "test::wmul2".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("w".into()) },
            ],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts, terminator: term },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let op = Operand::Copy(Place::local(2));
    // (b) Call-dest reassign: `w = x as i64;` then `w = f()` (Call dest into w).
    let call_fn = func(
        vec![cast_w()],
        Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "f".to_string(),
            args: vec![],
            dest: Place::local(2),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
        },
    );
    assert_eq!(
        crate::generate::v2_widening_bv_source(&call_fn, &op, 64),
        None,
        "cast operand reassigned via Call dest must decline (full-width fallback)"
    );
    // (a) BinaryOp reassign: `w = x as i64; w = w + 1`.
    let binop_fn = func(
        vec![
            cast_w(),
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
                span: SourceSpan::default(),
            },
        ],
        Terminator::Return,
    );
    assert_eq!(
        crate::generate::v2_widening_bv_source(&binop_fn, &op, 64),
        None,
        "cast operand reassigned via BinaryOp must decline (full-width fallback)"
    );
}

#[test]
fn const_folding_index_store_is_a_counted_array_element_store() {
    // Hole 1: a const-folding `a[Index(j)]` store (j == const) must still be a
    // counted array-theory element store. The scalar `[c;min=len]` path is
    // bypassed for an eligible array, so if such a store were dropped it would
    // vanish entirely and a same-slot read would go stale -> false-PROVE.
    let set_idx = Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 64))),
        span: SourceSpan::default(),
    };
    let store = Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Index(2)] },
        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
        span: SourceSpan::default(),
    };
    let func = array_param_fn(8, vec![set_idx, store]);
    assert!(index_local_const(&func, 2).is_some(), "index const-folds to 5");
    assert!(
        is_array_theory_element_store(&func, 1, &func.body.blocks[0].stmts[1]),
        "a const-folding index store must be a counted array element store"
    );
}

#[test]
fn array_theory_local_none_when_function_has_if_else_join() {
    // Same array + variable-index store, but the CFG has a join block (two preds).
    // bb0: SwitchInt -> bb1 / bb2 ; bb1: Goto bb3 ; bb2: Goto bb3 ; bb3: Return.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let func = VerifiableFunction {
        name: "arr_join".to_string(),
        def_path: "test::arr_join".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![variable_index_store()],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(!func_has_no_join(&func), "bb3 has two predecessors");
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn array_theory_local_none_for_mutable_borrow_escape() {
    // `&mut a[i]` (a mutable borrow whose base is the array) escapes => ineligible.
    let borrow = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Index(2)] },
        },
        span: SourceSpan::default(),
    };
    let func = array_param_fn(8, vec![variable_index_store(), borrow]);
    assert!(array_local_escapes(&func, 1));
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn array_theory_local_none_for_nonscalar_elem() {
    // Slice element and Adt element are non-scalar => ineligible even with a
    // variable-index store in a no-join function.
    let slice_arr = Ty::Array { elem: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }), len: 4 };
    let func = VerifiableFunction {
        name: "arr_slice".to_string(),
        def_path: "test::arr_slice".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: slice_arr, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![variable_index_store()],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_eq!(array_theory_local(&func, 1), None);
}

#[test]
fn array_term_var_name_shape() {
    let f = array_term_var(1, 2, Sort::Int);
    match &f {
        Formula::Var(name, sort) => {
            assert_eq!(name, "arr$1$v2");
            assert_eq!(*sort, Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        }
        other => panic!("expected Var, got {other:?}"),
    }
}

#[test]
fn func_has_no_join_true_for_single_block() {
    let func = array_param_fn(8, vec![variable_index_store()]);
    assert!(func_has_no_join(&func));
}

#[test]
fn func_has_no_join_false_for_diamond_join() {
    // bb0: SwitchInt -> bb1 / bb2 ; bb1: Goto bb3 ; bb2: Goto bb3 ; bb3: Return.
    let func = VerifiableFunction {
        name: "diamond".to_string(),
        def_path: "test::diamond".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(!func_has_no_join(&func));
}

#[test]
fn array_theory_read_emits_select_based_formula() {
    // Straight-line: `a[i] = w; t = a[i]; q = w / t`. The division-by-zero VC on
    // `t` carries the block def `t == Select(arr$1$v1, i)`, so SOME generated VC
    // formula contains array theory and NONE names a `[c;min=len]` free var.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 8 };
    let func = VerifiableFunction {
        name: "arr_read".to_string(),
        def_path: "test::arr_read".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("w".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("t".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // a[i] = w  (variable-index element store -> eligible).
                    variable_index_store(),
                    // t = a[i]  (variable-index element read -> Select).
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    },
                    // q = w / t  (division-by-zero VC references t).
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(array_theory_local(&func, 1).is_some(), "array must be eligible");

    let vcs = generate_vcs(&func);
    assert!(!vcs.is_empty(), "expected at least the division-by-zero VC");

    // Some VC formula must use array theory (Select/Store or an Array-sorted var).
    assert!(
        vcs.iter().any(|vc| vc.formula.has_arrays()),
        "an eligible array read must produce a Select-based formula"
    );

    // No VC formula may name a `[c;min=len]` literal free var for this array — the
    // array-theory channel replaces that scalar naming entirely.
    for vc in &vcs {
        for name in vc.formula.free_variables() {
            assert!(
                !name.contains(";min="),
                "array-theory VC must not contain a [c;min=len] free var, found {name}"
            );
        }
    }
}

/// loop-backedge regression: a loop variable reassigned on the back-edge
/// via a `Call { dest }` (not a statement assign) must HAVOC the pre-loop fact at
/// the loop header. Before the fix, `v2_path_def_fixpoint` never generated a
/// killing def for the Call-dest reassignment, so the back-edge re-entered the
/// header carrying the unchanged pre-loop fact `i == 0`; the header intersection
/// did not shrink, `i == 0` survived into the loop body, and the loop-body
/// overflow VC on `i + i` was vacuously discharged (`0 + 0` never overflows) —
/// a false-PROVE of a real overflow.
#[test]
fn loop_backedge_call_dest_havocs_preloop_fact() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    // Loop where `i` (_1) is reassigned in the body via a CALL DEST (not a
    // statement assign). The loop-body overflow VC is `i + i`.
    //   bb0: _1 = 0; goto bb1
    //   bb1: _2 = (_1 < 4_000_000_000); switch _2 [0 -> bb4] else bb2
    //   bb2: _3 = CheckedAdd(_1, _1); assert(!_3.1) -> bb3
    //   bb3: _1 = call f();  goto bb1            <-- back-edge, Call-dest reassign
    //   bb4: return
    let func = VerifiableFunction {
        name: "call_loop".to_string(),
        def_path: "call_loop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("_3".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(4_000_000_000, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place {
                            local: 3,
                            projections: vec![trust_types::Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "next_i".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // The loop header (bb1) is reached from the entry edge (`i == 0`) and the
    // back-edge (bb3, which reassigns `i` via its Call dest). Because the
    // reassignment havocs `i`, the header intersection must NOT carry the stale
    // pre-loop fact `i == 0`.
    let map = crate::generate::v2_build_path_definition_map_pub(&func);
    let header_facts = map.get(&BlockId(1)).cloned().unwrap_or_default();
    let stale_i_eq_0 =
        Formula::Eq(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(0)));
    assert!(
        !header_facts.contains(&stale_i_eq_0),
        "loop header must HAVOC `i` across the Call-dest back-edge; stale `i == 0` \
         leaked into header facts: {header_facts:?}"
    );

    // The loop-body overflow VC on `i + i` must remain satisfiable (a real
    // overflow when `i` is large), i.e. it must NOT be vacuously discharged by a
    // stale `i == 0` hypothesis. Pin that the conjoined formula does not contain
    // the stale fact as a top-level hypothesis.
    let vcs = generate_vcs(&func);
    let overflow_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("expected an ArithmeticOverflow VC for `i + i`");
    assert!(
        !formula_contains_subformula(&overflow_vc.formula, &stale_i_eq_0),
        "loop-body overflow VC must not carry the stale `i == 0` hypothesis that \
         vacuously proves the overflow; formula: {:?}",
        overflow_vc.formula
    );
}

#[test]
fn call_arg_mut_ref_havocs_pointee_fact() {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    // bb0: x = 5; p = &mut x;  goto bb1
    // bb1: _3 = call mutate(move p) -> bb2     <-- &mut x escapes into the call
    // bb2: return
    // `mutate` can write any value through `&mut x`, so the post-call facts must
    // NOT carry the stale pre-call `x == 5` (soundness round-11).
    let func = VerifiableFunction {
        name: "mut_ref_escape".to_string(),
        def_path: "mut_ref_escape".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 3, ty: Ty::Unit, name: Some("_3".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "mutate".to_string(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let map = crate::generate::v2_build_path_definition_map_pub(&func);
    let post_call_facts = map.get(&BlockId(2)).cloned().unwrap_or_default();
    let stale_x_eq_5 =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    assert!(
        !post_call_facts.contains(&stale_x_eq_5),
        "a Call receiving `&mut x` must HAVOC `x`; stale `x == 5` survived: {post_call_facts:?}"
    );
}

#[test]
fn store_through_pointer_havocs_referent_fact() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        VerifiableFunction,
    };
    // bb0: x = 5; r = &mut x; *r = 4_000_000_000; t = CheckedAdd(x, x); assert(!t.1) -> bb1
    // bb1: return
    // `*r = 4e9` mutates x, so the `x + x` overflow VC must NOT carry the stale
    // `x == 5` (which would vacuously prove no-overflow). With x = 4e9, x + x
    // overflows u32, so the VC must be satisfiable (Failed), not Proved.
    let func = VerifiableFunction {
        name: "store_through_ptr".to_string(),
        def_path: "store_through_ptr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("t".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place { local: 2, projections: vec![Projection::Deref] },
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                                4_000_000_000,
                                32,
                            ))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let stale_x_eq_5 =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    let vcs = generate_vcs(&func);
    let overflow_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("expected an ArithmeticOverflow VC for `x + x`");
    assert!(
        !formula_contains_subformula(&overflow_vc.formula, &stale_x_eq_5),
        "store-through-pointer `*r = v` must HAVOC the referent `x`; stale `x == 5` \
         leaked into the overflow VC and vacuously proves it: {:?}",
        overflow_vc.formula
    );
}

// SOUNDNESS regression (staleness class, cast-laundered pointer channel). A store
// `*p = v` through `p = &mut x as *mut u32` gives `p` a UNIQUE def (the Cast) — so
// the OLD havoc gate (`unique_whole_local_def(p).is_none()`) did NOT fire — and
// `resolve_referent` cannot fold the Cast, so `*p` names the opaque `p*` (never
// overlapping `x`). The stale `x == 5` thus leaked into the `x + x` overflow VC,
// vacuously PROVING no-overflow while live `x = 4e9` overflows u32.
// `deref_pointer_is_opaque` now treats the cast-laundered pointer as opaque.
#[cfg(test)]
#[test]
fn cast_laundered_pointer_store_havocs_referent_fact() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        VerifiableFunction,
    };
    let func = VerifiableFunction {
        name: "cast_laundered_store".to_string(),
        def_path: "cast_laundered_store".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("tmp".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("t".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Cast(
                                Operand::Copy(Place::local(2)),
                                Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place { local: 3, projections: vec![Projection::Deref] },
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                                4_000_000_000,
                                32,
                            ))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place {
                            local: 4,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let stale_x_eq_5 =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    let overflow_vc = generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("expected an ArithmeticOverflow VC");
    assert!(
        !formula_contains_subformula(&overflow_vc.formula, &stale_x_eq_5),
        "cast-laundered `*p = v` must havoc referent `x`; stale `x == 5` leaked: {:?}",
        overflow_vc.formula
    );
}

// SOUNDNESS regression (staleness class, deref-store channel): the single-borrow
// test above, but RESEATING `r` (a SECOND `r = &mut x`) before `*r = 4e9`. The
// reseat defeats the round-12 `*r -> x` canonicalization fold, so the store names
// the opaque `r*` instead of `x`. Before the fix, the redef-kill missed the
// mutation and the stale `x == 5` leaked into the `x + x` overflow VC, vacuously
// PROVING no-overflow while the live `x = 4e9` actually overflows u32 (a confirmed
// false-PROVE). `deref_store_havoc_names` now havocs every mutably-borrowed local
// on a non-canonicalizable deref-store, dropping the stale fact.
#[cfg(test)]
#[test]
fn reseated_ptr_deref_store_havocs_referent_fact() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        VerifiableFunction,
    };
    let reseat = |reseated: bool| {
        let mut stmts = vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            },
        ];
        if reseated {
            // second whole-local def of `r` -> unique_whole_local_def(r) = None
            stmts.push(Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            });
        }
        stmts.push(Statement::Assign {
            place: Place { local: 2, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(4_000_000_000, 32))),
            span: SourceSpan::default(),
        });
        stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(1)),
            ),
            span: SourceSpan::default(),
        });
        VerifiableFunction {
            name: "reseated_store_through_ptr".to_string(),
            def_path: "reseated_store_through_ptr".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("r".into()),
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("t".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts,
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place {
                                local: 3,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };
    let stale_x_eq_5 =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    let overflow_formula = |reseated: bool| {
        generate_vcs(&reseat(reseated))
            .into_iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("expected an ArithmeticOverflow VC")
            .formula
    };
    // The reseated deref-store must HAVOC `x` exactly like the single-borrow case.
    assert!(
        !formula_contains_subformula(&overflow_formula(true), &stale_x_eq_5),
        "reseated `*r = v` must havoc referent `x`; stale `x == 5` leaked and vacuously proves \
         the overflow VC"
    );
    // Sanity: the single-borrow variant (no reseat) is also havoced (owner's invariant).
    assert!(
        !formula_contains_subformula(&overflow_formula(false), &stale_x_eq_5),
        "single-borrow `*r = v` must havoc referent `x`"
    );
}

// SOUNDNESS regression (staleness class, same-block compare-then-reassign):
// `c = (hi <= 1000); hi = big; switch(c) { _ => bb1 }`, bb1: `hi + hi` overflow.
// The guard resolves to `hi <= 1000` and is added on the edge to bb1 AFTER `hi`
// is reassigned in bb0 — past the path-guard inherited-kill. Before the fix the
// stale `hi <= 1000` leaked into the overflow VC, vacuously PROVING `hi + hi`
// non-overflowing while the live `hi = big` can be u32::MAX. The comparison
// resolver now withholds a guard whose operand is reassigned later in the block.
#[cfg(test)]
#[test]
fn same_block_compare_then_reassign_drops_stale_guard() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        VerifiableFunction,
    };
    let build = |reassign: bool| {
        let mut bb0 = vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1000, 32)),
            ),
            span: SourceSpan::default(),
        }];
        if reassign {
            bb0.push(Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            });
        }
        VerifiableFunction {
            name: "v2_compare_then_reassign".to_string(),
            def_path: "test::v2_compare_then_reassign".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
                    LocalDecl {
                        index: 4,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("t".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: bb0,
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(3)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place {
                                local: 4,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };
    let overflow_smt = |reassign: bool| {
        generate_vcs(&build(reassign))
            .into_iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("overflow VC")
            .formula
            .to_smtlib()
    };
    // Reassigned: the resolved guard `hi <= 1000` is stale and must be withheld.
    assert!(
        !overflow_smt(true).contains("(<= hi 1000)"),
        "stale guard `hi <= 1000` must be withheld when `hi` is reassigned after the comparison; \
         got {}",
        overflow_smt(true)
    );
    // Control: no reassignment -> the guard is live and resolves normally.
    assert!(
        overflow_smt(false).contains("(<= hi 1000)"),
        "a live comparison guard must still resolve when the operand is not reassigned; got {}",
        overflow_smt(false)
    );
}

// SOUNDNESS regression (staleness class, cross-block BitAnd range guard):
// bb0 `_4 = (x>=10) & (x<=20)`; bb1 `x = big; switch(_4)`; bb2 `x*x` overflow.
// `(L..=U).contains(&x)` lowers to the BitAnd; the guard resolves to
// `And(x>=10, x<=20)` and is added on the bb1->bb2 edge AFTER bb1 reassigned `x`.
// The path-guard inherited-kill never checks the freshly-added switch guard
// against bb1's redef, and the same-block comparison gate is bb0-scoped — so the
// stale `x<=20` leaked into the overflow VC, false-PROVING `x*x` non-overflowing
// while the live `x = big` overflows. The BitAnd leaf resolution now fails closed
// on a whole-function-unstable operand.
#[cfg(test)]
#[test]
fn cross_block_bitand_range_guard_dropped_on_reassign() {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        VerifiableFunction,
    };
    let build = |reassign: bool| {
        let mut bb1 = vec![];
        if reassign {
            bb1.push(Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(4_000_000_000, 32))),
                span: SourceSpan::default(),
            });
        }
        VerifiableFunction {
            name: "bitand_range_reassign".to_string(),
            def_path: "test::bitand_range_reassign".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("ge".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("le".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("inrange".into()) },
                    LocalDecl {
                        index: 5,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("t".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Ge,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(10, 32)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Le,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(20, 32)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::BitAnd,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Copy(Place::local(3)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: bb1,
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(4)),
                            targets: vec![(0, BlockId(3))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Mul,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place {
                                local: 5,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Mul),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };
    let overflow_smt = |reassign: bool| {
        generate_vcs(&build(reassign))
            .into_iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("overflow VC")
            .formula
            .to_smtlib()
    };
    // Reassigned: S2c — the range guard is no longer WITHHELD; it is conjoined
    // EXEMPT (bare `x`, entry) while the reassignment `x = 4e9` carries a versioned
    // `x#token`. Soundness = name-disjointness: the bare guard `(<= x 20)` cannot
    // bound the reassigned overflow, so the bare reassignment atom `(= x 4000000000)`
    // must be ABSENT (it is versioned), disjoint from the guard's bare `x`.
    let reassigned = overflow_smt(true);
    assert!(
        !reassigned.contains("(= x 4000000000)"),
        "the reassignment must be versioned (`x#token`), DISJOINT from the bare stale \
         guard `x` (else false-PROVE); got {reassigned}"
    );
    // Control: no reassignment -> the range guard is live and resolves.
    assert!(
        overflow_smt(false).contains("(<= x 20)"),
        "a live range guard must still resolve when the operand is not reassigned; got {}",
        overflow_smt(false)
    );
}

/// Recursively test whether `needle` appears anywhere inside `haystack`.
#[cfg(test)]
fn formula_contains_subformula(haystack: &Formula, needle: &Formula) -> bool {
    if haystack == needle {
        return true;
    }
    match haystack {
        Formula::And(items) | Formula::Or(items) => {
            items.iter().any(|f| formula_contains_subformula(f, needle))
        }
        Formula::Not(inner) => formula_contains_subformula(inner, needle),
        Formula::Eq(a, b) | Formula::Lt(a, b) | Formula::Le(a, b) | Formula::Gt(a, b) => {
            formula_contains_subformula(a, needle) || formula_contains_subformula(b, needle)
        }
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Store-side / reference-side index bounds checks.
//
// Before this recognizer, index-bounds obligations only fired on READ
// projections (`let x = arr[i]`). STORE-side (`arr[i] = v`) and REFERENCE-side
// (`&arr[i]`, `&mut arr[i]`, `&raw mut arr[i]`, compiler-inserted
// `CopyForDeref(arr[i])`) index projections received ZERO bounds check, so an
// out-of-bounds write or borrow was silently reported safe. These tests pin the
// fire-on-bug behavior (an unguarded index emits the same `index < len`
// obligation the read path uses) and the no-false-positive behavior (a
// dominating `if i < arr.len()` guard discharges it to UNSAT, i.e. proves).
// ----------------------------------------------------------------------------

/// Build `fn f(arr: [u32;4], i: usize, v: u32)` whose single block performs a
/// bare, unguarded `arr[i] = v` store (the `rvalue` argument lets each test
/// swap in a Ref / AddressOf / CopyForDeref instead).
fn index_projection_func(dest: Place, rvalue: Rvalue, dest_local0_ty: Ty) -> VerifiableFunction {
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let return_ty = dest_local0_ty.clone();
    VerifiableFunction {
        name: "f".into(),
        def_path: "store_bounds::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_local0_ty, name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign { place: dest, rvalue, span: SourceSpan::default() }],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn index_bounds_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds))
        .collect()
}

/// FIDELITY PIN (Rust side of the end-to-end bounds chain). The live bounds-VC emitter
/// (`rvalue_safety.rs::index_bounds_violation`, unsigned arm) builds EXACTLY the literal
/// `Formula::Ge(index, len)` for a read `arr[i]`. This is what makes the clean theorem
/// `proofs/trust-soundness/memory_bounds_obligation.lean::index_obligation_is_rust_panic`
/// (`evalBool (indexBoundsObligation index len) = rustIndexPanics index len`, where
/// `rustIndexPanics index len := index >= len`) denote the REAL emitter output rather than a
/// chosen predicate. Together with that file's `index_proved_implies_no_panic`
/// (PROVED ⟹ no OOB panic), this is the bounds class closed end-to-end:
///   real emitter (this test) → literal `index >= len` → MIR panic condition (clean, given the
///   stated `Assert(Lt(index,len))` fidelity anchor) → PROVED ⟹ no out-of-bounds panic.
/// If this shape ever drifts, the clean fidelity assumption silently decouples — so this test is
/// load-bearing, not decorative. Mirrors the store-side pin below.
#[test]
fn read_side_index_bounds_vc_is_literal_index_ge_len() {
    // `_0 = arr[i]` — the `Index(i)` projection on the rvalue (read) path.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Index(2)] })),
        Ty::u32(),
    );
    let vcs = index_bounds_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "unsigned `arr[i]` read must emit one IndexOutOfBounds VC, got: {vcs:?}"
    );
    // The literal `index >= len` (len = 4 from arr_ty, index = the usize local `i`). NOT the signed
    // arm's `Or([Lt(i,0), Ge(i,len)])`, and NOT a base-offset BvUGe sum — a direct comparison,
    // exactly the shape clean's `indexBoundsObligation`/`rustIndexPanics` model.
    assert_eq!(
        vcs[0].formula,
        Formula::Ge(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(4))),
        "read-side bounds VC must be the literal `index >= len`"
    );
}

#[test]
fn store_side_index_projection_flags_out_of_bounds() {
    // `arr[i] = v` — the `Index(i)` projection lives on the assignment
    // DESTINATION, not the rvalue, so the read/rvalue walk never saw it.
    let func = index_projection_func(
        Place { local: 1, projections: vec![Projection::Index(2)] },
        Rvalue::Use(Operand::Copy(Place::local(3))),
        Ty::Unit,
    );
    let vcs = index_bounds_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "an unguarded `arr[i] = v` store must emit exactly one IndexOutOfBounds VC, got: {vcs:?}"
    );
    // The obligation is the same `i >= len` violation the read path builds.
    assert_eq!(
        vcs[0].formula,
        Formula::Ge(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(4))),
        "store-side bounds VC must be `i >= len`"
    );
}

#[test]
fn mut_ref_index_projection_flags_out_of_bounds() {
    // `&mut arr[i]` — Rvalue::Ref over an indexed place. Borrowing an
    // out-of-bounds element is UB just like writing it.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Index(2)] },
        },
        Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
    );
    let vcs = index_bounds_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "`&mut arr[i]` must emit exactly one IndexOutOfBounds VC, got: {vcs:?}"
    );
    assert_eq!(
        vcs[0].formula,
        Formula::Ge(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(4))),
    );
}

#[test]
fn shared_ref_index_projection_flags_out_of_bounds() {
    // `&arr[i]` — a shared borrow of an indexed place must be bounds-checked too.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![Projection::Index(2)] },
        },
        Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
    );
    assert_eq!(index_bounds_vcs(&func).len(), 1, "`&arr[i]` must emit one IndexOutOfBounds VC");
}

#[test]
fn raw_addr_of_index_projection_flags_out_of_bounds() {
    // `&raw mut arr[i]` — Rvalue::AddressOf over an indexed place.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::AddressOf(true, Place { local: 1, projections: vec![Projection::Index(2)] }),
        Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
    );
    assert_eq!(
        index_bounds_vcs(&func).len(),
        1,
        "`&raw mut arr[i]` must emit one IndexOutOfBounds VC"
    );
}

#[test]
fn copy_for_deref_index_projection_flags_out_of_bounds() {
    // Compiler-inserted `CopyForDeref(arr[i])` — semantically a read of the
    // indexed element; must be bounds-checked.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::CopyForDeref(Place { local: 1, projections: vec![Projection::Index(2)] }),
        Ty::u32(),
    );
    assert_eq!(
        index_bounds_vcs(&func).len(),
        1,
        "`CopyForDeref(arr[i])` must emit one IndexOutOfBounds VC"
    );
}

#[test]
fn plain_store_without_index_emits_no_bounds_vc() {
    // NO-FALSE-POSITIVE (shape): an ordinary non-indexed store `arr = ...`
    // (or `_0 = v`) carries no Index projection and must NOT emit a bounds VC.
    let func = index_projection_func(
        Place::local(0),
        Rvalue::Use(Operand::Copy(Place::local(3))),
        Ty::u32(),
    );
    assert!(
        index_bounds_vcs(&func).is_empty(),
        "a non-indexed store must not produce an IndexOutOfBounds VC"
    );
}

#[test]
fn guarded_store_side_index_projection_proves() {
    // NO-FALSE-POSITIVE (discharge): a dominating `if i < arr.len()` guard
    // must discharge the store-side bounds obligation, exactly as it does for
    // the read path. We build:
    //   bb0: c = (i < 4); switch c [0 -> bb2] else bb1
    //   bb1: arr[i] = v; return        (reached only when c != 0, i.e. i < 4)
    //   bb2: return
    // The store VC violation `i >= 4` is conjoined with the path/block-def
    // assumption `i < 4`, yielding an UNSATISFIABLE formula — the obligation
    // proves (no reachable out-of-bounds write).
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "store_bounds::guarded".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("v".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(4, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Index(2)] },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = index_bounds_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "the store still produces a bounds obligation (it is discharged, not skipped)"
    );
    assert!(
        !index_bounds_violation_is_satisfiable(&vcs[0].formula),
        "guarded `if i < arr.len() {{ arr[i] = v }}` must discharge the store-side bounds VC to \
         UNSAT (proved in-bounds); got a satisfiable counterexample: {:?}",
        vcs[0].formula
    );
}

#[test]
fn guarded_mut_ref_index_projection_proves() {
    // NO-FALSE-POSITIVE (discharge), reference side: `if i < arr.len() { &mut arr[i] }`.
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let func = VerifiableFunction {
        name: "g".into(),
        def_path: "store_bounds::guarded_ref".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: None,
                },
                LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(4, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Ref {
                            mutable: true,
                            place: Place { local: 1, projections: vec![Projection::Index(2)] },
                        },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = index_bounds_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(
        !index_bounds_violation_is_satisfiable(&vcs[0].formula),
        "guarded `&mut arr[i]` must discharge to UNSAT, got: {:?}",
        vcs[0].formula
    );
}

/// Tiny finite-domain satisfiability check for the linear-integer bounds
/// formulas emitted here (Int/Bool vars, no quantifiers). Mirrors the
/// `discriminant_vc_is_sat` helper used by the enum-match discharge tests:
/// a bounds VC formula is SAT iff a reachable out-of-bounds index exists, so
/// UNSAT == the obligation proves.
fn index_bounds_violation_is_satisfiable(formula: &Formula) -> bool {
    use std::collections::{BTreeMap, BTreeSet};
    fn vars(f: &Formula, out: &mut BTreeSet<String>) {
        if let Some(n) = f.var_name() {
            out.insert(n.to_string());
            return;
        }
        match f {
            Formula::Not(a) | Formula::Neg(a) => vars(a, out),
            Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| vars(x, out)),
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b) => {
                vars(a, out);
                vars(b, out);
            }
            _ => {}
        }
    }
    // A node is "boolean-shaped" if it can only be a predicate, not an integer
    // term. `c == (i < 4)` puts such a node in `Eq`'s integer position, so the
    // integer evaluator must coerce boolean-shaped subterms to 0/1.
    fn is_bool_shaped(f: &Formula) -> bool {
        matches!(
            f,
            Formula::Bool(_)
                | Formula::Not(_)
                | Formula::And(_)
                | Formula::Or(_)
                | Formula::Implies(_, _)
                | Formula::Lt(_, _)
                | Formula::Le(_, _)
                | Formula::Gt(_, _)
                | Formula::Ge(_, _)
                | Formula::Eq(_, _)
        )
    }
    fn ei(f: &Formula, env: &BTreeMap<String, i128>) -> i128 {
        if let Some(n) = f.var_name() {
            return *env.get(n).unwrap_or(&0);
        }
        match f {
            Formula::Int(n) => *n,
            Formula::UInt(n) => *n as i128,
            Formula::Neg(a) => -ei(a, env),
            Formula::Add(a, b) => ei(a, env) + ei(b, env),
            Formula::Sub(a, b) => ei(a, env) - ei(b, env),
            Formula::Mul(a, b) => ei(a, env) * ei(b, env),
            // A boolean-shaped subterm in integer position (e.g. the RHS of
            // `c == (i < 4)`) evaluates to 0/1.
            other if is_bool_shaped(other) => i128::from(eb(other, env)),
            other => panic!("bounds VC: unexpected node in integer position: {other:?}"),
        }
    }
    fn eb(f: &Formula, env: &BTreeMap<String, i128>) -> bool {
        match f {
            Formula::Bool(b) => *b,
            Formula::Var(_, _) | Formula::SymVar(_, _) => {
                *env.get(f.var_name().expect("var")).unwrap_or(&0) != 0
            }
            Formula::Not(a) => !eb(a, env),
            Formula::And(xs) => xs.iter().all(|x| eb(x, env)),
            Formula::Or(xs) => xs.iter().any(|x| eb(x, env)),
            Formula::Implies(a, b) => !eb(a, env) || eb(b, env),
            // `Eq` can compare booleans (`c == (i < 4)`) or integers; `ei`
            // coerces boolean-shaped operands, so this stays correct for both.
            Formula::Eq(a, b) => ei(a, env) == ei(b, env),
            Formula::Lt(a, b) => ei(a, env) < ei(b, env),
            Formula::Le(a, b) => ei(a, env) <= ei(b, env),
            Formula::Gt(a, b) => ei(a, env) > ei(b, env),
            Formula::Ge(a, b) => ei(a, env) >= ei(b, env),
            other => panic!("bounds VC: unexpected node in boolean position: {other:?}"),
        }
    }
    let mut names = BTreeSet::new();
    vars(formula, &mut names);
    let names: Vec<String> = names.into_iter().collect();
    let domain: Vec<i128> = (-2..=8).collect();
    let total = domain.len().checked_pow(names.len() as u32).expect("small domain");
    for mut idx in 0..total {
        let mut env = BTreeMap::new();
        for n in &names {
            env.insert(n.clone(), domain[idx % domain.len()]);
            idx /= domain.len();
        }
        if eb(formula, &env) {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Owned-aggregate-field discriminant CSE (Multiplicity::mul tuple-match shape).
// `build_discriminant_cse_facts` must tie same-owned-field discriminant reads so
// the per-temp enum range facts can discharge the shared `otherwise->Unreachable`
// — but ONLY when the aggregate root is stable (no projected store etc.).
// ---------------------------------------------------------------------------

/// `_3 = (_1, _2)` then two reads `_4 = disc(_3.0)`, `_5 = disc(_3.0)`. When
/// `stable` is false, an extra projected store `_3.0 = _1` makes
/// `place_source_is_stable(_3)` fail, so the reads must NOT be tied.
fn tuple_field_discriminant_function(stable: bool) -> VerifiableFunction {
    let span = SourceSpan::default();
    let field0 = Place::field(3, 0);
    let mut stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        ),
        span: span.clone(),
    }];
    if !stable {
        // projected store into the aggregate => place_source_is_stable(_3) is false
        stmts.push(Statement::Assign {
            place: field0.clone(),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: span.clone(),
        });
    }
    stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Discriminant(field0.clone()),
        span: span.clone(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Discriminant(field0.clone()),
        span: span.clone(),
    });
    VerifiableFunction {
        name: "tuple_field_discriminant".to_string(),
        def_path: "test::tuple_field_discriminant".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
                LocalDecl { index: 4, ty: Ty::i32(), name: None },
                LocalDecl { index: 5, ty: Ty::i32(), name: None },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// True iff `facts` contains an equality between vars `a` and `b` (either order).
fn facts_tie(facts: &[Formula], a: &str, b: &str) -> bool {
    facts.iter().any(|f| {
        if let Formula::Eq(l, r) = f {
            let (Some(ln), Some(rn)) = (l.var_name(), r.var_name()) else { return false };
            (ln == a && rn == b) || (ln == b && rn == a)
        } else {
            false
        }
    })
}

#[test]
fn owned_aggregate_field_discriminants_are_tied() {
    // The Multiplicity::mul fix: two reads of `disc(_3.0)` on a stable owned
    // aggregate must be tied so the range facts discharge the shared Unreachable.
    let func = tuple_field_discriminant_function(true);
    let facts = crate::generate::build_discriminant_cse_facts(&func);
    assert!(
        facts_tie(&facts, "_4", "_5"),
        "owned aggregate field discriminant reads must be tied; got {facts:?}"
    );
}

#[test]
fn unstable_aggregate_field_discriminants_not_tied() {
    // SOUNDNESS / necessity: a projected store into the aggregate makes the field
    // value non-stable across reads, so the tie must NOT be emitted (fail-closed).
    let func = tuple_field_discriminant_function(false);
    let facts = crate::generate::build_discriminant_cse_facts(&func);
    assert!(
        !facts_tie(&facts, "_4", "_5"),
        "unstable aggregate field reads must NOT be tied (fail-closed); got {facts:?}"
    );
}

// ── Trust (R3, generics): pre-monomorphization alias declaration relaxation ──

/// A trivial function whose only non-return local is declared at an
/// `Unsupported { kind: "TyKind::Alias", detail }` marker type.
fn alias_marker_local_function(detail: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "alias_local".to_string(),
        def_path: "test::alias_local".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Unsupported {
                        kind: trust_types::PRE_MONO_ALIAS_KIND.to_string(),
                        detail: detail.to_string(),
                    },
                    name: Some("opaque".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_pre_mono_alias_declaration_emits_no_unsupported_mir_vc() {
    // R3: the pre-monomorphization param-bearing alias marker is a DECLARATION
    // relaxation (exactly like `TyKind::Param`): a value of such a type carries
    // no safety obligation by itself, so the declaration walk must not stamp.
    let func = alias_marker_local_function(trust_types::PRE_MONO_ALIAS_DETAIL);
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == trust_types::PRE_MONO_ALIAS_KIND
        )),
        "pre-mono alias declaration must not stamp an UnsupportedMir VC; got {vcs:?}"
    );
}

#[test]
fn test_monomorphic_alias_details_still_stamp_unsupported_mir_vc() {
    // SOUNDNESS (exact-scope regression): every OTHER `TyKind::Alias` detail is
    // a MONOMORPHIC alias that merely failed normalization — its runtime type
    // may be a concrete primitive on which MIR performs primitive ops, so the
    // declaration marker must stay fail-closed.
    for detail in [
        "alias args nest ADTs too deep (9) to normalize safely",
        "opaque alias has no typing env to reveal against",
        "alias type Projection has no typing env to normalize against",
        "alias did not resolve to a supported concrete type",
    ] {
        let func = alias_marker_local_function(detail);
        let vcs = generate_vcs(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == trust_types::PRE_MONO_ALIAS_KIND
            )),
            "monomorphic alias detail {detail:?} must keep stamping UnsupportedMir"
        );
    }
}
