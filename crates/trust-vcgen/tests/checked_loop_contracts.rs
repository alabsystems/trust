use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "checked_loop_contracts.rs".to_string(),
        line_start: line,
        col_start: 0,
        line_end: line,
        col_end: 80,
    }
}

/// The post-optimization MIR shape of
/// `while n > 0 { n -= STEP; }`: a checked subtraction tuple, its overflow
/// assert, and the successful value copied back before the latch.
fn checked_countdown(guard_op: BinOp, step: u128) -> VerifiableFunction {
    VerifiableFunction {
        name: "checked_countdown".to_string(),
        def_path: "test::checked_countdown".to_string(),
        span: span(1),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".to_string()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            guard_op,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: span(10),
                    }],
                    // rustc uses the `otherwise` edge for the true arm of this
                    // Boolean switch, producing `!(n > 0 == false)`.
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span(10),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(step, 32)),
                        ),
                        span: span(12),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(3),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: span(12),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Move(Place::field(3, 0))),
                        span: span(12),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn loop_spec(kind: LoopContractKind, body: &str) -> LoopContractSpec {
    LoopContractSpec {
        kind,
        source_loop_id: 0,
        source_hir_local_id: None,
        mir_header: None,
        loop_head: SourceSpan { line_end: 14, ..span(10) },
        header_span: span(10),
        span: span(11),
        body: body.to_string(),
    }
}

fn loop_unknowns(
    func: &VerifiableFunction,
) -> (Vec<VerificationCondition>, Vec<VerificationCondition>) {
    let (mut all, preclassified) = generate_vcs_with_discharge(func);
    let mut unsupported = Vec::new();
    for (vc, result) in preclassified {
        if matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. }
                if kind == "UserLoopContractUnsupported"
        ) && matches!(result, VerificationResult::Unknown { .. })
        {
            unsupported.push(vc.clone());
        }
        all.push(vc);
    }
    (all, unsupported)
}

#[test]
fn checked_unsigned_unit_decrement_under_positive_otherwise_guard_is_exact() {
    let mut func = checked_countdown(BinOp::Gt, 1);
    assert!(
        bind_compiler_loop_contracts(
            &mut func,
            &[
                loop_spec(LoopContractKind::Invariant, "n >= 0"),
                loop_spec(LoopContractKind::Decreases, "n"),
            ],
        )
        .is_empty()
    );

    let (all, unsupported) = loop_unknowns(&func);
    assert!(
        unsupported.is_empty(),
        "canonical checked countdown must be in-fragment: {unsupported:#?}"
    );
    assert!(all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. })));
    assert!(all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. })));
    assert!(all.iter().any(|vc| {
        matches!(&vc.kind, VcKind::NonTermination { context, measure }
            if context == "loop-decreases" && measure == "n")
    }));
}

#[test]
fn contextual_signed_literal_retains_the_declared_i128_checked_domain() {
    let mut func = checked_countdown(BinOp::Gt, 1);
    func.body.locals[1].ty = Ty::i128();
    func.body.locals[3].ty = Ty::Tuple(vec![Ty::i128(), Ty::Bool]);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut func.body.blocks[1].stmts[0]
    else {
        unreachable!()
    };
    *guard_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, update_rhs), .. } =
        &mut func.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    // Portable MIR erases the width of this contextual signed literal.  Its
    // value is nevertheless exactly representable in the declared i128 LHS
    // domain and the checked tuple independently preserves that domain.
    *update_rhs = Operand::Constant(ConstValue::Int(1));

    assert!(
        bind_compiler_loop_contracts(
            &mut func,
            &[
                loop_spec(LoopContractKind::Invariant, "n >= 0"),
                loop_spec(LoopContractKind::Decreases, "n"),
            ],
        )
        .is_empty()
    );
    let (all, unsupported) = loop_unknowns(&func);
    assert!(
        unsupported.is_empty(),
        "an in-range contextual literal must inherit the exact i128 checked domain: \
         {unsupported:#?}",
    );
    assert!(all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. })));
    assert!(all.iter().any(|vc| {
        matches!(&vc.kind, VcKind::NonTermination { context, measure }
            if context == "loop-decreases" && measure == "n")
    }));
    let mut exact_i128_subtraction = false;
    for vc in &all {
        vc.formula.visit(&mut |formula| {
            exact_i128_subtraction |= matches!(formula, Formula::BvSub(_, _, 128));
        });
    }
    assert!(
        exact_i128_subtraction,
        "the accepted checked update must retain an exact 128-bit subtraction: {all:#?}",
    );
}

#[test]
fn non_positive_guard_uses_exact_wrapping_unsigned_decrement() {
    let mut func = checked_countdown(BinOp::Ge, 1);
    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(LoopContractKind::Invariant, "true")],)
            .is_empty()
    );

    let (all, unsupported) = loop_unknowns(&func);
    assert!(all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. })));
    assert!(
        unsupported.is_empty(),
        "the guard need not prove non-underflow when the transition keeps exact wrapping semantics: {unsupported:#?}",
    );
}

#[test]
fn positive_guard_uses_exact_wrapping_wider_decrement() {
    let mut func = checked_countdown(BinOp::Gt, 2);
    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(LoopContractKind::Invariant, "true")],)
            .is_empty()
    );

    let (all, unsupported) = loop_unknowns(&func);
    assert!(all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. })));
    assert!(
        unsupported.is_empty(),
        "a wider step remains exact in declared-width BV even when it may wrap: {unsupported:#?}",
    );
}

#[test]
fn checked_shift_accepts_an_independently_typed_integer_rhs() {
    // The canonical rustc spelling of an overflow-checked shift: a
    // `CheckedBinaryOp(Shl)` tuple does NOT exist (admission outlaws it —
    // only Add/Sub/Mul produce the audited `(value, bool)` carrier). rustc
    // guards the shift with a `Lt(amount, BITS)` assert of `expected: true`
    // polarity, then performs the plain shift in the assert's target block:
    //
    //   bb2: _3 = Lt(const 1_u16, const 32_u16);
    //        assert(move _3, expected: true, Overflow(Shl)) -> bb3;
    //   bb3: n = Shl(copy n, const 1_u16);
    let mut func = checked_countdown(BinOp::Gt, 1);
    func.body.locals[3].ty = Ty::Bool;
    func.body.blocks[2].stmts[0] = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::BinaryOp(
            BinOp::Lt,
            Operand::Constant(ConstValue::Uint(1, 16)),
            Operand::Constant(ConstValue::Uint(32, 16)),
        ),
        span: span(12),
    };
    func.body.blocks[2].terminator = Terminator::Assert {
        cond: Operand::Move(Place::local(3)),
        expected: true,
        msg: AssertMessage::Overflow(BinOp::Shl),
        target: BlockId(3),
        unwind: trust_types::UnwindEdge::Unreachable,
        span: span(12),
    };
    func.body.blocks[3].stmts[0] = Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::BinaryOp(
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(1, 16)),
        ),
        span: span(12),
    };

    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(LoopContractKind::Invariant, "true")],)
            .is_empty()
    );
    let (all, unsupported) = loop_unknowns(&func);
    assert!(
        unsupported.is_empty(),
        "MIR permits a u32 shift with a u16 count; its exact type must not fail-close: \
         {unsupported:#?}",
    );
    assert!(
        all.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. })),
        "the authenticated checked shift must retain its exact E4 transition: {all:#?}",
    );
    assert!(
        all.iter().any(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. })),
        "the guarded shift must still mint its shift-overflow obligation: {all:#?}",
    );
}

fn assert_checked_shape_declines(mut func: VerifiableFunction, case: &str) {
    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(LoopContractKind::Invariant, "true")],)
            .is_empty()
    );
    let (all, unsupported) = loop_unknowns(&func);
    assert!(
        !all.iter().any(|vc| matches!(
            vc.kind,
            VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
        )),
        "malformed checked update `{case}` must mint no E4 row: {all:#?}"
    );
    assert_eq!(
        unsupported.len(),
        1,
        "malformed checked update `{case}` must retain one visible source marker: {unsupported:#?}"
    );
}

/// A TYPE-inconsistent checked update is not merely an unsupported loop
/// shape: it is malformed TrustIR, and the admission audit collapses the
/// whole function to one visible `MalformedTrustIr` marker before any
/// loop-contract row can exist. The mismatch still never verifies — the
/// collapse marker replaces the row-level refusal.
fn assert_checked_type_mismatch_collapses(mut func: VerifiableFunction, case: &str) {
    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(LoopContractKind::Invariant, "true")],)
            .is_empty()
    );
    let (all, _) = loop_unknowns(&func);
    assert!(
        !all.iter().any(|vc| matches!(
            vc.kind,
            VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
        )),
        "type-mismatched checked update `{case}` must mint no E4 row: {all:#?}"
    );
    assert_eq!(
        all.iter()
            .filter(|vc| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr"
            ))
            .count(),
        1,
        "type-mismatched checked update `{case}` must retain one visible MalformedTrustIr \
         marker: {all:#?}"
    );
    assert!(
        all.iter().all(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "no proof-bearing row may survive the `{case}` collapse: {all:#?}"
    );
}

#[test]
fn checked_update_shape_mismatches_fail_closed() {
    // Two decline lanes, one per kind of mismatch. `shape_cases` are
    // TYPE-VALID TrustIR whose checked-update SHAPE the loop lane refuses:
    // admission passes and the refusal stays a row-level
    // `UserLoopContractUnsupported`. `type_cases` are TYPE-INCONSISTENT
    // operations: genuinely malformed TrustIR, which the admission audit
    // collapses whole-function to `MalformedTrustIr` before the loop lane
    // runs. Either way the mismatch never verifies.
    let mut shape_cases = Vec::new();
    let mut type_cases = Vec::new();

    let mut missing_assert = checked_countdown(BinOp::Gt, 1);
    missing_assert.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
    shape_cases.push(("missing-assert", missing_assert));

    let mut wrong_cond_field = checked_countdown(BinOp::Gt, 1);
    let Terminator::Assert { cond, .. } = &mut wrong_cond_field.body.blocks[2].terminator else {
        unreachable!()
    };
    *cond = Operand::Move(Place::field(3, 0));
    shape_cases.push(("wrong-assert-field", wrong_cond_field));

    let mut wrong_expected = checked_countdown(BinOp::Gt, 1);
    let Terminator::Assert { expected, .. } = &mut wrong_expected.body.blocks[2].terminator else {
        unreachable!()
    };
    *expected = true;
    shape_cases.push(("wrong-assert-expected", wrong_expected));

    let mut wrong_message = checked_countdown(BinOp::Gt, 1);
    let Terminator::Assert { msg, .. } = &mut wrong_message.body.blocks[2].terminator else {
        unreachable!()
    };
    *msg = AssertMessage::Overflow(BinOp::Add);
    shape_cases.push(("wrong-assert-operation", wrong_message));

    let mut wrong_value_type = checked_countdown(BinOp::Gt, 1);
    wrong_value_type.body.locals[3].ty = Ty::Tuple(vec![Ty::u16(), Ty::Bool]);
    type_cases.push(("wrong-tuple-value-type", wrong_value_type));

    let mut wrong_flag_type = checked_countdown(BinOp::Gt, 1);
    wrong_flag_type.body.locals[3].ty = Ty::Tuple(vec![Ty::u32(), Ty::u8()]);
    type_cases.push(("wrong-tuple-flag-type", wrong_flag_type));

    let mut mismatched_operand_types = checked_countdown(BinOp::Gt, 1);
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, rhs), .. } =
        &mut mismatched_operand_types.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    *rhs = Operand::Constant(ConstValue::Uint(1, 16));
    type_cases.push(("mismatched-operand-types", mismatched_operand_types));

    let mut out_of_range_contextual_literal = checked_countdown(BinOp::Gt, 1);
    out_of_range_contextual_literal.body.locals[1].ty = Ty::i8();
    out_of_range_contextual_literal.body.locals[3].ty = Ty::Tuple(vec![Ty::i8(), Ty::Bool]);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut out_of_range_contextual_literal.body.blocks[1].stmts[0]
    else {
        unreachable!()
    };
    *guard_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, update_rhs), .. } =
        &mut out_of_range_contextual_literal.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    *update_rhs = Operand::Constant(ConstValue::Int(128));
    type_cases.push(("out-of-range-contextual-literal", out_of_range_contextual_literal));

    let mut negative_contextual_unsigned_literal = checked_countdown(BinOp::Gt, 1);
    negative_contextual_unsigned_literal.body.locals[1].ty = Ty::u8();
    negative_contextual_unsigned_literal.body.locals[3].ty = Ty::Tuple(vec![Ty::u8(), Ty::Bool]);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut negative_contextual_unsigned_literal.body.blocks[1].stmts[0]
    else {
        unreachable!()
    };
    *guard_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, update_rhs), .. } =
        &mut negative_contextual_unsigned_literal.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    *update_rhs = Operand::Constant(ConstValue::Int(-1));
    type_cases.push(("negative-contextual-unsigned-literal", negative_contextual_unsigned_literal));

    let mut wrong_width_u128_literal = checked_countdown(BinOp::Gt, 1);
    wrong_width_u128_literal.body.locals[1].ty = Ty::u128();
    wrong_width_u128_literal.body.locals[3].ty = Ty::Tuple(vec![Ty::u128(), Ty::Bool]);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut wrong_width_u128_literal.body.blocks[1].stmts[0]
    else {
        unreachable!()
    };
    *guard_rhs = Operand::Constant(ConstValue::Uint(0, 128));
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, update_rhs), .. } =
        &mut wrong_width_u128_literal.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    *update_rhs = Operand::Constant(ConstValue::Uint(1, 64));
    type_cases.push(("wrong-width-u128-literal", wrong_width_u128_literal));

    let mut typed_i64_rhs_for_i128 = checked_countdown(BinOp::Gt, 1);
    typed_i64_rhs_for_i128.body.locals[1].ty = Ty::i128();
    typed_i64_rhs_for_i128.body.locals[3].ty = Ty::Tuple(vec![Ty::i128(), Ty::Bool]);
    typed_i64_rhs_for_i128.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::i64(),
        name: Some("step_i64".to_string()),
    });
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut typed_i64_rhs_for_i128.body.blocks[1].stmts[0]
    else {
        unreachable!()
    };
    *guard_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(_, _, update_rhs), .. } =
        &mut typed_i64_rhs_for_i128.body.blocks[2].stmts[0]
    else {
        unreachable!()
    };
    *update_rhs = Operand::Copy(Place::local(4));
    type_cases.push(("typed-i64-rhs-for-i128", typed_i64_rhs_for_i128));

    let mut second_checked_definition = checked_countdown(BinOp::Gt, 1);
    let duplicate_checked = second_checked_definition.body.blocks[2].stmts[0].clone();
    second_checked_definition.body.blocks[2].stmts.push(duplicate_checked);
    shape_cases.push(("second-checked-definition", second_checked_definition));

    let mut missing_copy_back = checked_countdown(BinOp::Gt, 1);
    missing_copy_back.body.blocks[3].stmts.clear();
    shape_cases.push(("missing-copy-back", missing_copy_back));

    let mut wrong_copy_back = checked_countdown(BinOp::Gt, 1);
    let Statement::Assign { rvalue, .. } = &mut wrong_copy_back.body.blocks[3].stmts[0] else {
        unreachable!()
    };
    *rvalue = Rvalue::Use(Operand::Move(Place::field(3, 1)));
    shape_cases.push(("wrong-copy-back-field", wrong_copy_back));

    let mut duplicate_subject_write = checked_countdown(BinOp::Gt, 1);
    let duplicate_write = duplicate_subject_write.body.blocks[3].stmts[0].clone();
    duplicate_subject_write.body.blocks[3].stmts.push(duplicate_write);
    shape_cases.push(("duplicate-subject-write", duplicate_subject_write));

    // The checked tuple is authenticated over the complete successful loop
    // path, not just its defining block and immediate assert target. Before the
    // SF-11 closure, this later whole-tuple overwrite left the cached `.0`
    // formula live and the following field read silently reused stale data.
    let mut later_tuple_rewrite = checked_countdown(BinOp::Gt, 1);
    later_tuple_rewrite.body.locals.extend([
        LocalDecl {
            index: 4,
            ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
            name: Some("replacement".to_string()),
        },
        LocalDecl { index: 5, ty: Ty::u32(), name: Some("observed".to_string()) },
    ]);
    later_tuple_rewrite.body.blocks[3].terminator = Terminator::Goto(BlockId(5));
    later_tuple_rewrite.body.blocks.push(BasicBlock {
        id: BlockId(5),
        stmts: vec![
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                span: span(13),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                span: span(13),
            },
        ],
        terminator: Terminator::Goto(BlockId(1)),
    });
    shape_cases.push(("later-whole-tuple-rewrite-and-read", later_tuple_rewrite));

    let mut later_duplicate_copy_back = checked_countdown(BinOp::Gt, 1);
    later_duplicate_copy_back.body.blocks[3].terminator = Terminator::Goto(BlockId(5));
    later_duplicate_copy_back.body.blocks.push(BasicBlock {
        id: BlockId(5),
        stmts: vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
            span: span(13),
        }],
        terminator: Terminator::Goto(BlockId(1)),
    });
    shape_cases.push(("later-duplicate-copy-back", later_duplicate_copy_back));

    for (case, func) in shape_cases {
        assert_checked_shape_declines(func, case);
    }
    for (case, func) in type_cases {
        assert_checked_type_mismatch_collapses(func, case);
    }
}
