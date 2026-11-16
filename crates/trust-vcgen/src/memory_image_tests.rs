// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Synthetic refusal controls, not evidence of compiler allocation extraction.

use trust_types::{
    CallableDefPathHash, ConstantImageLayout, ConstantImageOwner, ConstantImageRoot,
    ConstantImageTarget, ConstantMemoryImage, LocalDecl, UnOp, VcKind, VerifiableBody,
    VerificationResult,
};

use super::*;

pub(crate) fn image(bits: u128) -> ConstValue {
    ConstValue::MemoryImage(Box::new(ConstantMemoryImage {
        schema_version: 1,
        owner: ConstantImageOwner {
            def_path: "fixture::memory_image".into(),
            def_path_hash: CallableDefPathHash::new(1, 2),
            mir_phase: "synthetic-test".into(),
        },
        target: ConstantImageTarget {
            triple: "synthetic".into(),
            data_layout: "e-p:64:64".into(),
            pointer_size_bytes: 8,
            little_endian: true,
        },
        ty: Ty::Int { width: 8, signed: false },
        ty_fingerprint: [1, 2],
        layout: ConstantImageLayout { size_bytes: 1, align_bytes: 1 },
        root: ConstantImageRoot::ScalarBits { bits, size_bytes: 1 },
        nodes: Default::default(),
    }))
}

pub(crate) fn nested_image(bits: u128) -> ConstValue {
    ConstValue::struct_scalar_fields_ref(
        "forged::Outer",
        vec![ConstValue::struct_scalar_fields_ref(
            "forged::Inner",
            vec![ConstValue::Uint(1, 8), image(bits)],
        )],
    )
}

pub(crate) fn function(rvalue: Rvalue) -> VerifiableFunction {
    let ty = Ty::Int { width: 8, signed: false };
    VerifiableFunction {
        name: "memory_image_test".into(),
        def_path: "fixture::memory_image_test".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue,
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

pub(crate) fn assert_refusal(vcs: &[VerificationCondition]) {
    assert!(!vcs.is_empty(), "unsupported observations must not produce an empty success");
    for vc in vcs {
        assert!(
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == MEMORY_IMAGE_KIND),
            "unexpected row: {vc:?}"
        );
        assert_eq!(vc.formula, Formula::Bool(true));
    }
}

fn assert_public_refusal(func: &VerifiableFunction) {
    assert_refusal(&generate_vcs(func));
    let error = try_generate_vcs(func).expect_err("fallible entry must reject memory images");
    assert!(error.to_string().contains(MEMORY_IMAGE_KIND));
    let (pending, classified) = generate_vcs_with_discharge(func);
    assert!(pending.is_empty(), "memory images must not reach solver dispatch");
    assert!(!classified.is_empty());
    for (vc, verdict) in classified {
        assert_refusal(&[vc]);
        assert!(matches!(verdict, VerificationResult::Unknown { .. }));
    }
}

#[test]
fn memory_image_public_entries_refuse_equal_distinct_and_nested_operands() {
    for (left, right) in
        [(image(0), image(0)), (image(0), image(8)), (nested_image(0), nested_image(8))]
    {
        for op in [BinOp::Eq, BinOp::Div, BinOp::Rem] {
            let func = function(Rvalue::BinaryOp(
                op,
                Operand::Constant(left.clone()),
                Operand::Constant(right.clone()),
            ));
            assert_public_refusal(&func);
        }
    }
}

#[test]
fn memory_image_checked_renderer_rejects_standalone_operands_and_tainted_bodies() {
    let clean = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
    assert_eq!(
        try_operand_to_formula(&clean, &Operand::Constant(ConstValue::Uint(7, 8))).unwrap(),
        Formula::Int(7),
    );
    for value in [image(0), image(8), nested_image(8)] {
        let operand = Operand::Constant(value);
        assert!(try_operand_to_formula(&clean, &operand).is_err());
        let tainted = function(Rvalue::Use(operand));
        assert!(try_operand_to_formula(&tainted, &Operand::Copy(Place::local(1))).is_err());
    }
}

#[test]
fn memory_image_dead_block_cannot_be_hidden_by_simplification() {
    let mut func = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
    func.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(nested_image(8))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    });
    assert_public_refusal(&func);
    // T3 C05: the consumed generation refuses the body, so it has no origin table.
    let mut rows = trust_types::vc_context::VcContext::new();
    let generation = generate_vcs_with_discharge_and_overflow_origins(
        &func,
        &modular::SummaryDatabase::new(),
        false,
        &VcgenContext::for_function(func.def_path.clone()),
        &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
        &mut rows,
    );
    assert!(generation.overflow_origins.complete().is_none());
    assert!(contracts::prepare_loop_invariant_feedback_validation(&func).is_none());
    assert!(chc::encode_function_loops(&func).is_err());
}

#[test]
fn memory_image_cached_empty_obligations_cannot_be_replayed_as_success() {
    let func = function(Rvalue::Use(Operand::Constant(nested_image(8))));
    let context = VcgenContext::for_function(func.def_path.clone());
    let (pending, classified) =
        discharge_captured_raw_body_with_context(&func, Vec::new(), &context);
    assert!(pending.is_empty());
    assert!(!classified.is_empty());
    for (vc, result) in classified {
        assert_refusal(&[vc]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }
}

#[test]
fn memory_image_modular_and_callsite_entries_refuse_before_summary_shortcuts() {
    let func = function(Rvalue::Use(Operand::Constant(nested_image(8))));
    let db = modular::SummaryDatabase::new();
    assert_refusal(&modular::generate_modular_vcs(&func, &db));
    let modular = modular::modular_vcgen(&func, &db);
    assert_refusal(&modular.body_vcs);
    assert!(modular.precondition_vcs.is_empty());
    assert_eq!(modular.assumptions_injected, 0);
    assert_refusal(&generate_callsite_precondition_vcs(&func, &db));
    for (vc, _, _) in generate_callsite_precondition_vcs_attributed(&func, &db) {
        assert_refusal(&[vc]);
    }
    assert_refusal(&contracts::regenerate_loop_decreases_with_invariant_feedback_vcs(&func, &[]));
    let (pending, classified) = generate_vcs_with_discharge_and_summaries(&func, &db);
    assert!(pending.is_empty());
    assert!(!classified.is_empty());
    assert!(
        classified.iter().all(|(_, result)| matches!(result, VerificationResult::Unknown { .. }))
    );
}

#[test]
fn memory_image_all_operand_statement_shapes_retain_public_refusal() {
    let operand = Operand::Constant(nested_image(8));
    for rvalue in [
        Rvalue::Use(operand.clone()),
        Rvalue::UnaryOp(UnOp::Not, operand.clone()),
        Rvalue::Cast(operand.clone(), Ty::Int { width: 8, signed: false }),
        Rvalue::Repeat(operand.clone(), 2),
        Rvalue::Aggregate(trust_types::AggregateKind::Tuple, vec![operand.clone()]),
        Rvalue::CheckedBinaryOp(BinOp::Add, operand.clone(), operand.clone()),
        Rvalue::UncheckedBinaryOp(BinOp::Add, operand.clone(), operand.clone()),
    ] {
        assert_public_refusal(&function(rvalue));
    }
}

#[test]
fn memory_image_switch_and_call_operands_retain_public_refusal() {
    let clean_rvalue = Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8)));
    let mut func = function(clean_rvalue);
    for terminator in [
        Terminator::SwitchInt {
            discr: Operand::Constant(nested_image(8)),
            targets: vec![(0, BlockId(0))],
            otherwise: BlockId(0),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
        Terminator::Call {
            func: "fixture::consume".into(),
            args: vec![Operand::Constant(nested_image(8))],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            unwind: trust_types::UnwindEdge::Unreachable,
        },
        Terminator::TailCall {
            func: "fixture::consume".into(),
            args: vec![Operand::Constant(nested_image(8))],
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
        },
        Terminator::Assert {
            cond: Operand::Constant(nested_image(8)),
            expected: true,
            msg: trust_types::AssertMessage::Custom("synthetic image".into()),
            target: BlockId(0),
            span: SourceSpan::default(),
            unwind: trust_types::UnwindEdge::Unreachable,
        },
    ] {
        func.body.blocks[0].terminator = terminator;
        assert_public_refusal(&func);
    }
}

#[test]
fn memory_image_intrinsic_and_copy_arguments_retain_public_refusal() {
    let mut func = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
    let image = Operand::Constant(nested_image(8));
    for statement in [
        Statement::Intrinsic { name: "assume".into(), args: vec![image.clone()] },
        Statement::CopyNonOverlapping {
            src: Operand::Copy(Place::local(1)),
            dst: Operand::Copy(Place::local(0)),
            count: image,
            elem_ty: Ty::Int { width: 8, signed: false },
            span: SourceSpan::default(),
        },
    ] {
        func.body.blocks[0].stmts = vec![statement];
        assert_public_refusal(&func);
    }
}

#[test]
fn memory_image_separation_preflight_preserves_exact_operation_origin() {
    use crate::unsafe_verify::MirOp;
    let mut func = function(Rvalue::Use(Operand::Constant(nested_image(8))));
    let std_span = SourceSpan {
        file: "/rustc/compiler/library/alloc/src/raw_vec/mod.rs".into(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 2,
    };
    let Statement::Assign { span, .. } = &mut func.body.blocks[0].stmts[0] else {
        panic!("fixture assignment");
    };
    *span = std_span.clone();
    // This is not an unsafe operation, and its span resembles the standard
    // library. Neither shortcut may erase a diagnostic-carrier refusal.
    let rows =
        sep_engine::check_sep_unsafe_blocked_ops(&func, &Default::default(), &Default::default());
    assert_eq!(rows.len(), 1);
    let (vc, block, operation) = &rows[0];
    assert_refusal(std::slice::from_ref(vc));
    assert_eq!(*block, BlockId(0));
    assert_eq!(*operation, MirOp::Statement(0));
    assert_eq!(vc.location, std_span);

    let mut engine = sep_engine::SepEngine::new(&func.name);
    engine.interpret_statement(&func.body.blocks[0].stmts[0], &std_span);
    assert_refusal(&engine.into_vcs());
}

#[test]
fn memory_image_dead_assignment_cannot_mint_definitional_callee_summaries() {
    let clean = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
    let funcs = std::slice::from_ref(&clean);
    assert_eq!(generate::compute_return_bound_summaries(funcs).get(&clean.def_path), Some(&7));
    assert_eq!(
        generate::compute_return_lower_bound_summaries(funcs).get(&clean.def_path),
        Some(&7)
    );
    assert_eq!(
        generate::compute_return_const_set_summaries(funcs).get(&clean.def_path),
        Some(&vec![7]),
    );
    for value in [image(0), nested_image(8)] {
        let mut tainted = clean.clone();
        tainted.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::Int { width: 8, signed: false },
            name: None,
        });
        tainted.body.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Constant(value)),
                span: SourceSpan::default(),
            },
        );
        let funcs = std::slice::from_ref(&tainted);
        assert!(generate::compute_return_bound_summaries(funcs).is_empty());
        assert!(generate::compute_return_lower_bound_summaries(funcs).is_empty());
        assert!(generate::compute_return_const_set_summaries(funcs).is_empty());
        assert!(generate::compute_trivial_setter_summaries(funcs).is_empty());
        assert!(generate::compute_return_disc_summaries(funcs).is_empty());
        assert!(generate::compute_return_bool_pred_summaries(funcs).is_empty());
    }
}

#[test]
fn memory_image_dead_assignment_cannot_mint_float_result_range() {
    let mut func = function(Rvalue::Use(Operand::Constant(ConstValue::Float(1.5))));
    func.body.return_ty = Ty::Float { width: 64 };
    func.body.locals[0].ty = func.body.return_ty.clone();
    assert_eq!(derive_float_result_range(&func), Some((1.5, 1.5)));
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(nested_image(8))),
            span: SourceSpan::default(),
        },
    );
    assert_eq!(derive_float_result_range(&func), None);
}

#[test]
fn memory_image_precondition_domination_refuses_before_vacuous_callee_shortcut() {
    let mut func = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
    let callee = "fixture::no_preconditions";
    let mut db = modular::SummaryDatabase::new();
    db.insert(modular::FunctionSummary::new(callee));
    func.body.blocks[0].terminator = Terminator::TailCall {
        func: callee.into(),
        args: vec![],
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
    };
    assert!(all_callsites_precondition_dominated(&func, &db, callee));
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(nested_image(8))),
            span: SourceSpan::default(),
        },
    );
    assert!(!all_callsites_precondition_dominated(&func, &db, callee));
}
