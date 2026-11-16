// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Synthetic boundary controls, not compiler-allocation or Wasm refinement proofs.

use trust_types::{
    AssertMessage, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place,
    ReconstructionValidationStatus, Rvalue, SourceSpan, Statement, Terminator, TrustLevel, Ty,
    VerifiableBody, VerifiableFunction,
};
use trust_wasm_bridge::{
    WasmConversion, WasmTargetValidationStatus, convert_function_to_wat, convert_functions_to_wat,
};

fn unit_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "unit_boundary".into(),
        def_path: "test::unit_boundary".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Return,
            }],
            arg_count: 0,
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

fn make_memory_image_constant(bits: u128) -> ConstValue {
    ConstValue::MemoryImage(Box::new(trust_types::ConstantMemoryImage {
        schema_version: 1,
        owner: trust_types::ConstantImageOwner {
            def_path: "synthetic::wasm_image".into(),
            def_path_hash: trust_types::CallableDefPathHash::new(1, 2),
            mir_phase: "synthetic-test".into(),
        },
        target: trust_types::ConstantImageTarget {
            triple: "synthetic".into(),
            data_layout: "e-p:64:64".into(),
            pointer_size_bytes: 8,
            little_endian: true,
        },
        ty: Ty::u64(),
        ty_fingerprint: [1, 2],
        layout: trust_types::ConstantImageLayout { size_bytes: 8, align_bytes: 8 },
        root: trust_types::ConstantImageRoot::ScalarBits { bits, size_bytes: 8 },
        nodes: Default::default(),
    }))
}

fn nested_image() -> ConstValue {
    ConstValue::struct_scalar_fields_ref(
        "synthetic::Outer",
        vec![ConstValue::struct_scalar_fields_ref(
            "synthetic::Inner",
            vec![ConstValue::Uint(0, 64), make_memory_image_constant(8)],
        )],
    )
}

fn ignored_assignment(value: ConstValue) -> Statement {
    Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(value)),
        span: SourceSpan::default(),
    }
}

fn assert_image_refusal(conversion: &WasmConversion) {
    assert!(conversion.wat.is_none(), "image-bearing input must emit no WAT");
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(!conversion.is_inspectable());
    assert!(!conversion.is_accepted());
    assert!(
        conversion.unsupported.records.iter().any(|record| {
            record.stage == "trust-wasm-bridge"
                && record.feature.contains("ConstValue::MemoryImage")
        }),
        "missing explicit image refusal: {:?}",
        conversion.diagnostics,
    );
    assert!(conversion.validation_records.iter().any(|record| {
        record.status == ReconstructionValidationStatus::Failed
            && record.trust_level == TrustLevel::Rejected
    }));
}

#[test]
fn memory_image_direct_ignored_assignment_is_not_emitted() {
    let mut function = unit_function();
    function.body.blocks[0].stmts.push(ignored_assignment(make_memory_image_constant(8)));
    assert_image_refusal(&convert_function_to_wat(&function));
}

#[test]
fn memory_image_nested_ignored_assignment_is_not_emitted() {
    let mut function = unit_function();
    function.body.blocks[0].stmts.push(ignored_assignment(nested_image()));
    assert_image_refusal(&convert_function_to_wat(&function));
}

#[test]
fn memory_image_dead_block_is_refused_before_control_flow_selection() {
    for value in [make_memory_image_constant(8), nested_image()] {
        let mut function = unit_function();
        function.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![ignored_assignment(value)],
            terminator: Terminator::Return,
        });
        assert_image_refusal(&convert_function_to_wat(&function));
    }
}

#[test]
fn memory_image_terminator_operand_is_refused_before_control_flow_selection() {
    for value in [make_memory_image_constant(8), nested_image()] {
        for terminator in [
            Terminator::SwitchInt {
                discr: Operand::Constant(value.clone()),
                targets: vec![(0, BlockId(0))],
                otherwise: BlockId(0),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
            Terminator::Assert {
                cond: Operand::Constant(value.clone()),
                expected: true,
                msg: AssertMessage::Custom("synthetic".into()),
                target: BlockId(0),
                span: SourceSpan::default(),
                unwind: trust_types::UnwindEdge::Unreachable,
            },
            Terminator::TailCall {
                func: "synthetic::consume".into(),
                args: vec![Operand::Constant(value)],
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
            },
        ] {
            let mut function = unit_function();
            function.body.blocks[0].terminator = terminator;
            assert_image_refusal(&convert_function_to_wat(&function));
        }
    }
}

#[test]
fn memory_image_ignored_intrinsic_arguments_are_not_emitted() {
    for value in [make_memory_image_constant(8), nested_image()] {
        let mut function = unit_function();
        function.body.blocks[0].stmts.push(Statement::Intrinsic {
            name: "synthetic::consume".into(),
            args: vec![Operand::Constant(value)],
        });
        assert_image_refusal(&convert_function_to_wat(&function));
    }
}

#[test]
fn memory_image_refusal_discards_partial_module_output() {
    let clean = unit_function();
    let mut tainted = unit_function();
    tainted.name = "tainted".into();
    tainted.def_path = "test::tainted".into();
    tainted.body.blocks[0].stmts.push(ignored_assignment(nested_image()));
    assert_image_refusal(&convert_functions_to_wat(&[clean, tainted]));
}

#[test]
fn memory_image_free_unit_stays_inspectable_without_proof_grade() {
    let conversion = convert_function_to_wat(&unit_function());
    assert!(conversion.wat.is_some());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Validated);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::InspectableRejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(conversion.is_inspectable());
    assert!(!conversion.is_accepted());
    assert!(conversion.unsupported.is_empty());
}
