// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Authored IR regression for the actual final-validation diagnostic caller.
//! This is not a source Rust capture or a claim about any production struct IDs.

use trust_ir::{
    Block, BlockId, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer,
    StructDef, StructId, StructRepr, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

use super::super::final_module_validation_errors;

fn call_module(mismatch: bool) -> (Module, StructId, StructId) {
    let mut module = Module::new("final_validation_diagnostic_fixture");
    let expected = module
        .add_struct_def(StructDef {
            id: StructId::new(0),
            name: "ExpectedNominal".to_string(),
            fields: vec![FieldDef { name: "payload".to_string(), ty: Ty::U64, offset: Some(0) }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
            origin: None,
        })
        .expect("Module::add_struct_def: test fixture");
    let alternate = module
        .add_struct_def(StructDef {
            id: StructId::new(1),
            name: "ActualNominal".to_string(),
            fields: vec![FieldDef { name: "payload".to_string(), ty: Ty::U32, offset: Some(0) }],
            size: Some(4),
            align: Some(4),
            repr: StructRepr::Rust,
            origin: None,
        })
        .expect("Module::add_struct_def: test fixture");
    assert_ne!(expected, alternate, "fixture must contain distinct returned nominal IDs");
    let actual = if mismatch { alternate } else { expected };
    let callee_type = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(expected)],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_type = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(actual)],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");

    let mut callee =
        Function::new(FuncId::new(1), "diagnostic_callee", callee_type, BlockId::new(0));
    callee.producer = Some(Producer::TRust);
    let mut callee_block = Block::new(BlockId::new(0));
    callee_block.params.push((ValueId::new(0), Ty::Struct(expected)));
    callee_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
    callee.blocks.push(callee_block);
    module.try_add_function(callee).expect("Module::try_add_function: test fixture");

    let mut caller =
        Function::new(FuncId::new(0), "diagnostic_caller", caller_type, BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    let mut caller_block = Block::new(BlockId::new(0));
    caller_block.params.push((ValueId::new(0), Ty::Struct(actual)));
    caller_block
        .body
        .push(InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] }));
    caller_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
    caller.blocks.push(caller_block);
    module.try_add_function(caller).expect("Module::try_add_function: test fixture");
    (module, expected, actual)
}

#[test]
fn final_validation_retains_nominal_refusal_and_appends_read_only_context() {
    let (module, expected, actual) = call_module(true);
    let original = module.clone();
    let typed_error = ValidationError::CallArgTypeMismatch {
        block: 0,
        callee: "diagnostic_callee".to_string(),
        arg_index: 0,
        expected: Ty::Struct(expected).to_string(),
        actual: Ty::Struct(actual).to_string(),
        caller_producer: Some("trust".to_string()),
        callee_producer: Some("trust".to_string()),
    };
    // The structural validator, not a hand-fed formatter error, rejects the
    // actual call. No unrelated malformed fixture may account for the refusal.
    assert_eq!(validate_module(&module), vec![typed_error.clone()]);
    let messages = final_module_validation_errors(&module);
    assert_eq!(messages.len(), 1);
    let original_prefix = format!(
        "final Trust-IR module validation failed [CallArgTypeMismatch] in `diagnostic_caller`: {typed_error:?}"
    );
    let suffix = messages[0].strip_prefix(&original_prefix).expect("original class/location/error");
    assert!(suffix.starts_with(
        " [type-context diagnostic-only proof_authority=false source_refinement=false"
    ));
    assert!(suffix.len() <= super::MAX_OUTPUT_BYTES);
    assert_eq!(suffix, super::for_error(&module, &typed_error));
    assert!(
        suffix
            .contains(&format!("expected=Struct({}){{name=\"ExpectedNominal\"", expected.index()))
    );
    assert!(suffix.contains(&format!("actual=Struct({}){{name=\"ActualNominal\"", actual.index())));
    assert!(suffix.contains("ty=U64"));
    assert!(suffix.contains("ty=U32"));
    assert_eq!(module, original, "validator and final diagnostic must not mutate the module");
    assert_eq!(validate_module(&module), vec![typed_error]);

    // A separately constructed matching call stays valid and diagnostic-free;
    // neither side uses an admission flag or bypasses structural validation.
    let (matching, _, _) = call_module(false);
    let original_matching = matching.clone();
    assert!(validate_module(&matching).is_empty());
    assert!(final_module_validation_errors(&matching).is_empty());
    assert_eq!(matching, original_matching);
}

fn store_module(mismatch: bool) -> (Module, StructId, StructId) {
    let (mut module, expected, actual) = call_module(mismatch);
    module.functions.clear();
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Struct(actual)],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: store fixture");
    let mut function =
        Function::new(FuncId::new(0), "diagnostic_store", signature, BlockId::new(0));
    function.producer = Some(Producer::TRust);
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.params.push((ValueId::new(1), Ty::Struct(actual)));
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::Struct(expected),
        ptr: ValueId::new(0),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    module.try_add_function(function).expect("Module::try_add_function: store fixture");
    (module, expected, actual)
}

#[test]
fn final_validation_explains_an_actual_struct_store_refusal_without_repairing_it() {
    let (module, expected, actual) = store_module(true);
    let original = module.clone();
    let typed_error = ValidationError::OperandTypeMismatch {
        block: 0,
        op: "store".to_string(),
        role: "value".to_string(),
        expected: Ty::Struct(expected).to_string(),
        actual: Ty::Struct(actual).to_string(),
    };
    assert_eq!(validate_module(&module), vec![typed_error.clone()]);
    let messages = final_module_validation_errors(&module);
    assert_eq!(messages.len(), 1);
    let prefix = format!(
        "final Trust-IR module validation failed [OperandTypeMismatch] in `diagnostic_store`: {typed_error:?}"
    );
    let context = messages[0].strip_prefix(&prefix).expect("original store class/location/error");
    assert!(context.starts_with(
        " [type-context diagnostic-only proof_authority=false source_refinement=false"
    ));
    assert!(context.len() <= super::MAX_OUTPUT_BYTES);
    assert!(
        context
            .contains(&format!("expected=Struct({}){{name=\"ExpectedNominal\"", expected.index()))
    );
    assert!(
        context.contains(&format!("actual=Struct({}){{name=\"ActualNominal\"", actual.index()))
    );
    assert!(context.contains("ty=U64"));
    assert!(context.contains("ty=U32"));
    assert_eq!(module, original);
    assert_eq!(validate_module(&module), vec![typed_error]);

    let (matching, _, _) = store_module(false);
    let original_matching = matching.clone();
    assert!(validate_module(&matching).is_empty());
    assert!(final_module_validation_errors(&matching).is_empty());
    assert_eq!(matching, original_matching);
}
