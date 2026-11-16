//! Synthetic image refusal at the MIR-to-LIR and output-semantics boundaries.
//! No image byte pattern is interpreted or admitted by these tests.

use trust_types::{
    BlockId, CallableDefPathHash, ConstantImageLayout, ConstantImageOwner, ConstantImageRoot,
    ConstantImageTarget, ConstantMemoryImage,
};

use super::*;

fn image() -> ConstValue {
    ConstValue::MemoryImage(Box::new(ConstantMemoryImage {
        schema_version: 1,
        owner: ConstantImageOwner {
            def_path: "fixture".into(),
            def_path_hash: CallableDefPathHash::new(1, 2),
            mir_phase: "test".into(),
        },
        target: ConstantImageTarget {
            triple: "test".into(),
            data_layout: "e-p:64:64".into(),
            pointer_size_bytes: 8,
            little_endian: true,
        },
        ty: Ty::u8(),
        ty_fingerprint: [1, 2],
        layout: ConstantImageLayout { size_bytes: 1, align_bytes: 1 },
        root: ConstantImageRoot::ScalarBits { bits: 7, size_bytes: 1 },
        nodes: Default::default(),
    }))
}

fn images() -> [ConstValue; 2] {
    [image(), ConstValue::struct_scalar_fields_ref("Nested", vec![image()])]
}

fn plain() -> VerifiableFunction {
    VerifiableFunction {
        name: "constant".into(),
        def_path: "fixture::constant".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    // Output semantics admits explicitly sized scalar constants.
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn ignored_intrinsic(value: ConstValue, dead: bool) -> VerifiableFunction {
    let mut func = plain();
    let statement = Statement::Intrinsic {
        name: "diagnostic_fixture".into(),
        args: vec![Operand::Constant(value)],
    };
    if dead {
        func.body.blocks.push(TrustBlock {
            id: BlockId(1),
            stmts: vec![statement],
            terminator: Terminator::Unreachable,
        });
    } else {
        func.body.blocks[0].stmts.insert(0, statement);
    }
    func
}

fn assert_refused<T>(result: Result<T, BridgeError>) {
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("memory image must not lower"),
    };
    assert!(
        matches!(&error, BridgeError::UnsupportedOp(reason)
        if reason.contains("ConstValue::MemoryImage")),
        "{error:?}"
    );
}

fn assert_entries_refuse(func: &VerifiableFunction) {
    let options = LoweringOptions::default();
    assert_refused(lower_to_lir(func));
    assert_refused(lower_to_lir_with_options(func, &options));
    assert_refused(lower_body_to_lir(&func.name, &func.body));
    assert_refused(lower_body_to_lir_with_options(&func.name, &func.body, &options));
    assert_refused(lower_body_to_lir_with_options_and_consumptions(
        &func.name, &func.body, &options,
    ));
}

#[test]
fn memory_image_live_constant_lowering_refuses_direct_and_nested() {
    for value in images() {
        let mut func = plain();
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
            panic!("constant fixture");
        };
        *rvalue = Rvalue::Use(Operand::Constant(value));
        assert_entries_refuse(&func);
    }
}

#[test]
fn memory_image_ignored_intrinsic_live_and_dead_args_refuse_before_lowering() {
    for value in images() {
        for dead in [false, true] {
            assert_entries_refuse(&ignored_intrinsic(value.clone(), dead));
        }
    }
}

#[test]
fn memory_image_guard_preserves_plain_scalar_lowering() {
    let func = plain();
    let options = LoweringOptions::default();
    for lowered in [
        lower_to_lir(&func),
        lower_to_lir_with_options(&func, &options),
        lower_body_to_lir(&func.name, &func.body),
        lower_body_to_lir_with_options(&func.name, &func.body, &options),
    ] {
        let lowered = lowered.expect("plain scalar remains modeled");
        crate::validation::validate_lir(&lowered).expect("valid scalar LIR");
    }
}

#[cfg(feature = "ay-proofs")]
#[test]
fn memory_image_output_semantics_refuses_even_unreachable_intrinsic_args() {
    assert!(crate::verify_output::trust_ir_semantics(&plain()).is_ok());
    for value in images() {
        for dead in [false, true] {
            let func = ignored_intrinsic(value.clone(), dead);
            let error = crate::verify_output::trust_ir_semantics(&func).unwrap_err();
            assert!(error.contains("ConstValue::MemoryImage"), "{error}");
        }
    }
}
