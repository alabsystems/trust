//! Synthetic carrier tests: these establish explicit refusal, not extraction,
//! executable allocation semantics, or new proof authority.

use trust_types::{
    CallableDefPathHash, ConstantImageLayout, ConstantImageOwner, ConstantImageRoot,
    ConstantImageTarget, ConstantMemoryImage, UnwindEdge, VerifiableBody,
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

fn nested_image() -> ConstValue {
    ConstValue::struct_scalar_fields_ref(
        "Outer",
        vec![ConstValue::struct_scalar_fields_ref("Inner", vec![image()])],
    )
}

fn assign(local: usize, value: ConstValue) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(value)),
        span: TrustSourceSpan::default(),
    }
}

fn fixture(value: ConstValue) -> VerifiableFunction {
    VerifiableFunction {
        name: "memory_image_fixture".into(),
        def_path: "fixture::memory_image_fixture".into(),
        span: TrustSourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![assign(0, value)],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn assert_refused<T>(result: Result<T, BridgeError>) {
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("memory image must not lower"),
    };
    assert!(
        matches!(&error, BridgeError::UnsupportedOp(detail)
        if detail.contains("ConstValue::MemoryImage")),
        "{error:?}"
    );
}

fn assert_public_entries_refuse(func: &VerifiableFunction) {
    assert_refused(lower_to_trust_ir(func));
    assert_refused(lower_functions_to_trust_ir("image", [func]));
    assert_refused(lower_to_trust_ir_functions("image", std::slice::from_ref(func)));
    let mut module = Module::new("existing");
    let before = serde_json::to_vec(&module).expect("module serializes");
    assert_refused(lower_to_trust_ir_function(func, &mut module));
    assert_eq!(serde_json::to_vec(&module).expect("module serializes"), before);
    let empty = FxHashSet::<String>::default();
    assert_refused(lower_to_trust_ir_functions_with_context(
        "image",
        std::slice::from_ref(func),
        &empty,
        &empty,
    ));
    assert!(!verifiable_function_lowers_in_module_context(
        std::slice::from_ref(func),
        0,
        &empty,
        &empty,
    ));
}

#[test]
fn memory_image_direct_and_nested_public_lowering_refuse() {
    for value in [image(), nested_image()] {
        assert_public_entries_refuse(&fixture(value));
    }
}

#[test]
fn memory_image_dead_assignment_and_dead_block_refuse_before_pruning() {
    for value in [image(), nested_image()] {
        let mut dead_assignment = fixture(ConstValue::Int(42));
        dead_assignment.body.blocks[0].stmts.insert(0, assign(1, value.clone()));
        assert_public_entries_refuse(&dead_assignment);

        let mut dead_block = fixture(ConstValue::Int(42));
        dead_block.body.blocks.push(TrustBlock {
            id: BlockId(1),
            stmts: vec![assign(1, value)],
            terminator: Terminator::Return,
        });
        assert_public_entries_refuse(&dead_block);
    }
}

#[test]
fn memory_image_bundle_refuses_even_when_only_later_member_contains_image() {
    let mut plain = fixture(ConstValue::Int(42));
    plain.name = "plain".into();
    plain.def_path = "fixture::plain".into();
    for value in [image(), nested_image()] {
        let image_func = fixture(value);
        assert_refused(lower_functions_to_trust_ir("bundle", [&plain, &image_func]));
        assert_refused(lower_to_trust_ir_functions("bundle", &[plain.clone(), image_func]));
    }
}

fn summarized_call(value: ConstValue) -> VerifiableFunction {
    let mut func = fixture(ConstValue::Int(42));
    func.body.blocks[0].stmts.clear();
    func.body.blocks[0].terminator = Terminator::Call {
        func: trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL.into(),
        args: vec![Operand::Constant(value)],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: TrustSourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Unreachable,
        callee_identity: None,
        callee_key: None,
    };
    func.body.blocks.push(TrustBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    func
}

#[test]
fn memory_image_call_argument_cannot_be_hidden_by_legacy_total_summary() {
    // Establish that this fixture reaches the old summary route. Its admitted
    // Undef is existing behavior, not newly granted value semantics.
    let control = lower_to_trust_ir(&summarized_call(ConstValue::Int(7)))
        .expect("existing total summary remains admitted");
    assert!(control.functions[0].blocks.iter().flat_map(|block| &block.body).any(|node| {
        matches!(node.inst, Inst::Undef { .. })
            && node.has_proof(&ProofAnnotation::FreshSymbolicHavoc)
    }));
    for value in [image(), nested_image()] {
        assert_public_entries_refuse(&summarized_call(value));
    }
}

#[test]
fn memory_image_private_type_and_emission_seams_refuse_without_emitting_undef() {
    let mut module = Module::new("seams");
    let mut cache = FxHashMap::default();
    let closures = ClosureEnvTypes::default();
    let no_known_functions = FxHashMap::default();
    let no_known_signatures = FxHashMap::default();
    let mut ctx = LoweringCtx::new(
        &[],
        0,
        TrustIrBlockId::new(0),
        &mut module,
        &no_known_functions,
        &no_known_signatures,
        &closures,
        &mut cache,
        "fixture::seams",
        &[],
    );
    let mut nodes = Vec::new();
    for value in [image(), nested_image()] {
        let operand = Operand::Constant(value.clone());
        assert_refused(operand_trust_ir_type(&operand, &ctx));
        assert_refused(operand_trust_type(&operand, &ctx));
        assert_refused(operand_trust_type_with_context(&operand, Some(&Ty::i64()), &ctx));
        assert_refused(ctx.emit_const(&value, &mut nodes));
        assert_refused(ctx.resolve_operand(&operand, &mut nodes));
        assert_refused(ctx.resolve_operand_as_trust_type(&operand, &Ty::i64(), &mut nodes));
        assert_refused(ctx.resolve_operand_expecting(&operand, Some(&Ty::i64()), &mut nodes));
        assert!(nodes.is_empty(), "refusal must not emit a value or Undef seed");
    }
    // Existing scalar emission/type inference remains unchanged.
    assert_eq!(
        operand_trust_type(&Operand::Constant(ConstValue::Int(42)), &ctx).unwrap(),
        Ty::i64()
    );
    let result = ctx.emit_const(&ConstValue::Int(42), &mut nodes).unwrap();
    assert_eq!(nodes[0].results.as_slice(), &[result]);
    assert!(matches!(nodes[0].inst, Inst::Const { value: TrustIrConstant::Int(42), .. }));
}

#[test]
fn memory_image_scalar_positive_control_stays_valid_through_all_public_entries() {
    let plain = fixture(ConstValue::Int(42));
    let mut modules = vec![
        lower_to_trust_ir(&plain).expect("single body"),
        lower_functions_to_trust_ir("scalar", [&plain]).expect("iterator bundle"),
        lower_to_trust_ir_functions("scalar", std::slice::from_ref(&plain)).expect("slice bundle"),
    ];
    let mut module = Module::new("incremental");
    let function = lower_to_trust_ir_function(&plain, &mut module).expect("incremental body");
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
    modules.push(module);
    for module in modules {
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{errors:?}");
        assert!(module.functions[0].blocks.iter().flat_map(|block| &block.body).any(|node| {
            matches!(node.inst, Inst::Const { value: TrustIrConstant::Int(42), .. })
        }));
    }
}
