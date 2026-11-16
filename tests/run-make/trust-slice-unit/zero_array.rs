//! Concrete checks over the real emitted zero-array function. Diagnostic wrappers
//! provide arguments only; they never replace its body or supply proof authority.

use run_make_support::trust_ir::reference::{
    Block, BlockId, Constant, FatPtrKind, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, ProofStatus, Ty, ValueId, binary,
    interpret::{InterpretErrorCode, InterpretOptions, InterpretValueKind, Interpreter},
};

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    EmptyArray,
    Panic,
    Other(String),
}

fn selected(module: &Module) -> &Function {
    let functions: Vec<_> = module
        .functions
        .iter()
        .filter(|f| f.display_path.as_deref() == Some("read_nonunit_zst"))
        .collect();
    assert_eq!(functions.len(), 1, "select the actual emitted function exactly once");
    functions[0]
}

fn run(module: &Module, length: u64, index: u64) -> Outcome {
    let callee = selected(module);
    let signature = module.func_type(callee.ty).unwrap();
    let [slice, Ty::Usize] = signature.params.as_slice() else { panic!("wrong parameters") };
    let Ty::FatPtr(FatPtrKind::Slice(element)) = slice else { panic!("not a slice") };
    let element_ty = module.types.get(element.0 as usize).unwrap();
    assert!(matches!(element_ty, Ty::Array(unit, 0) if module.types.get(unit.0 as usize) == Some(&Ty::Unit)));
    assert_eq!(signature.returns, vec![element_ty.clone()], "the result is [(); 0], not ()");
    assert!(!signature.is_vararg);
    let mut block = Block::new(BlockId::new(0));
    let mut push = |id: u32, inst| {
        let value = ValueId::new(id);
        block.body.push(InstrNode::new(inst).with_result(value));
        value
    };
    // Both supported macOS targets use 64-bit slice metadata. A real nonnull
    // allocation backs the zero-sized elements, even at the largest length.
    let data = push(0, Inst::Alloca { ty: Ty::U8, count: None, align: None });
    let metadata = push(1, Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(length)) });
    let argument = push(2, Inst::PtrFromParts {
        ptr_ty: slice.clone(), metadata_ty: Ty::U64, data, metadata,
    });
    let index = push(3, Inst::Const { ty: Ty::Usize, value: Constant::Int(i128::from(index)) });
    let result = push(4, Inst::Call { callee: callee.id, args: vec![argument, index] });
    block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
    let mut extended = module.clone();
    let id = FuncId::new(module.functions.iter().map(|f| f.id.0).max().unwrap().checked_add(1).unwrap());
    let ty = extended.add_func_type(FuncTy {
        params: vec![], returns: signature.returns.clone(), is_vararg: false, abi: None,
    }).unwrap();
    let mut wrapper = Function::new(id, "diagnostic_zero_array_arguments", ty, BlockId::new(0));
    wrapper.blocks.push(block);
    extended.try_add_function(wrapper).unwrap();
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(binary::serialize_module(&restored), binary::serialize_module(module),
        "every original body and obligation must remain byte-identical");
    match Interpreter::with_module(&extended)
        .with_options(InterpretOptions { fuel: 10_000, max_call_depth: 8, ..Default::default() })
        .execute_func(id, [])
    {
        Ok(result) => {
            assert_eq!(result.host_calls, 0, "no opaque call substitutes for the subject");
            assert_eq!(result.returns.len(), 1);
            assert_eq!(&result.returns[0].ty, element_ty);
            assert!(matches!(&result.returns[0].kind, InterpretValueKind::Array(values) if values.is_empty()));
            Outcome::EmptyArray
        }
        Err(error) if error.code == InterpretErrorCode::Panic => Outcome::Panic,
        Err(error) => Outcome::Other(error.to_string()),
    }
}

pub fn check(module: &Module) {
    let function = selected(module);
    let nodes: Vec<_> = function.blocks.iter().flat_map(|b| &b.body).collect();
    assert_eq!(nodes.iter().filter(|n| matches!(n.inst, Inst::Assert { .. })).count(), 1);
    assert_eq!(nodes.iter().filter(|n| matches!(&n.inst,
        Inst::Const { ty: Ty::Array(_, 0), value: Constant::Array(values) } if values.is_empty())).count(), 1);
    assert!(!nodes.iter().any(|n| matches!(n.inst, Inst::PtrData { .. } | Inst::GEP { .. } | Inst::Load { .. })));
    let obligations: Vec<_> = module.proof_obligations.iter()
        .filter(|row| row.function == Some(function.id)).collect();
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].status, ProofStatus::Pending);
    let cases = [(0, 0), (1, 0), (1, 1), (5, 4), (5, 5), (u64::MAX, u64::MAX - 1), (u64::MAX, u64::MAX)];
    for (length, index) in cases {
        let expected = if index < length { Outcome::EmptyArray } else { Outcome::Panic };
        assert_eq!(run(module, length, index), expected, "length={length}, index={index}");
    }
    // An empty array is still an indexed slice element: erasing the bounds
    // check must turn an out-of-bounds panic into a detectable wrong success.
    let mut missing = module.clone();
    missing.functions.iter_mut().find(|f| f.id == function.id).unwrap().blocks.iter_mut()
        .for_each(|block| block.body.retain(|node| !matches!(node.inst, Inst::Assert { .. })));
    missing.proof_obligations.retain(|row| row.function != Some(function.id));
    assert_eq!(run(&missing, 0, 0), Outcome::EmptyArray);
    let mut reversed = module.clone();
    let mut changed = 0;
    for node in reversed.functions.iter_mut().find(|f| f.id == function.id).unwrap()
        .blocks.iter_mut().flat_map(|block| &mut block.body)
    {
        if let Inst::ICmp { op, .. } = &mut node.inst {
            assert_eq!(*op, ICmpOp::Ult);
            *op = ICmpOp::Uge;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert_eq!(run(&reversed, 1, 0), Outcome::Panic);
}
