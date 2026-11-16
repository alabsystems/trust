//! Concrete unit-slice execution on fresh compiler output; no refinement claim.

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, FatPtrKind, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, Ty, ValueId,
};

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Returned(Vec<u64>),
    Panic,
    Other(String),
}

fn function<'a>(module: &'a Module, name: &str) -> &'a Function {
    let matches: Vec<_> = module.functions.iter().filter(|f| f.name == name).collect();
    assert_eq!(matches.len(), 1, "missing/duplicate actual function {name}");
    matches[0]
}

fn value(block: &mut Block, next: &mut u32, inst: Inst) -> ValueId {
    let id = ValueId::new(*next);
    *next += 1;
    block.body.push(InstrNode::new(inst).with_result(id));
    id
}

fn run(module: &Module, name: &str, lengths: &[u64], index: u64) -> Outcome {
    let callee = function(module, name);
    let signature = module.func_type(callee.ty).unwrap().clone();
    assert!(!signature.is_vararg);
    assert_eq!(signature.params.len(), lengths.len() + 1);
    assert_eq!(signature.params.last(), Some(&Ty::Usize));
    assert_eq!(
        signature.returns,
        if name == "unit_index_effect" { vec![Ty::Usize] } else { vec![] }
    );
    let mut block = Block::new(BlockId::new(0));
    let mut next = 0;
    let mut args = Vec::new();
    for (ty, length) in signature.params.iter().zip(lengths) {
        assert!(
            matches!(ty, Ty::FatPtr(FatPtrKind::Slice(id)) if module.types.get(id.0 as usize) == Some(&Ty::Unit))
        );
        // A nonnull aligned allocation backs a unit slice. Its elements occupy
        // zero bytes, even for a length at the full usize boundary. No Unit SSA
        // value is fabricated and the selected body must perform no payload load.
        let data =
            value(&mut block, &mut next, Inst::Alloca { ty: Ty::U8, count: None, align: None });
        let metadata = value(
            &mut block,
            &mut next,
            Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(*length)) },
        );
        args.push(value(
            &mut block,
            &mut next,
            Inst::PtrFromParts { ptr_ty: ty.clone(), metadata_ty: Ty::U64, data, metadata },
        ));
    }
    args.push(value(
        &mut block,
        &mut next,
        Inst::Const { ty: Ty::Usize, value: Constant::Int(i128::from(index)) },
    ));
    let call = Inst::Call { callee: callee.id, args };
    let returns = if signature.returns.is_empty() {
        block.body.push(InstrNode::new(call));
        Vec::new()
    } else {
        vec![value(&mut block, &mut next, call)]
    };
    block.body.push(InstrNode::new(Inst::Return { values: returns }));
    let mut extended = module.clone();
    let id =
        FuncId::new(module.functions.iter().map(|f| f.id.0).max().unwrap().checked_add(1).unwrap());
    let ty = extended
        .add_func_type(FuncTy {
            params: vec![],
            returns: signature.returns,
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrapper = Function::new(id, "diagnostic_unit_slice_driver", ty, BlockId::new(0));
    wrapper.blocks.push(block);
    extended.try_add_function(wrapper).expect("Module::try_add_function: test fixture");
    assert!(trust_ir_build::validate_module(&extended).is_empty(), "invalid wrapper/subject");
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(
        trust_ir::binary::serialize_module(&restored),
        trust_ir::binary::serialize_module(module),
        "wrapper must preserve all original bodies and obligations"
    );
    match Interpreter::with_module(&extended)
        .with_options(InterpretOptions { fuel: 10_000, max_call_depth: 8, ..Default::default() })
        .execute_func(id, [])
    {
        Ok(result) => Outcome::Returned(
            result
                .returns
                .iter()
                .map(|v| u64::try_from(v.as_int().expect("usize result").as_unsigned()).unwrap())
                .collect(),
        ),
        Err(error) if error.code == InterpretErrorCode::Panic => Outcome::Panic,
        Err(error) => Outcome::Other(error.to_string()),
    }
}

fn check_subject(module: &Module) {
    for name in ["read_unit", "unit_index_effect", "reseat_unit"] {
        let function = function(module, name);
        let nodes: Vec<_> = function.blocks.iter().flat_map(|b| &b.body).collect();
        assert_eq!(nodes.iter().filter(|n| matches!(n.inst, Inst::Assert { .. })).count(), 1);
        assert_eq!(
            module.proof_obligations.iter().filter(|r| r.function == Some(function.id)).count(),
            1
        );
        assert!(
            !nodes.iter().any(|n| matches!(
                n.inst,
                Inst::PtrData { .. } | Inst::GEP { .. } | Inst::Load { .. }
            )),
            "unit payload must not be read"
        );
    }
    for (length, index) in
        [(0, 0), (1, 0), (1, 1), (5, 4), (5, 5), (u64::MAX, u64::MAX - 1), (u64::MAX, u64::MAX)]
    {
        for name in ["read_unit", "unit_index_effect"] {
            let expected = if index >= length {
                Outcome::Panic
            } else {
                Outcome::Returned(if name == "unit_index_effect" { vec![0] } else { vec![] })
            };
            assert_eq!(
                run(module, name, &[length], index),
                expected,
                "{name}: length={length}, index={index}"
            );
        }
    }
    for (a, b, index) in [(0, 1, 0), (1, 0, 0), (2, 5, 4), (5, 2, 4), (1, 1, 0)] {
        let expected = if index >= b { Outcome::Panic } else { Outcome::Returned(vec![]) };
        assert_eq!(
            run(module, "reseat_unit", &[a, b], index),
            expected,
            "must check reseated b, not original a"
        );
    }
}

#[test]
#[ignore = "requires a freshly emitted, compiler-bound unit-slice module"]
fn actual_unit_slices_preserve_bounds_effects_and_zero_results() {
    check_subject(&super::module("TRUST_SLICE_UNIT_IR"));
}

#[test]
#[ignore = "requires the fixed subject; diagnostic mutations never supply authority"]
fn actual_unit_slice_controls_detect_removed_checks_and_stale_metadata() {
    let module = super::module("TRUST_SLICE_UNIT_IR");
    check_subject(&module);
    let id = function(&module, "read_unit").id;
    let mut removed = module.clone();
    let body = &mut removed.functions.iter_mut().find(|f| f.id == id).unwrap().blocks;
    assert_eq!(body.len(), 1);
    body[0].body.retain(|n| !matches!(n.inst, Inst::Assert { .. }));
    removed.proof_obligations.retain(|r| r.function != Some(id));
    assert_eq!(run(&removed, "read_unit", &[0], 0), Outcome::Returned(vec![]));
    let mut reversed = module.clone();
    let mut count = 0;
    for node in reversed
        .functions
        .iter_mut()
        .find(|f| f.id == id)
        .unwrap()
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
    {
        if let Inst::ICmp { op, .. } = &mut node.inst {
            assert_eq!(*op, ICmpOp::Ult);
            *op = ICmpOp::Uge;
            count += 1;
        }
    }
    assert_eq!(count, 1);
    assert_eq!(run(&reversed, "read_unit", &[1], 0), Outcome::Panic);
    let id = function(&module, "reseat_unit").id;
    let mut stale = module.clone();
    let function = stale.functions.iter_mut().find(|f| f.id == id).unwrap();
    let original = function.blocks.iter().find(|b| b.id == function.entry).unwrap().params[0].0;
    let mut count = 0;
    for node in function.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::PtrMetadata { ptr, .. } = &mut node.inst {
            assert_ne!(*ptr, original);
            *ptr = original;
            count += 1;
        }
    }
    assert_eq!(count, 1);
    assert_eq!(run(&stale, "reseat_unit", &[0, 1], 0), Outcome::Panic);
}
