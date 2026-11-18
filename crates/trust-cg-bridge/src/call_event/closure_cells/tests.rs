use trust_ir::{
    Block, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, FuncTy, Function, InstrNode, Ty,
};

use super::*;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn f(id: u32) -> FuncId {
    FuncId::new(id)
}

fn fixture(captured: bool) -> Module {
    let nominal = ClosureTyId::new(0);
    let captures = if captured { vec![Ty::U64] } else { vec![] };
    let mut module = Module::new("nominal_cells");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    for params in [vec![], captures.clone(), captures.clone(), vec![Ty::Closure(nominal)]] {
        module
            .add_func_type(FuncTy { params, returns: vec![Ty::U64], is_vararg: false, abi: None })
            .unwrap();
    }
    module.closure_types.push(ClosureTy { func: trust_ir::FuncTyId::new(0), captures });
    let alignment = if captured { 8 } else { 1 };
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: nominal,
        size: if captured { 8 } else { 0 },
        align: alignment,
        capture_offsets: if captured { vec![0] } else { vec![] },
    });
    let mut caller = Function::new(f(0), "caller", trust_ir::FuncTyId::new(1), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    if captured {
        block = block.with_param(v(0), Ty::U64);
    }
    block.body = vec![
        InstrNode::new(Inst::MakeClosure {
            ty: nominal,
            func: f(1),
            captures: if captured { vec![v(0)] } else { vec![] },
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Alloca {
            ty: Ty::Closure(nominal),
            count: None,
            align: Some(alignment),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Store {
            ty: Ty::Closure(nominal),
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: Some(alignment),
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::Closure(nominal),
            ptr: v(2),
            volatile: false,
            align: Some(alignment),
        })
        .with_result(v(3)),
        if captured {
            InstrNode::new(Inst::Call { callee: f(2), args: vec![v(3)] }).with_result(v(4))
        } else {
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(41) }).with_result(v(4))
        },
        InstrNode::new(Inst::Return { values: vec![v(4)] }),
    ];
    caller.blocks.push(block);
    let mut target = Function::new(f(1), "target", trust_ir::FuncTyId::new(2), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    if captured {
        block = block.with_param(v(0), Ty::U64);
        block.body = vec![InstrNode::new(Inst::Return { values: vec![v(0)] })];
    } else {
        block.body = vec![
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(17) }).with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ];
    }
    target.blocks.push(block);
    let mut receiver = Function::new(f(2), "receiver", trust_ir::FuncTyId::new(3), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(v(0), Ty::Closure(nominal));
    block.body = vec![
        if captured {
            InstrNode::new(Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 0 })
                .with_result(v(1))
        } else {
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(17) }).with_result(v(1))
        },
        InstrNode::new(Inst::Return { values: vec![v(1)] }),
    ];
    receiver.blocks.push(block);
    module.functions = vec![caller, target, receiver];
    for function in &mut module.functions {
        function.producer = Some(trust_ir::Producer::TRust);
        function.calling_conv = CallingConv::Rust;
    }
    module
}

fn evaluate(module: &Module) -> Result<SpecResult, String> {
    let maps = BTreeMap::new();
    let places = BTreeMap::new();
    let input = CerInput {
        m_cg: module,
        producers: &[],
        bodies: &maps,
        placements: &places,
        object: &[],
        relocation_model: RelocationModel::Static,
    };
    let function = &module.functions[0];
    let signature = signature_of(module, function.ty)?;
    let scalar = ParamPlace::Scalar(ScalarPlace::gpr(0, 64));
    let place = FnPlacement {
        params: signature.0.iter().map(|_| scalar.clone()).collect(),
        ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
    };
    let mut decisions = BTreeMap::new();
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            if matches!(node.inst, Inst::Call { .. }) {
                decisions.insert(
                    (block.id.index(), index),
                    SiteDecision::Called {
                        symbol: "receiver".into(),
                        place: FnPlacement { params: vec![scalar.clone()], ret: place.ret.clone() },
                        result_width: Some(64),
                    },
                );
            }
        }
    }
    eval_spec(&input, module, function, &signature, &place, &decisions)
}

fn reference(module: &Module, captured: bool) -> i128 {
    let args = if captured {
        vec![trust_ir::interpret::InterpretValue::int(Ty::U64, 73).unwrap()]
    } else {
        vec![]
    };
    let result =
        trust_ir::interpret::Interpreter::with_module(module).execute_func(f(0), args).unwrap();
    assert_eq!(result.host_calls, 0);
    result.returns[0].as_int().unwrap().as_signed()
}

#[test]
fn empty_nominal_cell_roundtrip_preserves_source_and_reference_result() {
    let module = fixture(false);
    let before = module.stable_digest();
    let spec = evaluate(&module).unwrap();
    assert_eq!(spec.value, Formula::BitVec { value: 41, width: 64 });
    assert!(spec.events.is_empty());
    assert!(spec.memory.accesses.is_empty());
    assert!(
        spec.memory.missing_integration().is_some(),
        "zero bytes do not discharge the actual allocation/frame proof"
    );
    assert_eq!(reference(&module, false), 41);
    assert_eq!(
        module.stable_digest(),
        before,
        "the evaluator preserves the actual source operations"
    );
}

#[test]
fn loaded_nominal_capture_remains_the_original_direct_call_argument() {
    let module = fixture(true);
    let spec = evaluate(&module).unwrap();
    assert_eq!(spec.events[&(0, 4)][0].args, vec![xn(0)]);
    assert!(spec.memory.accesses.is_empty(), "the cell address never escapes");
    assert!(spec.memory.missing_integration().is_some(), "logical storage is not O4/O5 evidence");
    assert_eq!(reference(&module, true), 73);
}

#[test]
fn a_second_store_replaces_the_full_capture_value() {
    let mut module = fixture(true);
    module.functions[0].blocks[0].body.splice(
        3..3,
        [
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(99) }).with_result(v(9)),
            InstrNode::new(Inst::MakeClosure {
                ty: ClosureTyId::new(0),
                func: f(1),
                captures: vec![v(9)],
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Store {
                ty: Ty::Closure(ClosureTyId::new(0)),
                ptr: v(2),
                value: v(10),
                volatile: false,
                align: Some(8),
            }),
        ],
    );
    let spec = evaluate(&module).unwrap();
    assert_eq!(spec.events[&(0, 7)][0].args, vec![Formula::BitVec { value: 99, width: 64 }]);
    assert_eq!(reference(&module, true), 99);
}

#[test]
fn borrowed_environment_pointer_to_a_real_callee_still_refuses() {
    let mut module = fixture(false);
    module.func_types[3].params = vec![Ty::Ptr];
    module.functions[2].blocks[0].params[0].1 = Ty::Ptr;
    module.functions[0].blocks[0].body.remove(3);
    module.functions[0].blocks[0].body[3] =
        InstrNode::new(Inst::Call { callee: f(2), args: vec![v(2)] }).with_result(v(4));
    assert_eq!(
        reference(&module, false),
        17,
        "this is a real valid source borrow, not a malformed fixture"
    );
    let error = evaluate(&module).err().unwrap();
    assert!(error.contains("address escapes"), "{error}");
}

#[test]
fn count_alignment_initialization_and_address_use_refusals_are_preserved() {
    for change in 0..10 {
        let mut module = fixture(true);
        let body = &mut module.functions[0].blocks[0].body;
        match change {
            0 => {
                let Inst::Alloca { count, .. } = &mut body[1].inst else { unreachable!() };
                *count = Some(v(0));
            }
            1 => {
                let Inst::Alloca { align, .. } = &mut body[1].inst else { unreachable!() };
                *align = Some(0);
            }
            2 => {
                let Inst::Alloca { align, .. } = &mut body[1].inst else { unreachable!() };
                *align = Some(1);
            }
            3 => {
                let Inst::Store { volatile, .. } = &mut body[2].inst else { unreachable!() };
                *volatile = true;
            }
            4 => {
                let Inst::Load { volatile, .. } = &mut body[3].inst else { unreachable!() };
                *volatile = true;
            }
            5 => {
                let Inst::Store { align, .. } = &mut body[2].inst else { unreachable!() };
                *align = Some(1);
            }
            6 => {
                let Inst::Load { ty, .. } = &mut body[3].inst else { unreachable!() };
                *ty = Ty::U64;
            }
            7 => {
                body.swap(2, 3);
            }
            8 => {
                body[3].results[0] = v(1);
            }
            _ => {
                let rest = body.split_off(2);
                body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] }));
                let mut next = Block::new(BlockId::new(1));
                next.body = rest;
                module.functions[0].blocks.push(next);
            }
        }
        assert!(evaluate(&module).is_err(), "hostile cell mutation {change}");
    }
}

#[test]
fn conflicting_targets_and_unknown_incoming_identity_cannot_be_laundered() {
    let module = fixture(true);
    let incoming = ClosureValue::incoming(
        &module,
        ClosureTyId::new(0),
        v(0),
        &ParamPlace::Scalar(ScalarPlace::gpr(0, 64)),
    )
    .unwrap();
    assert!(incoming.check_local_storage(ClosureTyId::new(0), f(1), &[Ty::U64]).is_err());
    let mut changed = module;
    let mut other = changed.functions[1].clone();
    other.id = f(3);
    other.name = "other_target".into();
    changed.functions.push(other);
    changed.functions[0].blocks[0].body.insert(
        4,
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: f(3),
            captures: vec![v(0)],
        })
        .with_result(v(9)),
    );
    let error = evaluate(&changed).err().unwrap();
    assert!(error.contains("conflicting closure storage targets"), "{error}");
}

#[test]
fn nominal_cell_source_support_cannot_issue_a_compiled_function_grade() {
    // Reuse ordinary retained Compiler bytes, then change BOTH source input
    // views by adding a nonescaping nominal allocation. This is hostile DATA,
    // not a fresh compiler/source capability or a positive native result.
    let mut data = crate::compiler_input_capture::CompilerInputCapture::from_bytes(include_bytes!(
        "../closure_original/strict-pointer-input.json"
    ))
    .unwrap()
    .decode_inputs()
    .unwrap();
    let (producer_index, id, symbol, nominal, alignment) = data
        .producers
        .iter()
        .enumerate()
        .find_map(|(index, producer)| {
            producer.module.functions.iter().find_map(|function| {
                let entry = function.block(function.entry)?;
                let (_, IrTy::Closure(nominal)) = entry.params.first()? else { return None };
                let binding = producer.module.closure_storage_binding(*nominal).ok()?;
                Some((index, function.id, function.name.clone(), *nominal, binding.layout.align))
            })
        })
        .expect("the retained ordinary input has its nominal closure body");
    let original = data.producers[producer_index].module.function_by_id(id).unwrap();
    let codegen = data.m_cg.functions.iter().find(|function| function.name == symbol).unwrap();
    let fresh = original
        .blocks
        .iter()
        .chain(&codegen.blocks)
        .flat_map(|block| {
            block
                .params
                .iter()
                .map(|(id, _)| id)
                .chain(block.body.iter().flat_map(|node| &node.results))
        })
        .map(|value| value.index())
        .max()
        .unwrap()
        .checked_add(1)
        .unwrap();
    let allocation = InstrNode::new(Inst::Alloca {
        ty: IrTy::Closure(nominal),
        count: None,
        align: Some(alignment),
    })
    .with_result(v(fresh));
    let module = Arc::make_mut(&mut data.producers[producer_index].module);
    let function = module.functions.iter_mut().find(|function| function.id == id).unwrap();
    function
        .blocks
        .iter_mut()
        .find(|block| block.id == function.entry)
        .unwrap()
        .body
        .insert(0, allocation.clone());
    let function = data.m_cg.functions.iter_mut().find(|function| function.name == symbol).unwrap();
    function
        .blocks
        .iter_mut()
        .find(|block| block.id == function.entry)
        .unwrap()
        .body
        .insert(0, allocation);
    let report = verify_compiled_module(&data.input()).unwrap();
    let row = report.certificate(&symbol).unwrap();
    assert!(
        row.obligations.o4_return.detail.contains("PTR.3b source memory modeled"),
        "{}",
        report.to_json()
    );
    assert!(matches!(row.verdict, OutputVerdict::Unknown { .. }));
    assert!(row.original_proof.is_none());
    assert!(!row.is_kernel_proved());
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
}
