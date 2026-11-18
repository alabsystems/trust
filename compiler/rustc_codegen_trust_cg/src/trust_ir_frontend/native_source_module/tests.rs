use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, ClosureLayoutDescriptor, ClosureTy, ClosureTyId,
    Constant, FuncTy, Function, InstrNode, TargetInfo, Ty, ValueId,
};

use super::*;

pub(super) fn fixture() -> (Module, Vec<NativeWorkItem>) {
    let mut module = Module::new("native_source");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module.files.push("source.rs".into());
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let physical = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let environment = module
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0))],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    module.closure_types.push(ClosureTy { func: apparent, captures: vec![Ty::U64] });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    for (id, name, ty, input_ty) in [
        (0, "owner", physical, Ty::U64),
        (1, "body", environment, Ty::Closure(ClosureTyId::new(0))),
        (2, "adapter", physical, Ty::U64),
    ] {
        let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
        function.producer = Some(Producer::TRust);
        function.calling_conv = CallingConv::Rust;
        function.linkage = if id == 0 { Linkage::External } else { Linkage::Internal };
        function.body_gate = Some(BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
        let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), input_ty);
        if id != 1 {
            block.body.push(
                InstrNode::new(Inst::MakeClosure {
                    ty: ClosureTyId::new(0),
                    func: FuncId::new(2),
                    captures: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
            );
        }
        let result = if id == 2 {
            block.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(1)] })
                    .with_result(ValueId::new(2)),
            );
            ValueId::new(2)
        } else if id == 1 {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) })
                    .with_result(ValueId::new(1)),
            );
            ValueId::new(1)
        } else {
            ValueId::new(0)
        };
        block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
        function.blocks.push(block);
        module.functions.push(function);
    }
    let items = vec![
        NativeWorkItem {
            func: FuncId::new(0),
            symbol: "owner".into(),
            linkage: FunctionLinkage::External,
            never_inline: false,
            placement: None,
            inventory_residue: false, adapter_identity: None,
        },
        NativeWorkItem {
            func: FuncId::new(1),
            symbol: "body".into(),
            linkage: FunctionLinkage::Internal,
            never_inline: false,
            placement: None,
            inventory_residue: false, adapter_identity: None,
        },
    ];
    (module, items)
}

fn output(
    module: &Module,
    base: &Module,
    items: &[NativeWorkItem],
    conserved: &[u32],
) -> CodegenModuleOutput {
    build(&NativeModuleInput {
        producer: module,
        base: Some(base),
        items,
        conserved: &conserved.iter().copied().map(FuncId::new).collect(),
        source_ids: &BTreeSet::from([FuncId::new(0), FuncId::new(1)]),
        foreign_declarations: &BTreeSet::new(),
        has_statics: false,
        target: &ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 },
    })
}

#[test]
fn complete_source_and_adapter_keep_logical_bodies_and_all_tables() {
    let (module, items) = fixture();
    let out = output(&module, &module, &items, &[0, 1, 2]);
    assert!(out.refusals.is_empty(), "{:?}", out.refusals);
    assert_eq!(out.m_cg, module);
    assert_eq!(out.bodies.len(), 3);
    assert_eq!(out.symbols.len(), 3);
    assert!(out.residue.is_empty(), "an adapter gets no fabricated Rust inventory row");
    let (module, mut items) = fixture();
    items[1].inventory_residue = true;
    let out = output(&module, &module, &items, &[0, 1, 2]);
    assert!(out.refusals.is_empty());
    assert_eq!(out.residue.len(), 1);
    assert_eq!(out.residue[0].producer_func, FuncId::new(1));
    assert_eq!(out.m_cg, module);
}

#[test]
fn adapter_license_cannot_survive_an_edited_handoff_or_missing_conservation() {
    let (module, items) = fixture();
    let mut changed = module.clone();
    changed.functions[1].blocks[0].body[0].inst =
        Inst::Const { ty: Ty::U64, value: Constant::Int(8) };
    assert!(!output(&changed, &module, &items, &[0, 1, 2]).refusals.is_empty());
    assert!(!output(&module, &module, &items, &[0, 1]).refusals.is_empty());
    assert!(!output(&module, &module, &items[..1], &[0, 1, 2]).refusals.is_empty());
    let missing_base = build(&NativeModuleInput {
        producer: &module,
        base: None,
        items: &items,
        conserved: &BTreeSet::from([FuncId::new(0), FuncId::new(1), FuncId::new(2)]),
        source_ids: &BTreeSet::from([FuncId::new(0), FuncId::new(1)]),
        foreign_declarations: &BTreeSet::new(),
        has_statics: false,
        target: &ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 },
    });
    assert!(!missing_base.refusals.is_empty());
}

#[test]
fn reachable_constructor_targets_are_censused_but_dead_ones_do_not_route_a_root() {
    let (mut module, items) = fixture();
    assert!(has_reachable_closure(&module, [FuncId::new(0)]));
    assert!(!has_reachable_closure(&module, [FuncId::new(1)]));
    module.functions[2].blocks[0].body[1].inst =
        Inst::Call { callee: FuncId::new(99), args: vec![ValueId::new(1)] };
    let out = output(&module, &module, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty(), "missing adapter target must remain a refusal");
}
