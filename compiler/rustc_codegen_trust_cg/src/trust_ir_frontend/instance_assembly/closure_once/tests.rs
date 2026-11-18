use trust_ir::{
    Block, BlockId, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, FuncTyId, InstrNode, Linkage,
    Ty, ValueId,
};

use super::*;

const SHIM: &str = "actual_rustc_closure_once_symbol";
fn origin() -> trust_ir::ty::TypeOrigin {
    let mut def_path_hash = [0; 16];
    def_path_hash[..8].copy_from_slice(&7u64.to_le_bytes());
    def_path_hash[8..].copy_from_slice(&3u64.to_le_bytes());
    trust_ir::ty::TypeOrigin::Rust {
        stable_crate_id: 7,
        def_path_hash,
        args_digest: trust_ir::ProofDigest::sha256_domain(
            trust_ir::ty::RUST_TYPE_ARGS_DOMAIN,
            b"exact source closure",
        ),
    }
}
fn fixture() -> Module {
    let mut module = Module::new("retained_closure_once");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
    module.func_types = vec![
        FuncTy { params: vec![Ty::U64], returns: vec![Ty::U64], is_vararg: false, abi: None },
        FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        },
    ];
    let closure = ClosureTyId::new(0);
    module.closure_types = vec![ClosureTy { func: FuncTyId::new(0), captures: vec![] }];
    module.closure_layouts = vec![ClosureLayoutDescriptor {
        origin: Some(origin()),
        closure,
        size: 0,
        align: 1,
        capture_offsets: vec![],
    }];
    let v = ValueId::new;
    let mut source =
        Function::new(FuncId::new(0), "actual_source_body", FuncTyId::new(1), BlockId::new(0))
            .with_producer(Producer::TRust);
    source.calling_conv = trust_ir::CallingConv::Rust;
    source.linkage = Linkage::Internal;
    source.blocks =
        vec![Block::new(BlockId::new(0)).with_param(v(0), Ty::Ptr).with_param(v(1), Ty::U64)];
    source.blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![v(1)] })];
    let mut adapter = Function::new(FuncId::new(1), SHIM, FuncTyId::new(0), BlockId::new(0))
        .with_producer(Producer::TRust);
    adapter.calling_conv = trust_ir::CallingConv::Rust;
    adapter.linkage = Linkage::Internal;
    adapter.body_gate = Some(BodyGate::Gated {
        authority: trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY.into(),
        evidence: None,
    });
    adapter.blocks = vec![Block::new(BlockId::new(0)).with_param(v(0), Ty::U64)];
    adapter.blocks[0].body = vec![
        InstrNode::new(Inst::MakeClosure { ty: closure, func: adapter.id, captures: vec![] })
            .with_result(v(1)),
        InstrNode::new(Inst::Alloca { ty: Ty::Closure(closure), count: None, align: Some(1) })
            .with_result(v(2)),
        InstrNode::new(Inst::Store {
            ty: Ty::Closure(closure),
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: Some(1),
        }),
        InstrNode::new(Inst::Call { callee: source.id, args: vec![v(2), v(0)] }).with_result(v(3)),
        InstrNode::new(Inst::Return { values: vec![v(3)] }),
    ];
    module.functions = vec![source, adapter];
    module
}
fn select(module: &Module) -> Result<FuncId, String> {
    select_adapter(
        module,
        FuncId::new(0),
        &origin(),
        SHIM,
        &BTreeSet::from([FuncId::new(0), FuncId::new(1)]),
    )
}

#[test]
fn retained_shim_selects_only_its_unchanged_nominal_adapter() {
    let module = fixture();
    let before = module.clone();
    assert_eq!(select(&module), Ok(FuncId::new(1)));
    assert_eq!(module, before, "binding creates or relabels no body or source image");
}

#[test]
fn retained_shim_requires_independent_source_and_adapter_conservation() {
    for ids in [BTreeSet::new(), BTreeSet::from([FuncId::new(0)]), BTreeSet::from([FuncId::new(1)])]
    {
        assert!(select_adapter(&fixture(), FuncId::new(0), &origin(), SHIM, &ids).is_err());
    }
}

#[test]
fn retained_shim_refuses_changed_protocol_or_authority() {
    for mutation in 0..5 {
        let mut module = fixture();
        let adapter = &mut module.functions[1];
        match mutation {
            0 => {
                adapter.blocks[0].body[1].inst =
                    Inst::Alloca { ty: Ty::Unit, count: None, align: Some(1) }
            }
            1 => {
                let Inst::Store { value, .. } = &mut adapter.blocks[0].body[2].inst else {
                    unreachable!()
                };
                *value = ValueId::new(0);
            }
            2 => adapter.blocks[0].body.insert(3, InstrNode::new(Inst::Unreachable)),
            3 => adapter.body_gate = None,
            _ => adapter.name = "another_real_shim".into(),
        }
        assert!(select(&module).is_err(), "protocol mutation {mutation}");
    }
}

#[test]
fn retained_shim_refuses_other_nominal_frames_targets_and_ambiguous_symbols() {
    for mutation in 0..7 {
        let mut module = fixture();
        match mutation {
            0 => module.closure_layouts.clear(),
            1 => module.closure_layouts[0].origin = None,
            2 => module.closure_layouts.push(module.closure_layouts[0].clone()),
            3 => module.closure_layouts[0].size = 8,
            4 => module.closure_layouts[0].align = 8,
            5 => {
                let Inst::Call { callee, .. } = &mut module.functions[1].blocks[0].body[3].inst
                else {
                    unreachable!()
                };
                *callee = FuncId::new(2);
            }
            _ => {
                let mut duplicate = module.functions[0].clone();
                duplicate.id = FuncId::new(2);
                duplicate.name = SHIM.into();
                module.functions.push(duplicate);
            }
        }
        assert!(select(&module).is_err(), "identity mutation {mutation}");
    }
}
