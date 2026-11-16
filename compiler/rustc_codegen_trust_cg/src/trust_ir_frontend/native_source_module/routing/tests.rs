use trust_ir::{Block, BlockId, Constant, FuncTy, Function, InstrNode, TargetInfo, ValueId};

use super::*;

fn scalar_module(ty: Ty, conv: CallingConv) -> Module {
    let mut module = Module::new("ordinary_source");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "ordinary_identity", sig, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    f.calling_conv = conv;
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), ty);
    entry.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module
}

fn routed(module: &Module) -> bool {
    let ids = module.functions.iter().map(|f| f.id).collect();
    uses_native_source(&NativeRouteInput {
        producer: module,
        base: Some(module),
        source_ids: &ids,
        roots: &BTreeSet::from([FuncId::new(0)]),
        has_statics: false,
        target_triple: "arm64-apple-macosx",
        pointer_size: 8,
    })
}

#[test]
fn ordinary_native_scalar_signatures_need_no_closure_anchor() {
    for conv in [CallingConv::Rust, CallingConv::C] {
        for ty in [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::Isize,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::Usize,
            Ty::Char,
            Ty::Ptr,
        ] {
            let module = scalar_module(ty.clone(), conv);
            assert!(!has_reachable_closure(&module, [FuncId::new(0)]));
            assert!(routed(&module), "{conv:?} {ty:?}");
        }
    }
}

#[test]
fn constants_unit_returns_and_local_source_dependencies_route_as_a_whole() {
    let mut module = scalar_module(Ty::U64, CallingConv::Rust);
    let mut helper = module.functions[0].clone();
    helper.id = FuncId::new(1);
    helper.name = "local_source_helper".into();
    module.functions.push(helper);
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
    ];
    assert!(routed(&module));
    let mut constant = scalar_module(Ty::U64, CallingConv::C);
    constant.func_types[0].params.clear();
    constant.functions[0].blocks[0].params.clear();
    constant.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(37) })
            .with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
    ];
    assert!(routed(&constant));
    constant.func_types[0].returns.clear();
    constant.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![] })];
    assert!(routed(&constant));
}

#[test]
fn changed_handoff_or_unowned_source_id_cannot_select_the_new_route() {
    let module = scalar_module(Ty::U64, CallingConv::Rust);
    let ids = BTreeSet::from([FuncId::new(0)]);
    let roots = ids.clone();
    let mut input = NativeRouteInput {
        producer: &module,
        base: Some(&module),
        source_ids: &ids,
        roots: &roots,
        has_statics: false,
        target_triple: "arm64-apple-macosx",
        pointer_size: 8,
    };
    assert!(uses_native_source(&input));
    let mut changed = module.clone();
    changed.files.push("another-source.rs".into());
    input.base = Some(&changed);
    assert!(!uses_native_source(&input));
    input.base = None;
    assert!(!uses_native_source(&input));
    input.base = Some(&module);
    let none = BTreeSet::new();
    input.source_ids = &none;
    assert!(!uses_native_source(&input));
    input.source_ids = &ids;
    input.roots = &none;
    assert!(!uses_native_source(&input));
    let absent = BTreeSet::from([FuncId::new(99)]);
    input.roots = &absent;
    assert!(!uses_native_source(&input));
}

#[test]
fn legacy_bool_wide_aggregate_and_rewritten_signatures_are_not_rerouted() {
    for ty in [Ty::Bool, Ty::I128, Ty::U128, Ty::Tuple(vec![Ty::U64])] {
        assert!(!routed(&scalar_module(ty.clone(), CallingConv::Rust)), "{ty:?}");
    }
    let mut module = scalar_module(Ty::U64, CallingConv::Rust);
    module.func_types[0].is_vararg = true;
    assert!(!routed(&module));
    module.func_types[0].is_vararg = false;
    let mut extra = module.func_types[0].clone();
    extra.params = vec![Ty::Tuple(vec![Ty::U64])];
    module.func_types.push(extra);
    assert!(!routed(&module), "unused aggregate signatures still need native witnesses");
}

#[test]
fn source_fp_route_retains_exact_target_image_and_source_ownership() {
    for ty in [Ty::F32, Ty::F64] {
        let module = scalar_module(ty, CallingConv::C);
        assert!(routed(&module));
        let ids = BTreeSet::from([FuncId::new(0)]);
        let mut input = NativeRouteInput { producer: &module, base: Some(&module),
            source_ids: &ids, roots: &ids, has_statics: false,
            target_triple: "arm64-apple-macosx", pointer_size: 8 };
        let empty = BTreeSet::new();
        input.source_ids = &empty;
        assert!(!uses_native_source(&input));
        input.source_ids = &ids;
        let mut changed = module.clone();
        changed.files.push("another-source.rs".into());
        input.base = Some(&changed);
        assert!(!uses_native_source(&input));
        let mut other_target = module.clone();
        other_target.target_info.as_mut().unwrap().triple = "x86_64-apple-macosx".into();
        input.producer = &other_target;input.base = Some(&other_target);
        input.target_triple = "x86_64-apple-macosx";
        assert!(!uses_native_source(&input), "other targets keep their previous route");
    }
}

#[test]
fn foreign_statics_wrong_target_and_non_source_bodies_keep_checked_legacy_routing() {
    let module = scalar_module(Ty::U8, CallingConv::C);
    let mut changed = module.clone();
    changed.functions[0].blocks.clear();
    assert!(!routed(&changed));
    let mut changed = module.clone();
    changed.functions[0].producer = None;
    assert!(!routed(&changed));
    let mut changed = module.clone();
    changed.global_asm.push("nop".into());
    assert!(!routed(&changed));
    let mut changed = module.clone();
    changed.target_info.as_mut().unwrap().pointer_size = 4;
    assert!(!routed(&changed));
    let mut changed = module.clone();
    changed.target_info.as_mut().unwrap().endianness = Endianness::Big;
    assert!(!routed(&changed));
    let mut changed = module.clone();
    changed.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
    assert!(!routed(&changed));
    let ids = BTreeSet::from([FuncId::new(0)]);
    let roots = ids.clone();
    let mut input = NativeRouteInput {
        producer: &module,
        base: Some(&module),
        source_ids: &ids,
        roots: &roots,
        has_statics: true,
        target_triple: "arm64-apple-macosx",
        pointer_size: 8,
    };
    assert!(!uses_native_source(&input));
    input.has_statics = false;
    input.target_triple = "aarch64-unknown-linux-gnu";
    assert!(!uses_native_source(&input));
}

#[test]
fn reachable_closures_still_select_native_refusals_when_primitive_guards_fail() {
    use trust_ir::{ClosureLayoutDescriptor, ClosureTy, ClosureTyId};
    let mut module = scalar_module(Ty::U64, CallingConv::Rust);
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![],
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
    let mut target = module.functions[0].clone();
    target.id = FuncId::new(1);
    target.name = "constructor_target".into();
    module.functions.push(target);
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(1),
            captures: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    assert!(has_reachable_closure(&module, [FuncId::new(0)]));
    assert!(!has_reachable_closure(&module, [FuncId::new(1)]));
    let none = BTreeSet::new();
    let roots = BTreeSet::from([FuncId::new(0)]);
    assert!(
        uses_native_source(&NativeRouteInput {
            producer: &module,
            base: None,
            source_ids: &none,
            roots: &roots,
            has_statics: true,
            target_triple: "not-the-target",
            pointer_size: 4,
        }),
        "closure data must never fall back to scalar ABI reconstruction"
    );
}

#[test]
fn unrelated_stored_source_bodies_do_not_broaden_the_emission_denominator() {
    let mut module = scalar_module(Ty::U64, CallingConv::Rust);
    let mut unrelated = module.functions[0].clone();
    unrelated.id = FuncId::new(1);
    unrelated.name = "unrelated_source_body".into();
    module.functions.push(unrelated);
    assert!(!routed(&module), "native whole-image emission must not replace existing root pruning");
    let ids = BTreeSet::from([FuncId::new(0), FuncId::new(1)]);
    assert!(uses_native_source(&NativeRouteInput {
        producer: &module,
        base: Some(&module),
        source_ids: &ids,
        roots: &ids,
        has_statics: false,
        target_triple: "arm64-apple-macosx",
        pointer_size: 8,
    }));
}
