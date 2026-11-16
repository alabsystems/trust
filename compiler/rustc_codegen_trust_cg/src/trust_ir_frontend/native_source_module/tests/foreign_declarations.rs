use trust_ir::{Block, BlockId, CallingConv, Constant, FuncTy, Function, InstrNode, TargetInfo, Ty, ValueId};
use trust_ir::signature_abi::*;
use super::*;

pub(crate) fn fixture() -> Module {
    let scalar = |place| AbiArgument {
        size: 4, align: 4,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister { class: AbiRegisterClass::Integer, bytes: 4 },
            source_offset: 0, source_bytes: 4, value_bits: 32,
            attributes: AbiAttributes::default(),
        }),
        bindings: vec![AbiBinding { place, source_offset: 0, source_bytes: 4,
            carrier_offset: 0, carrier_bytes: 4 }],
    };
    let mut m = Module::new("source_foreign");
    m.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(), pointer_size: 8,
        endianness: Endianness::Little, abi: None, struct_passing: StructPassingPolicy::Unclassified,
    });
    let body_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I32], returns: vec![Ty::I32], is_vararg: false, abi: None,
    }).unwrap();
    let foreign_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I32], returns: vec![Ty::I32], is_vararg: true,
        abi: Some(SignatureAbi {
            target: AbiTarget { triple: "arm64-apple-macosx".into(), data_layout: "e-p:64:64".into(),
                abi: String::new(), cpu: "generic".into(), features: vec![],
                target_spec: "original-target-fixture".into(), pointer_bytes: 8, little_endian: true },
            frontend: AbiFrontend { name: "source-fixture".into(), revision: "1".into() },
            convention: "C".into(), lowered_convention: CallingConv::C, source_abi: "C".into(),
            can_unwind: false, variadic: true, fixed_count: 1,
            arguments: vec![scalar(AbiBindingPlace::Parameter(0))], result: scalar(AbiBindingPlace::Result(0)),
        }),
    }).unwrap();
    let mut caller = Function::new(FuncId::new(0), "caller", body_sig, BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    caller.calling_conv = CallingConv::Rust;
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I32);
    entry.body = vec![
        InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(73) }).with_result(ValueId::new(1)),
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0), ValueId::new(1)] })
            .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
    ];
    caller.blocks.push(entry);
    let mut foreign = Function::new(FuncId::new(1), "original_foreign", foreign_sig, BlockId::new(0));
    foreign.calling_conv = CallingConv::C;
    m.functions = vec![caller, foreign];
    m
}

#[test]
fn recorded_foreign_prefix_routes_but_requires_original_source_admission() {
    let m = fixture();
    let ids = BTreeSet::from([FuncId::new(0)]);
    let roots = ids.clone();
    let route = routing::NativeRouteInput { producer: &m, base: Some(&m), source_ids: &ids,
        roots: &roots, has_statics: false, target_triple: "arm64-apple-macosx", pointer_size: 8 };
    assert!(routing::uses_native_source(&route));
    let items = [NativeWorkItem { func: FuncId::new(0), symbol: "caller".into(),
        linkage: FunctionLinkage::External, never_inline: false, placement: None, inventory_residue: false }];
    let mut input = NativeModuleInput { producer: &m, base: Some(&m), items: &items,
        conserved: &ids, source_ids: &ids, foreign_declarations: &BTreeSet::new(), has_statics: false,
        target: &ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 } };
    assert!(!build(&input).refusals.is_empty(), "a descriptor alone cannot admit a foreign source");
    let foreign = BTreeSet::from([FuncId::new(1)]);
    input.foreign_declarations = &foreign;
    let out = build(&input);
    assert!(out.refusals.is_empty(), "{:?}", out.refusals);
    assert_eq!(out.m_cg, m);
    assert_eq!(out.symbols.get(&FuncId::new(1)).map(String::as_str), Some("original_foreign"));
    assert!(!out.bodies.contains_key("original_foreign"), "ABI does not invent a callee body");
    assert!(!out.placements.contains_key("original_foreign"), "ABI does not invent independent placement evidence");
}

#[test]
fn unsupported_unwind_target_and_source_census_keep_refusals() {
    for damage in 0..4 {
        let mut m = fixture();
        let abi = m.func_types[1].abi.as_mut().unwrap();
        match damage {
            0 => abi.can_unwind = true,
            1 => abi.target.pointer_bytes = 4,
            2 => abi.arguments[0].bindings.clear(),
            3 => abi.source_abi = "RustCall".into(),
            _ => unreachable!(),
        }
        assert!(!foreign_declarations::recorded(&m, FuncId::new(1)), "damage {damage}");
    }
}
