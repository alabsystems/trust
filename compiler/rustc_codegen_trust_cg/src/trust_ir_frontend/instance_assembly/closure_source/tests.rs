use trust_ir::{
    Block, BlockId, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Constant, FuncTy, Function,
    Inst, InstrNode, ValueId,
};

use super::*;
const SYMBOL: &str = "_RNC_source_once";
const AUTHORITY: &str = "trust-direct-lane-structural";
fn fixture() -> Module {
    let mut module = Module::new("source_closure");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![Ty::U8],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    module.closure_types.push(ClosureTy { func: apparent, captures: vec![Ty::Ptr, Ty::U8] });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 8],
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0)), Ty::U8],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), SYMBOL, signature, BlockId::new(0));
    function.calling_conv = CallingConv::Rust;
    function.producer = Some(Producer::TRust);
    function.body_gate = Some(BodyGate::Gated { authority: AUTHORITY.into(), evidence: None });
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Closure(ClosureTyId::new(0))),
            (ValueId::new(1), Ty::U8),
        ],
        body: vec![
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ],
    });
    module.functions.push(function);
    module
}
fn check(module: &Module) -> Result<(), String> {
    validate(module, FuncId::new(0), SYMBOL, 2, AUTHORITY)
}
#[test]
fn authentic_source_body_keeps_its_complete_table_image() {
    let module = fixture();
    let before = module.clone();
    check(&module).unwrap();
    assert_eq!(module, before);
}
#[test]
fn source_identity_and_authority_cannot_be_replaced() {
    for change in 0..6 {
        let mut module = fixture();
        match change {
            0 => module.functions[0].name = "another_symbol".into(),
            1 => module.functions[0].producer = Some(Producer::Clean),
            2 => module.functions[0].blocks.clear(),
            3 => module.functions[0].body_gate = None,
            4 => module.functions[0].body_gate = Some(BodyGate::Ungated),
            _ => {
                module.functions[0].body_gate =
                    Some(BodyGate::Gated { authority: "another-authority".into(), evidence: None })
            }
        }
        assert!(check(&module).is_err(), "identity mutation {change}");
    }
}
#[test]
fn env_pointer_or_wrong_capture_count_is_refused() {
    let mut module = fixture();
    let signature = module.functions[0].ty;
    module.func_types[signature.as_usize()].params[0] = Ty::Ptr;
    assert!(check(&module).unwrap_err().contains("by value"));
    assert!(
        validate(&fixture(), FuncId::new(0), SYMBOL, 3, AUTHORITY)
            .unwrap_err()
            .contains("capture count")
    );
}
#[test]
fn observed_layout_is_required_and_cannot_be_recomputed() {
    for change in 0..3 {
        let mut module = fixture();
        match change {
            0 => module.closure_layouts.clear(),
            1 => module.closure_layouts[0].capture_offsets = vec![0, 0],
            _ => module.closure_layouts[0].align = 3,
        }
        assert!(check(&module).is_err(), "layout mutation {change}");
    }
}
#[test]
fn actual_entry_and_apparent_call_signature_must_agree() {
    for change in 0..4 {
        let mut module = fixture();
        let signature = module.functions[0].ty;
        match change {
            0 => module.func_types[0].params[0] = Ty::U16,
            1 => module.func_types[signature.as_usize()].returns = vec![Ty::U32],
            2 => module.functions[0].blocks[0].params[0].1 = Ty::Ptr,
            _ => module.functions[0].calling_conv = CallingConv::C,
        }
        assert!(check(&module).is_err(), "signature mutation {change}");
    }
}
