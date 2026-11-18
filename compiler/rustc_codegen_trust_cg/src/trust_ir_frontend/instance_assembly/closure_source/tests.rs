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

fn zero_origin_with_crate(stable_crate_id: u64) -> trust_ir::ty::TypeOrigin {
    let mut def_path_hash = [0; 16];
    def_path_hash[..8].copy_from_slice(&stable_crate_id.to_le_bytes());
    def_path_hash[8..].copy_from_slice(&9u64.to_le_bytes());
    trust_ir::ty::TypeOrigin::Rust {
        stable_crate_id,
        def_path_hash,
        args_digest: trust_ir::ProofDigest::sha256_domain(
            trust_ir::ty::RUST_TYPE_ARGS_DOMAIN,
            b"fixture",
        ),
    }
}
fn zero_origin() -> trust_ir::ty::TypeOrigin {
    zero_origin_with_crate(7)
}

fn zero_fixture() -> Module {
    let mut module = fixture();
    module.closure_types[0].captures.clear();
    module.closure_layouts[0].origin = Some(zero_origin());
    module.closure_layouts[0].size = 0;
    module.closure_layouts[0].align = 1;
    module.closure_layouts[0].capture_offsets.clear();
    let signature = module.functions[0].ty;
    module.func_types[signature.as_usize()].params[0] = Ty::Ptr;
    module.functions[0].blocks[0].params[0].1 = Ty::Ptr;
    module
}

#[test]
fn owned_zero_body_retains_its_typed_frame_and_apparent_arguments() {
    let mut module = zero_fixture();
    let signature = module.functions[0].ty;
    module.func_types[signature.as_usize()].params[0] = Ty::Closure(ClosureTyId::new(0));
    module.functions[0].blocks[0].params[0].1 = Ty::Closure(ClosureTyId::new(0));
    let before = module.clone();
    validate(&module, FuncId::new(0), SYMBOL, 0, AUTHORITY).unwrap();
    assert_eq!(module, before);
    assert!(check_zero(&module).is_err(), "owned FnOnce must not acquire a borrowed Fn ABI");
    module.closure_layouts[0].size = 8;
    assert!(validate(&module, FuncId::new(0), SYMBOL, 0, AUTHORITY).is_err());
}

fn check_zero(module: &Module) -> Result<(), String> {
    validate_borrowed_zero(module, FuncId::new(0), SYMBOL, &zero_origin(), AUTHORITY)
}

#[test]
fn borrowed_zero_body_retains_actual_source_origin_and_pointer_signature() {
    let module = zero_fixture();
    let before = module.clone();
    assert!(check_zero(&module).is_ok());
    assert_eq!(module, before);
    assert!(check(&module).is_err(), "borrowed Fn must not masquerade as by-value FnOnce");
}

#[test]
fn borrowed_zero_refuses_lost_changed_or_ambiguous_source_frames() {
    for change in 0..5 {
        let mut module = zero_fixture();
        match change {
            0 => module.closure_layouts.clear(),
            1 => module.closure_layouts[0].origin = None,
            2 => module.closure_layouts[0].origin = Some(zero_origin_with_crate(8)),
            3 => {
                module.closure_layouts[0].size = 8;
                module.closure_layouts[0].align = 8;
            }
            _ => module.closure_layouts.push(module.closure_layouts[0].clone()),
        }
        assert!(check_zero(&module).is_err(), "frame mutation {change}");
    }
}

#[test]
fn borrowed_zero_retains_source_body_signature_entry_and_gate_refusals() {
    for change in 0..5 {
        let mut module = zero_fixture();
        let signature = module.functions[0].ty;
        match change {
            0 => module.functions[0].body_gate = None,
            1 => module.functions[0].blocks[0].params[0].1 = Ty::Unit,
            2 => module.func_types[signature.as_usize()].params[0] = Ty::Unit,
            3 => module.func_types[signature.as_usize()].returns = vec![Ty::U32],
            _ => module.functions[0].name.push_str("_wrong_source"),
        }
        assert!(check_zero(&module).is_err(), "source mutation {change}");
    }
}
