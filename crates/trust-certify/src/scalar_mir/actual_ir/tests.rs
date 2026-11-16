use super::*;

// The instruction population is the actual compiler08 direct THIR spelling,
// not the separate native MIR compatibility bundle (which remains refused).
fn actual_shape() -> Module {
    trust_ir::parser::parse_module(
        r#"
module "scalar_actual"
target "arm64-apple-macosx" 8 little structpass=unclassified
functy.0 = (u8) -> (u16)
rustcc fn @successor(functy.0) {
bb0(%0: u8):
    %1 = zext u8 %0 to u16
    %2 = const u16 1
    %3, %4 = add.overflow u16 %1, %2
    %5 = const bool false
    %6 = const bool true
    %7 = select bool %4, %5, %6
    assert %7
    ret %3
}
"#,
    )
    .unwrap()
}

#[test]
fn actual_ir_reader_preserves_all_eight_instructions_and_typed_ids() {
    assert_eq!(read(&actual_shape(), FuncId::new(0)).unwrap(), fixed_program());
}

/// Trust (trust-ir v52): the producer now names its check — the u16 add overflow — and the
/// reader admits exactly that kind beside `Unspecified` (the same check, unnamed); a kind that
/// names another panic, or a SITED assert (v54: an entry call the model does not have), is not
/// this family's.
#[test]
fn actual_ir_reader_admits_only_the_checks_own_kind_and_no_site() {
    let with = |kind: AssertKind, site: Option<trust_ir::PanicSite>| {
        let mut changed = actual_shape();
        changed.functions[0].blocks[0].body[6].inst =
            Inst::Assert { cond: ValueId::new(7), kind, site };
        read(&changed, FuncId::new(0))
    };
    assert_eq!(with(AssertKind::Overflow(AssertOverflowOp::Add), None).unwrap(), fixed_program());
    assert_eq!(with(AssertKind::Unspecified, None).unwrap(), fixed_program());
    for kind in [
        AssertKind::Overflow(AssertOverflowOp::Sub),
        AssertKind::Overflow(AssertOverflowOp::Mul),
        AssertKind::DivByZero,
        AssertKind::NullPtr,
    ] {
        assert!(with(kind, None).is_err(), "{kind:?}");
    }
    let site = trust_ir::PanicSite {
        entry: FuncId::new(0),
        location: trust_ir::PanicLocation::Value(ValueId::new(0)),
    };
    assert!(with(AssertKind::Overflow(AssertOverflowOp::Add), Some(site)).is_err());
}

#[test]
fn actual_ir_reader_rejects_close_semantic_and_inventory_mutations() {
    let original = actual_shape();
    let mut changes = Vec::new();
    for index in 0..8 {
        let mut changed = original.clone();
        changed.functions[0].blocks[0].body.remove(index);
        changes.push(changed);
    }
    let mut changed = original.clone();
    let extra = changed.functions[0].blocks[0].body[0].clone();
    changed.functions[0].blocks[0].body.push(extra);
    changes.push(changed);
    for inst in [
        Inst::Const { ty: Ty::U16, value: Constant::Int(2) },
        Inst::Const { ty: Ty::U8, value: Constant::Int(1) },
        Inst::Undef { ty: Ty::U16 },
    ] {
        let mut changed = original.clone();
        changed.functions[0].blocks[0].body[1].inst = inst;
        changes.push(changed);
    }
    for index in [3, 4] {
        let mut changed = original.clone();
        changed.functions[0].blocks[0].body[index].inst =
            Inst::Const { ty: Ty::Bool, value: Constant::Bool(index == 3) };
        changes.push(changed);
    }
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[5].inst = Inst::Select {
        ty: Ty::Bool,
        cond: ValueId::new(4),
        then_val: ValueId::new(6),
        else_val: ValueId::new(5),
    };
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[6].inst = Inst::Assume { cond: ValueId::new(7) };
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[7].inst = Inst::Return { values: vec![ValueId::new(1)] };
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[2].results.swap(0, 1);
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions[0].calling_conv = CallingConv::C;
    changes.push(changed);
    let mut changed = original.clone();
    changed.func_types[0].is_vararg = true;
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions.push(changed.functions[0].clone());
    changes.push(changed);
    for inst in [
        Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] },
        Inst::Br { target: original.functions[0].entry, args: vec![ValueId::new(0)] },
    ] {
        let mut changed = original.clone();
        changed.functions[0].blocks[0].body[7].inst = inst;
        changes.push(changed);
    }
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[6].proof_context = Some(Default::default());
    changes.push(changed);
    let mut changed = original.clone();
    changed.functions[0].blocks[0].body[6].proofs =
        vec![trust_ir::ProofAnnotation::NoOverflow, trust_ir::ProofAnnotation::Pure];
    changes.push(changed);
    for (index, changed) in changes.iter().enumerate() {
        assert!(read(changed, FuncId::new(0)).is_err(), "mutation {index}");
    }
    assert!(read(&original, FuncId::new(1)).is_err());
}

#[test]
#[ignore = "requires the retained actual compiler direct module and native bundle"]
fn retained_actual_direct_module_checks_but_native_compatibility_remains_refused() {
    let path = std::env::var("TRUST_SCALAR_ACTUAL_IR_BINARY").unwrap();
    let bytes = std::fs::read(path).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    let certificate = prove_actual_successor_ir(&module, FuncId::new(0)).unwrap();
    certificate.replay(&module, FuncId::new(0)).unwrap();
    let mut changed = module.clone();
    changed.name.push_str("_changed");
    assert!(certificate.replay(&changed, FuncId::new(0)).is_err());
    assert!(certificate.replay(&module, FuncId::new(1)).is_err());
    assert!(!module.proof_obligations.is_empty());
    let mut changed = module.clone();
    changed.proof_obligations[0].description.push_str("_changed");
    assert!(certificate.replay(&changed, FuncId::new(0)).is_err());
    let native_path = std::env::var("TRUST_SCALAR_ACTUAL_NATIVE_JSON").unwrap();
    let native: trust_ir::NativeVerificationBundle =
        serde_json::from_slice(&std::fs::read(native_path).unwrap()).unwrap();
    assert!(read(&native.module, FuncId::new(0)).is_err());
}

#[test]
fn actual_module_retained_byte_limit_is_enforced_while_serializing() {
    let mut module = actual_shape();
    module.name = "x".repeat(1024 * 1024);
    assert!(module_bytes(&module).is_err());
}
