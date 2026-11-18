use trust_ir::function_dependencies::inspect_function_dependencies;
use trust_ir_build::ModuleBuilder;

use super::*;

fn subject(extra: &str) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("rust_inventory_fragment");
    let signature = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("subject", signature);
    let entry = fb.create_block();
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let value = fb.binop(BinOp::Xor, Ty::U64, x, y);
    match extra {
        "panic" => {
            let no = fb.bool_const(false);
            fb.assert(no);
        }
        "memory" => {
            fb.alloca(Ty::U64);
        }
        "unknown-value" => {
            fb.undef(Ty::U64);
        }
        "function-address" => {
            fb.fn_addr(signature, FuncId::new(0));
        }
        "arithmetic" => {
            fb.add(Ty::U64, x, y);
        }
        "none" => {}
        _ => panic!("unrecognized fixture"),
    }
    fb.ret(vec![value]);
    let function = fb.build();
    let mut module = mb.build().unwrap();
    module.function_by_id_mut(function).unwrap().producer = Some(Producer::TRust);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, function)
}

#[test]
fn exact_scalar_body_answers_without_mutating_the_handoff() {
    let (module, function) = subject("none");
    let before = module.clone();
    assert!(ModuleInventory::new(&module).call_free(function));
    assert_eq!(module, before);
}

#[test]
fn absent_panic_dependencies_do_not_make_the_body_inventory_complete() {
    let (module, function) = subject("panic");
    // The explicit census deliberately does not model the panic runtime.
    assert!(inspect_function_dependencies(&module, function).refusals().is_empty());
    assert!(!ModuleInventory::new(&module).call_free(function));
}

#[test]
fn unsupported_values_keep_the_existing_inventory_walk() {
    for extra in ["unknown-value", "function-address"] {
        let (module, function) = subject(extra);
        assert!(!ModuleInventory::new(&module).call_free(function), "{extra}");
    }
}

#[test]
fn scalar_cells_and_explicit_modular_arithmetic_have_no_runtime_dependencies() {
    for extra in ["memory", "arithmetic"] {
        let (module, function) = subject(extra);
        assert!(ModuleInventory::new(&module).call_free(function), "{extra}");
    }
}

fn pointer_comparison() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("scalar_cell_pointer_inventory");
    let signature = mb.add_func_type(vec![Ty::U64], vec![Ty::U32]);
    let mut fb = mb.function("compare_cell", signature);
    let entry = fb.create_block();
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let cell = fb.alloca(Ty::U64);
    fb.store(Ty::U64, cell, input);
    let loaded = fb.load(Ty::U64, cell);
    let mixed = fb.binop(BinOp::Add, Ty::U64, loaded, input);
    fb.store(Ty::U64, cell, mixed);
    let same = fb.icmp(trust_ir::ICmpOp::Eq, Ty::Ptr, cell, cell);
    let result = fb.cast(CastOp::ZExt, Ty::Bool, Ty::U32, same);
    fb.ret(vec![result]);
    let function = fb.build();
    let mut module = mb.build().unwrap();
    module.function_by_id_mut(function).unwrap().producer = Some(Producer::TRust);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, function)
}

#[test]
fn local_memory_pointer_comparison_reads_the_original_image() {
    let (module, function) = pointer_comparison();
    let before = module.clone();
    assert!(ModuleInventory::new(&module).call_free(function));
    assert_eq!(module, before);
}

#[test]
fn volatile_memory_does_not_disappear_from_the_inventory() {
    for load in [false, true] {
        let (mut module, function) = pointer_comparison();
        let body = &mut module.function_by_id_mut(function).unwrap().blocks[0].body;
        let access = body
            .iter_mut()
            .find(|node| {
                matches!(
                    (&node.inst, load),
                    (Inst::Load { .. }, true) | (Inst::Store { .. }, false)
                )
            })
            .unwrap();
        match &mut access.inst {
            Inst::Load { volatile, .. } | Inst::Store { volatile, .. } => *volatile = true,
            _ => unreachable!(),
        }
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(!ModuleInventory::new(&module).call_free(function));
    }
}

#[test]
fn invalid_input_or_another_producer_cannot_replace_the_inventory() {
    let (mut module, function) = subject("none");
    module.function_by_id_mut(function).unwrap().producer = Some(Producer::Clean);
    assert!(!ModuleInventory::new(&module).call_free(function));
    module.function_by_id_mut(function).unwrap().producer = Some(Producer::TRust);
    let Inst::BinOp { rhs, .. } =
        &mut module.function_by_id_mut(function).unwrap().blocks[0].body[0].inst
    else {
        panic!("fixture has one bitwise expression")
    };
    *rhs = trust_ir::ValueId::new(999);
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    assert!(!ModuleInventory::new(&module).call_free(function));
}

#[test]
fn one_batch_keeps_original_function_ids_and_classifies_each_body() {
    let (mut module, function) = subject("none");
    let mut other = module.function_by_id(function).unwrap().clone();
    other.id = FuncId::new(71);
    other.name = "checked_arithmetic".into();
    let Inst::BinOp { op, .. } = &mut other.blocks[0].body[0].inst else {
        panic!("bitwise fixture")
    };
    *op = BinOp::UDiv;
    module.functions.push(other);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let before = module.clone();
    let inventory = ModuleInventory::new(&module);
    assert!(inventory.call_free(function));
    assert!(!inventory.call_free(FuncId::new(71)));
    assert!(!inventory.call_free(FuncId::new(999)));
    assert_eq!(module, before);
}
