//! Trust (step 2 increment 4c): the drop-glue lane's pure checks. The lane's `TyCtxt` half is
//! exercised end to end by `tests/run-make/trust-cg-f1-drop-glue`.

use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, BodyGate, FuncTy, Function, Inst, InstrNode, Module, Ty};

use super::*;

/// `f0` calls `f1`, which drops through a slot; `f2` stands alone.
fn module() -> Module {
    let mut m = Module::new("m");
    let sig = m
        .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
        .expect("Module::add_func_type: test fixture");
    let mut f0 = Function::new(FuncId::new(0), "caller", sig, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![] }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f0.blocks = vec![b];
    let mut f1 = Function::new(FuncId::new(1), "dropper", sig, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::U32, count: None, align: None })
            .with_result(ValueId::new(0)),
    );
    b.body.push(InstrNode::new(Inst::Drop { ty: Ty::U32, ptr: ValueId::new(0) }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f1.blocks = vec![b];
    let mut f2 = Function::new(FuncId::new(2), "alone", sig, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f2.blocks = vec![b];
    m.try_add_function(f0).expect("Module::try_add_function: test fixture");
    m.try_add_function(f1).expect("Module::try_add_function: test fixture");
    m.try_add_function(f2).expect("Module::try_add_function: test fixture");
    m
}

#[test]
fn an_item_reaches_a_drop_through_its_call_census() {
    let m = module();
    assert!(reaches_drop(&m, FuncId::new(0)), "the caller reaches its callee's drop");
    assert!(reaches_drop(&m, FuncId::new(1)));
    assert!(!reaches_drop(&m, FuncId::new(2)), "an item that reaches no drop is left alone");
}

#[test]
fn the_table_tripwire_names_the_table_that_moved() {
    let base = module();
    let mut same = base.clone();
    let sig: FuncTyId = same
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    same.try_add_function(Function::new(FuncId::new(3), "glue", sig, BlockId::new(0)))
        .expect("Module::try_add_function: test fixture");
    assert_eq!(tables_unchanged(&base, &same), Ok(()), "functions and signatures are not tables");
    let mut moved = base.clone();
    moved.add_type(Ty::I8).expect("Module::add_type: test fixture");
    let err = tables_unchanged(&base, &moved).unwrap_err();
    assert!(err.contains("`types`"), "{err}");
}

#[test]
fn only_a_body_carrying_the_lanes_gate_is_disclosed_as_glue() {
    let mut m = module();
    let sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    // Rewrite the drop into a call of a glue body gated by the lane's authority.
    let mut glue = Function::new(FuncId::new(3), "glue", sig, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    glue.blocks = vec![b];
    glue.body_gate = Some(BodyGate::Gated {
        authority: trust_thir_lower::drop_glue::TRUST_DROP_GLUE_AUTHORITY.to_string(),
        evidence: None,
    });
    m.try_add_function(glue).expect("Module::try_add_function: test fixture");
    let f1 = m.function_by_id_mut(FuncId::new(1)).unwrap();
    f1.blocks[0].body[1].inst = Inst::Call { callee: FuncId::new(3), args: vec![ValueId::new(0)] };
    assert_eq!(reached_glue(&m, FuncId::new(0)), [FuncId::new(3)].into_iter().collect());
    assert!(reached_glue(&m, FuncId::new(2)).is_empty());
    // The same body under another authority is not this lane's.
    m.function_by_id_mut(FuncId::new(3)).unwrap().body_gate = Some(BodyGate::Gated {
        authority: "trust-direct-lane-structural".to_string(),
        evidence: None,
    });
    assert!(reached_glue(&m, FuncId::new(0)).is_empty());
}

#[test]
fn a_function_only_named_is_not_reached_through_the_call_closure() {
    let mut m = module();
    // `f2` names the dropper as a function value and calls nothing.
    let f2 = m.function_by_id_mut(FuncId::new(2)).unwrap();
    f2.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: trust_ir::Constant::FnDef(FuncId::new(1)),
        })
        .with_result(ValueId::new(0)),
    );
    assert_eq!(call_closure(&m, FuncId::new(2)), vec![FuncId::new(2)]);
    assert!(!reaches_drop(&m, FuncId::new(2)), "a named function's drops are its own item's");
    assert_eq!(call_closure(&m, FuncId::new(0)), vec![FuncId::new(0), FuncId::new(1)]);
}

#[test]
fn drop_resolution_cannot_change_closure_frames() {
    let base = Module::new("base");
    let mut changed = base.clone();
    changed.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        origin: None,
        closure: trust_ir::ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    assert!(tables_unchanged(&base, &changed).unwrap_err().contains("closure_layouts"));
}
