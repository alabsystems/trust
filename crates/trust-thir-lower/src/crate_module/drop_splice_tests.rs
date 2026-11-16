//! Trust (step 2 increment 4b, D18 OD-1): the frozen splice ADMITS `Inst::Drop`, and
//! the seam differential treats a drop as an uninterpreted event.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! Before OD-1, `inst_embedded_tys` had no `Drop` arm, so a body carrying the producer's drops
//! (`drops.rs`) was refused `Splice(unmodeled instruction)` and never reached the crate module,
//! the codegen handoff or the sidecar. D18 OD-1 (the stricter waiver form)
//! admits it: the drop's type is remapped like every other embedded type, every
//! drop is judged as an event against rustc's drop elaboration by the effect-conservation gate
//! (`effect_conservation::drop_leg`, `drop_oracle.rs`), and NO body is excluded from the seam
//! differential — the seam interprets the THIR side with its drops removed
//! ([`module_without_drops`]), because the interpreter refuses `Inst::Drop` with a `TypeError`
//! that would read as a THIR defect. Every executing consumer still refuses `Inst::Drop` by name
//! (trust-cg's adapter, `module_to_lir`, the interpreter, `to_mir`).
//!
//! Records here are authored in the shape the producer emits (`LowerCx::emit_one_drop`: an
//! entry-block `Alloca`, a `Store` of the value, the `Drop` through the slot); the pin over the
//! real producer is `tests/run-make/trust-effect-conservation` and
//! `tests/ui/trust/trust_ir_lower_drops_placed.rs`.

use std::collections::BTreeSet;

use trust_ir::{
    Block, BlockId, FieldDef, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module,
    StructDef, StructId, StructRepr, Ty, ValueId,
};

use super::authority_tests::lineage_body_record;
use super::*;

/// `fn name(g: S) { /* drop g */ }` with `S` the body's struct row 0, named `struct_name`.
fn drop_body(def_index: u32, name: &str, struct_name: &str) -> BodyRecord {
    let mut record = lineage_body_record(def_index, name);
    let s = Ty::Struct(StructId::new(0));
    record.structs = vec![StructDef {
        id: StructId::new(0),
        name: struct_name.to_string(),
        fields: vec![FieldDef { name: "0".to_string(), ty: Ty::I32, offset: Some(0) }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    }];
    let signature =
        FuncTy { params: vec![s.clone()], returns: Vec::new(), is_vararg: false, abi: None };
    let mut function = record.function.take().expect("the probe record carries a function");
    function.ty = FuncTyId::new(0);
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), s.clone());
    block.body.push(
        InstrNode::new(Inst::Alloca { ty: s.clone(), count: None, align: None })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: s.clone(),
        ptr: ValueId::new(1),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));
    block.body.push(InstrNode::new(Inst::Drop { ty: s, ptr: ValueId::new(1) }));
    block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
    function.blocks.push(block);
    record.function = Some(function);
    record.func_ty = Some(signature.clone());
    record.func_types = vec![signature];
    // The producer forces a drop-bearing body out of interpretation (`drops::
    // drops_force_not_interpretable`), which defers it to the seam.
    record.contains_call = true;
    record.deferred = true;
    record.instr_count = 4;
    record
}

fn drop_tys(f: &Function) -> Vec<Ty> {
    f.blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .filter_map(|n| match &n.inst {
            Inst::Drop { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect()
}

/// THE ADMISSION. A drop-bearing body is spliced (it was `Splice(unmodeled instruction)` at the
/// pin), and its drop's type is remapped with the body's tables: the second body's `S` lands at
/// assembled `StructId(1)`, and its `Drop` names that row, the same one its `Alloca` names. A
/// drop left at the body's own `StructId(0)` would drop the FIRST body's type.
#[test]
fn a_drop_bearing_body_is_spliced_with_its_drop_type_remapped() {
    let first = drop_body(1, "probe::drop_a", "probe::A");
    let second = drop_body(2, "probe::drop_b", "probe::B");
    assert_eq!(splice_refusal(&first, std::slice::from_ref(&first)), None);
    let records = vec![first, second];
    let assembled = assemble("drop_splice", &records, &BTreeSet::new());
    let refusals: Vec<_> =
        assembled.coverage_rows.iter().map(|r| (r.spliced, r.splice_refusal)).collect();
    assert_eq!(assembled.spliced, 2, "both drop-bearing bodies splice: {refusals:?}");
    let a = assembled.module.functions.iter().find(|f| f.name == "probe::drop_a").expect("a");
    let b = assembled.module.functions.iter().find(|f| f.name == "probe::drop_b").expect("b");
    assert_eq!(drop_tys(a), vec![Ty::Struct(StructId::new(0))]);
    assert_eq!(drop_tys(b), vec![Ty::Struct(StructId::new(1))], "the drop's type is remapped");
    let alloca_ty = b.blocks[0].body.iter().find_map(|n| match &n.inst {
        Inst::Alloca { ty, .. } => Some(ty.clone()),
        _ => None,
    });
    assert_eq!(alloca_ty, Some(Ty::Struct(StructId::new(1))));
    assert_eq!(assembled.module.structs[1].name, "probe::B");
}

/// `fn f(x: i64) -> i64 { <spill x; drop it>; x }` against an oracle `fn f(x: i64) -> i64 { x }`.
fn scalar_pair() -> (Module, Module) {
    let sig = FuncTy { params: vec![Ty::I64], returns: vec![Ty::I64], is_vararg: false, abi: None };
    let mut thir = Module::new("thir");
    let ty = thir.add_func_type(sig.clone()).expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I64);
    b.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None })
            .with_result(ValueId::new(1)),
    );
    b.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: ValueId::new(1),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));
    b.body.push(InstrNode::new(Inst::Drop { ty: Ty::I64, ptr: ValueId::new(1) }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    f.blocks.push(b);
    thir.try_add_function(f).expect("Module::try_add_function: test fixture");
    let mut oracle = Module::new("oracle");
    let ty = oracle.add_func_type(sig).expect("Module::add_func_type: test fixture");
    let mut g = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I64);
    b.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    g.blocks.push(b);
    oracle.try_add_function(g).expect("Module::try_add_function: test fixture");
    (thir, oracle)
}

/// THE SEAM HAZARD AND ITS FIX (design §1.6). Interpreted as it stands, the THIR side's drop
/// cannot be run. Since trust-ir v55 the reference interpreter resolves a drop through the
/// module's drop-glue table, and an unresolved one is `UnsupportedInstruction`
/// (`unsupported.destructor`): an infra limit the differential skips, so nothing is compared
/// (`NotRun`, no sample). Until v55 it was a `TypeError`, which the differential counted as a
/// THIR defect: a FALSE divergence, a strict error for a faithful body. Either way the body's
/// value flow goes unchecked. With the drop modelled as an event ([`module_without_drops`]) the
/// value flow around it is compared and agrees. A closure without a drop is left as it is.
#[test]
fn the_seam_interprets_the_thir_side_without_its_drops() {
    use crate::differential::{DiffMode, compare_entries};
    let (thir, oracle) = scalar_pair();
    let raw = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
    assert_eq!(raw.mode, DiffMode::NotRun, "an interpreted drop is not run: {raw:?}");
    assert!(!raw.equal && raw.samples_checked == 0, "{raw:?}");
    assert!(raw.notes.iter().any(|n| n.contains("drop_glue")), "{raw:?}");
    let stripped = module_without_drops(&thir, &[FuncId::new(0)]).expect("the closure has a drop");
    assert!(!crate::drops::function_has_drop(&stripped.functions[0]));
    let rep = compare_entries(&stripped, FuncId::new(0), &oracle, FuncId::new(0));
    assert_eq!(rep.mode, DiffMode::Agreed, "{rep:?}");
    assert!(rep.equal && rep.samples_checked > 0);
    assert!(module_without_drops(&oracle, &[FuncId::new(0)]).is_none());
    // Only the closure's functions are touched.
    assert!(module_without_drops(&thir, &[FuncId::new(7)]).is_none());
}

/// THE EDGE SCAN MODELS IT TOO. `inst_referenced_funcs` must model the set `inst_embedded_tys`
/// admits: a drop names a type and a pointer, no `FuncId`, so a drop-bearing body that names no
/// declaration has `DeclarationEdge::Absent`. At the pin a drop was an unmodeled shape, and every
/// drop-bearing body of a crate with an unsignable declaration was refused for an edge it could
/// not have (`UnsignableRustAbiDeclaration`, "an instruction shape the edge scan does not
/// model").
#[test]
fn a_drop_names_no_call_edge() {
    let drop = Inst::Drop { ty: Ty::I64, ptr: ValueId::new(1) };
    assert_eq!(inst_referenced_funcs(&drop), Some(Vec::new()));
    let record = drop_body(3, "probe::drop_c", "probe::C");
    let function = record.function.as_ref().expect("a function");
    assert!(matches!(declaration_edge(function, FuncId::new(9)), DeclarationEdge::Absent));
}
