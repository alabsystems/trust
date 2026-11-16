// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Trust (trust-ir v52-v57): the general-body merge offsets the module ids of the shapes its drain
//! loop lists and no others, so every instruction that names a module id outside that list is
//! refused by name in the fallible pre-pass, before `dst` is touched: a SITED assert (its panic
//! entry and location, v54) and the unwinding and no-unwind twins (callee, signature or drop
//! type; v53/v55/v56). A siteless assert of any kind carries only registers and still merges.

use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{AssertKind, CallingConv, PanicLocation, PanicSite};

use super::{FuncTyId, Inst, remap_general_inst_tys};

fn site() -> PanicSite {
    PanicSite { entry: FuncId::new(0), location: PanicLocation::Value(ValueId::new(9)) }
}

#[test]
fn a_siteless_assert_of_any_kind_merges_unchanged() {
    for kind in [
        AssertKind::Unspecified,
        AssertKind::DivByZero,
        AssertKind::BoundsCheck { index: ValueId::new(2), len: ValueId::new(3) },
    ] {
        let original = Inst::Assert { cond: ValueId::new(1), kind, site: None };
        let mut remapped = original.clone();
        remap_general_inst_tys(&mut remapped, &[FuncTyId::new(41)], &[])
            .expect("a siteless assert carries no module id");
        assert_eq!(remapped, original);
    }
}

#[test]
fn module_id_bearing_instructions_are_refused_by_name() {
    let refused = [
        (
            Inst::Assert {
                cond: ValueId::new(1),
                kind: AssertKind::Unspecified,
                site: Some(site()),
            },
            "sited Assert",
        ),
        (
            Inst::AssertInvoke {
                cond: ValueId::new(1),
                kind: AssertKind::Unspecified,
                site: site(),
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            },
            "AssertInvoke",
        ),
        (Inst::CallCannotUnwind { callee: FuncId::new(0), args: vec![] }, "CallCannotUnwind"),
        (
            Inst::CallIndirectCannotUnwind {
                callee: ValueId::new(1),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: CallingConv::Rust,
            },
            "CallIndirectCannotUnwind",
        ),
        (
            Inst::DropInvoke {
                ty: trust_ir::Ty::Ptr,
                ptr: ValueId::new(1),
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            },
            "DropInvoke",
        ),
        (
            Inst::InvokeIndirect {
                callee: ValueId::new(1),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: CallingConv::Rust,
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            },
            "InvokeIndirect",
        ),
    ];
    for (inst, name) in refused {
        let mut probe = inst.clone();
        let err = remap_general_inst_tys(&mut probe, &[FuncTyId::new(41)], &[])
            .expect_err("a module id this merge does not offset is refused");
        assert!(err.contains(name), "{name}: {err}");
        assert_eq!(probe, inst, "a refusal rewrites nothing");
    }
}

/// A reachable, valid constructor must refuse even when its value is unused.
/// The interpreter and scalar twin keep this independent of malformed IR.
#[test]
fn runtime_closure_constructor_refuses_without_rewriting_valid_ids() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    use trust_ir::{ClosureTy, Ty};

    let mut mb = trust_ir_build::ModuleBuilder::new("clean-general::runtime-closure");
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    for name in ["gen_entry", "gen_target"] {
        let mut fb = mb.function(name, physical);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }
    let mut module = mb.build().expect("valid scalar fixture");
    let apparent = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("apparent signature");
    let closure = module
        .add_closure_type(ClosureTy { func: apparent, captures: vec![Ty::U64] })
        .expect("capture declaration");
    let constructor =
        Inst::MakeClosure { ty: closure, func: FuncId::new(1), captures: vec![ValueId::new(0)] };
    module.functions[0].blocks[0].body.insert(
        0,
        trust_ir::node::InstrNode::new(constructor.clone()).with_result(ValueId::new(100)),
    );
    let validation = trust_ir_build::validate_module(&module);
    assert!(validation.is_empty(), "valid runtime constructor: {validation:?}");
    let args = vec![InterpretValue::int(Ty::U64, 17).expect("u64 fixture")];
    let actual = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), args.clone())
        .expect("reachable runtime construction executes");
    assert_eq!(actual.returns, args);
    assert_eq!(actual.host_calls, 0);

    let mut candidate = constructor.clone();
    let refusal = remap_general_inst_tys(&mut candidate, &[FuncTyId::new(41)], &[])
        .expect_err("constructor identities cannot pass the general remap");
    assert!(refusal.contains("MakeClosure"), "{refusal}");
    assert_eq!(candidate, constructor, "a refusal must not partially remap ids");

    module.functions[0].blocks[0].body.remove(0);
    for node in &mut module.functions[0].blocks[0].body {
        remap_general_inst_tys(&mut node.inst, &[FuncTyId::new(41)], &[])
            .expect("the same scalar return stays supported");
    }
    let scalar = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), args)
        .expect("scalar twin executes");
    assert_eq!(scalar.returns, actual.returns);
}

/// Trust (trust-ir v55): a general module carrying a drop-glue table is refused whole, like the
/// other tables this merge does not remap: the table keys glue FUNCTIONS by the types they drop,
/// and the drain loop neither offsets those ids nor interns those types.
#[test]
fn a_general_module_with_a_drop_glue_table_is_refused() {
    use trust_ir::{DropGlueEntry, Module, Ty};

    use super::{
        CleanOriginIrOutcome, GeneralCleanIr, GeneralOutcome, GeneralRow, append_clean_origin,
    };

    let mut mb = trust_ir_build::ModuleBuilder::new("clean-general::probe");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("gen_id", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut src = mb.build().expect("ModuleBuilder::build: test fixture");
    src.drop_glue.push(DropGlueEntry { glue: FuncId::new(0), ty: Ty::Ptr });
    let outcome = CleanOriginIrOutcome::General(GeneralCleanIr {
        rows: vec![GeneralRow {
            clean_name: "genId".to_string(),
            outcome: GeneralOutcome::Compiled { tv_mint_certified: false },
        }],
        module: Some(src),
    });
    let mut module = Module::new("crate_under_test");
    let mut errors = Vec::new();
    let summary = append_clean_origin(&mut module, vec![outcome], &mut errors);
    assert!(module.functions.is_empty(), "a refused batch merges nothing");
    assert!(
        summary
            .general
            .iter()
            .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("does not yet remap")),
        "the drop-glue table refuses the batch by the table rule"
    );
}

/// Trust (trust-ir v58): a general module carrying a closure-frame table is refused whole, even
/// with no closure type of its own: the table keys each frame by a `ClosureTyId`, which the drain
/// loop does not remap. Only the new table is set, so this pins its own clause of the table rule.
#[test]
fn a_general_module_with_a_closure_layout_table_is_refused() {
    use trust_ir::{ClosureLayoutDescriptor, ClosureTyId, Module, Ty};

    use super::{
        CleanOriginIrOutcome, GeneralCleanIr, GeneralOutcome, GeneralRow, append_clean_origin,
    };

    let mut mb = trust_ir_build::ModuleBuilder::new("clean-general::probe");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("gen_id", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut src = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(src.closure_types.is_empty(), "the probe declares no closure type");
    src.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let outcome = CleanOriginIrOutcome::General(GeneralCleanIr {
        rows: vec![GeneralRow {
            clean_name: "genId".to_string(),
            outcome: GeneralOutcome::Compiled { tv_mint_certified: false },
        }],
        module: Some(src),
    });
    let mut module = Module::new("crate_under_test");
    let mut errors = Vec::new();
    let summary = append_clean_origin(&mut module, vec![outcome], &mut errors);
    assert!(module.functions.is_empty(), "a refused batch merges nothing");
    assert!(
        summary
            .general
            .iter()
            .any(|(_, d, _, r)| *d == "merge-refused" && r.contains("does not yet remap")),
        "the closure-frame table refuses the batch by the table rule"
    );
}
