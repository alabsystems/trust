// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use trust_ir::{BlockId, ModuleFunctionCatalog, Ty};

use super::tests::{append_general, destination, general_pair};
use super::*;

fn refuse_unchanged(mut dst: Module, src: Module, reason: &str) {
    let before = dst.clone();
    let summary = append_general(&mut dst, src);
    assert_eq!(summary.general.len(), 1, "the real compiled row must be disclosed");
    assert_eq!(summary.general[0].1, "merge-refused");
    assert!(summary.general[0].3.contains(reason), "{:?}", summary.general);
    assert!(summary.general_functions.is_empty());
    assert_eq!(dst.functions, before.functions);
    assert_eq!(dst.func_types, before.func_types, "preflight precedes type interning");
    assert_eq!(dst.types, before.types);
    assert_eq!(dst.globals, before.globals);
}

fn global(ty: Ty, value: Constant) -> trust_ir::Global {
    trust_ir::Global {
        name: "checked-function-table".to_owned(),
        ty,
        mutable: false,
        initializer: Some(value),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}

#[test]
fn public_append_dangling_call_invoke_and_seqmap_never_capture_owner() {
    for missing in [77, u32::MAX] {
        for kind in 0..3 {
            let mut src = general_pair();
            let node = src.functions[1].blocks[0]
                .body
                .iter_mut()
                .find(|node| matches!(node.inst, Inst::Call { .. }))
                .unwrap();
            let Inst::Call { args, .. } = &node.inst else { unreachable!() };
            let args = args.clone();
            node.inst = match kind {
                0 => Inst::Call { callee: FuncId::new(missing), args },
                1 => Inst::Invoke {
                    callee: FuncId::new(missing),
                    args,
                    normal_dest: BlockId::new(0),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(0),
                },
                _ => Inst::SeqMap { ty: Ty::U64, seq: args[0], fwd: FuncId::new(missing) },
            };
            // Definitions0/1 themselves have safe, noncolliding projections.
            // Without the reference guard, offset1 + MAX captures owner0.
            refuse_unchanged(destination(&[0]), src, "function reference");
        }
    }
}

#[test]
fn public_append_recursive_function_constants_and_switch_values_refuse_missing_targets() {
    let bad = Constant::FnDef(FuncId::new(u32::MAX));
    let values = vec![
        bad.clone(),
        Constant::Aggregate(vec![bad.clone()]),
        Constant::Array(vec![bad.clone()]),
        Constant::Vector(vec![bad.clone()]),
        Constant::Sequence(vec![bad.clone()]),
        Constant::Set(vec![bad.clone()]),
        Constant::Record(vec![("target".into(), bad.clone())]),
        Constant::Splat { elem: Box::new(bad.clone()), len: u64::MAX },
        Constant::Closure { func: FuncId::new(u32::MAX), captures: vec![] },
        Constant::Closure { func: FuncId::new(0), captures: vec![bad] },
    ];
    for value in values {
        for in_switch in [false, true] {
            let mut src = general_pair();
            let inst = if in_switch {
                Inst::Switch {
                    value: trust_ir::ValueId::new(0),
                    default: BlockId::new(0),
                    default_args: vec![],
                    cases: vec![trust_ir::SwitchCase {
                        value: value.clone(),
                        target: BlockId::new(0),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                }
            } else {
                Inst::Const { ty: Ty::Ptr, value: value.clone() }
            };
            src.functions[1].blocks[0].body.insert(0, trust_ir::InstrNode::new(inst));
            refuse_unchanged(destination(&[0]), src, "function reference");
        }
    }
}

#[test]
fn public_append_invalid_global_references_and_initializers_publish_no_tables() {
    for missing in [1, u32::MAX] {
        let mut src = general_pair();
        src.globals.push(global(Ty::U64, Constant::Int(3)));
        src.functions[1].blocks[0].body.insert(
            0,
            trust_ir::InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(missing),
            }),
        );
        let mut dst = destination(&[0]);
        dst.globals.push(global(Ty::U64, Constant::Int(9)));
        refuse_unchanged(dst, src, "global reference");
    }
    for target in [77, u32::MAX] {
        let mut src = general_pair();
        src.globals.push(global(
            Ty::Ptr,
            Constant::Record(vec![(
                "nested".into(),
                Constant::Closure {
                    func: FuncId::new(0),
                    captures: vec![Constant::Splat {
                        elem: Box::new(Constant::FnDef(FuncId::new(target))),
                        len: 2,
                    }],
                },
            )]),
        ));
        refuse_unchanged(destination(&[0]), src, "function reference");
    }
}

#[test]
fn public_append_global_initializer_and_type_bind_the_actual_appended_callee() {
    let mut src = general_pair();
    let source_sig = src.functions[0].ty;
    src.globals.push(global(
        Ty::Tuple(vec![Ty::Func(source_sig), Ty::Tuple(vec![Ty::Func(source_sig)])]),
        Constant::Aggregate(vec![
            Constant::FnDef(FuncId::new(0)),
            Constant::Aggregate(vec![Constant::FnDef(FuncId::new(0))]),
        ]),
    ));
    src.functions[1].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) })
            .with_result(trust_ir::ValueId::new(99)),
    );
    assert!(trust_ir_build::validate_module(&src).is_empty(), "real typed source initializer");
    let mut dst = destination(&[0]);
    // The retained owner is a local definition, not a target-dependent C import.
    // The physical-ID fixture's default bodyless External/C row needs a target.
    let mut entry = trust_ir::Block::new(BlockId::new(0));
    entry.body.push(trust_ir::InstrNode::new(Inst::Return { values: vec![] }));
    dst.functions[0].blocks.push(entry);
    assert!(
        trust_ir_build::validate_module(&dst).is_empty(),
        "real typed destination before joining"
    );
    let mut owner_data = global(Ty::U64, Constant::Int(9));
    owner_data.name = "owner-data".to_owned();
    dst.globals.push(owner_data);
    let owner = dst.functions[0].clone();
    let summary = append_general(&mut dst, src);
    assert_eq!(summary.general.len(), 1);
    assert_eq!(summary.general[0].1, "compiled", "{:?}", summary.general);
    assert_eq!(dst.functions[0], owner, "owner0 remains its original function");
    let catalog = ModuleFunctionCatalog::new(&dst);
    let callee = catalog.unique(FuncId::new(1)).unwrap();
    assert_eq!(callee.name, "checked-callee");
    let caller = catalog.unique(FuncId::new(2)).unwrap();
    assert!(caller.blocks.iter().flat_map(|block| &block.body).any(|node|
            matches!(node.inst, Inst::GlobalAddr { global } if global == trust_ir::value::GlobalId::new(1))));
    assert_eq!(dst.globals[1].name, "checked-function-table");
    assert_eq!(
        dst.globals[1].ty,
        Ty::Tuple(vec![Ty::Func(callee.ty), Ty::Tuple(vec![Ty::Func(callee.ty)])])
    );
    let mut targets = Vec::new();
    dst.globals[1].initializer.as_ref().unwrap().visit_constants(|constant| {
        if let Constant::FnDef(target) = constant {
            targets.push(*target);
        }
    });
    assert_eq!(targets, vec![FuncId::new(1), FuncId::new(1)]);
    for target in targets {
        assert_eq!(catalog.unique(target).unwrap().name, "checked-callee");
    }
    assert!(trust_ir_build::validate_module(&dst).is_empty(), "real typed joined initializer");
}

#[test]
fn public_append_cannot_hide_an_unpinned_external_owner_boundary() {
    let mut dst = destination(&[0]);
    let owner = dst.functions[0].clone();
    assert!(trust_ir_build::validate_module(&dst).iter().any(
        |error| matches!(error, trust_ir_build::ValidationError::TargetInfoRequired { boundary }
            if boundary.contains("owner-0"))
    ));
    let summary = append_general(&mut dst, general_pair());
    assert_eq!(summary.general.len(), 1);
    assert_eq!(summary.general[0].1, "compiled");
    assert_eq!(dst.functions[0], owner);
    assert!(
        trust_ir_build::validate_module(&dst).iter().any(
            |error| matches!(error, trust_ir_build::ValidationError::TargetInfoRequired { boundary }
            if boundary.contains("owner-0"))
        ),
        "structural append disclosure does not validate an unpinned external boundary"
    );
}
