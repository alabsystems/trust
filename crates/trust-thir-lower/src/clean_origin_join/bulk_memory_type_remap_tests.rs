// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

use trust_ir::ty::Ty;
use trust_ir::value::ValueId;

use super::{FuncTyId, Inst, TyId, remap_general_inst_tys};

#[test]
fn bulk_memory_type_remap_preserves_operands_and_overlap_policy() {
    let instructions = [
        Inst::MemCopy {
            dst: ValueId::new(0),
            src: ValueId::new(1),
            bytes: ValueId::new(23),
            overlap: false,
        },
        Inst::MemCopy {
            dst: ValueId::new(0),
            src: ValueId::new(1),
            bytes: ValueId::new(23),
            overlap: true,
        },
        Inst::MemSet { dst: ValueId::new(0), byte: ValueId::new(1), bytes: ValueId::new(23) },
    ];
    for original in instructions {
        // No type table is needed; SSA IDs are not type-table indices.
        let mut remapped = original.clone();
        remap_general_inst_tys(&mut remapped, &[], &[]).expect("no embedded types");
        assert_eq!(remapped, original);

        // Nonidentity maps would visibly corrupt operands 0/1 if this pass
        // confused their namespace with either module-relative type table.
        remap_general_inst_tys(
            &mut remapped,
            &[FuncTyId::new(41), FuncTyId::new(43)],
            &[TyId::new(47), TyId::new(53)],
        )
        .expect("bulk-memory operands remain function-local");
        assert_eq!(remapped, original);
    }
}

#[test]
fn bulk_memory_noop_does_not_disable_type_remapping_or_dangling_type_refusal() {
    let operand = ValueId::new(23);
    let mut typed = Inst::Copy {
        ty: Ty::Tuple(vec![Ty::Func(FuncTyId::new(0)), Ty::Array(TyId::new(1), 3)]),
        operand,
    };
    remap_general_inst_tys(&mut typed, &[FuncTyId::new(41)], &[TyId::new(47), TyId::new(53)])
        .expect("embedded types still remap");
    assert_eq!(
        typed,
        Inst::Copy {
            ty: Ty::Tuple(vec![Ty::Func(FuncTyId::new(41)), Ty::Array(TyId::new(53), 3)]),
            operand,
        }
    );

    let mut dangling = Inst::Copy { ty: Ty::Func(FuncTyId::new(2)), operand };
    let before = dangling.clone();
    let error = remap_general_inst_tys(&mut dangling, &[FuncTyId::new(41)], &[])
        .expect_err("a missing embedded function type remains refused");
    assert!(error.contains("Ty::Func(2) indexes outside"), "{error}");
    assert_eq!(dangling, before);
}
