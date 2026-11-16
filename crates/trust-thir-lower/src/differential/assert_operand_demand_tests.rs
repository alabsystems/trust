// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Trust (trust-ir v52/v54): an assert's kind operands and a sited assert's run-time location
//! are consumers too. A parametric column consumed as a kind operand is demanded at the
//! validator's `usize` (never left at a stale declared spelling); one consumed as a panic
//! location is a pointer, outside the model, so the column is refused.

use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    AssertKind, Block, FuncTy, Function, Inst, InstrNode, PanicLocation, PanicSite, Ty,
};

use super::demanded_column_ty;

fn one_assert(kind: AssertKind, site: Option<PanicSite>) -> (Function, FuncTy) {
    let mut function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::Bool), (ValueId::new(1), Ty::U64)];
    block.body.push(InstrNode::new(Inst::Assert { cond: ValueId::new(0), kind, site }));
    block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    (
        function,
        FuncTy { params: vec![Ty::Bool, Ty::U64], returns: vec![], is_vararg: false, abi: None },
    )
}

#[test]
fn a_kind_operand_is_demanded_at_usize() {
    let kind = AssertKind::BoundsCheck { index: ValueId::new(1), len: ValueId::new(1) };
    let (f, sig) = one_assert(kind, None);
    assert_eq!(demanded_column_ty(&f, &sig, ValueId::new(1), &Ty::U64), Some(Ty::Usize));
    assert_eq!(demanded_column_ty(&f, &sig, ValueId::new(0), &Ty::Bool), Some(Ty::Bool));
}

#[test]
fn a_panic_location_consumer_refuses_the_column() {
    let site = PanicSite { entry: FuncId::new(0), location: PanicLocation::Value(ValueId::new(1)) };
    let (f, sig) = one_assert(AssertKind::Unspecified, Some(site));
    assert_eq!(demanded_column_ty(&f, &sig, ValueId::new(1), &Ty::U64), None);
}

#[test]
fn an_unconsumed_column_keeps_its_declared_type() {
    let (f, sig) = one_assert(AssertKind::DivByZero, None);
    assert_eq!(demanded_column_ty(&f, &sig, ValueId::new(1), &Ty::U64), Some(Ty::U64));
}
