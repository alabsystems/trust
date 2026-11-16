// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A plain MIR `Shl`/`Shr` (`Rvalue::BinaryOp`, the shape rustc emits with no
//! overflow `Assert` when `-C overflow-checks` is off) lowers with Rust's
//! shift-count mask.
//!
//! rustc_middle's `mir::BinOp::Shl`/`Shr` take the offset as
//! `RHS.rem_euclid(LHS::BITS)`, and `rustc_codegen_ssa::base::build_shift_expr_rhs`
//! ANDs the count with `BITS - 1` for every shift that is not `*Unchecked`. A
//! trust-ir `Shl`/`LShr`/`AShr` is undefined at or above `BITS`. The bridge used
//! to emit the bare trust-ir shift on the resized amount, calling the
//! out-of-range amount "Rust UB rustc already excludes"; trust-mc then encoded
//! that shift as a total `bvshl` (`x << 33u32 == 0`), and
//! `-Ztrust-policy=memory-safe -Coverflow-checks=off` PROVED
//! `ensures s < 32 || result == 0` over `x << s`, whose binary returns 2 for
//! `(1, 33)` (docs/KNOWN_HAZARDS.md, "shift count").
//!
//! Every row lowers, VALIDATES and EXECUTES on the reference interpreter, so the
//! claim checked is the value Rust computes, not a module shape. Before the fix
//! every out-of-range row below trapped in the interpreter (`shift_amount`'s
//! undefined-behaviour refusal) instead of returning Rust's value.

use trust_ir::Module;
use trust_ir::inst::{BinOp as TrustIrBinOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty as TrustIrTy;
use trust_ir_bridge::lower_to_trust_ir;
use trust_types::{
    BasicBlock as TrustBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn one_block_function(
    name: &str,
    locals: Vec<Ty>,
    arg_count: usize,
    rvalue: Rvalue,
) -> VerifiableFunction {
    let return_ty = locals[0].clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("plain_shift::{name}"),
        span: Default::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue,
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn plain_shift(name: &str, op: BinOp, locals: Vec<Ty>, amount: Operand) -> VerifiableFunction {
    let arg_count = locals.len() - 1;
    one_block_function(
        name,
        locals,
        arg_count,
        Rvalue::BinaryOp(op, Operand::Copy(Place::local(1)), amount),
    )
}

fn lowered_valid(func: &VerifiableFunction) -> Module {
    let module = lower_to_trust_ir(func)
        .unwrap_or_else(|error| panic!("`{}` must lower, got {error:?}", func.name));
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "`{}` lowered to an invalid module: {errors:?}\n{module}",
        func.name
    );
    module
}

fn run(module: &Module, args: Vec<InterpretValue>) -> Result<i128, InterpretErrorCode> {
    match Interpreter::with_module(module).execute_func(module.functions[0].id, args) {
        Ok(outcome) => {
            let value = &outcome.returns[0];
            let bits = value.as_int().unwrap_or_else(|| panic!("an integer result, got {value:?}"));
            let signed = matches!(
                value.ty,
                TrustIrTy::I8
                    | TrustIrTy::I16
                    | TrustIrTy::I32
                    | TrustIrTy::I64
                    | TrustIrTy::I128
                    | TrustIrTy::Isize
            );
            Ok(if signed {
                bits.as_signed()
            } else {
                i128::try_from(bits.as_unsigned()).expect("fixture results fit i128")
            })
        }
        Err(error) => Err(error.code),
    }
}

fn int(ty: TrustIrTy, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("in-range interpreter integer")
}

fn entry_insts(module: &Module) -> Vec<&Inst> {
    module.functions[0].blocks[0].body.iter().map(|node| &node.inst).collect()
}

fn has_and(module: &Module) -> bool {
    entry_insts(module).iter().any(|inst| matches!(inst, Inst::BinOp { op: TrustIrBinOp::And, .. }))
}

/// The scout's `sym`: `x << s` for `x, s: u32`. `(1, 33)` is `1 << (33 & 31) == 2`
/// in Rust; before the fix the lowered shift trapped there (and trust-mc read it
/// as `0`).
#[test]
fn symbolic_count_is_masked_to_the_value_width() {
    let module = lowered_valid(&plain_shift(
        "sym",
        BinOp::Shl,
        vec![Ty::u32(), Ty::u32(), Ty::u32()],
        Operand::Copy(Place::local(2)),
    ));
    assert!(has_and(&module), "a symbolic count must be masked: {module}");
    let u32 = TrustIrTy::U32;
    assert_eq!(run(&module, vec![int(u32.clone(), 1), int(u32.clone(), 33)]), Ok(2));
    assert_eq!(run(&module, vec![int(u32.clone(), 1), int(u32.clone(), 32)]), Ok(1));
    assert_eq!(run(&module, vec![int(u32.clone(), 1), int(u32.clone(), 31)]), Ok(1 << 31));
    assert_eq!(run(&module, vec![int(u32.clone(), 5), int(u32.clone(), 0)]), Ok(5));
    assert_eq!(
        run(&module, vec![int(u32.clone(), 3), int(u32, i128::from(u32::MAX))]),
        Ok(i128::from(3u32 << 31)),
        "u32::MAX & 31 == 31, and the shifted-out bit is dropped"
    );
}

/// The scout's `shr_sym`: logical `x >> s` for `x, s: u32`; `(4, 33)` is `4 >> 1 == 2`.
#[test]
fn logical_shift_right_count_is_masked() {
    let module = lowered_valid(&plain_shift(
        "shr_sym",
        BinOp::Shr,
        vec![Ty::u32(), Ty::u32(), Ty::u32()],
        Operand::Copy(Place::local(2)),
    ));
    assert!(has_and(&module), "{module}");
    let u32 = TrustIrTy::U32;
    assert_eq!(run(&module, vec![int(u32.clone(), 4), int(u32.clone(), 33)]), Ok(2));
    assert_eq!(run(&module, vec![int(u32.clone(), 4), int(u32, 64)]), Ok(4));
}

/// A `u8` value shifted by a `u32` count: the count is truncated to `u8` and then
/// masked with 7. `256` truncates to `0` and `256 & 7 == 0` too; `9 & 7 == 1`.
#[test]
fn a_narrow_value_with_a_wide_count_masks_after_the_resize() {
    let module = lowered_valid(&plain_shift(
        "shl_u8",
        BinOp::Shl,
        vec![Ty::u8(), Ty::u8(), Ty::u32()],
        Operand::Copy(Place::local(2)),
    ));
    assert!(has_and(&module), "{module}");
    let (u8t, u32t) = (TrustIrTy::U8, TrustIrTy::U32);
    assert_eq!(run(&module, vec![int(u8t.clone(), 1), int(u32t.clone(), 9)]), Ok(2));
    assert_eq!(run(&module, vec![int(u8t.clone(), 1), int(u32t.clone(), 256)]), Ok(1));
    assert_eq!(run(&module, vec![int(u8t.clone(), 1), int(u32t.clone(), 263)]), Ok(0x80));
    assert_eq!(run(&module, vec![int(u8t, 0x81), int(u32t, 7)]), Ok(0x80));
}

/// A SIGNED value and a SIGNED count: arithmetic shift, and a negative count is
/// its `rem_euclid(32)` (`-1 -> 31`), exactly as rustc's zero-extend-then-mask
/// computes it.
#[test]
fn a_signed_negative_count_takes_its_rem_euclid() {
    let module = lowered_valid(&plain_shift(
        "ashr_i32",
        BinOp::Shr,
        vec![Ty::i32(), Ty::i32(), Ty::Int { width: 8, signed: true }],
        Operand::Copy(Place::local(2)),
    ));
    assert!(entry_insts(&module).iter().any(|inst| matches!(
        inst,
        Inst::BinOp { op: TrustIrBinOp::AShr, ty: TrustIrTy::I32, .. }
    )));
    let (i32t, i8t) = (TrustIrTy::I32, TrustIrTy::I8);
    assert_eq!(run(&module, vec![int(i32t.clone(), -64), int(i8t.clone(), 3)]), Ok(-8));
    assert_eq!(run(&module, vec![int(i32t.clone(), -64), int(i8t.clone(), 35)]), Ok(-8));
    assert_eq!(run(&module, vec![int(i32t.clone(), -64), int(i8t.clone(), -1)]), Ok(-1));
    assert_eq!(run(&module, vec![int(i32t.clone(), 1 << 30), int(i8t.clone(), -1)]), Ok(0));
    assert_eq!(run(&module, vec![int(i32t, 64), int(i8t, -128)]), Ok(64), "-128 & 31 == 0");
}

/// A pointer-sized value takes the bridge's pinned 64-bit width: `65 & 63 == 1`.
#[test]
fn a_pointer_sized_value_masks_at_the_pinned_width() {
    let module = lowered_valid(&plain_shift(
        "shl_usize",
        BinOp::Shl,
        vec![Ty::PtrSizedInt { signed: false }, Ty::PtrSizedInt { signed: false }, Ty::u32()],
        Operand::Copy(Place::local(2)),
    ));
    assert!(has_and(&module), "{module}");
    assert_eq!(run(&module, vec![int(TrustIrTy::Usize, 1), int(TrustIrTy::U32, 65)]), Ok(2));
}

/// The scout's `konst`: `x << 9u32` for `x: u8`. The out-of-range LITERAL folds to
/// `9 & 7 == 1` at lowering time — no `And`, and the shift reads a constant `1`.
#[test]
fn an_out_of_range_literal_count_folds_to_its_masked_value() {
    let module = lowered_valid(&plain_shift(
        "konst",
        BinOp::Shl,
        vec![Ty::u8(), Ty::u8()],
        Operand::Constant(ConstValue::Uint(9, 32)),
    ));
    assert!(!has_and(&module), "a literal count is folded, not masked at run time: {module}");
    assert_eq!(run(&module, vec![int(TrustIrTy::U8, 1)]), Ok(2));
    assert_eq!(run(&module, vec![int(TrustIrTy::U8, 0x41)]), Ok(0x82));

    // A width-less negative literal on a signed value: `-1 rem_euclid 16 == 15`.
    let module = lowered_valid(&plain_shift(
        "neg_literal",
        BinOp::Shl,
        vec![Ty::Int { width: 16, signed: true }, Ty::Int { width: 16, signed: true }],
        Operand::Constant(ConstValue::Int(-1)),
    ));
    assert!(!has_and(&module), "{module}");
    assert_eq!(run(&module, vec![int(TrustIrTy::I16, 1)]), Ok(i128::from(i16::MIN)));
}

/// An IN-RANGE literal count lowers exactly as it did before the fix: no `And`
/// and no extra constant, so every ordinary `x << 3` keeps its instruction
/// sequence.
#[test]
fn an_in_range_literal_count_adds_no_instruction() {
    let func = plain_shift(
        "in_range",
        BinOp::Shl,
        vec![Ty::u8(), Ty::u8()],
        Operand::Constant(ConstValue::Uint(3, 32)),
    );
    let module = lowered_valid(&func);
    assert!(!has_and(&module), "{module}");
    let consts =
        entry_insts(&module).iter().filter(|inst| matches!(inst, Inst::Const { .. })).count();
    assert_eq!(consts, 1, "only the literal itself: {module}");
    assert_eq!(run(&module, vec![int(TrustIrTy::U8, 1)]), Ok(8));
}

/// The unchecked shift keeps its charged precondition: its `ShiftInRange`
/// `Assert` still fails on an out-of-range amount BEFORE the (now masked) plain
/// lowering it reuses, so the mask cannot hide the UB the `*Unchecked` op has.
#[test]
fn the_unchecked_shift_still_fails_its_precondition_out_of_range() {
    let func = one_block_function(
        "unchecked",
        vec![Ty::u32(), Ty::u32(), Ty::u32()],
        2,
        Rvalue::UncheckedBinaryOp(
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let module = lowered_valid(&func);
    let u32 = TrustIrTy::U32;
    assert_eq!(run(&module, vec![int(u32.clone(), 1), int(u32.clone(), 3)]), Ok(8));
    assert_eq!(
        run(&module, vec![int(u32.clone(), 1), int(u32, 33)]),
        Err(InterpretErrorCode::Panic),
        "the unchecked precondition is charged by its assert, not masked away"
    );
}
