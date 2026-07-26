// trust_vcgen/cross_check/reference_vcgen.rs: Independent reference VC generator
//
// The primary generator (`generate_vcs`) emits safety VCs
// (overflow, divzero, remainder-by-zero, negation-overflow) for callers that
// still invoke it directly (e.g., `real_ay_verification`, `m5_e2e_loop`). The
// reference generator below mirrors those kinds by walking MIR via a
// completely independent code path so cross-check can confirm both generators
// agree on the coarse safety-VC categorisation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BinOp, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, UnOp, VcKind,
    VerifiableFunction,
};

/// Independent VC generator that walks MIR directly.
///
/// Emits the same safety VC kinds as the primary `generate_vcs`
/// path in the canonical pipeline for coarse cross-checking.
/// The walking order and logic are deliberately different from the primary
/// implementation so cross-check catches generator drift.
pub(crate) fn reference_vcgen(func: &VerifiableFunction) -> Vec<VcKind> {
    let mut kinds = Vec::new();

    for block in &func.body.blocks {
        // 1. Overflow VCs: Assert terminators carrying an Overflow message.
        if let Terminator::Assert { msg: AssertMessage::Overflow(op), .. } = &block.terminator
            && let Some((lhs_ty, rhs_ty)) = find_checked_binop_tys(block, *op, func)
            && let Some(kind) = checked_overflow_kind(*op, lhs_ty, rhs_ty)
        {
            kinds.push(kind);
        }

        // 2. Div/Rem VCs from BinaryOp statements. Skip constant non-zero
        //    divisors — these cannot produce a zero-divisor VC.
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                match rvalue {
                    Rvalue::BinaryOp(BinOp::Div, lhs, divisor) => {
                        let is_float =
                            is_float_operand(lhs, func) || is_float_operand(divisor, func);
                        // Trust §9: float division is TOTAL/defined (±inf/NaN, never
                        // traps) — no obligation, matching the main generator. Only
                        // integer `/` (which aborts on zero) keeps DivisionByZero.
                        if !is_float && !divisor_is_nonzero_constant(divisor) {
                            kinds.push(VcKind::DivisionByZero);
                        }
                        if !is_float
                            && let Some(kind) =
                                signed_binary_overflow_kind(BinOp::Div, lhs, divisor, func)
                        {
                            kinds.push(kind);
                        }
                        // Trust (float-residuals F1): float Div CAN create ±inf
                        // from finite operands — the main generator now mints a
                        // FloatOverflowToInfinity obligation at width 64
                        // (category FloatSafety); mirror it here.
                        if is_float {
                            let operand_ty = operand_ty_owned(lhs, func);
                            if matches!(operand_ty, Ty::Float { width: 64 }) {
                                kinds.push(VcKind::FloatOverflowToInfinity {
                                    op: BinOp::Div,
                                    operand_ty,
                                });
                            }
                        }
                    }
                    Rvalue::BinaryOp(BinOp::Rem, lhs, divisor)
                        if !divisor_is_nonzero_constant(divisor) =>
                    {
                        kinds.push(VcKind::RemainderByZero);
                        if let Some(kind) =
                            signed_binary_overflow_kind(BinOp::Rem, lhs, divisor, func)
                        {
                            kinds.push(kind);
                        }
                    }
                    Rvalue::BinaryOp(op @ (BinOp::Shl | BinOp::Shr), lhs, rhs) => {
                        let operand_ty = operand_ty_owned(lhs, func);
                        if operand_ty.int_width().is_some() {
                            let shift_ty = operand_ty_owned(rhs, func);
                            kinds.push(VcKind::ShiftOverflow { op: *op, operand_ty, shift_ty });
                        }
                    }
                    // Float Add | Sub | Mul (float-residuals F1: Sub joins the
                    // arm, mirroring the main generator's honest L1 widening).
                    Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs)
                        if is_float_operand(lhs, func) || is_float_operand(rhs, func) =>
                    {
                        let operand_ty = operand_ty_owned(lhs, func);
                        if matches!(operand_ty, Ty::Float { width: 64 }) {
                            kinds.push(VcKind::FloatOverflowToInfinity { op: *op, operand_ty });
                        }
                    }
                    Rvalue::UnaryOp(UnOp::Neg, operand) => {
                        let ty = operand_ty_owned(operand, func);
                        if ty.is_signed() {
                            kinds.push(VcKind::NegationOverflow { ty });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    kinds
}

/// If this block contains an `Assign { rvalue: CheckedBinaryOp(op, lhs, rhs) }`
/// statement, return the operand types as `(lhs_ty, rhs_ty)`.
fn find_checked_binop_tys(
    block: &trust_types::BasicBlock,
    op: BinOp,
    func: &VerifiableFunction,
) -> Option<(Ty, Ty)> {
    for stmt in &block.stmts {
        if let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs), .. } = stmt
            && *stmt_op == op
        {
            return Some((operand_ty_owned(lhs, func), operand_ty_owned(rhs, func)));
        }
    }
    None
}

fn checked_overflow_kind(op: BinOp, lhs_ty: Ty, rhs_ty: Ty) -> Option<VcKind> {
    match op {
        BinOp::Shl | BinOp::Shr => {
            Some(VcKind::ShiftOverflow { op, operand_ty: lhs_ty, shift_ty: rhs_ty })
        }
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            Some(VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) })
        }
        _ => None,
    }
}

/// Return true iff `divisor` is a constant whose numeric value is non-zero.
/// Variable divisors and zero constants conservatively return false.
fn divisor_is_nonzero_constant(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        Operand::Constant(ConstValue::Float(v)) => *v != 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            !crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

fn is_float_operand(operand: &Operand, func: &VerifiableFunction) -> bool {
    matches!(operand_ty_owned(operand, func), Ty::Float { .. })
}

fn signed_binary_overflow_kind(
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    func: &VerifiableFunction,
) -> Option<VcKind> {
    let lhs_ty = operand_ty_owned(lhs, func);
    let rhs_ty = operand_ty_owned(rhs, func);
    (lhs_ty.is_signed() && rhs_ty.is_signed())
        .then_some(VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) })
}

/// Get the type of an operand by looking up its local declaration.
fn operand_ty_owned(operand: &Operand, func: &VerifiableFunction) -> Ty {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            func.body.locals.get(place.local).map(|decl| decl.ty.clone()).unwrap_or(Ty::Unit)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(_) => Ty::Bool,
            ConstValue::Int(_) => Ty::Unit,
            ConstValue::Uint(_, _) => Ty::Unit,
            ConstValue::Float(_) => Ty::Float { width: 64 },
            ConstValue::FloatBits { width, .. } => Ty::Float { width: *width },
            ConstValue::Unit | ConstValue::CallableItem { .. } => Ty::Unit,
            _ => Ty::Unit,
        },
        _ => Ty::Unit,
    }
}
