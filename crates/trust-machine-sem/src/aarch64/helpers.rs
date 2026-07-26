// trust-machine-sem: AArch64 semantic helpers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{MemoryOperand, Operand, ShiftType};
use trust_types::Formula;

use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

/// Convert a disassembler `Operand` to a symbolic `Formula`.
pub(super) fn operand_to_formula(
    state: &MachineState,
    operand: Option<&Operand>,
    opcode: Opcode,
    index: usize,
    width: u32,
) -> Result<Formula, SemError> {
    let op = operand.ok_or_else(|| SemError::InvalidOperand {
        opcode,
        index,
        detail: "missing operand".into(),
    })?;

    match op {
        Operand::Reg(r) => {
            if r.is_zero_register() {
                Ok(Formula::BitVec { value: 0, width })
            } else if r.is_stack_pointer() {
                Ok(state.read_sp(width))
            } else {
                Ok(state.read_gpr(r.index, width))
            }
        }
        Operand::ShiftedReg { reg, shift, amount } => {
            let base = if reg.is_zero_register() {
                Formula::BitVec { value: 0, width }
            } else {
                state.read_gpr(reg.index, width)
            };
            Ok(apply_shift(base, *shift, *amount, width))
        }
        Operand::Imm(v) => Ok(Formula::BitVec { value: *v as i128, width }),
        Operand::SignedImm(v) => Ok(Formula::BitVec { value: *v as i128, width }),
        _ => Err(SemError::InvalidOperand {
            opcode,
            index,
            detail: format!("unexpected operand type: {op:?}"),
        }),
    }
}

/// Apply a barrel-shifter operation.
fn apply_shift(base: Formula, shift: ShiftType, amount: u8, width: u32) -> Formula {
    if amount == 0 {
        return base;
    }
    let shift_amt = Formula::BitVec { value: i128::from(amount), width };
    match shift {
        ShiftType::Lsl => Formula::BvShl(Box::new(base), Box::new(shift_amt), width),
        ShiftType::Lsr => Formula::BvLShr(Box::new(base), Box::new(shift_amt), width),
        ShiftType::Asr => Formula::BvAShr(Box::new(base), Box::new(shift_amt), width),
        ShiftType::Ror => {
            // ROR(x, n) = (x >> n) | (x << (width - n))
            let right = Formula::BvLShr(Box::new(base.clone()), Box::new(shift_amt.clone()), width);
            let left_amt = Formula::BitVec { value: i128::from(width) - i128::from(amount), width };
            let left = Formula::BvShl(Box::new(base), Box::new(left_amt), width);
            Formula::BvOr(Box::new(right), Box::new(left), width)
        }
        _ => base, // future shift types
    }
}

/// Resolve a `MemoryOperand` to a 64-bit address formula.
pub(super) fn resolve_mem_address(
    state: &MachineState,
    mem: &MemoryOperand,
) -> Result<Formula, SemError> {
    match mem {
        MemoryOperand::Base { base } => Ok(read_base_reg(state, base)),
        MemoryOperand::BaseOffset { base, offset } => {
            let base_val = read_base_reg(state, base);
            Ok(Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::BaseRegister { base, index, shift, .. } => {
            let base_val = read_base_reg(state, base);
            let mut idx_val = state.read_gpr(index.index, 64);
            if *shift > 0 {
                idx_val = Formula::BvShl(
                    Box::new(idx_val),
                    Box::new(Formula::BitVec { value: i128::from(*shift), width: 64 }),
                    64,
                );
            }
            Ok(Formula::BvAdd(Box::new(base_val), Box::new(idx_val), 64))
        }
        MemoryOperand::PreIndex { base, offset } => {
            // Address = base + offset (writeback handled separately).
            let base_val = read_base_reg(state, base);
            Ok(Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::PostIndex { base, .. } => {
            // Address = base (offset applied after, writeback handled separately).
            Ok(read_base_reg(state, base))
        }
        MemoryOperand::PcRelative { offset } => Ok(Formula::BvAdd(
            Box::new(Formula::Var("PC".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
            64,
        )),
        _ => Err(SemError::InvalidOperand {
            opcode: Opcode::Ldr,
            index: 1,
            detail: "unsupported memory addressing mode".into(),
        }),
    }
}

/// Read a base register (GPR or SP) as a 64-bit value.
fn read_base_reg(state: &MachineState, reg: &trust_disasm::operand::Register) -> Formula {
    if reg.is_stack_pointer() { state.read_sp(64) } else { state.read_gpr(reg.index, 64) }
}

/// Compute NZCV flag updates for an addition or subtraction.
///
/// `is_sub`: true for SUB/SUBS/CMP, false for ADD/ADDS/CMN.
pub(super) fn compute_nzcv(
    lhs: &Formula,
    rhs: &Formula,
    result: &Formula,
    width: u32,
    is_sub: bool,
) -> Effect {
    let sign_bit = width - 1;

    // N = result[sign_bit]
    let n = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(result.clone()),
            high: sign_bit,
            low: sign_bit,
        }),
        Box::new(Formula::BitVec { value: 1, width: 1 }),
    );

    // Z = (result == 0)
    let z = Formula::Eq(Box::new(result.clone()), Box::new(Formula::BitVec { value: 0, width }));

    // C (carry):
    //   ADD: carry out of unsigned addition
    //   SUB: NOT borrow (i.e., lhs >= rhs unsigned)
    let c = if is_sub {
        // For SUB, C = (lhs >=u rhs) which is NOT(lhs <u rhs)
        Formula::Not(Box::new(Formula::BvULt(Box::new(lhs.clone()), Box::new(rhs.clone()), width)))
    } else {
        // For ADD, C = (result <u lhs) — unsigned overflow
        Formula::BvULt(Box::new(result.clone()), Box::new(lhs.clone()), width)
    };

    // V (signed overflow):
    //   ADD: lhs[sign] == rhs[sign] && result[sign] != lhs[sign]
    //   SUB: lhs[sign] != rhs[sign] && result[sign] != lhs[sign]
    let lhs_sign =
        Formula::BvExtract { inner: Box::new(lhs.clone()), high: sign_bit, low: sign_bit };
    let rhs_sign =
        Formula::BvExtract { inner: Box::new(rhs.clone()), high: sign_bit, low: sign_bit };
    let res_sign =
        Formula::BvExtract { inner: Box::new(result.clone()), high: sign_bit, low: sign_bit };

    let signs_match = Formula::Eq(Box::new(lhs_sign.clone()), Box::new(rhs_sign));
    let result_differs =
        Formula::Not(Box::new(Formula::Eq(Box::new(res_sign), Box::new(lhs_sign))));

    let v = if is_sub {
        // SUB overflow: signs differ AND result sign != lhs sign
        Formula::And(vec![Formula::Not(Box::new(signs_match)), result_differs])
    } else {
        // ADD overflow: signs same AND result sign != lhs sign
        Formula::And(vec![signs_match, result_differs])
    };

    Effect::FlagUpdate { n, z, c, v }
}
