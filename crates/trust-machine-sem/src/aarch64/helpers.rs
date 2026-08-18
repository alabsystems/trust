// trust-machine-sem: AArch64 semantic helpers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{ExtendType, MemoryOperand, Operand, RegKind, Register, ShiftType};
use trust_types::Formula;

use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

/// Read a register operand on an INTEGER data-processing path.
///
/// SOUNDNESS: this used to be an `if is_zero_register / else if
/// is_stack_pointer / else read_gpr(r.index)` chain, which NEVER CONSULTED
/// `r.kind`. `Register` carries a kind and the decoder fills it in correctly —
/// `str d13,[x28,#0xa0]` (fd00538d) decodes to `Reg { kind: Simd, index: 13 }` —
/// but the `else` swallowed every non-ZR, non-SP kind and read the
/// GENERAL-PURPOSE register of the same NUMBER. The native semantic
/// differential measured the consequence directly against silicon: 5,721
/// disagreements, in which the model stored or loaded X13 where the hardware
/// used D13. Two register files, one index space, and a discarded tag.
///
/// A SIMD register is not the GPR of the same number, and on an integer path
/// there is no correct reading of one at all — the instruction shapes that
/// legitimately take a SIMD operand (the `LDR`/`STR` SIMD&FP forms) now handle
/// it themselves, against `MachineState::read_fpr`, before reaching here. So
/// every other kind is REFUSED. Approximating onto the neighbouring file is the
/// failure this whole function's history is about.
///
/// `RegKind` is `#[non_exhaustive]` and lives in another crate, so the wildcard
/// is mandatory and the compiler can never point at this site when a variant is
/// added. That is exactly why the wildcard must be a refusal and not a default
/// read.
fn integer_reg_value(
    state: &MachineState,
    reg: &Register,
    opcode: Opcode,
    index: usize,
    width: u32,
) -> Result<Formula, SemError> {
    match reg.kind {
        RegKind::Zr => Ok(Formula::BitVec { value: 0, width }),
        RegKind::Sp => Ok(state.read_sp(width)),
        RegKind::Gpr => Ok(state.read_gpr(reg.index, width)),
        other => Err(SemError::InvalidOperand {
            opcode,
            index,
            detail: format!(
                "operand is a {other:?} register (number {}), not a GPR; reading it as \
                 X{} would model a DIFFERENT register file — refusing rather than \
                 approximating onto the neighbour",
                reg.index, reg.index
            ),
        }),
    }
}

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
        Operand::Reg(r) => integer_reg_value(state, r, opcode, index, width),
        Operand::ShiftedReg { reg, shift, amount } => {
            // The SAME discard lived here: `reg.kind` was consulted only for ZR
            // and everything else fell through to `read_gpr`.
            let base = integer_reg_value(state, reg, opcode, index, width)?;
            apply_shift(base, *shift, *amount, width, opcode, index)
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
///
/// SOUNDNESS: this used to end in `_ => base, // future shift types`.
/// [`ShiftType`] is `#[non_exhaustive]` and lives in another crate, so a match
/// here is REQUIRED to carry a wildcard and the compiler can never point at this
/// site when a variant is added. That arm therefore meant "a shift type I do not
/// recognize is NO SHIFT AT ALL" — the register would be read straight through
/// and the gate would model, say, `MSL` as the identity. This is exactly the
/// class that let `Effect::PcUpdate` be dropped: a variant the function HANDLES
/// ITSELF is protected only by enumerating it correctly, never by the state
/// threader's catch-all. An unrecognized shift now fails closed.
///
/// The type is validated BEFORE the `amount == 0` identity short-circuit: a
/// zero-amount shift is the identity for all four architectural types, but that
/// is a fact about LSL/LSR/ASR/ROR, not about an unknown one (NEON's `MSL #0`,
/// for instance, shifts in ones and is NOT the identity). Recognizing the type
/// first means the short-circuit never has to be trusted for a type we do not
/// model.
fn apply_shift(
    base: Formula,
    shift: ShiftType,
    amount: u8,
    width: u32,
    opcode: Opcode,
    index: usize,
) -> Result<Formula, SemError> {
    match shift {
        ShiftType::Lsl | ShiftType::Lsr | ShiftType::Asr | ShiftType::Ror => {}
        other => {
            return Err(SemError::InvalidOperand {
                opcode,
                index,
                detail: format!(
                    "shifted-register operand uses unmodeled shift type {other:?}; \
                     refusing rather than treating it as no shift"
                ),
            });
        }
    }

    if amount == 0 {
        return Ok(base);
    }
    let shift_amt = Formula::BitVec { value: i128::from(amount), width };
    Ok(match shift {
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
        // Unreachable: the guard above already refused every other shape. Kept
        // as a REFUSAL, not a value, so the two matches cannot drift apart.
        other => {
            return Err(SemError::InvalidOperand {
                opcode,
                index,
                detail: format!("unmodeled shift type {other:?}"),
            });
        }
    })
}

/// Resolve a `MemoryOperand` to a 64-bit address formula.
pub(super) fn resolve_mem_address(
    state: &MachineState,
    mem: &MemoryOperand,
) -> Result<Formula, SemError> {
    match mem {
        MemoryOperand::Base { base } => read_base_reg(state, base),
        MemoryOperand::BaseOffset { base, offset } => {
            let base_val = read_base_reg(state, base)?;
            Ok(Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::BaseRegister { base, index, extend, shift } => {
            let base_val = read_base_reg(state, base)?;
            // ExtendReg first, THEN the left shift — in that order, and both in
            // 64 bits. Destructuring the extend away here (`shift, ..`) and
            // always reading the full X register made all four encodable forms
            // produce byte-identical effects; see `extended_index_value`.
            let mut idx_val = extended_index_value(state, index, *extend)?;
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
            let base_val = read_base_reg(state, base)?;
            Ok(Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::PostIndex { base, .. } => {
            // Address = base (offset applied after, writeback handled separately).
            read_base_reg(state, base)
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
///
/// SOUNDNESS: this was `if is_stack_pointer { sp } else { read_gpr(index) }` —
/// the same `r.kind` discard as `integer_reg_value`, one indirection away. An
/// addressing mode's base is a GPR or SP by every encoding the decoder builds
/// (`gpr_or_sp`), so no legal word reaches the refusal; that is precisely why
/// it belongs here rather than being left to the decoder's ordering. The
/// register-file confusion in the `Ldr`/`Str` family was a discard exactly like
/// this one, and it was reachable.
fn read_base_reg(state: &MachineState, reg: &Register) -> Result<Formula, SemError> {
    match reg.kind {
        RegKind::Sp => Ok(state.read_sp(64)),
        RegKind::Gpr => Ok(state.read_gpr(reg.index, 64)),
        other => Err(SemError::InvalidOperand {
            opcode: Opcode::Ldr,
            index: 1,
            detail: format!(
                "memory base operand is a {other:?} register (number {}); only a GPR or \
                 SP can be a base address",
                reg.index
            ),
        }),
    }
}

/// Read the index register of a register-offset addressing mode and apply the
/// architectural extension, yielding a 64-bit value.
///
/// ARM ARM `ExtendReg(m, extend_type, 0)`: `UXTW`/`SXTW` take the LOW 32 BITS of
/// `Xm` and zero-/sign-extend them to 64; `LSL` (which the decoder represents as
/// `extend: None`) and `UXTX`/`SXTX` take the full 64-bit register. The caller
/// applies the `S`-bit left shift AFTER this, in 64 bits.
///
/// SOUNDNESS: this used to be `state.read_gpr(index.index, 64)` for every form —
/// the extend was destructured away. That made `ldr w0,[x1,x2,lsl#2]` and the
/// `uxtw#2` / `sxtw#2` / `sxtx#2` forms produce BYTE-IDENTICAL `Effect` lists, so
/// the output gate could not distinguish them for ANY spec: a miscompile that
/// swapped one for another was invisible. `UXTW`/`SXTW` differ from `LSL`
/// whenever `Xm`'s high half is non-zero, and `UXTW` differs from `SXTW`
/// whenever `Wm` is negative.
///
/// Every shape that is not one of the four architectural forms is REFUSED, never
/// approximated: the byte/halfword extends are not encodable in a load/store
/// register offset, `ExtendType` is `#[non_exhaustive]` so a future variant must
/// not fall through to "no extension", and an extend that disagrees with the
/// decoded index-register width means the `option` field was one of the reserved
/// values.
fn extended_index_value(
    state: &MachineState,
    index: &Register,
    extend: Option<ExtendType>,
) -> Result<Formula, SemError> {
    let (src_width, signed) = match extend {
        // LSL — the index is the full 64-bit X register, unextended.
        None | Some(ExtendType::Uxtx) => (64u32, false),
        // SXTX of a 64-bit source is the identity; kept explicit, not merged.
        Some(ExtendType::Sxtx) => (64, true),
        Some(ExtendType::Uxtw) => (32, false),
        Some(ExtendType::Sxtw) => (32, true),
        other => {
            return Err(SemError::InvalidOperand {
                opcode: Opcode::Ldr,
                index: 1,
                detail: format!(
                    "register-offset index extend {other:?} is not encodable in a \
                     load/store register offset"
                ),
            });
        }
    };

    if u32::from(index.width) != src_width {
        return Err(SemError::InvalidOperand {
            opcode: Opcode::Ldr,
            index: 1,
            detail: format!(
                "register-offset index width {} disagrees with extend {extend:?} \
                 (expected {src_width}); reserved `option` encoding",
                index.width
            ),
        });
    }

    // The third `r.kind` discard on this path. The index register is built by
    // `gpr_or_zr`, so it is a GPR or ZR and `read_gpr` answers 0 for ZR's index
    // 31 correctly — but "correct because of what the decoder happens to
    // build" is the property that failed for the SIMD load/store forms.
    match index.kind {
        RegKind::Gpr | RegKind::Zr => {}
        other => {
            return Err(SemError::InvalidOperand {
                opcode: Opcode::Ldr,
                index: 1,
                detail: format!(
                    "register-offset index is a {other:?} register (number {}); only a \
                     GPR or ZR can be an index",
                    index.index
                ),
            });
        }
    }

    let raw = state.read_gpr(index.index, src_width);
    Ok(if src_width == 64 {
        raw
    } else if signed {
        // The second field of BvSignExt/BvZeroExt is the SMT-LIB extension
        // AMOUNT (bits added), not the target width.
        Formula::BvSignExt(Box::new(raw), 64 - src_width)
    } else {
        Formula::BvZeroExt(Box::new(raw), 64 - src_width)
    })
}

/// Compute NZCV flag updates for an ADD-WITH-CARRY or SUBTRACT-WITH-BORROW.
///
/// SOUNDNESS: `ADCS`/`SBCS` used to call [`compute_nzcv`], which takes only
/// `(lhs, rhs, result)` and therefore computes the carry-OUT as though the
/// carry-IN were zero. The RESULT already carried it — the arms add
/// `Ite(C, 1, 0)` — so the register was right and the flag beside it was wrong,
/// which is the quietest possible shape for this bug. The native semantic
/// differential measured 456 disagreements; `adcs w5,w0,w3` (3a030005) with C=1
/// gave `nzcv` where the hardware gave `nzCv`.
///
/// N, Z and V need no change and get none: all three are functions of the
/// with-carry `result` (and the operand signs), and the ARM sign rule for V
/// stays exact when a carry-in is folded into the result. C is the only flag
/// that cannot be recovered from `(lhs, rhs, result)` alone.
///
/// THE CARRY-OUT, EXACTLY. For `result = lhs + y + c` in `width` bits, the ARM
/// pseudocode's `UInt(result) != UInt(lhs) + UInt(y) + UInt(c)` is
///
/// ```text
///     C  =  (result <u lhs)  OR  (c AND result == lhs)
/// ```
///
/// — with `c` clear this is the ordinary wrapped-around test, and with `c` set
/// the boundary case `result == lhs` (which `lhs + y + 1 ≡ lhs`, i.e.
/// `y = all-ones`, produces) is a carry too. That second disjunct is the entire
/// 456.
///
/// `SBCS` is `AddWithCarry(Rn, NOT(Rm), C)`, so `lhs` is still `Rn` and the same
/// formula applies unchanged; the caller passes `rhs = Rm` only so the V rule
/// can use `is_sub`, exactly as [`compute_nzcv`] does.
pub(super) fn compute_nzcv_with_carry(
    lhs: &Formula,
    rhs: &Formula,
    result: &Formula,
    width: u32,
    is_sub: bool,
    carry_in: &Formula,
) -> Effect {
    let Effect::FlagUpdate { n, z, v, .. } = compute_nzcv(lhs, rhs, result, width, is_sub) else {
        // `compute_nzcv` returns exactly one variant, by construction.
        unreachable!("compute_nzcv returns Effect::FlagUpdate")
    };

    let wrapped = Formula::BvULt(Box::new(result.clone()), Box::new(lhs.clone()), width);
    let boundary = Formula::And(vec![
        carry_in.clone(),
        Formula::Eq(Box::new(result.clone()), Box::new(lhs.clone())),
    ]);
    let c = Formula::Or(vec![wrapped, boundary]);

    Effect::FlagUpdate { n, z, c, v }
}

/// Compute NZCV flag updates for an addition or subtraction.
///
/// `is_sub`: true for SUB/SUBS/CMP, false for ADD/ADDS/CMN.
///
/// The carry-IN is zero for ADD/ADDS and one for SUB/SUBS, which is what makes
/// the `C` computed here exact for those forms and ONLY those forms. ADC/SBC
/// take a symbolic carry-in and must use [`compute_nzcv_with_carry`].
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
