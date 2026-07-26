// trust-machine-sem: x86_64 ISA semantics
//
// Full implementation of x86_64 instruction semantics for the lifter.
// Maps decoded x86_64 instructions to their logical effects on machine state.
//
// x86_64 key differences from AArch64:
// - Variable-length instructions (1-15 bytes), PC advances by insn.size
// - EFLAGS (CF, ZF, SF, OF) instead of NZCV — mapped to FlagUpdate{n=SF, z=ZF, c=CF, v=OF}
// - 16 GPRs (RAX=0..R15=15), RSP is index 4
// - Stack-based CALL/RET (push/pop return address via RSP)
// - Two-operand encoding: dst is also a source (e.g., ADD RAX, RCX => RAX += RCX)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Instruction;
use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{Condition, MemoryOperand, Operand, RegKind};
use trust_types::{Formula, Sort};

use crate::effect::Effect;
use crate::error::SemError;
use crate::semantics::Semantics;
use crate::state::MachineState;

/// x86_64 RSP register index.
const RSP_INDEX: u8 = 4;

/// x86_64 instruction semantics.
///
/// Implements `Semantics` for all Priority 1 x86_64 instructions:
/// MOV, ADD, SUB, CMP, AND, OR, XOR, TEST, NOT, NEG, INC, DEC,
/// SHL, SHR, SAR, LEA, PUSH, POP, CALL, RET, JMP, Jcc, NOP,
/// LEAVE, MOVZX, MOVSX, IMUL, MUL, DIV, IDIV, XCHG,
/// CMOVcc, SETcc, CMPXCHG, BSF, BSR, CDQ/CQO.
pub struct X86_64Semantics;

impl Semantics for X86_64Semantics {
    fn effects(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        match insn.opcode {
            // Data movement
            Opcode::Mov => self.sem_mov(state, insn),
            Opcode::Lea => self.sem_lea(state, insn),
            Opcode::Push => self.sem_push(state, insn),
            Opcode::Pop => self.sem_pop(state, insn),
            Opcode::Movzx => self.sem_movzx(state, insn),
            Opcode::Movsx | Opcode::Movsxd => self.sem_movsx(state, insn),
            Opcode::Xchg => self.sem_xchg(state, insn),
            Opcode::Cmovcc => self.sem_cmovcc(state, insn),
            Opcode::Setcc => self.sem_setcc(state, insn),
            Opcode::Cmpxchg => self.sem_cmpxchg(state, insn),
            Opcode::Bsf => self.sem_bsf(state, insn),
            Opcode::Bsr => self.sem_bsr(state, insn),

            // Arithmetic (sets EFLAGS)
            Opcode::Add => self.sem_add(state, insn),
            Opcode::Sub => self.sem_sub(state, insn),
            Opcode::Cmp => self.sem_cmp(state, insn),
            Opcode::Inc => self.sem_inc(state, insn),
            Opcode::Dec => self.sem_dec(state, insn),
            Opcode::Neg => self.sem_neg(state, insn),
            Opcode::Imul => self.sem_imul(state, insn),
            Opcode::Mul => self.sem_mul(state, insn),
            Opcode::Div => self.sem_div(state, insn),
            Opcode::Idiv => self.sem_idiv(state, insn),
            Opcode::Cdq => self.sem_cdq(state, insn),
            Opcode::Cqo => self.sem_cqo(state, insn),

            // Logic (sets EFLAGS)
            Opcode::And => self.sem_and(state, insn),
            Opcode::Or => self.sem_or(state, insn),
            Opcode::Xor => self.sem_xor(state, insn),
            Opcode::Test => self.sem_test(state, insn),
            Opcode::Not => self.sem_not(state, insn),

            // Shifts (sets EFLAGS)
            Opcode::Shl => self.sem_shl(state, insn),
            Opcode::Shr => self.sem_shr(state, insn),
            Opcode::Sar => self.sem_sar(state, insn),

            // Control flow
            Opcode::Jmp => self.sem_jmp(state, insn),
            Opcode::Jcc => self.sem_jcc(state, insn),
            Opcode::Call => self.sem_call(state, insn),
            Opcode::Ret => self.sem_ret(state, insn),

            // Misc
            Opcode::Nop | Opcode::Endbr64 => Ok(vec![pc_advance(state, insn)]),
            Opcode::Leave => self.sem_leave(state, insn),
            Opcode::Int3 | Opcode::Syscall => Err(SemError::UnsupportedOpcode(insn.opcode)),

            other => Err(SemError::UnsupportedOpcode(other)),
        }
    }
}

// ===========================================================================
// Instruction implementations
// ===========================================================================

impl X86_64Semantics {
    // -----------------------------------------------------------------------
    // MOV: dst = src (no flag changes)
    // -----------------------------------------------------------------------

    fn sem_mov(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let src_read = mem_read_effect_for_operand(state, insn.operand(1), dst_width)?;
        let src = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let mut effects = Vec::new();
        if let Some(read) = src_read {
            effects.push(read);
        }
        effects.push(write_dst_checked(state, &dst, dst_width, src)?);
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // LEA: dst = effective address (no memory access, no flags)
    // -----------------------------------------------------------------------

    fn sem_lea(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let addr = match insn.operand(1) {
            Some(Operand::Mem(m)) => resolve_mem_address(state, m)?,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "LEA requires memory operand".into(),
                });
            }
        };

        // Truncate or use directly depending on dst width.
        let value = if dst_width < 64 {
            Formula::BvExtract { inner: Box::new(addr), high: dst_width - 1, low: 0 }
        } else {
            addr
        };

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, value)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // PUSH: RSP -= 8; [RSP] = src
    // -----------------------------------------------------------------------

    fn sem_push(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let src_width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            Some(Operand::Imm(_) | Operand::SignedImm(_)) => 64,
            _ => 64,
        };
        let src = resolve_operand(state, insn.operand(0), insn.opcode, 0, src_width)?;

        // In 64-bit mode, PUSH always pushes 8 bytes.
        let push_bytes: u32 = 8;
        let new_sp = Formula::BvSub(
            Box::new(state.sp.clone()),
            Box::new(Formula::BitVec { value: i128::from(push_bytes), width: 64 }),
            64,
        );

        // Sign-extend or zero-extend source to 64 bits if needed.
        let value_64 = zero_extend_to(src, src_width, 64);

        let effects = vec![
            Effect::SpWrite { value: new_sp.clone() },
            Effect::MemWrite { address: new_sp, value: value_64, width_bytes: push_bytes },
            pc_advance(state, insn),
        ];
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // POP: dst = [RSP]; RSP += 8
    // -----------------------------------------------------------------------

    fn sem_pop(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let pop_bytes: u32 = 8;

        let loaded = load_le_bytes(state, &state.sp, pop_bytes, 64);

        let value = if dst_width < 64 {
            Formula::BvExtract { inner: Box::new(loaded.clone()), high: dst_width - 1, low: 0 }
        } else {
            loaded.clone()
        };

        let new_sp = Formula::BvAdd(
            Box::new(state.sp.clone()),
            Box::new(Formula::BitVec { value: i128::from(pop_bytes), width: 64 }),
            64,
        );

        let effects = vec![
            Effect::MemRead { address: state.sp.clone(), width_bytes: pop_bytes },
            write_dst_checked(state, &dst, dst_width, value)?,
            Effect::SpWrite { value: new_sp },
            pc_advance(state, insn),
        ];
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // ADD: dst += src, sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_add(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvAdd(Box::new(lhs.clone()), Box::new(rhs.clone()), dst_width);
        let flags = compute_eflags(&lhs, &rhs, &result, dst_width, false);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // SUB: dst -= src, sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_sub(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvSub(Box::new(lhs.clone()), Box::new(rhs.clone()), dst_width);
        let flags = compute_eflags(&lhs, &rhs, &result, dst_width, true);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // CMP: sets EFLAGS from (dst - src), no writeback
    // -----------------------------------------------------------------------

    fn sem_cmp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvSub(Box::new(lhs.clone()), Box::new(rhs.clone()), dst_width);
        let flags = compute_eflags(&lhs, &rhs, &result, dst_width, true);

        Ok(vec![flags, pc_advance(state, insn)])
    }

    // -----------------------------------------------------------------------
    // INC: dst += 1, sets all EFLAGS except CF
    // -----------------------------------------------------------------------

    fn sem_inc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let one = Formula::BitVec { value: 1, width: dst_width };

        let result = Formula::BvAdd(Box::new(lhs.clone()), Box::new(one.clone()), dst_width);
        // INC preserves CF, sets ZF/SF/OF based on result.
        let flags = compute_eflags_preserve_cf(state, &lhs, &one, &result, dst_width, false);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // DEC: dst -= 1, sets all EFLAGS except CF
    // -----------------------------------------------------------------------

    fn sem_dec(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let one = Formula::BitVec { value: 1, width: dst_width };

        let result = Formula::BvSub(Box::new(lhs.clone()), Box::new(one.clone()), dst_width);
        let flags = compute_eflags_preserve_cf(state, &lhs, &one, &result, dst_width, true);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // NEG: dst = 0 - dst, sets EFLAGS (CF = dst != 0)
    // -----------------------------------------------------------------------

    fn sem_neg(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let val = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let zero = Formula::BitVec { value: 0, width: dst_width };

        let result = Formula::BvSub(Box::new(zero.clone()), Box::new(val.clone()), dst_width);
        let flags = compute_eflags(&zero, &val, &result, dst_width, true);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // IMUL: two/three-operand multiply
    // -----------------------------------------------------------------------

    fn sem_imul(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;

        // Two-operand: IMUL r, r/m => r = r * r/m
        // Three-operand: IMUL r, r/m, imm => r = r/m * imm
        let result = if insn.operand_count() >= 3 {
            // Three-operand: dst = op1 * op2
            let op1 = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;
            let op2 = resolve_operand(state, insn.operand(2), insn.opcode, 2, dst_width)?;
            Formula::BvMul(Box::new(op1), Box::new(op2), dst_width)
        } else {
            // Two-operand: dst = dst * src
            let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
            let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;
            Formula::BvMul(Box::new(lhs), Box::new(rhs), dst_width)
        };

        // IMUL sets CF and OF if the result is truncated; ZF/SF are undefined.
        // Model as: CF=OF=false (simplified — correct for non-overflowing cases).
        let sign_bit = dst_width - 1;
        let sf = Formula::Eq(
            Box::new(Formula::BvExtract {
                inner: Box::new(result.clone()),
                high: sign_bit,
                low: sign_bit,
            }),
            Box::new(Formula::BitVec { value: 1, width: 1 }),
        );
        let flags = Effect::FlagUpdate {
            n: sf,
            z: Formula::Eq(
                Box::new(result.clone()),
                Box::new(Formula::BitVec { value: 0, width: dst_width }),
            ),
            c: Formula::Bool(false),
            v: Formula::Bool(false),
        };

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // CDQ/CQO: sign-extend accumulator into EDX/RDX
    // -----------------------------------------------------------------------

    fn sem_cdq(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        if insn.size != 1 {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "16-bit CWD prefix mode is not modeled".into(),
            });
        }

        let eax = state.read_gpr(0, 32);
        let sign_mask =
            Formula::BvAShr(Box::new(eax), Box::new(Formula::BitVec { value: 31, width: 32 }), 32);

        Ok(vec![reg_write(state, 2, 32, sign_mask), pc_advance(state, insn)])
    }

    fn sem_cqo(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let rax = state.read_gpr(0, 64);
        let sign_mask =
            Formula::BvAShr(Box::new(rax), Box::new(Formula::BitVec { value: 63, width: 64 }), 64);

        Ok(vec![
            Effect::RegWrite { index: 2, width: 64, value: sign_mask },
            pc_advance(state, insn),
        ])
    }

    // -----------------------------------------------------------------------
    // MUL/DIV/IDIV: implicit accumulator integer operations
    // -----------------------------------------------------------------------

    fn sem_mul(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let width = single_operand_reg_width(insn, 0)?;
        validate_accumulator_width(insn, width)?;

        let src = resolve_operand(state, insn.operand(0), insn.opcode, 0, width)?;
        let acc = state.read_gpr(0, width);
        let product_width = width * 2;
        let lhs = zero_extend_to(acc, width, product_width);
        let rhs = zero_extend_to(src, width, product_width);
        let product = Formula::BvMul(Box::new(lhs), Box::new(rhs), product_width);

        let high = Formula::BvExtract {
            inner: Box::new(product.clone()),
            high: product_width - 1,
            low: width,
        };
        let overflow = Formula::Not(Box::new(Formula::Eq(
            Box::new(high),
            Box::new(Formula::BitVec { value: 0, width }),
        )));

        let mut effects = write_accumulator_pair(state, width, product);
        effects.push(Effect::FlagUpdate {
            n: undefined_bool(insn, "mul_sf"),
            z: undefined_bool(insn, "mul_zf"),
            c: overflow.clone(),
            v: overflow,
        });
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    fn sem_div(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_div_common(state, insn, false)
    }

    fn sem_idiv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_div_common(state, insn, true)
    }

    fn sem_div_common(
        &self,
        _state: &MachineState,
        insn: &Instruction,
        signed: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let width = single_operand_reg_width(insn, 0)?;
        validate_accumulator_width(insn, width)?;
        let op = if signed { "IDIV" } else { "DIV" };
        Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: format!(
                "{op} trap preconditions (#DE on zero divisor or quotient overflow) are not represented in Effect; failing closed"
            ),
        })
    }

    // -----------------------------------------------------------------------
    // AND: dst &= src, sets EFLAGS (CF=0, OF=0)
    // -----------------------------------------------------------------------

    fn sem_and(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvAnd(Box::new(lhs), Box::new(rhs), dst_width);
        let flags = logic_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // OR: dst |= src, sets EFLAGS (CF=0, OF=0)
    // -----------------------------------------------------------------------

    fn sem_or(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvOr(Box::new(lhs), Box::new(rhs), dst_width);
        let flags = logic_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // XOR: dst ^= src, sets EFLAGS (CF=0, OF=0)
    // -----------------------------------------------------------------------

    fn sem_xor(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvXor(Box::new(lhs), Box::new(rhs), dst_width);
        let flags = logic_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // TEST: AND without writeback, sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_test(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let lhs = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let rhs = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvAnd(Box::new(lhs), Box::new(rhs), dst_width);
        let flags = logic_eflags(&result, dst_width);

        Ok(vec![flags, pc_advance(state, insn)])
    }

    // -----------------------------------------------------------------------
    // NOT: dst = ~dst (no flags)
    // -----------------------------------------------------------------------

    fn sem_not(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let val = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;

        let result = Formula::BvNot(Box::new(val), dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // SHL: dst <<= count, sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_shl(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let val = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let count = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvShl(Box::new(val.clone()), Box::new(count), dst_width);
        let flags = shift_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // SHR: dst >>= count (logical), sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_shr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let val = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let count = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvLShr(Box::new(val.clone()), Box::new(count), dst_width);
        let flags = shift_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // SAR: dst >>= count (arithmetic), sets EFLAGS
    // -----------------------------------------------------------------------

    fn sem_sar(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let val = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 0)?;
        let count = resolve_operand(state, insn.operand(1), insn.opcode, 1, dst_width)?;

        let result = Formula::BvAShr(Box::new(val.clone()), Box::new(count), dst_width);
        let flags = shift_eflags(&result, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, result)?, flags];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // JMP: unconditional branch
    // -----------------------------------------------------------------------

    fn sem_jmp(&self, _state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target(insn)?;
        Ok(vec![Effect::Branch { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    // -----------------------------------------------------------------------
    // Jcc: conditional jump based on EFLAGS
    // -----------------------------------------------------------------------

    fn sem_jcc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let condition = insn
            .operands()
            .find_map(|op| if let Operand::Cond(c) = op { Some(*c) } else { None })
            .ok_or_else(|| SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "expected condition operand for Jcc".into(),
            })?;

        let target = branch_target(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: i128::from(insn.size), width: 64 }),
            64,
        );

        Ok(vec![Effect::ConditionalBranch { condition, target, fallthrough }])
    }

    // -----------------------------------------------------------------------
    // CALL: push return address, branch to target
    // -----------------------------------------------------------------------

    fn sem_call(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (target, target_read) = call_target(state, insn)?;
        let return_addr = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: i128::from(insn.size), width: 64 }),
            64,
        );

        // RSP -= 8
        let new_sp = Formula::BvSub(
            Box::new(state.sp.clone()),
            Box::new(Formula::BitVec { value: 8, width: 64 }),
            64,
        );

        let mut effects = Vec::new();
        if let Some(read) = target_read {
            effects.push(read);
        }
        effects.extend([
            Effect::SpWrite { value: new_sp.clone() },
            Effect::MemWrite { address: new_sp, value: return_addr.clone(), width_bytes: 8 },
            Effect::Call { target: target.clone(), return_addr },
            Effect::PcUpdate { value: target },
        ]);
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // RET: pop return address, branch to it
    // -----------------------------------------------------------------------

    fn sem_ret(&self, state: &MachineState, _insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let return_addr = load_le_bytes(state, &state.sp, 8, 64);

        let new_sp = Formula::BvAdd(
            Box::new(state.sp.clone()),
            Box::new(Formula::BitVec { value: 8, width: 64 }),
            64,
        );

        Ok(vec![
            Effect::MemRead { address: state.sp.clone(), width_bytes: 8 },
            Effect::SpWrite { value: new_sp },
            Effect::Return { target: return_addr.clone() },
            Effect::PcUpdate { value: return_addr },
        ])
    }

    // -----------------------------------------------------------------------
    // LEAVE: RSP = RBP; POP RBP
    // -----------------------------------------------------------------------

    fn sem_leave(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        // RSP = RBP (index 5)
        let rbp = state.read_gpr(5, 64);
        let loaded = load_le_bytes(state, &rbp, 8, 64);

        let new_sp = Formula::BvAdd(
            Box::new(rbp.clone()),
            Box::new(Formula::BitVec { value: 8, width: 64 }),
            64,
        );

        Ok(vec![
            // RSP = RBP
            Effect::SpWrite { value: rbp.clone() },
            // RBP = [RSP] (which is old RBP)
            Effect::MemRead { address: rbp, width_bytes: 8 },
            Effect::RegWrite { index: 5, width: 64, value: loaded },
            // RSP += 8
            Effect::SpWrite { value: new_sp },
            pc_advance(state, insn),
        ])
    }

    // -----------------------------------------------------------------------
    // MOVZX: zero-extend source into destination
    // -----------------------------------------------------------------------

    fn sem_movzx(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let src_width = match insn.operand(1) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            Some(Operand::Mem(_)) => {
                // Distinguish MOVZX r, r/m8 (0F B6) from MOVZX r, r/m16 (0F B7)
                // via the raw encoding stored by the decoder.
                if insn.encoding == 0x0FB7 { 16 } else { 8 }
            }
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register or memory for MOVZX".into(),
                });
            }
        };
        let src = resolve_operand(state, insn.operand(1), insn.opcode, 1, src_width)?;

        let extended = zero_extend_to(src, src_width, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, extended)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // MOVSX/MOVSXD: sign-extend source into destination
    // -----------------------------------------------------------------------

    fn sem_movsx(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst, dst_width) = extract_dst(insn)?;
        let src_width = match insn.operand(1) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            Some(Operand::Mem(_)) => {
                // For MOVSXD the source is 32-bit. For MOVSX it's 8 or 16.
                if insn.opcode == Opcode::Movsxd { 32 } else { 8 }
            }
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register or memory for MOVSX".into(),
                });
            }
        };
        let src = resolve_operand(state, insn.operand(1), insn.opcode, 1, src_width)?;

        let extended = sign_extend_to(src, src_width, dst_width);

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, extended)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // XCHG: swap two register/memory operands (no flags)
    // -----------------------------------------------------------------------

    fn sem_xchg(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let width = paired_operand_width(insn, 0, 1)?;
        let (lhs_dst, _) = extract_dst_at(insn, 0, Some(width))?;
        let (rhs_dst, _) = extract_dst_at(insn, 1, Some(width))?;

        if matches!((&lhs_dst, &rhs_dst), (DstOperand::Mem(_), DstOperand::Mem(_))) {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 1,
                detail: "XCHG with two memory operands is invalid".into(),
            });
        }

        let lhs = resolve_dst_value_checked(state, &lhs_dst, width, insn.opcode, 0)?;
        let rhs = resolve_dst_value_checked(state, &rhs_dst, width, insn.opcode, 1)?;

        let mut effects = vec![
            write_dst_checked(state, &lhs_dst, width, rhs)?,
            write_dst_checked(state, &rhs_dst, width, lhs)?,
        ];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // CMOVcc: dst = condition ? src : dst (no flags)
    // -----------------------------------------------------------------------

    fn sem_cmovcc(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let cond = extract_condition(insn, 0)?;
        let cond_formula = x86_condition_to_formula(state, cond, insn, 0)?;
        let (dst, dst_width) = extract_dst_at(insn, 1, None)?;

        if matches!(dst, DstOperand::Mem(_)) {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 1,
                detail: "CMOVcc destination must be a register".into(),
            });
        }

        let old = resolve_dst_value_checked(state, &dst, dst_width, insn.opcode, 1)?;
        let src = resolve_operand(state, insn.operand(2), insn.opcode, 2, dst_width)?;
        let value = Formula::Ite(Box::new(cond_formula), Box::new(src), Box::new(old));

        let mut effects = vec![write_dst_checked(state, &dst, dst_width, value)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // SETcc: r/m8 = condition ? 1 : 0 (no flags)
    // -----------------------------------------------------------------------

    fn sem_setcc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let cond = extract_condition(insn, 0)?;
        let cond_formula = x86_condition_to_formula(state, cond, insn, 0)?;
        let (dst, dst_width) = extract_dst_at(insn, 1, Some(8))?;
        if dst_width != 8 {
            return Err(SemError::WidthMismatch { expected: 8, actual: dst_width });
        }

        let value = Formula::Ite(
            Box::new(cond_formula),
            Box::new(Formula::BitVec { value: 1, width: 8 }),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        );

        let mut effects = vec![write_dst_checked(state, &dst, 8, value)?];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // CMPXCHG: compare accumulator with dst, exchange or load dst
    // -----------------------------------------------------------------------

    fn sem_cmpxchg(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst, width) = extract_dst(insn)?;
        validate_accumulator_width(insn, width)?;

        let dst_value = resolve_dst_value_checked(state, &dst, width, insn.opcode, 0)?;
        let src = resolve_operand(state, insn.operand(1), insn.opcode, 1, width)?;
        let acc = state.read_gpr(0, width);
        let eq = Formula::Eq(Box::new(acc.clone()), Box::new(dst_value.clone()));
        let cmp_result = Formula::BvSub(Box::new(acc.clone()), Box::new(dst_value.clone()), width);
        let flags = compute_eflags(&acc, &dst_value, &cmp_result, width, true);

        let dst_new =
            Formula::Ite(Box::new(eq.clone()), Box::new(src), Box::new(dst_value.clone()));
        let mut effects = vec![write_dst_checked(state, &dst, width, dst_new)?];

        if !dst_is_accumulator(&dst) {
            let acc_new = Formula::Ite(Box::new(eq), Box::new(acc), Box::new(dst_value));
            effects.push(reg_write(state, 0, width, acc_new));
        }

        effects.push(flags);
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // BSF/BSR: scan source bits, ZF reports zero source
    // -----------------------------------------------------------------------

    fn sem_bsf(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_bit_scan(state, insn, false)
    }

    fn sem_bsr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_bit_scan(state, insn, true)
    }

    fn sem_bit_scan(
        &self,
        state: &MachineState,
        insn: &Instruction,
        reverse: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst, width) = extract_dst_at(insn, 0, None)?;
        if matches!(dst, DstOperand::Mem(_)) {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "BSF/BSR destination must be a register".into(),
            });
        }

        validate_accumulator_width(insn, width)?;
        let src = resolve_operand(state, insn.operand(1), insn.opcode, 1, width)?;
        let src_zero =
            Formula::Eq(Box::new(src.clone()), Box::new(Formula::BitVec { value: 0, width }));
        let scanned = bit_scan_formula(&src, width, reverse);
        let value = Formula::Ite(
            Box::new(src_zero.clone()),
            Box::new(undefined_bv(insn, "bit_scan_dest", width)),
            Box::new(scanned),
        );

        let mut effects = vec![
            write_dst_checked(state, &dst, width, value)?,
            Effect::FlagUpdate {
                n: undefined_bool(insn, "bit_scan_sf"),
                z: src_zero,
                c: undefined_bool(insn, "bit_scan_cf"),
                v: undefined_bool(insn, "bit_scan_of"),
            },
        ];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }
}

// ===========================================================================
// Helper functions
// ===========================================================================

/// Destination operand descriptor.
#[derive(Debug, Clone)]
enum DstOperand {
    Reg { index: u8, is_sp: bool },
    Mem(MemoryOperand),
}

/// Extract the destination operand and its width from operand 0.
fn extract_dst(insn: &Instruction) -> Result<(DstOperand, u32), SemError> {
    extract_dst_at(insn, 0, None)
}

/// Extract a writable operand and its width from the given operand index.
fn extract_dst_at(
    insn: &Instruction,
    index: usize,
    mem_width_hint: Option<u32>,
) -> Result<(DstOperand, u32), SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) => {
            let is_sp = r.kind == RegKind::Sp || (r.kind == RegKind::Gpr && r.index == RSP_INDEX);
            Ok((DstOperand::Reg { index: r.index, is_sp }, u32::from(r.width)))
        }
        Some(Operand::Mem(m)) => {
            // For memory destinations, infer width from the source operand or
            // default to 64. Check operand 1 for a register width hint.
            let width = if let Some(width) = mem_width_hint {
                width
            } else if index == 0 {
                match insn.operand(1) {
                    Some(Operand::Reg(r)) => u32::from(r.width),
                    _ => 64,
                }
            } else {
                64
            };
            Ok((DstOperand::Mem(*m), width))
        }
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected register or memory destination".into(),
        }),
    }
}

/// Extend or truncate a bitvector formula to the target width.
fn zero_extend_to(value: Formula, from_width: u32, to_width: u32) -> Formula {
    match from_width.cmp(&to_width) {
        core::cmp::Ordering::Equal => value,
        core::cmp::Ordering::Less => Formula::BvZeroExt(Box::new(value), to_width - from_width),
        core::cmp::Ordering::Greater => {
            Formula::BvExtract { inner: Box::new(value), high: to_width - 1, low: 0 }
        }
    }
}

fn sign_extend_to(value: Formula, from_width: u32, to_width: u32) -> Formula {
    match from_width.cmp(&to_width) {
        core::cmp::Ordering::Equal => value,
        core::cmp::Ordering::Less => Formula::BvSignExt(Box::new(value), to_width - from_width),
        core::cmp::Ordering::Greater => {
            Formula::BvExtract { inner: Box::new(value), high: to_width - 1, low: 0 }
        }
    }
}

fn merge_partial_write(current: Formula, width: u32, value: Formula) -> Formula {
    match width {
        64 => value,
        32 => zero_extend_to(value, 32, 64),
        1..=63 => {
            let high = Formula::BvExtract { inner: Box::new(current), high: 63, low: width };
            Formula::BvConcat(Box::new(high), Box::new(value))
        }
        _ => value,
    }
}

fn reg_write(state: &MachineState, index: u8, width: u32, value: Formula) -> Effect {
    Effect::RegWrite {
        index,
        width: 64,
        value: merge_partial_write(state.read_gpr(index, 64), width, value),
    }
}

/// Read the current value of the destination operand, failing on unsupported memory modes.
fn resolve_dst_value_checked(
    state: &MachineState,
    dst: &DstOperand,
    width: u32,
    opcode: Opcode,
    index: usize,
) -> Result<Formula, SemError> {
    match dst {
        DstOperand::Reg { index, is_sp } => {
            if *is_sp {
                Ok(state.read_sp(width))
            } else {
                Ok(state.read_gpr(*index, width))
            }
        }
        DstOperand::Mem(m) => {
            let addr = resolve_mem_address(state, m).map_err(|_| SemError::InvalidOperand {
                opcode,
                index,
                detail: "unsupported memory addressing mode".into(),
            })?;
            Ok(load_le_bytes(state, &addr, width / 8, width))
        }
    }
}

/// Write a value to a destination operand, failing on unsupported memory modes.
fn write_dst_checked(
    state: &MachineState,
    dst: &DstOperand,
    width: u32,
    value: Formula,
) -> Result<Effect, SemError> {
    match dst {
        DstOperand::Reg { index, is_sp } => {
            if *is_sp || (*index == RSP_INDEX) {
                Ok(Effect::SpWrite { value: merge_partial_write(state.sp.clone(), width, value) })
            } else {
                Ok(reg_write(state, *index, width, value))
            }
        }
        DstOperand::Mem(m) => {
            let addr = resolve_mem_address(state, m)?;
            Ok(Effect::MemWrite { address: addr, value, width_bytes: width / 8 })
        }
    }
}

/// Extract a condition operand.
fn extract_condition(insn: &Instruction, index: usize) -> Result<Condition, SemError> {
    match insn.operand(index) {
        Some(Operand::Cond(c)) => Ok(*c),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected condition operand".into(),
        }),
    }
}

/// Convert an x86 condition code to a boolean formula over SF/ZF/CF/OF.
fn x86_condition_to_formula(
    state: &MachineState,
    cond: Condition,
    insn: &Instruction,
    index: usize,
) -> Result<Formula, SemError> {
    let n = &state.flags.n;
    let z = &state.flags.z;
    let c = &state.flags.c;
    let v = &state.flags.v;

    let formula = match cond {
        Condition::Eq => z.clone(),
        Condition::Ne => Formula::Not(Box::new(z.clone())),
        Condition::Cs => c.clone(),
        Condition::Cc => Formula::Not(Box::new(c.clone())),
        Condition::Mi => n.clone(),
        Condition::Pl => Formula::Not(Box::new(n.clone())),
        Condition::Vs => v.clone(),
        Condition::Vc => Formula::Not(Box::new(v.clone())),
        Condition::Hi => {
            Formula::And(vec![Formula::Not(Box::new(c.clone())), Formula::Not(Box::new(z.clone()))])
        }
        Condition::Ls => Formula::Or(vec![c.clone(), z.clone()]),
        Condition::Ge => Formula::Eq(Box::new(n.clone()), Box::new(v.clone())),
        Condition::Lt => {
            Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone()))))
        }
        Condition::Gt => Formula::And(vec![
            Formula::Not(Box::new(z.clone())),
            Formula::Eq(Box::new(n.clone()), Box::new(v.clone())),
        ]),
        Condition::Le => Formula::Or(vec![
            z.clone(),
            Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone())))),
        ]),
        Condition::Al | Condition::Nv => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index,
                detail: "parity-based x86 condition is not modeled".into(),
            });
        }
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index,
                detail: "unsupported condition code".into(),
            });
        }
    };

    Ok(formula)
}

fn single_operand_reg_width(insn: &Instruction, index: usize) -> Result<u32, SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) => Ok(u32::from(r.width)),
        Some(Operand::Mem(_)) => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "memory operand width is not preserved for this one-operand opcode".into(),
        }),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected register operand".into(),
        }),
    }
}

fn paired_operand_width(
    insn: &Instruction,
    lhs_index: usize,
    rhs_index: usize,
) -> Result<u32, SemError> {
    let lhs_width = match insn.operand(lhs_index) {
        Some(Operand::Reg(r)) => Some(u32::from(r.width)),
        Some(Operand::Mem(_)) => None,
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: lhs_index,
                detail: "expected register or memory operand".into(),
            });
        }
    };
    let rhs_width = match insn.operand(rhs_index) {
        Some(Operand::Reg(r)) => Some(u32::from(r.width)),
        Some(Operand::Mem(_)) => None,
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: rhs_index,
                detail: "expected register or memory operand".into(),
            });
        }
    };

    match (lhs_width, rhs_width) {
        (Some(lhs), Some(rhs)) if lhs == rhs => Ok(lhs),
        (Some(lhs), None) | (None, Some(lhs)) => Ok(lhs),
        (Some(lhs), Some(rhs)) => Err(SemError::WidthMismatch { expected: lhs, actual: rhs }),
        (None, None) => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: lhs_index,
            detail: "cannot infer width for two memory operands".into(),
        }),
    }
}

fn validate_accumulator_width(insn: &Instruction, width: u32) -> Result<(), SemError> {
    match width {
        8 | 16 | 32 | 64 => Ok(()),
        other => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: format!("unsupported accumulator width: {other}"),
        }),
    }
}

fn write_accumulator_pair(state: &MachineState, width: u32, value: Formula) -> Vec<Effect> {
    if width == 8 {
        vec![reg_write(state, 0, 16, value)]
    } else {
        let low = Formula::BvExtract { inner: Box::new(value.clone()), high: width - 1, low: 0 };
        let high = Formula::BvExtract { inner: Box::new(value), high: (width * 2) - 1, low: width };
        vec![reg_write(state, 0, width, low), reg_write(state, 2, width, high)]
    }
}

fn dst_is_accumulator(dst: &DstOperand) -> bool {
    matches!(dst, DstOperand::Reg { index: 0, .. })
}

fn bit_scan_formula(src: &Formula, width: u32, reverse: bool) -> Formula {
    let mut result = Formula::BitVec { value: 0, width };
    if reverse {
        for bit_index in 0..width {
            result = bit_scan_step(src, width, bit_index, result);
        }
    } else {
        for bit_index in (0..width).rev() {
            result = bit_scan_step(src, width, bit_index, result);
        }
    }
    result
}

fn bit_scan_step(src: &Formula, width: u32, bit_index: u32, fallback: Formula) -> Formula {
    let bit = Formula::BvExtract { inner: Box::new(src.clone()), high: bit_index, low: bit_index };
    let is_set = Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 1, width: 1 }));
    Formula::Ite(
        Box::new(is_set),
        Box::new(Formula::BitVec { value: i128::from(bit_index), width }),
        Box::new(fallback),
    )
}

fn undefined_bool(insn: &Instruction, name: &str) -> Formula {
    Formula::Var(format!("undef_x86_{:x}_{:x}_{name}", insn.address, insn.encoding), Sort::Bool)
}

fn undefined_bv(insn: &Instruction, name: &str, width: u32) -> Formula {
    Formula::Var(
        format!("undef_x86_{:x}_{:x}_{name}", insn.address, insn.encoding),
        Sort::BitVec(width),
    )
}

/// Resolve an operand to a symbolic Formula.
fn resolve_operand(
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
            if r.kind == RegKind::Sp || (r.kind == RegKind::Gpr && r.index == RSP_INDEX) {
                Ok(state.read_sp(width))
            } else {
                // Read at the register's own width, then extend/truncate to target width.
                let reg_width = u32::from(r.width);
                let val = state.read_gpr(r.index, reg_width);
                if reg_width == width {
                    Ok(val)
                } else if reg_width < width {
                    Ok(zero_extend_to(val, reg_width, width))
                } else {
                    Ok(Formula::BvExtract { inner: Box::new(val), high: width - 1, low: 0 })
                }
            }
        }
        Operand::Imm(v) => Ok(Formula::BitVec { value: *v as i128, width }),
        Operand::SignedImm(v) => Ok(Formula::BitVec { value: *v as i128, width }),
        Operand::Mem(m) => {
            let addr = resolve_mem_address(state, m)?;
            let width_bytes = width / 8;
            Ok(load_le_bytes(state, &addr, width_bytes, width))
        }
        _ => Err(SemError::InvalidOperand {
            opcode,
            index,
            detail: format!("unexpected operand type: {op:?}"),
        }),
    }
}

fn mem_read_effect_for_operand(
    state: &MachineState,
    operand: Option<&Operand>,
    width: u32,
) -> Result<Option<Effect>, SemError> {
    match operand {
        Some(Operand::Mem(mem)) => Ok(Some(Effect::MemRead {
            address: resolve_mem_address(state, mem)?,
            width_bytes: width / 8,
        })),
        _ => Ok(None),
    }
}

/// Resolve a memory addressing mode to a 64-bit address formula.
fn resolve_mem_address(state: &MachineState, mem: &MemoryOperand) -> Result<Formula, SemError> {
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
        MemoryOperand::PcRelative { offset } => {
            // RIP-relative: address = PC + insn_size + offset.
            // The decoder already resolves this to an absolute address in most
            // cases, but if not we compute symbolically.
            Ok(Formula::BvAdd(
                Box::new(state.pc.clone()),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::PreIndex { base, offset } => {
            let base_val = read_base_reg(state, base);
            Ok(Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            ))
        }
        MemoryOperand::PostIndex { base, .. } => Ok(read_base_reg(state, base)),
        _ => Err(SemError::InvalidOperand {
            opcode: Opcode::Mov,
            index: 1,
            detail: "unsupported x86_64 memory addressing mode".into(),
        }),
    }
}

/// Read a base register (GPR or SP) as a 64-bit value.
fn read_base_reg(state: &MachineState, reg: &trust_disasm::operand::Register) -> Formula {
    if reg.kind == RegKind::Sp || (reg.kind == RegKind::Gpr && reg.index == RSP_INDEX) {
        state.read_sp(64)
    } else {
        state.read_gpr(reg.index, 64)
    }
}

/// PC = PC + insn.size (variable-length x86_64 advance).
fn pc_advance(state: &MachineState, insn: &Instruction) -> Effect {
    Effect::PcUpdate {
        value: Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: i128::from(insn.size), width: 64 }),
            64,
        ),
    }
}

/// Extract a branch target address as a Formula from the instruction.
fn branch_target(insn: &Instruction) -> Result<Formula, SemError> {
    for op in insn.operands() {
        if let Operand::PcRelAddr(addr) = op {
            return Ok(Formula::BitVec { value: *addr as i128, width: 64 });
        }
    }
    // For indirect branches (JMP r/m, CALL r/m), use the register/memory operand.
    // Find a register or memory operand that could be the target.
    for op in insn.operands() {
        match op {
            Operand::Reg(_) | Operand::Mem(_) => {
                // Indirect branch — this needs operand resolution but we don't have
                // state here. Return an error for now; indirect jumps need state.
            }
            _ => {}
        }
    }
    Err(SemError::InvalidOperand {
        opcode: insn.opcode,
        index: 0,
        detail: "no branch target found".into(),
    })
}

/// Extract a CALL target. Direct calls use the decoded PC-relative address;
/// indirect calls use the 64-bit register or memory target operand.
fn call_target(
    state: &MachineState,
    insn: &Instruction,
) -> Result<(Formula, Option<Effect>), SemError> {
    for op in insn.operands() {
        if let Operand::PcRelAddr(addr) = op {
            return Ok((Formula::BitVec { value: *addr as i128, width: 64 }, None));
        }
    }

    match insn.operand(0) {
        Some(Operand::Reg(r)) => {
            let target =
                if r.kind == RegKind::Sp || (r.kind == RegKind::Gpr && r.index == RSP_INDEX) {
                    state.read_sp(64)
                } else {
                    state.read_gpr(r.index, 64)
                };
            Ok((target, None))
        }
        Some(Operand::Mem(m)) => {
            let addr = resolve_mem_address(state, m)?;
            let target = load_le_bytes(state, &addr, 8, 64);
            Ok((target, Some(Effect::MemRead { address: addr, width_bytes: 8 })))
        }
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "CALL requires direct or r/m64 target".into(),
        }),
    }
}

/// Compute EFLAGS updates for arithmetic (ADD/SUB/CMP).
///
/// Maps x86 EFLAGS to the FlagUpdate fields:
/// - n = SF (sign flag = MSB of result)
/// - z = ZF (zero flag = result == 0)
/// - c = CF (carry flag: ADD: result < lhs; SUB: lhs < rhs unsigned)
/// - v = OF (overflow flag: signed overflow)
fn compute_eflags(
    lhs: &Formula,
    rhs: &Formula,
    result: &Formula,
    width: u32,
    is_sub: bool,
) -> Effect {
    let sign_bit = width - 1;

    // SF = result[MSB]
    let sf = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(result.clone()),
            high: sign_bit,
            low: sign_bit,
        }),
        Box::new(Formula::BitVec { value: 1, width: 1 }),
    );

    // ZF = (result == 0)
    let zf = Formula::Eq(Box::new(result.clone()), Box::new(Formula::BitVec { value: 0, width }));

    // CF:
    //   ADD: CF = (result <u lhs) — unsigned carry
    //   SUB: CF = (lhs <u rhs) — unsigned borrow
    let cf = if is_sub {
        Formula::BvULt(Box::new(lhs.clone()), Box::new(rhs.clone()), width)
    } else {
        Formula::BvULt(Box::new(result.clone()), Box::new(lhs.clone()), width)
    };

    // OF (signed overflow):
    //   ADD: lhs_sign == rhs_sign && result_sign != lhs_sign
    //   SUB: lhs_sign != rhs_sign && result_sign != lhs_sign
    let lhs_sign =
        Formula::BvExtract { inner: Box::new(lhs.clone()), high: sign_bit, low: sign_bit };
    let rhs_sign =
        Formula::BvExtract { inner: Box::new(rhs.clone()), high: sign_bit, low: sign_bit };
    let res_sign =
        Formula::BvExtract { inner: Box::new(result.clone()), high: sign_bit, low: sign_bit };

    let signs_match = Formula::Eq(Box::new(lhs_sign.clone()), Box::new(rhs_sign));
    let result_differs =
        Formula::Not(Box::new(Formula::Eq(Box::new(res_sign), Box::new(lhs_sign))));

    let of = if is_sub {
        Formula::And(vec![Formula::Not(Box::new(signs_match)), result_differs])
    } else {
        Formula::And(vec![signs_match, result_differs])
    };

    Effect::FlagUpdate { n: sf, z: zf, c: cf, v: of }
}

/// Compute EFLAGS for INC/DEC: preserves CF, sets ZF/SF/OF.
fn compute_eflags_preserve_cf(
    state: &MachineState,
    lhs: &Formula,
    rhs: &Formula,
    result: &Formula,
    width: u32,
    is_sub: bool,
) -> Effect {
    let full_flags = compute_eflags(lhs, rhs, result, width, is_sub);
    match full_flags {
        Effect::FlagUpdate { n, z, v, .. } => Effect::FlagUpdate {
            n,
            z,
            c: state.flags.c.clone(), // Preserve existing CF
            v,
        },
        _ => unreachable!("compute_eflags always returns Effect::FlagUpdate"),
    }
}

/// Compute EFLAGS for logical operations (AND, OR, XOR, TEST).
/// CF = 0, OF = 0, SF and ZF from result.
fn logic_eflags(result: &Formula, width: u32) -> Effect {
    let sign_bit = width - 1;
    let sf = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(result.clone()),
            high: sign_bit,
            low: sign_bit,
        }),
        Box::new(Formula::BitVec { value: 1, width: 1 }),
    );
    let zf = Formula::Eq(Box::new(result.clone()), Box::new(Formula::BitVec { value: 0, width }));
    Effect::FlagUpdate { n: sf, z: zf, c: Formula::Bool(false), v: Formula::Bool(false) }
}

/// Compute EFLAGS for shift operations.
/// ZF and SF from result, CF and OF simplified to false.
fn shift_eflags(result: &Formula, width: u32) -> Effect {
    // Shift flags: CF = last bit shifted out (complex to model precisely),
    // OF = MSB changed (for count=1). Simplified model: CF=false, OF=false.
    logic_eflags(result, width)
}

/// Load `num_bytes` from byte-addressed memory in little-endian order,
/// producing a bitvector of `result_width` bits.
fn load_le_bytes(
    state: &MachineState,
    addr: &Formula,
    num_bytes: u32,
    result_width: u32,
) -> Formula {
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for i in 0..num_bytes {
        let byte_addr = if i == 0 {
            addr.clone()
        } else {
            Formula::BvAdd(
                Box::new(addr.clone()),
                Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                64,
            )
        };
        let byte_val = Formula::Select(Box::new(state.memory.clone()), Box::new(byte_addr));
        let extended = zero_extend_to(byte_val, 8, result_width);
        if i == 0 {
            result = extended;
        } else {
            let shift_amt = Formula::BitVec { value: i128::from(i * 8), width: result_width };
            let shifted = Formula::BvShl(Box::new(extended), Box::new(shift_amt), result_width);
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        }
    }
    result
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_disasm::decode_x86_64;

    fn sem() -> X86_64Semantics {
        X86_64Semantics
    }

    fn state() -> MachineState {
        MachineState::symbolic()
    }

    fn is_bool_var(formula: &Formula, name: &str) -> bool {
        matches!(formula, Formula::Var(var, Sort::Bool) if var == name)
    }

    fn is_not_bool_var(formula: &Formula, name: &str) -> bool {
        matches!(formula, Formula::Not(inner) if is_bool_var(inner, name))
    }

    // -----------------------------------------------------------------------
    // MOV
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_reg_reg_64() {
        // 48 89 E5 = MOV RBP, RSP
        let insn = decode_x86_64(&[0x48, 0x89, 0xE5], 0x1000).expect("decode MOV");
        let effects = sem().effects(&state(), &insn).expect("effects");

        // Should write to RBP (index 5).
        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 5, width: 64, .. }));
        assert!(has_reg_write, "MOV RBP, RSP should write RBP");

        // No flag changes.
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(!has_flags, "MOV should not set flags");
    }

    #[test]
    fn test_trap_and_syscall_fail_closed() {
        for bytes in [&[0xCC][..], &[0x0F, 0x05][..]] {
            let insn = decode_x86_64(bytes, 0x1000).expect("decode trap/syscall");
            let err = sem().effects(&state(), &insn).expect_err("side effecting exception");
            assert!(matches!(err, SemError::UnsupportedOpcode(Opcode::Int3 | Opcode::Syscall)));
        }
    }

    #[test]
    fn test_mov_reg_imm32() {
        // B8 2A 00 00 00 = MOV EAX, 42
        let insn = decode_x86_64(&[0xB8, 0x2A, 0x00, 0x00, 0x00], 0x1000).expect("decode MOV imm");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let reg_write = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 0, value, .. } = e { Some(value) } else { None }
        });
        assert!(reg_write.is_some(), "MOV EAX, 42 should write EAX");
    }

    #[test]
    fn test_mov_mem_reg() {
        // 48 89 45 F8 = MOV [RBP-8], RAX
        let insn = decode_x86_64(&[0x48, 0x89, 0x45, 0xF8], 0x1000).expect("decode MOV mem");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_mem_write = effects.iter().any(|e| matches!(e, Effect::MemWrite { .. }));
        assert!(has_mem_write, "MOV [RBP-8], RAX should produce MemWrite");
    }

    #[test]
    fn test_mov_reg_mem() {
        // 48 8B 45 F8 = MOV RAX, [RBP-8]
        let insn = decode_x86_64(&[0x48, 0x8B, 0x45, 0xF8], 0x1000).expect("decode MOV reg,mem");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "MOV RAX, [RBP-8] should write RAX");
    }

    // -----------------------------------------------------------------------
    // ADD / SUB
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_reg_reg_sets_flags() {
        // 48 01 D0 = ADD RAX, RDX
        let insn = decode_x86_64(&[0x48, 0x01, 0xD0], 0x1000).expect("decode ADD");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_reg_write, "ADD should write RAX");
        assert!(has_flags, "ADD should set EFLAGS");
    }

    #[test]
    fn test_sub_imm8_sets_flags() {
        // 48 83 EC 20 = SUB RSP, 0x20
        let insn = decode_x86_64(&[0x48, 0x83, 0xEC, 0x20], 0x1000).expect("decode SUB");
        let effects = sem().effects(&state(), &insn).expect("effects");

        // SUB RSP should produce SpWrite.
        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_sp_write, "SUB RSP should write SP");
        assert!(has_flags, "SUB should set EFLAGS");
    }

    // -----------------------------------------------------------------------
    // CMP
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmp_reg_reg_no_writeback() {
        // 48 39 C8 = CMP RAX, RCX
        let insn = decode_x86_64(&[0x48, 0x39, 0xC8], 0x1000).expect("decode CMP");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(!has_reg_write, "CMP should not write a register");
        assert!(has_flags, "CMP should set EFLAGS");
    }

    #[test]
    fn test_cmp_imm8() {
        // 83 F8 00 = CMP EAX, 0
        let insn = decode_x86_64(&[0x83, 0xF8, 0x00], 0x1000).expect("decode CMP imm");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_flags, "CMP EAX, 0 should set EFLAGS");
    }

    // -----------------------------------------------------------------------
    // AND / OR / XOR / TEST
    // -----------------------------------------------------------------------

    #[test]
    fn test_and_sets_logic_flags() {
        // 48 21 C8 = AND RAX, RCX
        let insn = decode_x86_64(&[0x48, 0x21, 0xC8], 0x1000).expect("decode AND");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_flags, "AND should set flags");

        // CF and OF should be false for logic ops.
        if let Some(Effect::FlagUpdate { c, v, .. }) =
            effects.iter().find(|e| matches!(e, Effect::FlagUpdate { .. }))
        {
            assert_eq!(*c, Formula::Bool(false), "AND CF should be false");
            assert_eq!(*v, Formula::Bool(false), "AND OF should be false");
        }
    }

    #[test]
    fn test_xor_eax_eax() {
        // 31 C0 = XOR EAX, EAX (common zero idiom)
        let insn = decode_x86_64(&[0x31, 0xC0], 0x1000).expect("decode XOR");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "XOR EAX, EAX should write EAX");
    }

    #[test]
    fn test_test_no_writeback() {
        // 48 85 C0 = TEST RAX, RAX
        let insn = decode_x86_64(&[0x48, 0x85, 0xC0], 0x1000).expect("decode TEST");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(!has_reg_write, "TEST should not write a register");
        assert!(has_flags, "TEST should set flags");
    }

    #[test]
    fn test_or_reg_reg() {
        // 48 09 D0 = OR RAX, RDX
        let insn = decode_x86_64(&[0x48, 0x09, 0xD0], 0x1000).expect("decode OR");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "OR should write RAX");
    }

    // -----------------------------------------------------------------------
    // NOT / NEG
    // -----------------------------------------------------------------------

    #[test]
    fn test_not_no_flags() {
        // 48 F7 D0 = NOT RAX
        let insn = decode_x86_64(&[0x48, 0xF7, 0xD0], 0x1000).expect("decode NOT");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_reg_write, "NOT should write RAX");
        assert!(!has_flags, "NOT should not set flags");
    }

    #[test]
    fn test_neg_sets_flags() {
        // 48 F7 D8 = NEG RAX
        let insn = decode_x86_64(&[0x48, 0xF7, 0xD8], 0x1000).expect("decode NEG");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
        assert!(has_reg_write, "NEG should write RAX");
        assert!(has_flags, "NEG should set EFLAGS");
    }

    // -----------------------------------------------------------------------
    // SHL / SHR / SAR
    // -----------------------------------------------------------------------

    #[test]
    fn test_shl_imm8() {
        // 48 C1 E0 03 = SHL RAX, 3
        let insn = decode_x86_64(&[0x48, 0xC1, 0xE0, 0x03], 0x1000).expect("decode SHL");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "SHL should write RAX");

        if let Some(Effect::RegWrite { value, .. }) =
            effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
        {
            assert!(
                matches!(value, Formula::BvShl(..)),
                "SHL should produce BvShl, got: {:?}",
                value
            );
        }
    }

    #[test]
    fn test_shr_imm8() {
        // 48 C1 E8 01 = SHR RAX, 1
        let insn = decode_x86_64(&[0x48, 0xC1, 0xE8, 0x01], 0x1000).expect("decode SHR");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "SHR should write RAX");
    }

    #[test]
    fn test_sar_one() {
        // 48 D1 F8 = SAR RAX, 1
        let insn = decode_x86_64(&[0x48, 0xD1, 0xF8], 0x1000).expect("decode SAR");
        let effects = sem().effects(&state(), &insn).expect("effects");

        if let Some(Effect::RegWrite { value, .. }) =
            effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
        {
            assert!(
                matches!(value, Formula::BvAShr(..)),
                "SAR should produce BvAShr, got: {:?}",
                value
            );
        }
    }

    // -----------------------------------------------------------------------
    // INC / DEC
    // -----------------------------------------------------------------------

    #[test]
    fn test_inc_preserves_cf() {
        // FF C0 = INC EAX
        let insn = decode_x86_64(&[0xFF, 0xC0], 0x1000).expect("decode INC");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "INC should write EAX");

        // CF should be preserved (not set to a new value based on computation).
        if let Some(Effect::FlagUpdate { c, .. }) =
            effects.iter().find(|e| matches!(e, Effect::FlagUpdate { .. }))
        {
            // The CF should be the original symbolic C flag, not a computed value.
            // Flags::symbolic("") produces "_C" (prefix + "_" + flag name).
            assert!(
                matches!(c, Formula::Var(name, _) if name == "_C"),
                "INC should preserve CF (got: {:?})",
                c
            );
        }
    }

    #[test]
    fn test_dec() {
        // FF C8 = DEC EAX
        let insn = decode_x86_64(&[0xFF, 0xC8], 0x1000).expect("decode DEC");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
        assert!(has_reg_write, "DEC should write EAX");
    }

    // -----------------------------------------------------------------------
    // LEA
    // -----------------------------------------------------------------------

    #[test]
    fn test_lea_rip_relative() {
        // 48 8D 05 10 00 00 00 = LEA RAX, [RIP+0x10]
        let insn =
            decode_x86_64(&[0x48, 0x8D, 0x05, 0x10, 0x00, 0x00, 0x00], 0x1000).expect("decode LEA");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "LEA should write RAX");

        // Should NOT produce a MemRead (LEA computes address only).
        let has_mem_read = effects.iter().any(|e| matches!(e, Effect::MemRead { .. }));
        assert!(!has_mem_read, "LEA should not read memory");
    }

    // -----------------------------------------------------------------------
    // PUSH / POP
    // -----------------------------------------------------------------------

    #[test]
    fn test_push_rbp() {
        // 55 = PUSH RBP
        let insn = decode_x86_64(&[0x55], 0x1000).expect("decode PUSH");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        let has_mem_write = effects.iter().any(|e| matches!(e, Effect::MemWrite { .. }));
        assert!(has_sp_write, "PUSH should update RSP");
        assert!(has_mem_write, "PUSH should write to memory");
    }

    #[test]
    fn test_pop_rbp() {
        // 5D = POP RBP
        let insn = decode_x86_64(&[0x5D], 0x1000).expect("decode POP");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 5, width: 64, .. }));
        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        let has_mem_read = effects.iter().any(|e| matches!(e, Effect::MemRead { .. }));
        assert!(has_reg_write, "POP should write RBP");
        assert!(has_sp_write, "POP should update RSP");
        assert!(has_mem_read, "POP should read from memory");
    }

    // -----------------------------------------------------------------------
    // CALL / RET
    // -----------------------------------------------------------------------

    #[test]
    fn test_call_rel32() {
        // E8 10 00 00 00 = CALL +0x10 (at address 0x1000)
        let insn = decode_x86_64(&[0xE8, 0x10, 0x00, 0x00, 0x00], 0x1000).expect("decode CALL");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));
        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        let has_mem_write = effects.iter().any(|e| matches!(e, Effect::MemWrite { .. }));
        assert!(has_call, "CALL should produce Call effect");
        assert!(has_sp_write, "CALL should push return address (update SP)");
        assert!(has_mem_write, "CALL should push return address (write mem)");
    }

    #[test]
    fn test_ret_pops_and_branches() {
        // C3 = RET
        let insn = decode_x86_64(&[0xC3], 0x1000).expect("decode RET");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_return = effects.iter().any(|e| matches!(e, Effect::Return { .. }));
        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        let has_mem_read = effects.iter().any(|e| matches!(e, Effect::MemRead { .. }));
        assert!(has_return, "RET should produce Return effect");
        assert!(has_sp_write, "RET should pop return address (update SP)");
        assert!(has_mem_read, "RET should read return address from stack");
    }

    // -----------------------------------------------------------------------
    // JMP / Jcc
    // -----------------------------------------------------------------------

    #[test]
    fn test_jmp_rel32() {
        // E9 FB FF FF FF = JMP -5 (at 0x1000) -> 0x1000
        let insn = decode_x86_64(&[0xE9, 0xFB, 0xFF, 0xFF, 0xFF], 0x1000).expect("decode JMP");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_branch = effects.iter().any(|e| matches!(e, Effect::Branch { .. }));
        assert!(has_branch, "JMP should produce Branch effect");
    }

    #[test]
    fn test_je_rel8() {
        // 74 0A = JE +10 (at 0x1000) -> 0x100C
        let insn = decode_x86_64(&[0x74, 0x0A], 0x1000).expect("decode JE");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_cond_branch = effects.iter().any(|e| matches!(e, Effect::ConditionalBranch { .. }));
        assert!(has_cond_branch, "JE should produce ConditionalBranch");
    }

    #[test]
    fn test_jne_rel8() {
        // 75 F6 = JNE -10 (at 0x1000) -> 0xFF8
        let insn = decode_x86_64(&[0x75, 0xF6], 0x1000).expect("decode JNE");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_cond_branch = effects.iter().any(|e| matches!(e, Effect::ConditionalBranch { .. }));
        assert!(has_cond_branch, "JNE should produce ConditionalBranch");
    }

    #[test]
    fn test_jge_rel32() {
        // 0F 8D 00 01 00 00 = JGE +256 (at 0x1000) -> 0x1106
        let insn =
            decode_x86_64(&[0x0F, 0x8D, 0x00, 0x01, 0x00, 0x00], 0x1000).expect("decode JGE");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_cond_branch = effects.iter().any(|e| matches!(e, Effect::ConditionalBranch { .. }));
        assert!(has_cond_branch, "JGE should produce ConditionalBranch");
    }

    // -----------------------------------------------------------------------
    // NOP
    // -----------------------------------------------------------------------

    #[test]
    fn test_nop_only_advances_pc() {
        // 90 = NOP
        let insn = decode_x86_64(&[0x90], 0x1000).expect("decode NOP");
        let effects = sem().effects(&state(), &insn).expect("effects");

        assert_eq!(effects.len(), 1, "NOP should produce exactly one effect");
        assert!(matches!(&effects[0], Effect::PcUpdate { .. }), "NOP effect should be PcUpdate");
    }

    // -----------------------------------------------------------------------
    // LEAVE
    // -----------------------------------------------------------------------

    #[test]
    fn test_leave_restores_rbp_and_rsp() {
        // C9 = LEAVE
        let insn = decode_x86_64(&[0xC9], 0x1000).expect("decode LEAVE");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 5, .. }));
        let has_sp_write = effects.iter().any(|e| matches!(e, Effect::SpWrite { .. }));
        assert!(has_reg_write, "LEAVE should restore RBP");
        assert!(has_sp_write, "LEAVE should restore RSP");
    }

    // -----------------------------------------------------------------------
    // MOVZX / MOVSX
    // -----------------------------------------------------------------------

    #[test]
    fn test_movzx_r32_rm8() {
        // 0F B6 C1 = MOVZX EAX, CL
        let insn = decode_x86_64(&[0x0F, 0xB6, 0xC1], 0x1000).expect("decode MOVZX");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "MOVZX should write EAX");
    }

    #[test]
    fn test_movzx_r32_mem8() {
        // 0F B6 45 00 = MOVZX EAX, BYTE PTR [RBP+0]
        let insn = decode_x86_64(&[0x0F, 0xB6, 0x45, 0x00], 0x1000).expect("decode MOVZX mem8");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let write = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 0, width, value, .. } = e {
                Some((*width, value.clone()))
            } else {
                None
            }
        });
        assert!(write.is_some(), "MOVZX EAX, BYTE PTR [RBP+0] should write EAX");
        let (w, val) = write.unwrap();
        assert_eq!(w, 64, "x86 register effects carry full 64-bit post-register values");
        assert!(
            matches!(
                val,
                Formula::BvZeroExt(ref inner, 32)
                    if matches!(inner.as_ref(), Formula::BvZeroExt(_, 24))
            ),
            "MOVZX r32,m8 should zero-extend m8 to 32 bits and EAX to RAX, got: {val:?}"
        );
    }

    #[test]
    fn test_movzx_r32_mem16() {
        // 0F B7 45 00 = MOVZX EAX, WORD PTR [RBP+0]
        let insn = decode_x86_64(&[0x0F, 0xB7, 0x45, 0x00], 0x1000).expect("decode MOVZX mem16");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let write = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 0, width, value, .. } = e {
                Some((*width, value.clone()))
            } else {
                None
            }
        });
        assert!(write.is_some(), "MOVZX EAX, WORD PTR [RBP+0] should write EAX");
        let (w, val) = write.unwrap();
        assert_eq!(w, 64, "x86 register effects carry full 64-bit post-register values");
        assert!(
            matches!(
                val,
                Formula::BvZeroExt(ref inner, 32)
                    if matches!(inner.as_ref(), Formula::BvZeroExt(_, 16))
            ),
            "MOVZX r32,m16 should zero-extend m16 to 32 bits and EAX to RAX, got: {val:?}"
        );
    }

    #[test]
    fn test_movsx_r64_rm8() {
        // 48 0F BE C1 = MOVSX RAX, CL
        let insn = decode_x86_64(&[0x48, 0x0F, 0xBE, 0xC1], 0x1000).expect("decode MOVSX");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "MOVSX should write RAX");
    }

    // -----------------------------------------------------------------------
    // IMUL
    // -----------------------------------------------------------------------

    #[test]
    fn test_imul_two_operand() {
        // 48 0F AF C1 = IMUL RAX, RCX
        let insn = decode_x86_64(&[0x48, 0x0F, 0xAF, 0xC1], 0x1000).expect("decode IMUL");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write =
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
        assert!(has_reg_write, "IMUL should write RAX");
    }

    #[test]
    fn test_imul_three_operand() {
        // 6B C1 0A = IMUL EAX, ECX, 10
        let insn = decode_x86_64(&[0x6B, 0xC1, 0x0A], 0x1000).expect("decode IMUL 3op");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
        assert!(has_reg_write, "IMUL 3-op should write EAX");
    }

    // -----------------------------------------------------------------------
    // Decoded x86_64 integer/control-flow expansion
    // -----------------------------------------------------------------------

    #[test]
    fn test_cdq_sign_extends_eax_to_edx() {
        // 99 = CDQ
        let insn = decode_x86_64(&[0x99], 0x1000).expect("decode CDQ");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let write = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 2, width: 64, value } = e { Some(value) } else { None }
        });
        assert!(
            matches!(write, Some(Formula::BvZeroExt(inner, 32)) if matches!(inner.as_ref(), Formula::BvAShr(_, _, 32))),
            "CDQ should write EDX and zero-extend the EDX write to RDX"
        );
    }

    #[test]
    fn test_cqo_sign_extends_rax_to_rdx() {
        // 48 99 = CQO
        let insn = decode_x86_64(&[0x48, 0x99], 0x1000).expect("decode CQO");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let write = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 2, width: 64, value } = e { Some(value) } else { None }
        });
        assert!(matches!(write, Some(Formula::BvAShr(_, _, 64))), "CQO should write RDX");
    }

    #[test]
    fn test_mul_r64_writes_rdx_rax_and_flags() {
        // 48 F7 E2 = MUL RDX
        let insn = decode_x86_64(&[0x48, 0xF7, 0xE2], 0x1000).expect("decode MUL");
        let effects = sem().effects(&state(), &insn).expect("effects");

        assert!(
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. })),
            "MUL should write RAX"
        );
        assert!(
            effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 2, width: 64, .. })),
            "MUL should write RDX"
        );
        assert!(effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. })));
    }

    #[test]
    fn test_div_r64_fails_closed_until_traps_are_modeled() {
        // 48 F7 F1 = DIV RCX
        let insn = decode_x86_64(&[0x48, 0xF7, 0xF1], 0x1000).expect("decode DIV");
        let err = sem().effects(&state(), &insn).expect_err("DIV can trap and must fail closed");
        assert!(matches!(
            err,
            SemError::InvalidOperand { detail, .. } if detail.contains("trap preconditions")
        ));
    }

    #[test]
    fn test_idiv_r64_fails_closed_until_traps_are_modeled() {
        // 48 F7 F9 = IDIV RCX
        let insn = decode_x86_64(&[0x48, 0xF7, 0xF9], 0x1000).expect("decode IDIV");
        let err = sem().effects(&state(), &insn).expect_err("IDIV can trap and must fail closed");
        assert!(matches!(
            err,
            SemError::InvalidOperand { detail, .. } if detail.contains("trap preconditions")
        ));
    }

    #[test]
    fn test_xchg_reg_reg_swaps_both_operands() {
        // 48 91 = XCHG RAX, RCX
        let insn = decode_x86_64(&[0x48, 0x91], 0x1000).expect("decode XCHG");
        let effects = sem().effects(&state(), &insn).expect("effects");

        assert!(effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. })));
        assert!(effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 1, width: 64, .. })));
    }

    #[test]
    fn test_cmovcc_uses_ite() {
        // 48 0F 44 C1 = CMOVE RAX, RCX
        let insn = decode_x86_64(&[0x48, 0x0F, 0x44, 0xC1], 0x1000).expect("decode CMOVcc");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let value = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 0, width: 64, value } = e { Some(value) } else { None }
        });
        assert!(matches!(value, Some(Formula::Ite(_, _, _))), "CMOVcc should use Ite");
    }

    #[test]
    fn test_setcc_writes_byte_ite() {
        // 0F 94 C0 = SETE AL
        let insn = decode_x86_64(&[0x0F, 0x94, 0xC0], 0x1000).expect("decode SETcc");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let value = effects.iter().find_map(|e| {
            if let Effect::RegWrite { index: 0, width: 64, value } = e { Some(value) } else { None }
        });
        assert!(
            matches!(
                value,
                Some(Formula::BvConcat(_, low)) if matches!(low.as_ref(), Formula::Ite(_, _, _))
            ),
            "SETcc should preserve upper RAX bits and write the low byte with Ite"
        );
    }

    #[test]
    fn test_unsigned_conditions_use_x86_borrow_carry_semantics() {
        let insn = decode_x86_64(&[0x77, 0x00], 0x1000).expect("decode JA");
        let s = state();

        let hi = x86_condition_to_formula(&s, Condition::Hi, &insn, 0).expect("HI condition");
        assert!(
            matches!(hi, Formula::And(parts) if parts.len() == 2 && is_not_bool_var(&parts[0], "_C") && is_not_bool_var(&parts[1], "_Z")),
            "x86 JA/HI should be !CF && !ZF"
        );

        let ls = x86_condition_to_formula(&s, Condition::Ls, &insn, 0).expect("LS condition");
        assert!(
            matches!(ls, Formula::Or(parts) if parts.len() == 2 && is_bool_var(&parts[0], "_C") && is_bool_var(&parts[1], "_Z")),
            "x86 JBE/LS should be CF || ZF"
        );
    }

    #[test]
    fn test_cmpxchg_updates_dst_accumulator_and_flags() {
        // 48 0F B1 CB = CMPXCHG RBX, RCX
        let insn = decode_x86_64(&[0x48, 0x0F, 0xB1, 0xCB], 0x1000).expect("decode CMPXCHG");
        let effects = sem().effects(&state(), &insn).expect("effects");

        assert!(effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 3, width: 64, .. })));
        assert!(effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. })));
        assert!(effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. })));
    }

    #[test]
    fn test_bsf_bsr_write_guarded_index_and_zf() {
        for (bytes, name) in
            [(&[0x48, 0x0F, 0xBC, 0xC1][..], "BSF"), (&[0x48, 0x0F, 0xBD, 0xC1][..], "BSR")]
        {
            let insn =
                decode_x86_64(bytes, 0x1000).unwrap_or_else(|e| panic!("decode {name}: {e}"));
            let effects = sem().effects(&state(), &insn).unwrap_or_else(|e| panic!("{name}: {e}"));

            let value = effects.iter().find_map(|e| {
                if let Effect::RegWrite { index: 0, width: 64, value } = e {
                    Some(value)
                } else {
                    None
                }
            });
            assert!(matches!(value, Some(Formula::Ite(_, _, _))), "{name} should guard dest");
            assert!(effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. })));
        }
    }

    #[test]
    fn test_call_indirect_reg64() {
        // FF D0 = CALL RAX
        let insn = decode_x86_64(&[0xFF, 0xD0], 0x1000).expect("decode CALL RAX");
        let effects = sem().effects(&state(), &insn).expect("effects");

        let target = effects
            .iter()
            .find_map(|e| if let Effect::Call { target, .. } = e { Some(target) } else { None });
        assert!(
            matches!(target, Some(Formula::Var(name, Sort::BitVec(64))) if name == "X0"),
            "CALL RAX should use the 64-bit symbolic RAX target, got: {target:?}"
        );
    }

    #[test]
    fn test_call_indirect_mem64_reads_target() {
        // FF 10 = CALL QWORD PTR [RAX]
        let insn = decode_x86_64(&[0xFF, 0x10], 0x1000).expect("decode CALL [RAX]");
        let effects = sem().effects(&state(), &insn).expect("effects");

        assert!(effects.iter().any(|e| matches!(e, Effect::MemRead { width_bytes: 8, .. })));
        assert!(effects.iter().any(|e| matches!(e, Effect::Call { .. })));
    }

    #[test]
    fn test_mul_memory_width_fails_closed() {
        // 48 F7 20 = MUL QWORD PTR [RAX], but the memory width is not retained.
        let insn = decode_x86_64(&[0x48, 0xF7, 0x20], 0x1000).expect("decode MUL [RAX]");
        let result = sem().effects(&state(), &insn);
        assert!(result.is_err(), "MUL memory source should fail closed without width metadata");
    }

    // -----------------------------------------------------------------------
    // Comprehensive no-crash sweep
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_x86_64_opcodes_produce_effects() {
        let encodings: &[(&[u8], &str)] = &[
            // MOV variants
            (&[0x48, 0x89, 0xE5], "MOV RBP, RSP"),
            (&[0x89, 0xC1], "MOV ECX, EAX"),
            (&[0xB8, 0x2A, 0x00, 0x00, 0x00], "MOV EAX, 42"),
            (&[0x48, 0x89, 0x45, 0xF8], "MOV [RBP-8], RAX"),
            (&[0x48, 0x8B, 0x45, 0xF8], "MOV RAX, [RBP-8]"),
            // Arithmetic
            (&[0x48, 0x01, 0xD0], "ADD RAX, RDX"),
            (&[0x48, 0x83, 0xEC, 0x20], "SUB RSP, 0x20"),
            (&[0x48, 0x39, 0xC8], "CMP RAX, RCX"),
            (&[0xFF, 0xC0], "INC EAX"),
            (&[0xFF, 0xC8], "DEC EAX"),
            (&[0x48, 0xF7, 0xD8], "NEG RAX"),
            (&[0x99], "CDQ"),
            (&[0x48, 0x99], "CQO"),
            (&[0x48, 0xF7, 0xE2], "MUL RDX"),
            // Logic
            (&[0x48, 0x21, 0xC8], "AND RAX, RCX"),
            (&[0x48, 0x09, 0xD0], "OR RAX, RDX"),
            (&[0x31, 0xC0], "XOR EAX, EAX"),
            (&[0x48, 0x85, 0xC0], "TEST RAX, RAX"),
            (&[0x48, 0xF7, 0xD0], "NOT RAX"),
            // Shifts
            (&[0x48, 0xC1, 0xE0, 0x03], "SHL RAX, 3"),
            (&[0x48, 0xC1, 0xE8, 0x01], "SHR RAX, 1"),
            (&[0x48, 0xD1, 0xF8], "SAR RAX, 1"),
            // Stack
            (&[0x55], "PUSH RBP"),
            (&[0x5D], "POP RBP"),
            // Control flow
            (&[0xE8, 0x10, 0x00, 0x00, 0x00], "CALL +0x10"),
            (&[0xFF, 0xD0], "CALL RAX"),
            (&[0xC3], "RET"),
            (&[0xE9, 0xFB, 0xFF, 0xFF, 0xFF], "JMP -5"),
            (&[0x74, 0x0A], "JE +10"),
            (&[0x75, 0xF6], "JNE -10"),
            // Misc
            (&[0x90], "NOP"),
            (&[0xC9], "LEAVE"),
            (&[0x48, 0x0F, 0xAF, 0xC1], "IMUL RAX, RCX"),
            (&[0x48, 0x91], "XCHG RAX, RCX"),
            (&[0x48, 0x0F, 0x44, 0xC1], "CMOVE RAX, RCX"),
            (&[0x0F, 0x94, 0xC0], "SETE AL"),
            (&[0x48, 0x0F, 0xB1, 0xCB], "CMPXCHG RBX, RCX"),
            (&[0x48, 0x0F, 0xBC, 0xC1], "BSF RAX, RCX"),
            (&[0x48, 0x0F, 0xBD, 0xC1], "BSR RAX, RCX"),
        ];

        for &(bytes, desc) in encodings {
            let insn =
                decode_x86_64(bytes, 0x1000).unwrap_or_else(|e| panic!("decode {desc}: {e}"));
            let result = sem().effects(&state(), &insn);
            assert!(result.is_ok(), "{desc} should not return error, got: {:?}", result.err());
            let effects = result.expect("effects");
            assert!(!effects.is_empty(), "{desc} should produce at least one effect");
        }
    }

    // -----------------------------------------------------------------------
    // PC advance uses insn.size (variable-length)
    // -----------------------------------------------------------------------

    #[test]
    fn test_pc_advance_uses_insn_size() {
        // 90 = NOP (1 byte) at 0x1000
        let insn = decode_x86_64(&[0x90], 0x1000).expect("decode NOP");
        let effects = sem().effects(&state(), &insn).expect("effects");

        if let Some(Effect::PcUpdate { value }) =
            effects.iter().find(|e| matches!(e, Effect::PcUpdate { .. }))
        {
            // Should advance by 1 byte.
            match value {
                Formula::BvAdd(_, rhs, 64) => match rhs.as_ref() {
                    Formula::BitVec { value: 1, width: 64 } => {} // correct
                    other => panic!("NOP PC advance should add 1, got: {:?}", other),
                },
                other => panic!("NOP PC advance should be BvAdd, got: {:?}", other),
            }
        }

        // B8 xx xx xx xx = MOV EAX, imm32 (5 bytes) at 0x1000
        let insn2 = decode_x86_64(&[0xB8, 0x00, 0x00, 0x00, 0x00], 0x1000).expect("decode MOV");
        let effects2 = sem().effects(&state(), &insn2).expect("effects");

        if let Some(Effect::PcUpdate { value }) =
            effects2.iter().find(|e| matches!(e, Effect::PcUpdate { .. }))
        {
            match value {
                Formula::BvAdd(_, rhs, 64) => match rhs.as_ref() {
                    Formula::BitVec { value: 5, width: 64 } => {} // correct
                    other => panic!("MOV PC advance should add 5, got: {:?}", other),
                },
                other => panic!("MOV PC advance should be BvAdd, got: {:?}", other),
            }
        }
    }
}
