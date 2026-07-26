// AArch64 instruction decode logic
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Encoding reference: ARM DDI 0487 (ARMv8-A Architecture Reference Manual).
// Top-level decode uses bits [28:25] (the "op0" field) to classify into
// major groups, then dispatches to group-specific decoders.

use crate::error::DisasmError;
use crate::instruction::{ControlFlow, Instruction};
use crate::opcode::Opcode;
use crate::operand::{
    BarrierDomain, BarrierType, Condition, ExtendType, MemoryOperand, Operand, Register, ShiftType,
};

// === Bit extraction helpers ===

/// Extract bits [hi:lo] (inclusive) from a 32-bit value.
#[inline]
fn bits(val: u32, hi: u32, lo: u32) -> u32 {
    (val >> lo) & ((1 << (hi - lo + 1)) - 1)
}

/// Extract a single bit.
#[inline]
fn bit(val: u32, pos: u32) -> u32 {
    (val >> pos) & 1
}

/// Sign-extend a value from `width` bits to i64.
#[inline]
fn sign_extend(val: u32, width: u32) -> i64 {
    let shift = 64 - width;
    ((val as i64) << shift) >> shift
}

/// Decode the `sf` bit: 1 = 64-bit, 0 = 32-bit.
#[inline]
fn is_64bit(encoding: u32) -> bool {
    bit(encoding, 31) == 1
}

/// Make a GPR or ZR depending on context. Index 31 => ZR.
#[inline]
fn gpr_or_zr(index: u8, is_64: bool) -> Register {
    if index == 31 { Register::zr(is_64) } else { Register::gpr(index, is_64) }
}

/// Make a GPR or SP depending on context. Index 31 => SP.
#[inline]
fn gpr_or_sp(index: u8, is_64: bool) -> Register {
    if index == 31 { Register::sp(is_64) } else { Register::gpr(index, is_64) }
}

// === Top-level decoder ===

pub(crate) fn decode_instruction(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // Top-level classification: bits [28:25]
    let op0 = bits(enc, 28, 25);

    match op0 {
        // 0b0000: Reserved / unallocated (some are constant-generation)
        0b0000 => Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),

        // 0b100x: Data processing — immediate
        0b1000 | 0b1001 => decode_dp_imm(enc, addr),

        // 0b101x: Branches, exception generation, system instructions
        0b1010 | 0b1011 => decode_branch_sys(enc, addr),

        // 0bx1x0: Loads and stores
        0b0100 | 0b0110 | 0b1100 | 0b1110 => decode_load_store(enc, addr),

        // 0bx101: Data processing — register
        0b0101 | 0b1101 => decode_dp_reg(enc, addr),

        // 0bx111: Data processing — SIMD & FP
        0b0111 | 0b1111 => decode_simd_fp(enc, addr),

        // Everything else
        _ => Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    }
}

// === Data Processing — Immediate ===

fn decode_dp_imm(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // bits [25:23] discriminate the subgroup
    let op1 = bits(enc, 25, 23);

    match op1 {
        // PC-rel addressing: ADR, ADRP
        0b000 | 0b001 => decode_pc_rel(enc, addr),
        // Add/subtract immediate
        0b010 | 0b011 => decode_add_sub_imm(enc, addr),
        // Logical immediate
        0b100 => decode_logical_imm(enc, addr),
        // Move wide immediate
        0b101 => decode_move_wide(enc, addr),
        // Bitfield
        0b110 => decode_bitfield(enc, addr),
        // Extract
        0b111 => decode_extract(enc, addr),
        _ => Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    }
}

fn decode_pc_rel(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let op = bit(enc, 31);
    let immhi = bits(enc, 23, 5);
    let immlo = bits(enc, 30, 29);
    let rd = bits(enc, 4, 0) as u8;

    let (opcode, target) = if op == 0 {
        // ADR: PC + sign_extend(immhi:immlo)
        let imm = (immhi << 2) | immlo;
        let offset = sign_extend(imm, 21);
        (Opcode::Adr, addr.wrapping_add(offset as u64))
    } else {
        // ADRP: (PC & ~0xFFF) + sign_extend(immhi:immlo) << 12
        let imm = (immhi << 2) | immlo;
        let offset = sign_extend(imm, 21) << 12;
        let base = addr & !0xFFF;
        (Opcode::Adrp, base.wrapping_add(offset as u64))
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::gpr(rd, true)));
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_add_sub_imm(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let s = bit(enc, 29);
    let sh = bit(enc, 22); // shift: 0=none, 1=LSL#12
    let imm12 = bits(enc, 21, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match (op, s) {
        (0, 0) => Opcode::Add,
        (0, 1) => Opcode::Adds,
        (1, 0) => Opcode::Sub,
        (1, 1) => Opcode::Subs,
        _ => unreachable!("(op, s) are single-bit fields: all 4 values handled"),
    };

    let imm_val = if sh == 1 { (imm12 as u64) << 12 } else { imm12 as u64 };

    // Rd can be SP for ADD/SUB (not ADDS/SUBS), Rn can be SP always
    let rd_reg = if s == 0 { gpr_or_sp(rd, sf) } else { gpr_or_zr(rd, sf) };
    let rn_reg = gpr_or_sp(rn, sf);

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(rd_reg));
    insn.push_operand(Operand::Reg(rn_reg));
    insn.push_operand(Operand::Imm(imm_val));
    Ok(insn)
}

fn decode_logical_imm(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let opc = bits(enc, 30, 29);
    let n = bit(enc, 22);
    let immr = bits(enc, 21, 16);
    let imms = bits(enc, 15, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    // 32-bit form requires N=0
    if !sf && n == 1 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match opc {
        0b00 => Opcode::And,
        0b01 => Opcode::Orr,
        0b10 => Opcode::Eor,
        0b11 => Opcode::Ands,
        _ => unreachable!("opc is a 2-bit field: all 4 values handled"),
    };

    let imm_val = decode_bitmask_immediate(n, imms, immr, sf);

    // Rd is SP for AND/ORR/EOR, ZR for ANDS
    let rd_reg = if opc == 0b11 { gpr_or_zr(rd, sf) } else { gpr_or_sp(rd, sf) };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(rd_reg));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Imm(imm_val));
    Ok(insn)
}

/// Decode a bitmask immediate (used by logical immediate instructions).
/// ARM DDI 0487 section C6.2.
fn decode_bitmask_immediate(n: u32, imms: u32, immr: u32, is_64: bool) -> u64 {
    let reg_size = if is_64 { 64u32 } else { 32 };

    // Determine element size
    let len = highest_set_bit((n << 6) | (!imms & 0x3F), 7);
    if len < 1 {
        return 0; // Invalid, but don't crash
    }
    let esize = 1u32 << len;
    let levels = esize - 1;

    let s = imms & levels;
    let r = immr & levels;

    // Create the element pattern
    let welem = (1u64 << (s + 1)) - 1;
    // Rotate right by r
    let elem = if r == 0 {
        welem
    } else {
        let mask = (1u64 << esize) - 1;
        ((welem >> r) | (welem << (esize - r))) & mask
    };

    // Replicate to fill register width
    replicate(elem, esize, reg_size)
}

/// Find the highest set bit in `val` (searching from bit `width-1` down).
fn highest_set_bit(val: u32, width: u32) -> u32 {
    for i in (0..width).rev() {
        if (val >> i) & 1 == 1 {
            return i;
        }
    }
    0
}

/// Replicate a pattern of `esize` bits to fill `reg_size` bits.
fn replicate(pattern: u64, esize: u32, reg_size: u32) -> u64 {
    let mut result = 0u64;
    let mut pos = 0;
    while pos < reg_size {
        result |= pattern << pos;
        pos += esize;
    }
    if reg_size < 64 { result & ((1u64 << reg_size) - 1) } else { result }
}

fn decode_move_wide(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let opc = bits(enc, 30, 29);
    let hw = bits(enc, 22, 21);
    let imm16 = bits(enc, 20, 5) as u64;
    let rd = bits(enc, 4, 0) as u8;

    // 32-bit form: hw must be 0 or 1
    if !sf && hw >= 2 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match opc {
        0b00 => Opcode::Movn,
        0b10 => Opcode::Movz,
        0b11 => Opcode::Movk,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let shift = hw * 16;

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Imm(imm16));
    if shift > 0 {
        insn.push_operand(Operand::Imm(shift as u64));
    }
    Ok(insn)
}

fn decode_bitfield(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let opc = bits(enc, 30, 29);
    let n = bit(enc, 22);
    let immr = bits(enc, 21, 16);
    let imms = bits(enc, 15, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    // sf must equal N
    if sf != (n == 1) {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match opc {
        0b00 => Opcode::Sbfm,
        0b01 => Opcode::Bfm,
        0b10 => Opcode::Ubfm,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Imm(immr as u64));
    insn.push_operand(Operand::Imm(imms as u64));
    Ok(insn)
}

fn decode_extract(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let n = bit(enc, 22);
    let rm = bits(enc, 20, 16) as u8;
    let imms = bits(enc, 15, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    if sf != (n == 1) {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let mut insn = Instruction::new(addr, enc, Opcode::Extr, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    insn.push_operand(Operand::Imm(imms as u64));
    Ok(insn)
}

// === Branches, Exception Generation, System ===

fn decode_branch_sys(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // B / BL: bits [31:26]
    let top6 = bits(enc, 31, 26);
    if top6 == 0b000101 {
        return decode_b(enc, addr);
    }
    if top6 == 0b100101 {
        return decode_bl(enc, addr);
    }

    // Check for conditional branch: bits [31:25] = 0101010
    let top7 = bits(enc, 31, 25);
    if top7 == 0b0101010 {
        return decode_b_cond(enc, addr);
    }

    // Compare and branch: bits [30:25] = 011010
    let top_pattern = bits(enc, 30, 25);
    if top_pattern == 0b011010 {
        return decode_cbz_cbnz(enc, addr);
    }

    // Test and branch: bits [30:25] = 011011
    if top_pattern == 0b011011 {
        return decode_tbz_tbnz(enc, addr);
    }

    // Unconditional branch register: bits [31:25] = 1101011
    if top7 == 0b1101011 {
        return decode_br_reg(enc, addr);
    }

    // Exception generation: bits [31:24] = 11010100
    let top8 = bits(enc, 31, 24);
    if top8 == 0b11010100 {
        return decode_exception(enc, addr);
    }

    // System instructions: bits [31:22] = 1101010100
    let top10 = bits(enc, 31, 22);
    if top10 == 0b1101010100 {
        return decode_system(enc, addr);
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_b(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let imm26 = bits(enc, 25, 0);
    let offset = sign_extend(imm26, 26) << 2;
    let target = addr.wrapping_add(offset as u64);

    let mut insn = Instruction::new(addr, enc, Opcode::B, ControlFlow::Branch);
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_bl(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let imm26 = bits(enc, 25, 0);
    let offset = sign_extend(imm26, 26) << 2;
    let target = addr.wrapping_add(offset as u64);

    let mut insn = Instruction::new(addr, enc, Opcode::Bl, ControlFlow::Call);
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_b_cond(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let imm19 = bits(enc, 23, 5);
    let cond = bits(enc, 3, 0) as u8;
    let offset = sign_extend(imm19, 19) << 2;
    let target = addr.wrapping_add(offset as u64);

    let mut insn = Instruction::new(addr, enc, Opcode::BCond, ControlFlow::ConditionalBranch);
    insn.push_operand(Operand::Cond(Condition::from_u8(cond)));
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_cbz_cbnz(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 24);
    let imm19 = bits(enc, 23, 5);
    let rt = bits(enc, 4, 0) as u8;
    let offset = sign_extend(imm19, 19) << 2;
    let target = addr.wrapping_add(offset as u64);

    let opcode = if op == 0 { Opcode::Cbz } else { Opcode::Cbnz };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::ConditionalBranch);
    insn.push_operand(Operand::Reg(gpr_or_zr(rt, sf)));
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_tbz_tbnz(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let b5 = bit(enc, 31);
    let op = bit(enc, 24);
    let b40 = bits(enc, 23, 19);
    let imm14 = bits(enc, 18, 5);
    let rt = bits(enc, 4, 0) as u8;

    let bit_pos = ((b5 << 5) | b40) as u8;
    let offset = sign_extend(imm14, 14) << 2;
    let target = addr.wrapping_add(offset as u64);
    let sf = b5 == 1; // 64-bit if testing bit >= 32

    let opcode = if op == 0 { Opcode::Tbz } else { Opcode::Tbnz };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::ConditionalBranch);
    insn.push_operand(Operand::Reg(gpr_or_zr(rt, sf)));
    insn.push_operand(Operand::BitPos(bit_pos));
    insn.push_operand(Operand::PcRelAddr(target));
    Ok(insn)
}

fn decode_br_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let opc = bits(enc, 24, 21);
    let rn = bits(enc, 9, 5) as u8;

    let (opcode, flow) = match opc {
        0b0000 => (Opcode::Br, ControlFlow::Branch),
        0b0001 => (Opcode::Blr, ControlFlow::Call),
        0b0010 => (Opcode::Ret, ControlFlow::Return),
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, flow);
    insn.push_operand(Operand::Reg(Register::gpr(rn, true)));
    Ok(insn)
}

fn decode_exception(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let opc = bits(enc, 23, 21);
    let imm16 = bits(enc, 20, 5) as u64;
    let ll = bits(enc, 1, 0);

    let opcode = match (opc, ll) {
        (0b000, 0b01) => Opcode::Svc,
        (0b000, 0b10) => Opcode::Hvc,
        (0b000, 0b11) => Opcode::Smc,
        (0b001, 0b00) => Opcode::Brk,
        (0b010, 0b00) => Opcode::Hlt,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Exception);
    insn.push_operand(Operand::Imm(imm16));
    Ok(insn)
}

fn decode_system(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let l = bit(enc, 21);
    let op0 = bits(enc, 20, 19);
    let op1 = bits(enc, 18, 16);
    let crn = bits(enc, 15, 12);
    let crm = bits(enc, 11, 8);
    let op2 = bits(enc, 7, 5);
    let rt = bits(enc, 4, 0) as u8;

    // Hint instructions: L=0, op0=0, op1=011, CRn=0010, Rt=11111
    if l == 0 && op0 == 0 && op1 == 0b011 && crn == 0b0010 && rt == 31 {
        return decode_hint(enc, addr, crm, op2);
    }

    // Barriers: L=0, op0=0, op1=011, CRn=0011
    if l == 0 && op0 == 0 && op1 == 0b011 && crn == 0b0011 {
        return decode_barrier(enc, addr, crm, op2);
    }

    // MSR/MRS (system register access)
    if op0 >= 2 {
        let sys_reg = ((op0 as u16) << 14)
            | ((op1 as u16) << 11)
            | ((crn as u16) << 7)
            | ((crm as u16) << 3)
            | (op2 as u16);

        if l == 0 {
            // MSR <sysreg>, Xt
            let mut insn = Instruction::new(addr, enc, Opcode::Msr, ControlFlow::Fallthrough);
            insn.push_operand(Operand::SysReg(sys_reg));
            insn.push_operand(Operand::Reg(Register::gpr(rt, true)));
            return Ok(insn);
        } else {
            // MRS Xt, <sysreg>
            let mut insn = Instruction::new(addr, enc, Opcode::Mrs, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(Register::gpr(rt, true)));
            insn.push_operand(Operand::SysReg(sys_reg));
            return Ok(insn);
        }
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_hint(enc: u32, addr: u64, crm: u32, op2: u32) -> Result<Instruction, DisasmError> {
    let hint_val = (crm << 3) | op2;
    let opcode = match hint_val {
        0b000_0000 => Opcode::Nop,
        0b000_0001 => Opcode::Yield,
        0b000_0010 => Opcode::Wfe,
        0b000_0011 => Opcode::Wfi,
        0b000_0100 => Opcode::Sev,
        0b000_0101 => Opcode::Sevl,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    Ok(insn)
}

fn decode_barrier(enc: u32, addr: u64, crm: u32, op2: u32) -> Result<Instruction, DisasmError> {
    let opcode = match op2 {
        0b001 => Opcode::Dsb,
        0b010 => {
            // CLREX
            let mut insn = Instruction::new(addr, enc, Opcode::Clrex, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Imm(crm as u64));
            return Ok(insn);
        }
        0b100 => Opcode::Dmb,
        0b110 => Opcode::Isb,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    // The operand model carries named domain/type pairs, not arbitrary numeric
    // barrier options. Keep numeric/reserved options fail-closed so reports do
    // not rewrite proof-relevant ordering scope into a different named option.
    let option = crm as u8;
    if matches!(opcode, Opcode::Dmb | Opcode::Dsb) && !is_named_data_barrier_option(option) {
        return Err(DisasmError::UnsupportedAarch64BarrierOption {
            encoding: enc,
            address: addr,
            option,
        });
    }
    if opcode == Opcode::Isb && option != 0b1111 {
        return Err(DisasmError::UnsupportedAarch64BarrierOption {
            encoding: enc,
            address: addr,
            option,
        });
    }

    let domain = match crm >> 2 {
        0b00 => BarrierDomain::Osh,
        0b01 => BarrierDomain::Nsh,
        0b10 => BarrierDomain::Ish,
        0b11 => BarrierDomain::Sy,
        _ => BarrierDomain::Sy,
    };

    let kind = match crm & 0b11 {
        0b01 => BarrierType::Ld,
        0b10 => BarrierType::St,
        _ => BarrierType::Full,
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Barrier { domain, kind });
    Ok(insn)
}

fn is_named_data_barrier_option(option: u8) -> bool {
    matches!(
        option,
        0b0001
            | 0b0010
            | 0b0011
            | 0b0101
            | 0b0110
            | 0b0111
            | 0b1001
            | 0b1010
            | 0b1011
            | 0b1101
            | 0b1110
            | 0b1111
    )
}

// === Loads and Stores ===

fn decode_load_store(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // Bit layout for loads/stores uses bits [31:28] and [25:24] and others.
    // We check specific patterns.

    let op0 = bits(enc, 31, 28);
    let op1 = bit(enc, 26);
    let op2 = bits(enc, 24, 23);
    let _op3 = bits(enc, 21, 16);
    let _op4 = bits(enc, 11, 10);

    // Load literal: bits [29:27]=011, V(bit26)=0 => load literal
    // Must check BEFORE exclusive, as some literal encodings match exclusive patterns.
    let bits_29_27 = bits(enc, 29, 27);
    if bits_29_27 == 0b011 && op1 == 0 {
        return decode_load_literal(enc, addr);
    }

    // Load/store exclusive: op0[1]=0, op1=0, op2[1]=0
    if op0 & 0b0010 == 0 && op1 == 0 && op2 & 0b10 == 0 {
        return decode_load_store_exclusive(enc, addr);
    }

    // Load/store pair: bits [29:27] = 101
    if bits_29_27 == 0b101 && op1 == 0 {
        return decode_load_store_pair(enc, addr);
    }

    // Load/store register (various addressing modes)
    // bits [29:27] = 111 (or 110)
    if (bits_29_27 == 0b111 || bits_29_27 == 0b110) && op1 == 0 {
        return decode_load_store_reg(enc, addr);
    }

    // SIMD/FP load/store register: op1=1, bits [29:27] = 111 (or 110).
    // Only the unsigned-offset scalar/SIMD register forms are decoded here.
    // The lifter still fails closed because FP/SIMD register state is not in
    // the scalar TrustIr layout.
    if (bits_29_27 == 0b111 || bits_29_27 == 0b110) && op1 == 1 {
        return decode_simd_fp_load_store_reg_unsigned_offset(enc, addr);
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_load_store_exclusive(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let size = bits(enc, 31, 30);
    let l = bit(enc, 22);
    let o0 = bit(enc, 15);
    let o2 = bit(enc, 23);
    let rs = bits(enc, 20, 16) as u8;
    let rt2 = bits(enc, 14, 10) as u8;
    let rt = bits(enc, 4, 0) as u8;
    let rn = bits(enc, 9, 5) as u8;

    let is_64 = size == 0b11;

    // Load-acquire / store-release set o2=1 and reserve Rs/Rt2 as 11111.
    // Exclusive acquire/release variants keep o2=0 and use o0 as the acquire/release bit.
    let opcode = match (l, o0, o2) {
        (1, 1, 1) if rs == 31 && rt2 == 31 => Opcode::Ldar,
        (0, 1, 1) if rs == 31 && rt2 == 31 => Opcode::Stlr,
        (1, 0, 0) if rs == 31 && rt2 == 31 => Opcode::Ldxr,
        (0, 0, 0) if rt2 == 31 => Opcode::Stxr,
        (1, 1, 0) if rs == 31 && rt2 == 31 => Opcode::Ldaxr,
        (0, 1, 0) if rt2 == 31 => Opcode::Stlxr,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let base = gpr_or_sp(rn, true);
    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);

    match opcode {
        Opcode::Stxr | Opcode::Stlxr => {
            insn.push_operand(Operand::Reg(Register::gpr(rs, false))); // Ws (status)
            insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
            insn.push_operand(Operand::Mem(MemoryOperand::Base { base }));
        }
        _ => {
            insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
            insn.push_operand(Operand::Mem(MemoryOperand::Base { base }));
        }
    }

    Ok(insn)
}

fn decode_simd_fp_load_store_reg_unsigned_offset(
    enc: u32,
    addr: u64,
) -> Result<Instruction, DisasmError> {
    let size = bits(enc, 31, 30);
    let opc = bits(enc, 23, 22);
    let rn = bits(enc, 9, 5) as u8;
    let rt = bits(enc, 4, 0) as u8;

    if bit(enc, 24) != 1 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    let (opcode, width, scale) = simd_fp_load_store_width(opc, size)
        .ok_or(DisasmError::UnallocatedEncoding { encoding: enc, address: addr })?;
    let imm12 = bits(enc, 21, 10);
    let offset = (imm12 as i64) << scale;
    let base = gpr_or_sp(rn, true);

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rt, width)));
    insn.push_operand(Operand::Mem(MemoryOperand::BaseOffset { base, offset }));
    Ok(insn)
}

fn simd_fp_load_store_width(opc: u32, size: u32) -> Option<(Opcode, u16, u32)> {
    match opc {
        0b00 => Some((Opcode::Str, 8u16 << size, size)),
        0b01 => Some((Opcode::Ldr, 8u16 << size, size)),
        0b10 if size == 0 => Some((Opcode::Str, 128, 4)),
        0b11 if size == 0 => Some((Opcode::Ldr, 128, 4)),
        _ => None,
    }
}

fn decode_load_literal(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let opc = bits(enc, 31, 30);
    let imm19 = bits(enc, 23, 5);
    let rt = bits(enc, 4, 0) as u8;
    let offset = sign_extend(imm19, 19) << 2;

    let is_64 = opc == 0b01;

    let opcode = match opc {
        0b00 | 0b01 => Opcode::LdrLiteral,
        0b10 => Opcode::Ldrsw,
        0b11 => Opcode::Prfm,
        _ => unreachable!("opc is a 2-bit field: all 4 values handled"),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    if opcode == Opcode::Prfm {
        insn.push_operand(Operand::Imm(rt as u64)); // prefetch operation
    } else {
        insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
    }
    insn.push_operand(Operand::Mem(MemoryOperand::PcRelative { offset }));
    Ok(insn)
}

fn decode_load_store_pair(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let opc = bits(enc, 31, 30);
    let l = bit(enc, 22);
    let imm7 = bits(enc, 21, 15);
    let rt2 = bits(enc, 14, 10) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rt = bits(enc, 4, 0) as u8;
    let mode = bits(enc, 24, 23); // 01=post, 10=signed offset, 11=pre

    let is_64 = opc == 0b10;
    let scale = if is_64 { 3 } else { 2 }; // 8 bytes for 64-bit, 4 for 32-bit
    let offset = sign_extend(imm7, 7) << scale;

    let opcode = if l == 1 { Opcode::Ldp } else { Opcode::Stp };
    let base = gpr_or_sp(rn, true);

    let mem = match mode {
        0b01 => MemoryOperand::PostIndex { base, offset },
        0b10 => MemoryOperand::BaseOffset { base, offset },
        0b11 => MemoryOperand::PreIndex { base, offset },
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rt2, is_64)));
    insn.push_operand(Operand::Mem(mem));
    Ok(insn)
}

fn decode_load_store_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let size = bits(enc, 31, 30);
    let v = bit(enc, 26);
    let opc_field = bits(enc, 23, 22);
    let rn = bits(enc, 9, 5) as u8;
    let rt = bits(enc, 4, 0) as u8;

    // Skip SIMD/FP loads for now
    if v == 1 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    // Determine opcode from size and opc
    let (opcode, is_64) = match (size, opc_field) {
        (0b00, 0b00) => (Opcode::Strb, false),
        (0b00, 0b01) => (Opcode::Ldrb, false),
        (0b00, 0b10) => (Opcode::Ldrsb, true), // 64-bit target
        (0b00, 0b11) => (Opcode::Ldrsb, false), // 32-bit target
        (0b01, 0b00) => (Opcode::Strh, false),
        (0b01, 0b01) => (Opcode::Ldrh, false),
        (0b01, 0b10) => (Opcode::Ldrsh, true), // 64-bit target
        (0b01, 0b11) => (Opcode::Ldrsh, false), // 32-bit target
        (0b10, 0b00) => (Opcode::Str, false),  // 32-bit
        (0b10, 0b01) => (Opcode::Ldr, false),  // 32-bit
        (0b10, 0b10) => (Opcode::Ldrsw, true),
        (0b11, 0b00) => (Opcode::Str, true), // 64-bit
        (0b11, 0b01) => (Opcode::Ldr, true), // 64-bit
        (0b11, 0b10) => (Opcode::Prfm, true),
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    // Determine addressing mode from bit 24 and bits [11:10]
    let bit24 = bit(enc, 24);
    let bit21 = bit(enc, 21);

    let base = gpr_or_sp(rn, true);

    if bit24 == 1 {
        // Unsigned offset: imm12 << scale
        let imm12 = bits(enc, 21, 10);
        let scale = size;
        let offset = (imm12 as i64) << scale;
        let mem = MemoryOperand::BaseOffset { base, offset };

        let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
        if opcode == Opcode::Prfm {
            insn.push_operand(Operand::Imm(rt as u64));
        } else {
            insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
        }
        insn.push_operand(Operand::Mem(mem));
        Ok(insn)
    } else if bit21 == 1 {
        // Register offset
        let rm = bits(enc, 20, 16) as u8;
        let option = bits(enc, 15, 13);
        let s = bit(enc, 12);
        let shift = if s == 1 { size as u8 } else { 0 };

        let extend = match option {
            0b010 => Some(ExtendType::Uxtw),
            0b011 => None, // LSL
            0b110 => Some(ExtendType::Sxtw),
            0b111 => Some(ExtendType::Sxtx),
            _ => None,
        };

        let index = if option == 0b011 {
            Register::gpr(rm, true) // 64-bit index with LSL
        } else {
            Register::gpr(rm, option & 1 == 1)
        };

        let mem = MemoryOperand::BaseRegister { base, index, extend, shift };

        let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
        if opcode == Opcode::Prfm {
            insn.push_operand(Operand::Imm(rt as u64));
        } else {
            insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
        }
        insn.push_operand(Operand::Mem(mem));
        Ok(insn)
    } else {
        // Unscaled immediate / pre-index / post-index
        let imm9 = bits(enc, 20, 12);
        let op2 = bits(enc, 11, 10);
        let offset = sign_extend(imm9, 9);

        let mem = match op2 {
            0b00 => {
                // Unscaled immediate (LDUR/STUR) - treat as base offset
                MemoryOperand::BaseOffset { base, offset }
            }
            0b01 => MemoryOperand::PostIndex { base, offset },
            0b11 => MemoryOperand::PreIndex { base, offset },
            0b10 => {
                // Unprivileged - treat as base offset
                MemoryOperand::BaseOffset { base, offset }
            }
            _ => unreachable!("idx_mode is a 2-bit field: all 4 values handled"),
        };

        let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
        if opcode == Opcode::Prfm {
            insn.push_operand(Operand::Imm(rt as u64));
        } else {
            insn.push_operand(Operand::Reg(gpr_or_zr(rt, is_64)));
        }
        insn.push_operand(Operand::Mem(mem));
        Ok(insn)
    }
}

// === Data Processing — Register ===

fn decode_dp_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let op1 = bit(enc, 28);
    let op2 = bits(enc, 24, 21);

    if op1 == 0 {
        // Logical shifted register: op2[3]=0 (op2 = 0xxx)
        if op2 & 0b1000 == 0 {
            return decode_logical_shifted_reg(enc, addr);
        }
        // Add/subtract shifted register: op2=1000
        if op2 == 0b1000 {
            return decode_add_sub_shifted_reg(enc, addr);
        }
        // Add/subtract extended register: op2=1001
        if op2 == 0b1001 {
            return decode_add_sub_extended_reg(enc, addr);
        }
    } else {
        // op1 == 1

        // Add/subtract with carry: op2=0000
        if op2 == 0b0000 {
            return decode_add_sub_carry(enc, addr);
        }

        // Conditional compare: op2=0010 or 0011 (bits[24:22]=001)
        if op2 == 0b0010 || op2 == 0b0011 {
            return decode_cond_compare(enc, addr);
        }

        // Conditional select: op2=0100 or 0101
        if op2 == 0b0100 || op2 == 0b0101 {
            return decode_cond_select(enc, addr);
        }

        // Data processing (2 or 1 source): op2=0110
        if op2 == 0b0110 {
            return decode_dp_2source(enc, addr);
        }

        // Data processing (3 source): op2[3]=1 (op2 = 1xxx)
        if op2 & 0b1000 != 0 {
            return decode_dp_3source(enc, addr);
        }
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_logical_shifted_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let opc = bits(enc, 30, 29);
    let n = bit(enc, 21);
    let shift_type = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let imm6 = bits(enc, 15, 10) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match (opc, n) {
        (0b00, 0) => Opcode::And,
        (0b00, 1) => Opcode::Bic,
        (0b01, 0) => Opcode::Orr,
        (0b01, 1) => Opcode::Orn,
        (0b10, 0) => Opcode::Eor,
        (0b10, 1) => Opcode::Eon,
        (0b11, 0) => Opcode::Ands,
        (0b11, 1) => Opcode::Bics,
        _ => unreachable!("(opc, n) are 2-bit and 1-bit fields: all 8 values handled"),
    };

    let shift = decode_shift_type(shift_type);

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    if imm6 == 0 {
        insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    } else {
        insn.push_operand(Operand::ShiftedReg { reg: gpr_or_zr(rm, sf), shift, amount: imm6 });
    }
    Ok(insn)
}

fn decode_add_sub_shifted_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let s = bit(enc, 29);
    let shift_type = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let imm6 = bits(enc, 15, 10) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    // ROR (shift_type=11) is reserved for add/sub
    if shift_type == 0b11 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match (op, s) {
        (0, 0) => Opcode::Add,
        (0, 1) => Opcode::Adds,
        (1, 0) => Opcode::Sub,
        (1, 1) => Opcode::Subs,
        _ => unreachable!("(op, s) are single-bit fields: all 4 values handled"),
    };

    let shift = decode_shift_type(shift_type);

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    if imm6 == 0 {
        insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    } else {
        insn.push_operand(Operand::ShiftedReg { reg: gpr_or_zr(rm, sf), shift, amount: imm6 });
    }
    Ok(insn)
}

fn decode_add_sub_extended_reg(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let s = bit(enc, 29);
    let rm = bits(enc, 20, 16) as u8;
    let option = bits(enc, 15, 13);
    let imm3 = bits(enc, 12, 10) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match (op, s) {
        (0, 0) => Opcode::Add,
        (0, 1) => Opcode::Adds,
        (1, 0) => Opcode::Sub,
        (1, 1) => Opcode::Subs,
        _ => unreachable!("(op, s) are single-bit fields: all 4 values handled"),
    };

    let extend = decode_extend_type(option);
    let rm_is_64 = option >= 0b100; // SXTB..SXTX operate on 64-bit view

    let rd_reg = if s == 0 { gpr_or_sp(rd, sf) } else { gpr_or_zr(rd, sf) };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(rd_reg));
    insn.push_operand(Operand::Reg(gpr_or_sp(rn, sf)));
    insn.push_operand(Operand::ExtendedReg { reg: gpr_or_zr(rm, rm_is_64), extend, shift: imm3 });
    Ok(insn)
}

fn decode_add_sub_carry(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let s = bit(enc, 29);
    let rm = bits(enc, 20, 16) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match (op, s) {
        (0, 0) => Opcode::Adc,
        (0, 1) => Opcode::Adcs,
        (1, 0) => Opcode::Sbc,
        (1, 1) => Opcode::Sbcs,
        _ => unreachable!(),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    Ok(insn)
}

fn decode_cond_compare(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let o2 = bit(enc, 10);
    let o3 = bit(enc, 4);
    let is_imm = bit(enc, 11) == 1;
    let cond = bits(enc, 15, 12) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let nzcv = bits(enc, 3, 0) as u64;

    if o2 != 0 || o3 != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = if op == 0 { Opcode::Ccmn } else { Opcode::Ccmp };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    if is_imm {
        let imm5 = bits(enc, 20, 16) as u64;
        insn.push_operand(Operand::Imm(imm5));
    } else {
        let rm = bits(enc, 20, 16) as u8;
        insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    }
    insn.push_operand(Operand::Imm(nzcv));
    insn.push_operand(Operand::Cond(Condition::from_u8(cond)));
    Ok(insn)
}

fn decode_cond_select(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op = bit(enc, 30);
    let s = bit(enc, 29);
    let rm = bits(enc, 20, 16) as u8;
    let cond = bits(enc, 15, 12) as u8;
    let op2 = bits(enc, 11, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    if s != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match (op, op2) {
        (0, 0b00) => Opcode::Csel,
        (0, 0b01) => Opcode::Csinc,
        (1, 0b00) => Opcode::Csinv,
        (1, 0b01) => Opcode::Csneg,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    insn.push_operand(Operand::Cond(Condition::from_u8(cond)));
    Ok(insn)
}

fn decode_dp_2source(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let s = bit(enc, 29);

    // 1-source vs 2-source: distinguished by bit 30
    if bit(enc, 30) == 1 {
        return decode_dp_1source(enc, addr);
    }

    if s != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode_field = bits(enc, 15, 10);
    let rm = bits(enc, 20, 16) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match opcode_field {
        0b000010 => Opcode::Udiv,
        0b000011 => Opcode::Sdiv,
        0b001000 => Opcode::Lslv,
        0b001001 => Opcode::Lsrv,
        0b001010 => Opcode::Asrv,
        0b001011 => Opcode::Rorv,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rm, sf)));
    Ok(insn)
}

fn decode_dp_1source(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let opcode_field = bits(enc, 15, 10);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match opcode_field {
        0b000000 => Opcode::Rbit,
        0b000001 => Opcode::Rev16,
        0b000010 => {
            if sf {
                Opcode::Rev32
            } else {
                Opcode::Rev
            }
        }
        0b000011 => Opcode::Rev,
        0b000100 => Opcode::Clz,
        0b000101 => Opcode::Cls,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    Ok(insn)
}

fn decode_dp_3source(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let op31 = bits(enc, 23, 21);
    let o0 = bit(enc, 15);
    let rm = bits(enc, 20, 16) as u8;
    let ra = bits(enc, 14, 10) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let opcode = match (sf, op31, o0) {
        (_, 0b000, 0) => Opcode::Madd,
        (_, 0b000, 1) => Opcode::Msub,
        (true, 0b001, 0) => Opcode::Smaddl,
        (true, 0b001, 1) => Opcode::Smsubl,
        (true, 0b010, 0) => Opcode::Smulh,
        (true, 0b101, 0) => Opcode::Umaddl,
        (true, 0b101, 1) => Opcode::Umsubl,
        (true, 0b110, 0) => Opcode::Umulh,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    // For SMADDL/etc., Rn and Rm are 32-bit, Rd and Ra are 64-bit
    let (rn_64, rm_64) = match opcode {
        Opcode::Smaddl | Opcode::Smsubl | Opcode::Umaddl | Opcode::Umsubl => (false, false),
        Opcode::Smulh | Opcode::Umulh => (true, true),
        _ => (sf, sf),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr_or_zr(rd, sf)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, rn_64)));
    insn.push_operand(Operand::Reg(gpr_or_zr(rm, rm_64)));
    // SMULH/UMULH don't have Ra
    if !matches!(opcode, Opcode::Smulh | Opcode::Umulh) {
        insn.push_operand(Operand::Reg(gpr_or_zr(ra, sf)));
    }
    Ok(insn)
}

// === SIMD & Floating-Point ===

fn decode_simd_fp(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // Basic FP data processing, FP<->integer conversion, FP compare.
    // Full SIMD is deferred. We dispatch using bits[11:10] to avoid
    // false matches between FP conversion and FP arithmetic.

    // Trust: FP<->int conversion has sf bit at [31], check [30:24]=0011110 + [21]=1
    // FP data processing has [31:29]=000, [28:24]=11110, [21]=1
    // Both share [28:24]=11110 and [21]=1.
    let is_fp_prefix = bits(enc, 28, 24) == 0b11110 && bit(enc, 21) == 1;
    let is_dp_prefix = bits(enc, 31, 29) == 0b000 && is_fp_prefix;
    let is_int_conv_prefix = bits(enc, 30, 29) == 0b00 && is_fp_prefix;

    if is_dp_prefix {
        let op_11_10 = bits(enc, 11, 10);

        match op_11_10 {
            // bits[11:10]=10: FP data processing (2-source)
            0b10 => {
                // 2-source: bits[15:12] selects FMUL/FDIV/FADD/FSUB
                return decode_fp_dp_2source(enc, addr);
            }
            // bits[11:10]=11: FP conditional select (FCSEL)
            0b11 => {
                return decode_fp_csel(enc, addr);
            }
            // bits[11:10]=00: FP compare, FP immediate, FP 1-source, or FP<->int conversion
            0b00 => {
                // Trust: FP 1-source (FMOV/FABS/FNEG/FSQRT/FCVT): bits[14:10]=10000
                if bits(enc, 14, 10) == 0b10000 {
                    return decode_fp_dp_1source(enc, addr);
                }
                // FP compare: bits[13:10]=1000 (i.e., bits[13:12]=10, bits[11:10]=00)
                if bits(enc, 13, 10) == 0b1000 {
                    return decode_fp_compare(enc, addr);
                }
                // FP immediate: bits[13:10]=0100, Rn=00000
                if bits(enc, 13, 10) == 0b0100 && bits(enc, 9, 5) == 0 {
                    return decode_fp_imm(enc, addr);
                }
                // FP<->integer conversion (FMOV GPR<->FP, SCVTF, UCVTF, FCVTZS, FCVTZU)
                return decode_fp_int_conv(enc, addr);
            }
            // bits[11:10]=01: also FP<->integer conversion variants
            0b01 => {
                return decode_fp_int_conv(enc, addr);
            }
            _ => {}
        }
    }

    // Trust: FP<->integer conversion with sf=1 (64-bit int): bit[31]=1
    // bits[30:24]=0011110, bit[21]=1
    if is_int_conv_prefix && bit(enc, 31) == 1 {
        return decode_fp_int_conv(enc, addr);
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_fp_int_conv(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let sf = is_64bit(enc);
    let ftype = bits(enc, 23, 22);
    let rmode = bits(enc, 20, 19);
    let opcode_field = bits(enc, 18, 16);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        0b11 => 16,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let (opcode, dst_is_fp, src_is_fp) = match (rmode, opcode_field) {
        // FMOV: integer <-> FP (rmode=00, opcode=110 or 111)
        (0b00, 0b110) => (Opcode::FmovReg, false, true), // Rd=GPR, Rn=FP
        (0b00, 0b111) => (Opcode::FmovReg, true, false), // Rd=FP, Rn=GPR
        // FCVTZS: FP -> signed int (rmode=11, opcode=000)
        (0b11, 0b000) => (Opcode::Fcvtzs, false, true),
        // FCVTZU: FP -> unsigned int (rmode=11, opcode=001)
        (0b11, 0b001) => (Opcode::Fcvtzu, false, true),
        // SCVTF: signed int -> FP (rmode=00, opcode=010)
        (0b00, 0b010) => (Opcode::Scvtf, true, false),
        // UCVTF: unsigned int -> FP (rmode=00, opcode=011)
        (0b00, 0b011) => (Opcode::Ucvtf, true, false),
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let dst = if dst_is_fp { Register::simd(rd, fp_width) } else { gpr_or_zr(rd, sf) };
    let src = if src_is_fp { Register::simd(rn, fp_width) } else { gpr_or_zr(rn, sf) };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(dst));
    insn.push_operand(Operand::Reg(src));
    Ok(insn)
}

fn decode_fp_dp_2source(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let ftype = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let opcode_field = bits(enc, 15, 12);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let opcode = match opcode_field {
        0b0000 => Opcode::Fmul,
        0b0001 => Opcode::Fdiv,
        0b0010 => Opcode::Fadd,
        0b0011 => Opcode::Fsub,
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rd, fp_width)));
    insn.push_operand(Operand::Reg(Register::simd(rn, fp_width)));
    insn.push_operand(Operand::Reg(Register::simd(rm, fp_width)));
    Ok(insn)
}

fn decode_fp_dp_1source(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let ftype = bits(enc, 23, 22);
    let opcode_field = bits(enc, 20, 15);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let opcode = match opcode_field {
        0b000000 => Opcode::FmovReg,
        0b000001 => Opcode::Fabs,
        0b000010 => Opcode::Fneg,
        0b000011 => Opcode::Fsqrt,
        0b000100 | 0b000101 => Opcode::Fcvt, // convert between precisions
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    // For FCVT, destination width differs from source
    let dst_width = if opcode == Opcode::Fcvt {
        match (ftype, opcode_field) {
            (0b00, 0b000101) => 64u16, // S -> D
            (0b01, 0b000100) => 32,    // D -> S
            _ => fp_width,
        }
    } else {
        fp_width
    };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rd, dst_width)));
    insn.push_operand(Operand::Reg(Register::simd(rn, fp_width)));
    Ok(insn)
}

fn decode_fp_compare(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let ftype = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let opc = bits(enc, 4, 3);

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, Opcode::Fcmp, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rn, fp_width)));
    if opc & 1 == 1 {
        // Compare with zero
        insn.push_operand(Operand::Imm(0));
    } else {
        insn.push_operand(Operand::Reg(Register::simd(rm, fp_width)));
    }
    Ok(insn)
}

fn decode_fp_csel(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let ftype = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let cond = bits(enc, 15, 12) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, Opcode::Fcsel, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rd, fp_width)));
    insn.push_operand(Operand::Reg(Register::simd(rn, fp_width)));
    insn.push_operand(Operand::Reg(Register::simd(rm, fp_width)));
    insn.push_operand(Operand::Cond(Condition::from_u8(cond)));
    Ok(insn)
}

fn decode_fp_imm(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    let ftype = bits(enc, 23, 22);
    let imm8 = bits(enc, 20, 13) as u64;
    let rd = bits(enc, 4, 0) as u8;

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    let mut insn = Instruction::new(addr, enc, Opcode::FmovImm, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(Register::simd(rd, fp_width)));
    insn.push_operand(Operand::Imm(imm8));
    Ok(insn)
}

// === Helpers ===

fn decode_shift_type(val: u32) -> ShiftType {
    match val & 3 {
        0b00 => ShiftType::Lsl,
        0b01 => ShiftType::Lsr,
        0b10 => ShiftType::Asr,
        _ => ShiftType::Ror,
    }
}

fn decode_extend_type(option: u32) -> ExtendType {
    match option & 7 {
        0b000 => ExtendType::Uxtb,
        0b001 => ExtendType::Uxth,
        0b010 => ExtendType::Uxtw,
        0b011 => ExtendType::Uxtx,
        0b100 => ExtendType::Sxtb,
        0b101 => ExtendType::Sxth,
        0b110 => ExtendType::Sxtw,
        _ => ExtendType::Sxtx,
    }
}
