// x86-64 instruction decode logic
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: Intel 64 and IA-32 Architectures SDM, Volume 2.
// Decodes the most common x86-64 instructions from raw bytes.
// Variable-length encoding: 1-15 bytes per instruction.

use crate::error::DisasmError;
use crate::instruction::{ControlFlow, Instruction};
use crate::opcode::Opcode;
use crate::operand::{Condition, Operand};

use super::modrm::{ModRM, decode_rm_operand, gpr};
use super::prefix::Prefixes;

/// Decode one x86-64 instruction from `bytes` at the given virtual address.
pub(crate) fn decode_instruction(bytes: &[u8], addr: u64) -> Result<Instruction, DisasmError> {
    if bytes.is_empty() {
        return Err(DisasmError::InsufficientBytes { needed: 1, available: 0 });
    }

    let prefixes = Prefixes::parse(bytes);
    let rest = &bytes[prefixes.len..];

    if rest.is_empty() {
        return Err(DisasmError::InsufficientBytes {
            needed: prefixes.len + 1,
            available: bytes.len(),
        });
    }

    let opcode_byte = rest[0];
    let after_opcode = &rest[1..];

    // Two-byte opcode escape (0x0F)
    let mut instruction = if opcode_byte == 0x0F {
        decode_two_byte_opcode(after_opcode, addr, &prefixes, prefixes.len + 1)?
    } else {
        decode_one_byte_opcode(opcode_byte, after_opcode, addr, &prefixes, prefixes.len + 1)?
    };

    let total_len = usize::from(instruction.size);
    if bytes.len() < total_len {
        return Err(DisasmError::InsufficientBytes { needed: total_len, available: bytes.len() });
    }
    instruction.bytes = bytes[..total_len].to_vec();
    Ok(instruction)
}

/// Decode a single-byte opcode instruction.
fn decode_one_byte_opcode(
    opcode: u8,
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    match opcode {
        // --- NOP (0x90) ---
        0x90 => {
            if prefixes.rex.present && prefixes.rex.b {
                // XCHG RAX, R8 (REX.B changes the meaning)
                let reg2 = gpr(8, prefixes.operand_size());
                let reg1 = gpr(0, prefixes.operand_size());
                let mut insn =
                    make_insn(addr, offset, 0x90, Opcode::Xchg, ControlFlow::Fallthrough);
                insn.push_operand(Operand::Reg(reg1));
                insn.push_operand(Operand::Reg(reg2));
                Ok(insn)
            } else {
                Ok(make_insn(addr, offset, 0x90, Opcode::Nop, ControlFlow::Fallthrough))
            }
        }

        // --- PUSH r64 (0x50+rd) ---
        0x50..=0x57 => {
            let reg_idx = (opcode - 0x50) | if prefixes.rex.b { 8 } else { 0 };
            let mut insn =
                make_insn(addr, offset, opcode as u32, Opcode::Push, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(reg_idx, 64)));
            Ok(insn)
        }

        // --- POP r64 (0x58+rd) ---
        0x58..=0x5F => {
            let reg_idx = (opcode - 0x58) | if prefixes.rex.b { 8 } else { 0 };
            let mut insn =
                make_insn(addr, offset, opcode as u32, Opcode::Pop, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(reg_idx, 64)));
            Ok(insn)
        }

        // --- MOV r/m, r (0x89) ---
        0x89 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Mov, false),

        // --- MOV r, r/m (0x8B) ---
        0x8B => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Mov),

        // --- MOV r/m8, r8 (0x88) ---
        0x88 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Mov, true),

        // --- MOV r8, r/m8 (0x8A) ---
        0x8A => decode_modrm_reg_rm_8bit(rest, addr, prefixes, offset, Opcode::Mov),

        // --- MOV r/m, imm32 (0xC7 /0) ---
        0xC7 => {
            if rest.is_empty() {
                return Err(insufficient(offset + 1, rest.len()));
            }
            let modrm = ModRM::decode(rest[0], prefixes);
            if modrm.reg & 0x07 != 0 {
                return Err(unknown_enc(addr, opcode));
            }
            let op_width = prefixes.operand_size();
            let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
            let imm_start = 1 + rm_result.extra_bytes;
            let imm_size = if op_width == 16 { 2 } else { 4 };
            if rest.len() < imm_start + imm_size {
                return Err(insufficient(offset + 1 + imm_start + imm_size, rest.len()));
            }
            let imm = read_imm_signed(&rest[imm_start..], imm_size);
            let total = offset + 1 + rm_result.extra_bytes + imm_size;
            let mut insn = make_insn(addr, total, 0xC7, Opcode::Mov, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            insn.push_operand(Operand::SignedImm(imm));
            Ok(insn)
        }

        // --- MOV r, imm (0xB8+rd for 32/64-bit) ---
        0xB8..=0xBF => {
            let reg_idx = (opcode - 0xB8) | if prefixes.rex.b { 8 } else { 0 };
            let (imm, imm_size) = if prefixes.rex.w {
                // 64-bit immediate
                if rest.len() < 8 {
                    return Err(insufficient(offset + 8, rest.len()));
                }
                (read_imm_unsigned(rest, 8) as i64, 8)
            } else if prefixes.legacy.operand_size {
                if rest.len() < 2 {
                    return Err(insufficient(offset + 2, rest.len()));
                }
                (read_imm_signed(rest, 2), 2)
            } else {
                if rest.len() < 4 {
                    return Err(insufficient(offset + 4, rest.len()));
                }
                (read_imm_signed(rest, 4), 4)
            };
            let width = prefixes.operand_size();
            let total = offset + imm_size;
            let mut insn =
                make_insn(addr, total, opcode as u32, Opcode::Mov, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(reg_idx, width)));
            if prefixes.rex.w {
                insn.push_operand(Operand::Imm(imm as u64));
            } else {
                insn.push_operand(Operand::SignedImm(imm));
            }
            Ok(insn)
        }

        // --- MOV r8, imm8 (0xB0+rb) ---
        0xB0..=0xB7 => {
            let reg_idx = (opcode - 0xB0) | if prefixes.rex.b { 8 } else { 0 };
            if rest.is_empty() {
                return Err(insufficient(offset + 1, 0));
            }
            let imm = rest[0] as i8 as i64;
            let total = offset + 1;
            let mut insn =
                make_insn(addr, total, opcode as u32, Opcode::Mov, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(reg_idx, 8)));
            insn.push_operand(Operand::SignedImm(imm));
            Ok(insn)
        }

        // --- LEA r, m (0x8D) ---
        0x8D => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Lea),

        // --- ADD r/m, r (0x01) ---
        0x01 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Add, false),

        // --- ADD r, r/m (0x03) ---
        0x03 => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Add),

        // --- ADD r/m, imm32 / SUB / CMP / AND / OR / XOR (0x81, 0x83) ---
        0x81 | 0x83 => decode_group1_imm(rest, addr, prefixes, offset, opcode),

        // --- ADD AL/RAX, imm (0x05) ---
        0x05 => decode_accum_imm(rest, addr, prefixes, offset, Opcode::Add),

        // --- SUB r/m, r (0x29) ---
        0x29 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Sub, false),

        // --- SUB r, r/m (0x2B) ---
        0x2B => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Sub),

        // --- SUB AL/RAX, imm (0x2D) ---
        0x2D => decode_accum_imm(rest, addr, prefixes, offset, Opcode::Sub),

        // --- CMP r/m, r (0x39) ---
        0x39 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Cmp, false),

        // --- CMP r, r/m (0x3B) ---
        0x3B => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Cmp),

        // --- CMP AL/RAX, imm (0x3D) ---
        0x3D => decode_accum_imm(rest, addr, prefixes, offset, Opcode::Cmp),

        // --- CMP r/m8, r8 (0x38) ---
        0x38 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Cmp, true),

        // --- CMP r/m8, imm8 (0x80 /7) and other Group 1 8-bit ---
        0x80 => decode_group1_imm8(rest, addr, prefixes, offset),

        // --- TEST r/m, r (0x85) ---
        0x85 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Test, false),

        // --- TEST AL/RAX, imm (0xA9) ---
        0xA9 => decode_accum_imm(rest, addr, prefixes, offset, Opcode::Test),

        // --- TEST r/m8, r8 (0x84) ---
        0x84 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Test, true),

        // --- AND r/m, r (0x21) ---
        0x21 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::And, false),

        // --- AND r, r/m (0x23) ---
        0x23 => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::And),

        // --- AND AL/RAX, imm (0x25) ---
        0x25 => decode_accum_imm(rest, addr, prefixes, offset, Opcode::And),

        // --- OR r/m, r (0x09) ---
        0x09 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Or, false),

        // --- OR r, r/m (0x0B) ---
        0x0B => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Or),

        // --- XOR r/m, r (0x31) ---
        0x31 => decode_modrm_rm_reg(rest, addr, prefixes, offset, Opcode::Xor, false),

        // --- XOR r, r/m (0x33) ---
        0x33 => decode_modrm_reg_rm(rest, addr, prefixes, offset, Opcode::Xor),

        // --- XOR AL/RAX, imm (0x35) ---
        0x35 => decode_accum_imm(rest, addr, prefixes, offset, Opcode::Xor),

        // --- INC/DEC/CALL/JMP/PUSH — Group 5 (0xFF) ---
        0xFF => decode_group5(rest, addr, prefixes, offset),

        // --- Unary Group 3: TEST/NOT/NEG/MUL/IMUL/DIV/IDIV (0xF7) ---
        0xF7 => decode_group3(rest, addr, prefixes, offset, false),

        // --- Unary Group 3 (8-bit): TEST/NOT/NEG/MUL/DIV (0xF6) ---
        0xF6 => decode_group3(rest, addr, prefixes, offset, true),

        // --- Shift Group 2: SHL/SHR/SAR r/m, imm8 (0xC1) ---
        0xC1 => decode_shift_imm(rest, addr, prefixes, offset),

        // --- Shift Group 2: SHL/SHR/SAR r/m, 1 (0xD1) ---
        0xD1 => decode_shift_one(rest, addr, prefixes, offset),

        // --- IMUL r, r/m, imm8 (0x6B) ---
        0x6B => decode_imul_imm8(rest, addr, prefixes, offset),

        // --- IMUL r, r/m, imm32 (0x69) ---
        0x69 => decode_imul_imm32(rest, addr, prefixes, offset),

        // --- CALL rel32 (0xE8) ---
        0xE8 => {
            if rest.len() < 4 {
                return Err(insufficient(offset + 4, rest.len()));
            }
            let rel = i32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]);
            let total = offset + 4;
            let target = addr.wrapping_add(total as u64).wrapping_add(rel as i64 as u64);
            let mut insn = make_insn(addr, total, 0xE8, Opcode::Call, ControlFlow::Call);
            insn.push_operand(Operand::PcRelAddr(target));
            Ok(insn)
        }

        // --- JMP rel32 (0xE9) ---
        0xE9 => {
            if rest.len() < 4 {
                return Err(insufficient(offset + 4, rest.len()));
            }
            let rel = i32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]);
            let total = offset + 4;
            let target = addr.wrapping_add(total as u64).wrapping_add(rel as i64 as u64);
            let mut insn = make_insn(addr, total, 0xE9, Opcode::Jmp, ControlFlow::Branch);
            insn.push_operand(Operand::PcRelAddr(target));
            Ok(insn)
        }

        // --- JMP rel8 (0xEB) ---
        0xEB => {
            if rest.is_empty() {
                return Err(insufficient(offset + 1, 0));
            }
            let rel = rest[0] as i8;
            let total = offset + 1;
            let target = addr.wrapping_add(total as u64).wrapping_add(rel as i64 as u64);
            let mut insn = make_insn(addr, total, 0xEB, Opcode::Jmp, ControlFlow::Branch);
            insn.push_operand(Operand::PcRelAddr(target));
            Ok(insn)
        }

        // --- Jcc rel8 (0x70-0x7F) ---
        0x70..=0x7F => {
            if rest.is_empty() {
                return Err(insufficient(offset + 1, 0));
            }
            let cc = opcode & 0x0F;
            let rel = rest[0] as i8;
            let total = offset + 1;
            let target = addr.wrapping_add(total as u64).wrapping_add(rel as i64 as u64);
            let mut insn =
                make_insn(addr, total, opcode as u32, Opcode::Jcc, ControlFlow::ConditionalBranch);
            insn.push_operand(Operand::Cond(x86_cc_to_condition(cc)));
            insn.push_operand(Operand::PcRelAddr(target));
            Ok(insn)
        }

        // --- RET near (0xC3) ---
        0xC3 => Ok(make_insn(addr, offset, 0xC3, Opcode::Ret, ControlFlow::Return)),

        // --- LEAVE (0xC9) ---
        0xC9 => Ok(make_insn(addr, offset, 0xC9, Opcode::Leave, ControlFlow::Fallthrough)),

        // --- INT3 (0xCC) ---
        0xCC => Ok(make_insn(addr, offset, 0xCC, Opcode::Int3, ControlFlow::Exception)),

        // --- CDQ/CQO (0x99) ---
        0x99 => {
            let op = if prefixes.rex.w { Opcode::Cqo } else { Opcode::Cdq };
            Ok(make_insn(addr, offset, 0x99, op, ControlFlow::Fallthrough))
        }

        // --- MOV r/m8, imm8 (0xC6 /0) ---
        0xC6 => {
            if rest.is_empty() {
                return Err(insufficient(offset + 1, 0));
            }
            let modrm = ModRM::decode(rest[0], prefixes);
            if modrm.reg & 0x07 != 0 {
                return Err(unknown_enc(addr, opcode));
            }
            let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, 8, addr)?;
            let imm_off = 1 + rm_result.extra_bytes;
            if rest.len() < imm_off + 1 {
                return Err(insufficient(offset + imm_off + 1, rest.len()));
            }
            let imm = rest[imm_off] as i8 as i64;
            let total = offset + imm_off + 1;
            let mut insn = make_insn(addr, total, 0xC6, Opcode::Mov, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            insn.push_operand(Operand::SignedImm(imm));
            Ok(insn)
        }

        // --- XCHG rAX, r (0x91-0x97) ---
        0x91..=0x97 => {
            let reg_idx = (opcode - 0x90) | if prefixes.rex.b { 8 } else { 0 };
            let width = prefixes.operand_size();
            let mut insn =
                make_insn(addr, offset, opcode as u32, Opcode::Xchg, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(0, width)));
            insn.push_operand(Operand::Reg(gpr(reg_idx, width)));
            Ok(insn)
        }

        // --- MOVSXD r, r/m32 (0x63 with REX.W) ---
        0x63 => {
            if prefixes.rex.w {
                // MOVSXD r64, r/m32 (sign-extend dword to qword)
                if rest.is_empty() {
                    return Err(insufficient(offset + 1, 0));
                }
                let modrm = ModRM::decode(rest[0], prefixes);
                let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, 32, addr)?;
                let total = offset + 1 + rm_result.extra_bytes;
                let mut insn =
                    make_insn(addr, total, 0x63, Opcode::Movsxd, ControlFlow::Fallthrough);
                insn.push_operand(Operand::Reg(gpr(modrm.reg, 64)));
                insn.push_operand(rm_result.operand);
                Ok(insn)
            } else {
                // Without REX.W, 0x63 is ARPL in 32-bit mode (not valid in 64-bit long mode
                // for normal use). Decode as MOVSXD with 32-bit operands for compatibility.
                if rest.is_empty() {
                    return Err(insufficient(offset + 1, 0));
                }
                let modrm = ModRM::decode(rest[0], prefixes);
                let op_width = prefixes.operand_size();
                let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
                let total = offset + 1 + rm_result.extra_bytes;
                let mut insn =
                    make_insn(addr, total, 0x63, Opcode::Movsxd, ControlFlow::Fallthrough);
                insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
                insn.push_operand(rm_result.operand);
                Ok(insn)
            }
        }

        // --- Shift Group 2: SHL/SHR/SAR r/m, CL (0xD3) ---
        0xD3 => decode_shift_cl(rest, addr, prefixes, offset),

        _ => Err(unknown_enc(addr, opcode)),
    }
}

/// Decode two-byte opcodes (0x0F xx).
fn decode_two_byte_opcode(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }

    let opcode2 = rest[0];
    let after = &rest[1..];
    let offset2 = offset + 1;

    match opcode2 {
        // --- Jcc rel32 (0x0F 0x80-0x8F) ---
        0x80..=0x8F => {
            if after.len() < 4 {
                return Err(insufficient(offset2 + 4, after.len()));
            }
            let cc = opcode2 & 0x0F;
            let rel = i32::from_le_bytes([after[0], after[1], after[2], after[3]]);
            let total = offset2 + 4;
            let target = addr.wrapping_add(total as u64).wrapping_add(rel as i64 as u64);
            let mut insn = make_insn(
                addr,
                total,
                0x0F00 | opcode2 as u32,
                Opcode::Jcc,
                ControlFlow::ConditionalBranch,
            );
            insn.push_operand(Operand::Cond(x86_cc_to_condition(cc)));
            insn.push_operand(Operand::PcRelAddr(target));
            Ok(insn)
        }

        // --- MOVZX r, r/m8 (0x0F B6) ---
        0xB6 => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 8, addr)?;
            let dst_width = prefixes.operand_size();
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0x0FB6, Opcode::Movzx, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(modrm.reg, dst_width)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- MOVZX r, r/m16 (0x0F B7) ---
        0xB7 => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 16, addr)?;
            let dst_width = prefixes.operand_size();
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0x0FB7, Opcode::Movzx, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(modrm.reg, dst_width)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- MOVSX r, r/m8 (0x0F BE) ---
        0xBE => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 8, addr)?;
            let dst_width = prefixes.operand_size();
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0x0FBE, Opcode::Movsx, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(modrm.reg, dst_width)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- MOVSX r, r/m16 (0x0F BF) ---
        0xBF => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 16, addr)?;
            let dst_width = prefixes.operand_size();
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0x0FBF, Opcode::Movsx, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(gpr(modrm.reg, dst_width)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- IMUL r, r/m (0x0F AF) ---
        0xAF => decode_modrm_reg_rm_2byte(after, addr, prefixes, offset2, Opcode::Imul),

        // --- SYSCALL (0x0F 05) ---
        0x05 => Ok(make_insn(addr, offset2, 0x0F05, Opcode::Syscall, ControlFlow::Exception)),

        // --- NOP / ENDBR64 area (0x0F 1E) ---
        0x1E => {
            // ENDBR64: F3 0F 1E FA
            if prefixes.has_rep() && !after.is_empty() && after[0] == 0xFA {
                Ok(make_insn(addr, offset2 + 1, 0x0F1E, Opcode::Endbr64, ControlFlow::Fallthrough))
            } else {
                // Multi-byte NOP (0x0F 1E + ModR/M)
                if after.is_empty() {
                    return Err(insufficient(offset2 + 1, 0));
                }
                let modrm = ModRM::decode(after[0], prefixes);
                let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 32, addr)?;
                let total = offset2 + 1 + rm_result.extra_bytes;
                Ok(make_insn(addr, total, 0x0F1E, Opcode::Nop, ControlFlow::Fallthrough))
            }
        }

        // --- Multi-byte NOP (0x0F 1F /0) ---
        0x1F => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 32, addr)?;
            let total = offset2 + 1 + rm_result.extra_bytes;
            Ok(make_insn(addr, total, 0x0F1F, Opcode::Nop, ControlFlow::Fallthrough))
        }

        // --- CMOVcc r, r/m (0x0F 40-4F) ---
        0x40..=0x4F => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let cc = opcode2 & 0x0F;
            let modrm = ModRM::decode(after[0], prefixes);
            let op_width = prefixes.operand_size();
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, op_width, addr)?;
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(
                addr,
                total,
                0x0F00 | opcode2 as u32,
                Opcode::Cmovcc,
                ControlFlow::Fallthrough,
            );
            insn.push_operand(Operand::Cond(x86_cc_to_condition(cc)));
            insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- SETcc r/m8 (0x0F 90-9F) ---
        0x90..=0x9F => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let cc = opcode2 & 0x0F;
            let modrm = ModRM::decode(after[0], prefixes);
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, 8, addr)?;
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(
                addr,
                total,
                0x0F00 | opcode2 as u32,
                Opcode::Setcc,
                ControlFlow::Fallthrough,
            );
            insn.push_operand(Operand::Cond(x86_cc_to_condition(cc)));
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }

        // --- CMPXCHG r/m, r (0x0F B1) ---
        0xB1 => {
            if after.is_empty() {
                return Err(insufficient(offset2 + 1, 0));
            }
            let modrm = ModRM::decode(after[0], prefixes);
            let op_width = prefixes.operand_size();
            let rm_result = decode_rm_operand(&modrm, &after[1..], prefixes, op_width, addr)?;
            let total = offset2 + 1 + rm_result.extra_bytes;
            let mut insn =
                make_insn(addr, total, 0x0FB1, Opcode::Cmpxchg, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
            Ok(insn)
        }

        // --- BSF r, r/m (0x0F BC) ---
        0xBC => decode_modrm_reg_rm_2byte(after, addr, prefixes, offset2, Opcode::Bsf),

        // --- BSR r, r/m (0x0F BD) ---
        0xBD => decode_modrm_reg_rm_2byte(after, addr, prefixes, offset2, Opcode::Bsr),

        _ => Err(unknown_enc(addr, opcode2)),
    }
}

// === Common decode patterns ===

/// Decode ModR/M instruction: dst=r/m, src=reg. If `is_8bit`, operands are 8-bit.
fn decode_modrm_rm_reg(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode: Opcode,
    is_8bit: bool,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = if is_8bit { 8 } else { prefixes.operand_size() };
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;
    let enc = opcode_to_enc(opcode);
    let mut insn = make_insn(addr, total, enc, opcode, opcode_flow(opcode));
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
    Ok(insn)
}

/// Decode ModR/M instruction: dst=reg, src=r/m.
fn decode_modrm_reg_rm(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode: Opcode,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;
    let enc = opcode_to_enc(opcode);
    let mut insn = make_insn(addr, total, enc, opcode, opcode_flow(opcode));
    insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
    insn.push_operand(rm_result.operand);
    Ok(insn)
}

/// Decode ModR/M instruction with 8-bit operands: dst=reg, src=r/m8.
fn decode_modrm_reg_rm_8bit(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode: Opcode,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, 8, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;
    let enc = opcode_to_enc(opcode);
    let mut insn = make_insn(addr, total, enc, opcode, opcode_flow(opcode));
    insn.push_operand(Operand::Reg(gpr(modrm.reg, 8)));
    insn.push_operand(rm_result.operand);
    Ok(insn)
}

/// Decode two-byte ModR/M instruction: dst=reg, src=r/m.
fn decode_modrm_reg_rm_2byte(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode: Opcode,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;
    let enc = opcode_to_enc(opcode);
    let mut insn = make_insn(addr, total, enc, opcode, opcode_flow(opcode));
    insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
    insn.push_operand(rm_result.operand);
    Ok(insn)
}

/// Decode accumulator + immediate (e.g., ADD RAX, imm32).
fn decode_accum_imm(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode: Opcode,
) -> Result<Instruction, DisasmError> {
    let op_width = prefixes.operand_size();
    let imm_size = if op_width == 16 { 2 } else { 4 };
    if rest.len() < imm_size {
        return Err(insufficient(offset + imm_size, rest.len()));
    }
    let imm = read_imm_signed(rest, imm_size);
    let total = offset + imm_size;
    let mut insn = make_insn(addr, total, opcode_to_enc(opcode), opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr(0, op_width)));
    insn.push_operand(Operand::SignedImm(imm));
    Ok(insn)
}

/// Decode Group 1 (0x81/0x83): ADD/OR/ADC/SBB/AND/SUB/XOR/CMP r/m, imm.
fn decode_group1_imm(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    opcode_byte: u8,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;

    let opcode = group1_opcode(modrm.reg & 0x07);

    let imm_off = 1 + rm_result.extra_bytes;
    let imm_size = if opcode_byte == 0x83 {
        1 // sign-extended imm8
    } else if op_width == 16 {
        2
    } else {
        4 // imm32 (sign-extended to 64 if REX.W)
    };

    if rest.len() < imm_off + imm_size {
        return Err(insufficient(offset + imm_off + imm_size, rest.len()));
    }
    let imm = read_imm_signed(&rest[imm_off..], imm_size);
    let total = offset + imm_off + imm_size;

    let mut insn = make_insn(addr, total, opcode_byte as u32, opcode, ControlFlow::Fallthrough);
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::SignedImm(imm));
    Ok(insn)
}

/// Decode Group 1 8-bit (0x80): ADD/OR/AND/SUB/XOR/CMP r/m8, imm8.
fn decode_group1_imm8(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, 8, addr)?;
    let opcode = group1_opcode(modrm.reg & 0x07);
    let imm_off = 1 + rm_result.extra_bytes;
    if rest.len() < imm_off + 1 {
        return Err(insufficient(offset + imm_off + 1, rest.len()));
    }
    let imm = rest[imm_off] as i8 as i64;
    let total = offset + imm_off + 1;
    let mut insn = make_insn(addr, total, 0x80, opcode, ControlFlow::Fallthrough);
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::SignedImm(imm));
    Ok(insn)
}

/// Decode Group 3 (0xF7/0xF6): TEST/NOT/NEG/MUL/IMUL/DIV/IDIV.
fn decode_group3(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
    is_8bit: bool,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = if is_8bit { 8 } else { prefixes.operand_size() };
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;

    let reg_field = modrm.reg & 0x07;

    match reg_field {
        0 => {
            // TEST r/m, imm
            let imm_off = 1 + rm_result.extra_bytes;
            let imm_size = if is_8bit {
                1
            } else if op_width == 16 {
                2
            } else {
                4
            };
            if rest.len() < imm_off + imm_size {
                return Err(insufficient(offset + imm_off + imm_size, rest.len()));
            }
            let imm = read_imm_signed(&rest[imm_off..], imm_size);
            let total = offset + imm_off + imm_size;
            let enc = if is_8bit { 0xF6u32 } else { 0xF7 };
            let mut insn = make_insn(addr, total, enc, Opcode::Test, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            insn.push_operand(Operand::SignedImm(imm));
            Ok(insn)
        }
        2 => {
            // NOT r/m
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Not, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        3 => {
            // NEG r/m
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Neg, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        4 => {
            // MUL r/m
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Mul, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        5 => {
            // IMUL r/m (single operand)
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Imul, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        6 => {
            // DIV r/m
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Div, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        7 => {
            // IDIV r/m
            let total = offset + 1 + rm_result.extra_bytes;
            let mut insn = make_insn(addr, total, 0xF7, Opcode::Idiv, ControlFlow::Fallthrough);
            insn.push_operand(rm_result.operand);
            Ok(insn)
        }
        _ => Err(unknown_enc(addr, 0xF7)),
    }
}

/// Decode Group 5 (0xFF): INC/DEC/CALL/JMP/PUSH.
fn decode_group5(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;
    let reg_field = modrm.reg & 0x07;

    let (opcode, flow) = match reg_field {
        0 => (Opcode::Inc, ControlFlow::Fallthrough),
        1 => (Opcode::Dec, ControlFlow::Fallthrough),
        2 => (Opcode::Call, ControlFlow::Call),  // CALL r/m64
        4 => (Opcode::Jmp, ControlFlow::Branch), // JMP r/m64
        6 => (Opcode::Push, ControlFlow::Fallthrough), // PUSH r/m64
        _ => return Err(unknown_enc(addr, 0xFF)),
    };

    let mut insn = make_insn(addr, total, 0xFF, opcode, flow);
    insn.push_operand(rm_result.operand);
    Ok(insn)
}

/// Decode shift with imm8 (0xC1): SHL/SHR/SAR r/m, imm8.
fn decode_shift_imm(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let imm_off = 1 + rm_result.extra_bytes;
    if rest.len() < imm_off + 1 {
        return Err(insufficient(offset + imm_off + 1, rest.len()));
    }
    let shift_amount = rest[imm_off];
    let total = offset + imm_off + 1;

    let opcode = shift_opcode(modrm.reg & 0x07)?;

    let mut insn = make_insn(addr, total, 0xC1, opcode, ControlFlow::Fallthrough);
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::Imm(shift_amount as u64));
    Ok(insn)
}

/// Decode shift by 1 (0xD1): SHL/SHR/SAR r/m, 1.
fn decode_shift_one(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;

    let opcode = shift_opcode(modrm.reg & 0x07)?;

    let mut insn = make_insn(addr, total, 0xD1, opcode, ControlFlow::Fallthrough);
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::Imm(1));
    Ok(insn)
}

/// Decode shift by CL (0xD3): SHL/SHR/SAR r/m, CL.
fn decode_shift_cl(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let total = offset + 1 + rm_result.extra_bytes;

    let opcode = shift_opcode(modrm.reg & 0x07)?;

    let mut insn = make_insn(addr, total, 0xD3, opcode, ControlFlow::Fallthrough);
    insn.push_operand(rm_result.operand);
    // CL is register index 1, 8-bit
    insn.push_operand(Operand::Reg(gpr(1, 8)));
    Ok(insn)
}

/// Decode IMUL r, r/m, imm8 (0x6B).
fn decode_imul_imm8(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let imm_off = 1 + rm_result.extra_bytes;
    if rest.len() < imm_off + 1 {
        return Err(insufficient(offset + imm_off + 1, rest.len()));
    }
    let imm = rest[imm_off] as i8 as i64;
    let total = offset + imm_off + 1;
    let mut insn = make_insn(addr, total, 0x6B, Opcode::Imul, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::SignedImm(imm));
    Ok(insn)
}

/// Decode IMUL r, r/m, imm32 (0x69).
fn decode_imul_imm32(
    rest: &[u8],
    addr: u64,
    prefixes: &Prefixes,
    offset: usize,
) -> Result<Instruction, DisasmError> {
    if rest.is_empty() {
        return Err(insufficient(offset + 1, 0));
    }
    let modrm = ModRM::decode(rest[0], prefixes);
    let op_width = prefixes.operand_size();
    let rm_result = decode_rm_operand(&modrm, &rest[1..], prefixes, op_width, addr)?;
    let imm_off = 1 + rm_result.extra_bytes;
    let imm_size = if op_width == 16 { 2 } else { 4 };
    if rest.len() < imm_off + imm_size {
        return Err(insufficient(offset + imm_off + imm_size, rest.len()));
    }
    let imm = read_imm_signed(&rest[imm_off..], imm_size);
    let total = offset + imm_off + imm_size;
    let mut insn = make_insn(addr, total, 0x69, Opcode::Imul, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(gpr(modrm.reg, op_width)));
    insn.push_operand(rm_result.operand);
    insn.push_operand(Operand::SignedImm(imm));
    Ok(insn)
}

// === Helpers ===

/// Create an instruction with variable size.
fn make_insn(
    addr: u64,
    total_len: usize,
    encoding: u32,
    opcode: Opcode,
    flow: ControlFlow,
) -> Instruction {
    Instruction::with_size(addr, total_len as u8, encoding, opcode, flow)
}

/// Map Group 1 /reg field to opcode.
fn group1_opcode(reg: u8) -> Opcode {
    match reg {
        0 => Opcode::Add,
        1 => Opcode::Or,
        // 2 => ADC (not yet in our Opcode enum)
        // 3 => SBB (not yet in our Opcode enum)
        4 => Opcode::And,
        5 => Opcode::Sub,
        6 => Opcode::Xor,
        7 => Opcode::Cmp,
        _ => Opcode::Unknown,
    }
}

/// Map shift /reg field to opcode.
fn shift_opcode(reg: u8) -> Result<Opcode, DisasmError> {
    match reg {
        4 => Ok(Opcode::Shl),
        5 => Ok(Opcode::Shr),
        7 => Ok(Opcode::Sar),
        _ => Ok(Opcode::Unknown), // ROL, ROR, RCL, RCR not yet supported
    }
}

/// Map x86 condition code (4 bits) to our Condition enum.
/// x86 CCs: 0=O, 1=NO, 2=B/C, 3=NB/NC, 4=Z/E, 5=NZ/NE,
/// 6=BE/NA, 7=A/NBE, 8=S, 9=NS, A=P, B=NP, C=L/NGE,
/// D=NL/GE, E=LE/NG, F=NLE/G
fn x86_cc_to_condition(cc: u8) -> Condition {
    match cc & 0x0F {
        0x0 => Condition::Vs, // O (overflow) -> Vs
        0x1 => Condition::Vc, // NO -> Vc
        0x2 => Condition::Cs, // B/C (carry set) -> Cs (= below)
        0x3 => Condition::Cc, // NB/NC -> Cc
        0x4 => Condition::Eq, // Z/E -> Eq
        0x5 => Condition::Ne, // NZ/NE -> Ne
        0x6 => Condition::Ls, // BE (below or equal) -> Ls
        0x7 => Condition::Hi, // A (above) -> Hi
        0x8 => Condition::Mi, // S (sign) -> Mi
        0x9 => Condition::Pl, // NS -> Pl
        // 0xA => Parity (no direct AArch64 equivalent, use Al as placeholder)
        0xA => Condition::Al,
        // 0xB => No parity
        0xB => Condition::Al,
        0xC => Condition::Lt, // L (less) -> Lt
        0xD => Condition::Ge, // GE (greater or equal) -> Ge
        0xE => Condition::Le, // LE -> Le
        0xF => Condition::Gt, // G (greater) -> Gt
        _ => Condition::Al,
    }
}

/// Read a signed immediate of 1, 2, 4, or 8 bytes.
fn read_imm_signed(bytes: &[u8], size: usize) -> i64 {
    match size {
        1 => bytes[0] as i8 as i64,
        2 => i16::from_le_bytes([bytes[0], bytes[1]]) as i64,
        4 => i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as i64,
        8 => i64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]),
        _ => 0,
    }
}

/// Read an unsigned immediate of 1, 2, 4, or 8 bytes.
fn read_imm_unsigned(bytes: &[u8], size: usize) -> u64 {
    match size {
        1 => bytes[0] as u64,
        2 => u16::from_le_bytes([bytes[0], bytes[1]]) as u64,
        4 => u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64,
        8 => u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]),
        _ => 0,
    }
}

fn insufficient(needed: usize, available: usize) -> DisasmError {
    DisasmError::InsufficientBytes { needed, available }
}

fn unknown_enc(addr: u64, opcode: u8) -> DisasmError {
    DisasmError::UnknownEncoding { encoding: opcode as u32, address: addr }
}

fn opcode_to_enc(opcode: Opcode) -> u32 {
    // Return a representative encoding byte for the opcode (for the encoding field).
    match opcode {
        Opcode::Mov => 0x89,
        Opcode::Add => 0x01,
        Opcode::Sub => 0x29,
        Opcode::Cmp => 0x39,
        Opcode::Test => 0x85,
        Opcode::And => 0x21,
        Opcode::Or => 0x09,
        Opcode::Xor => 0x31,
        Opcode::Lea => 0x8D,
        Opcode::Imul => 0x0FAF,
        Opcode::Movsxd => 0x63,
        Opcode::Cmpxchg => 0x0FB1,
        Opcode::Bsf => 0x0FBC,
        Opcode::Bsr => 0x0FBD,
        _ => 0,
    }
}

fn opcode_flow(opcode: Opcode) -> ControlFlow {
    match opcode {
        Opcode::Call => ControlFlow::Call,
        Opcode::Jmp => ControlFlow::Branch,
        Opcode::Jcc => ControlFlow::ConditionalBranch,
        Opcode::Ret => ControlFlow::Return,
        Opcode::Int3 | Opcode::Syscall => ControlFlow::Exception,
        _ => ControlFlow::Fallthrough,
    }
}
