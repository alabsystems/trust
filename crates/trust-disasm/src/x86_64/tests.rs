// x86-64 decoder tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Tests use known-good encodings from the Intel SDM and cross-checked
// with `objdump -d` on x86-64 Linux binaries.

use crate::arch::{Arch, Decoder};
use crate::instruction::ControlFlow;
use crate::opcode::Opcode;
use crate::operand::{Condition, MemoryOperand, Operand};
use crate::x86_64::X86_64Decoder;

/// Helper: decode bytes at address 0.
fn decode(bytes: &[u8]) -> crate::instruction::Instruction {
    let d = X86_64Decoder::new();
    d.decode(bytes, 0).expect("decode should succeed")
}

/// Helper: decode at a specific address.
fn decode_at(bytes: &[u8], addr: u64) -> crate::instruction::Instruction {
    let d = X86_64Decoder::new();
    d.decode(bytes, addr).expect("decode should succeed")
}

// ==========================================================================
// Architecture Trait
// ==========================================================================

#[test]
fn test_arch_trait() {
    let d = X86_64Decoder::new();
    assert_eq!(d.name(), "x86-64");
    assert_eq!(d.min_insn_size(), 1);
    assert_eq!(d.max_insn_size(), 15);
    assert_eq!(d.alignment(), 1);
    assert_eq!(d.gpr_count(), 16);
    assert_eq!(d.stack_pointer(), Some(4));
    assert_eq!(d.link_register(), None);
    assert_eq!(d.program_counter(), None);
}

// ==========================================================================
// NOP / RET / LEAVE / INT3
// ==========================================================================

#[test]
fn test_nop() {
    // 90 = NOP
    let insn = decode(&[0x90]);
    assert_eq!(insn.opcode, Opcode::Nop);
    assert_eq!(insn.size, 1);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
}

#[test]
fn test_original_bytes_preserved_for_1_byte_instruction() {
    let insn = decode(&[0x90, 0xCC]);
    assert_eq!(insn.opcode, Opcode::Nop);
    assert_eq!(insn.size, 1);
    assert_eq!(insn.bytes, vec![0x90]);
}

#[test]
fn test_ret() {
    // C3 = RET
    let insn = decode(&[0xC3]);
    assert_eq!(insn.opcode, Opcode::Ret);
    assert_eq!(insn.size, 1);
    assert_eq!(insn.flow, ControlFlow::Return);
}

#[test]
fn test_leave() {
    // C9 = LEAVE
    let insn = decode(&[0xC9]);
    assert_eq!(insn.opcode, Opcode::Leave);
    assert_eq!(insn.size, 1);
}

#[test]
fn test_int3() {
    // CC = INT3
    let insn = decode(&[0xCC]);
    assert_eq!(insn.opcode, Opcode::Int3);
    assert_eq!(insn.flow, ControlFlow::Exception);
}

// ==========================================================================
// PUSH / POP
// ==========================================================================

#[test]
fn test_push_rbp() {
    // 55 = PUSH RBP
    let insn = decode(&[0x55]);
    assert_eq!(insn.opcode, Opcode::Push);
    assert_eq!(insn.size, 1);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 5 && r.width == 64));
}

#[test]
fn test_push_rax() {
    // 50 = PUSH RAX
    let insn = decode(&[0x50]);
    assert_eq!(insn.opcode, Opcode::Push);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0));
}

#[test]
fn test_push_r12() {
    // 41 54 = PUSH R12 (REX.B + 0x54)
    let insn = decode(&[0x41, 0x54]);
    assert_eq!(insn.opcode, Opcode::Push);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 12));
}

#[test]
fn test_pop_rbp() {
    // 5D = POP RBP
    let insn = decode(&[0x5D]);
    assert_eq!(insn.opcode, Opcode::Pop);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 5));
}

// ==========================================================================
// MOV
// ==========================================================================

#[test]
fn test_mov_reg_reg_64() {
    // 48 89 E5 = MOV RBP, RSP (REX.W + MOV r/m64, r64)
    let insn = decode(&[0x48, 0x89, 0xE5]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 3);
    // dst = RBP (index 5), src = RSP (index 4)
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 5 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 4 && r.width == 64));
}

#[test]
fn test_original_bytes_preserved_for_3_byte_instruction() {
    let insn = decode(&[0x48, 0x89, 0xE5, 0x90]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 3);
    assert_eq!(insn.bytes, vec![0x48, 0x89, 0xE5]);
}

#[test]
fn test_mov_reg_reg_32() {
    // 89 C1 = MOV ECX, EAX
    let insn = decode(&[0x89, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 1 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
}

#[test]
fn test_mov_reg_imm32() {
    // B8 2A 00 00 00 = MOV EAX, 42
    let insn = decode(&[0xB8, 0x2A, 0x00, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 5);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(42))));
}

#[test]
fn test_mov_reg_imm64() {
    // 48 B8 xx xx xx xx xx xx xx xx = MOV RAX, imm64
    let insn = decode(&[0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 10);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Imm(0x12345678))));
}

#[test]
fn test_original_bytes_preserved_for_10_byte_instruction() {
    let bytes = [0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00, 0x90];
    let insn = decode(&bytes);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 10);
    assert_eq!(insn.bytes, bytes[..10].to_vec());
}

#[test]
fn test_provenance_preserves_long_variable_length_instruction() {
    // 48 B8 imm64 = MOV RAX, imm64. The legacy compact `encoding` stores the opcode;
    // `bytes` carries the exact variable-length instruction, excluding the trailing NOP.
    let bytes = [0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0xEF, 0xCD, 0xAB, 0x90, 0x90];
    let addr = 0x401080;
    let insn = decode_at(&bytes, addr);

    assert_eq!(insn.address, addr);
    assert_eq!(insn.size, 10);
    assert_eq!(insn.encoding, 0xB8);
    assert_eq!(insn.bytes, bytes[..10].to_vec());
    assert_eq!(insn.opcode, Opcode::Mov);
}

#[test]
fn test_mov_mem_reg() {
    // 48 89 45 F8 = MOV [RBP-8], RAX (REX.W + MOV r/m64,r64, ModRM=[01 000 101], disp8=-8)
    let insn = decode(&[0x48, 0x89, 0x45, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 4);
    // dst = [RBP - 8]
    match insn.operand(0) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -8);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
    // src = RAX
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0));
}

#[test]
fn test_mov_reg_mem() {
    // 48 8B 45 F8 = MOV RAX, [RBP-8]
    let insn = decode(&[0x48, 0x8B, 0x45, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    match insn.operand(1) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5);
            assert_eq!(*offset, -8);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

#[test]
fn test_mov_r8_imm8() {
    // B0 FF = MOV AL, 0xFF
    let insn = decode(&[0xB0, 0xFF]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 8));
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(-1))));
}

// ==========================================================================
// LEA
// ==========================================================================

#[test]
fn test_lea_rip_relative() {
    // 48 8D 05 xx xx xx xx = LEA RAX, [RIP+disp32]
    let insn = decode(&[0x48, 0x8D, 0x05, 0x10, 0x00, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Lea);
    assert_eq!(insn.size, 7);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0));
    assert!(matches!(
        insn.operand(1),
        Some(Operand::Mem(MemoryOperand::PcRelative { offset: 0x10 }))
    ));
}

// ==========================================================================
// ADD / SUB / CMP / AND / OR / XOR
// ==========================================================================

#[test]
fn test_add_reg_reg() {
    // 48 01 D0 = ADD RAX, RDX
    let insn = decode(&[0x48, 0x01, 0xD0]);
    assert_eq!(insn.opcode, Opcode::Add);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0)); // RAX
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 2)); // RDX
}

#[test]
fn test_sub_imm8() {
    // 48 83 EC 20 = SUB RSP, 0x20
    let insn = decode(&[0x48, 0x83, 0xEC, 0x20]);
    assert_eq!(insn.opcode, Opcode::Sub);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 4 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(0x20))));
}

#[test]
fn test_cmp_reg_reg() {
    // 48 39 C8 = CMP RAX, RCX
    let insn = decode(&[0x48, 0x39, 0xC8]);
    assert_eq!(insn.opcode, Opcode::Cmp);
    assert_eq!(insn.size, 3);
}

#[test]
fn test_cmp_imm8() {
    // 83 F8 00 = CMP EAX, 0
    let insn = decode(&[0x83, 0xF8, 0x00]);
    assert_eq!(insn.opcode, Opcode::Cmp);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(0))));
}

#[test]
fn test_and_reg_reg() {
    // 48 21 C8 = AND RAX, RCX
    let insn = decode(&[0x48, 0x21, 0xC8]);
    assert_eq!(insn.opcode, Opcode::And);
}

#[test]
fn test_or_reg_reg() {
    // 48 09 D0 = OR RAX, RDX
    let insn = decode(&[0x48, 0x09, 0xD0]);
    assert_eq!(insn.opcode, Opcode::Or);
}

#[test]
fn test_xor_reg_reg() {
    // 31 C0 = XOR EAX, EAX (common zero idiom)
    let insn = decode(&[0x31, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Xor);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
}

#[test]
fn test_xor_64bit() {
    // 48 31 C0 = XOR RAX, RAX
    let insn = decode(&[0x48, 0x31, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Xor);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.width == 64));
}

#[test]
fn test_test_reg_reg() {
    // 48 85 C0 = TEST RAX, RAX
    let insn = decode(&[0x48, 0x85, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Test);
}

// ==========================================================================
// Shifts
// ==========================================================================

#[test]
fn test_shl_imm8() {
    // 48 C1 E0 03 = SHL RAX, 3
    let insn = decode(&[0x48, 0xC1, 0xE0, 0x03]);
    assert_eq!(insn.opcode, Opcode::Shl);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(1), Some(Operand::Imm(3))));
}

#[test]
fn test_shr_imm8() {
    // 48 C1 E8 01 = SHR RAX, 1
    let insn = decode(&[0x48, 0xC1, 0xE8, 0x01]);
    assert_eq!(insn.opcode, Opcode::Shr);
}

#[test]
fn test_sar_one() {
    // 48 D1 F8 = SAR RAX, 1
    let insn = decode(&[0x48, 0xD1, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Sar);
    assert!(matches!(insn.operand(1), Some(Operand::Imm(1))));
}

// ==========================================================================
// CALL / JMP / Jcc / RET
// ==========================================================================

#[test]
fn test_call_rel32() {
    // E8 10 00 00 00 = CALL +0x10 (at address 0x1000)
    // Target = 0x1000 + 5 + 0x10 = 0x1015
    let insn = decode_at(&[0xE8, 0x10, 0x00, 0x00, 0x00], 0x1000);
    assert_eq!(insn.opcode, Opcode::Call);
    assert_eq!(insn.flow, ControlFlow::Call);
    assert_eq!(insn.size, 5);
    assert_eq!(insn.branch_target(), Some(0x1015));
}

#[test]
fn test_jmp_rel32() {
    // E9 FB FF FF FF = JMP -5 (at address 0x1000) -> target = 0x1000 + 5 + (-5) = 0x1000
    let insn = decode_at(&[0xE9, 0xFB, 0xFF, 0xFF, 0xFF], 0x1000);
    assert_eq!(insn.opcode, Opcode::Jmp);
    assert_eq!(insn.flow, ControlFlow::Branch);
    assert_eq!(insn.branch_target(), Some(0x1000));
}

#[test]
fn test_jmp_rel8() {
    // EB 0A = JMP +10 (at addr 0)
    // target = 0 + 2 + 10 = 12
    let insn = decode(&[0xEB, 0x0A]);
    assert_eq!(insn.opcode, Opcode::Jmp);
    assert_eq!(insn.size, 2);
    assert_eq!(insn.branch_target(), Some(12));
}

#[test]
fn test_je_rel8() {
    // 74 0A = JE +10 (at addr 0x1000)
    // target = 0x1000 + 2 + 10 = 0x100C
    let insn = decode_at(&[0x74, 0x0A], 0x1000);
    assert_eq!(insn.opcode, Opcode::Jcc);
    assert_eq!(insn.flow, ControlFlow::ConditionalBranch);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Eq))));
    assert_eq!(insn.branch_target(), Some(0x100C));
}

#[test]
fn test_jne_rel8() {
    // 75 F6 = JNE -10 (at addr 0x1000) -> target = 0x1000 + 2 + (-10) = 0xFF8
    let insn = decode_at(&[0x75, 0xF6], 0x1000);
    assert_eq!(insn.opcode, Opcode::Jcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Ne))));
    assert_eq!(insn.branch_target(), Some(0xFF8));
}

#[test]
fn test_jge_rel32() {
    // 0F 8D 00 01 00 00 = JGE +256 (at addr 0x1000) -> target = 0x1000 + 6 + 256 = 0x1106
    let insn = decode_at(&[0x0F, 0x8D, 0x00, 0x01, 0x00, 0x00], 0x1000);
    assert_eq!(insn.opcode, Opcode::Jcc);
    assert_eq!(insn.size, 6);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Ge))));
    assert_eq!(insn.branch_target(), Some(0x1106));
}

#[test]
fn test_jl_rel32() {
    // 0F 8C 10 00 00 00 = JL +16 (at addr 0)
    let insn = decode(&[0x0F, 0x8C, 0x10, 0x00, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Jcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Lt))));
}

// ==========================================================================
// MOVZX / MOVSX
// ==========================================================================

#[test]
fn test_movzx_r32_rm8() {
    // 0F B6 C1 = MOVZX EAX, CL
    let insn = decode(&[0x0F, 0xB6, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Movzx);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8));
}

#[test]
fn test_movsx_r64_rm8() {
    // 48 0F BE C1 = MOVSX RAX, CL
    let insn = decode(&[0x48, 0x0F, 0xBE, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Movsx);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8));
}

// ==========================================================================
// IMUL / IDIV / NEG / NOT
// ==========================================================================

#[test]
fn test_imul_r_rm() {
    // 48 0F AF C1 = IMUL RAX, RCX
    let insn = decode(&[0x48, 0x0F, 0xAF, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Imul);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

#[test]
fn test_imul_r_rm_imm8() {
    // 6B C1 0A = IMUL EAX, ECX, 10
    let insn = decode(&[0x6B, 0xC1, 0x0A]);
    assert_eq!(insn.opcode, Opcode::Imul);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(2), Some(Operand::SignedImm(10))));
}

#[test]
fn test_idiv() {
    // 48 F7 F9 = IDIV RCX
    let insn = decode(&[0x48, 0xF7, 0xF9]);
    assert_eq!(insn.opcode, Opcode::Idiv);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

#[test]
fn test_neg() {
    // 48 F7 D8 = NEG RAX
    let insn = decode(&[0x48, 0xF7, 0xD8]);
    assert_eq!(insn.opcode, Opcode::Neg);
}

#[test]
fn test_not() {
    // 48 F7 D0 = NOT RAX
    let insn = decode(&[0x48, 0xF7, 0xD0]);
    assert_eq!(insn.opcode, Opcode::Not);
}

// ==========================================================================
// INC / DEC
// ==========================================================================

#[test]
fn test_inc_via_ff() {
    // FF C0 = INC EAX (Group 5 /0)
    let insn = decode(&[0xFF, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Inc);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
}

#[test]
fn test_dec_via_ff() {
    // FF C8 = DEC EAX (Group 5 /1)
    let insn = decode(&[0xFF, 0xC8]);
    assert_eq!(insn.opcode, Opcode::Dec);
}

// ==========================================================================
// SYSCALL / ENDBR64
// ==========================================================================

#[test]
fn test_syscall() {
    // 0F 05 = SYSCALL
    let insn = decode(&[0x0F, 0x05]);
    assert_eq!(insn.opcode, Opcode::Syscall);
    assert_eq!(insn.flow, ControlFlow::Exception);
    assert_eq!(insn.size, 2);
}

#[test]
fn test_endbr64() {
    // F3 0F 1E FA = ENDBR64
    let insn = decode(&[0xF3, 0x0F, 0x1E, 0xFA]);
    assert_eq!(insn.opcode, Opcode::Endbr64);
    assert_eq!(insn.size, 4);
}

// ==========================================================================
// MOV with memory addressing modes
// ==========================================================================

#[test]
fn test_mov_reg_indirect() {
    // 8B 01 = MOV EAX, [RCX]
    let insn = decode(&[0x8B, 0x01]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0));
    assert!(
        matches!(insn.operand(1), Some(Operand::Mem(MemoryOperand::Base { base })) if base.index == 1)
    );
}

#[test]
fn test_mov_disp32() {
    // 48 8B 85 F0 FE FF FF = MOV RAX, [RBP-0x110]
    let insn = decode(&[0x48, 0x8B, 0x85, 0xF0, 0xFE, 0xFF, 0xFF]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert_eq!(insn.size, 7);
    match insn.operand(1) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -0x110);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

// ==========================================================================
// Group 1 (ADD/SUB/CMP/AND/OR/XOR with immediate)
// ==========================================================================

#[test]
fn test_add_imm32() {
    // 81 C0 00 01 00 00 = ADD EAX, 256
    let insn = decode(&[0x81, 0xC0, 0x00, 0x01, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Add);
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(256))));
}

#[test]
fn test_and_imm8() {
    // 83 E0 0F = AND EAX, 0x0F
    let insn = decode(&[0x83, 0xE0, 0x0F]);
    assert_eq!(insn.opcode, Opcode::And);
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(0x0F))));
}

#[test]
fn test_or_imm8() {
    // 83 C8 01 = OR EAX, 1
    let insn = decode(&[0x83, 0xC8, 0x01]);
    assert_eq!(insn.opcode, Opcode::Or);
}

#[test]
fn test_xor_imm8() {
    // 83 F0 FF = XOR EAX, -1
    let insn = decode(&[0x83, 0xF0, 0xFF]);
    assert_eq!(insn.opcode, Opcode::Xor);
    assert!(matches!(insn.operand(1), Some(Operand::SignedImm(-1))));
}

// ==========================================================================
// decode_all (variable-length stream)
// ==========================================================================

#[test]
fn test_decode_all() {
    let d = X86_64Decoder::new();
    // PUSH RBP; MOV RBP, RSP; SUB RSP, 0x20; RET
    let bytes = [
        0x55, // PUSH RBP
        0x48, 0x89, 0xE5, // MOV RBP, RSP
        0x48, 0x83, 0xEC, 0x20, // SUB RSP, 0x20
        0xC3, // RET
    ];
    let results = d.decode_all(&bytes, 0x1000);
    assert_eq!(results.len(), 4);

    let insn0 = results[0].as_ref().expect("push should decode");
    assert_eq!(insn0.opcode, Opcode::Push);
    assert_eq!(insn0.address, 0x1000);
    assert_eq!(insn0.size, 1);

    let insn1 = results[1].as_ref().expect("mov should decode");
    assert_eq!(insn1.opcode, Opcode::Mov);
    assert_eq!(insn1.address, 0x1001);
    assert_eq!(insn1.size, 3);

    let insn2 = results[2].as_ref().expect("sub should decode");
    assert_eq!(insn2.opcode, Opcode::Sub);
    assert_eq!(insn2.address, 0x1004);
    assert_eq!(insn2.size, 4);

    let insn3 = results[3].as_ref().expect("ret should decode");
    assert_eq!(insn3.opcode, Opcode::Ret);
    assert_eq!(insn3.address, 0x1008);
}

// ==========================================================================
// Error handling
// ==========================================================================

#[test]
fn test_empty_bytes() {
    let d = X86_64Decoder::new();
    let result = d.decode(&[], 0);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        crate::error::DisasmError::InsufficientBytes { needed: 1, available: 0 }
    ));
}

#[test]
fn test_truncated_instruction() {
    let d = X86_64Decoder::new();
    // E8 needs 4 more bytes for rel32
    let result = d.decode(&[0xE8, 0x00], 0);
    assert!(result.is_err());
}

// ==========================================================================
// REX prefix register extension
// ==========================================================================

#[test]
fn test_mov_r8_r9() {
    // 4D 89 C1 = MOV R9, R8 (REX.WRB)
    let insn = decode(&[0x4D, 0x89, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Mov);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 9 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 8 && r.width == 64));
}

// ==========================================================================
// Convenience function
// ==========================================================================

#[test]
fn test_convenience_function() {
    let insn = crate::decode_x86_64(&[0xC3], 0).expect("decode RET");
    assert_eq!(insn.opcode, Opcode::Ret);
}

// ==========================================================================
// Multi-byte NOP
// ==========================================================================

#[test]
fn test_multibyte_nop() {
    // 0F 1F 00 = NOP DWORD [RAX] (3-byte NOP)
    let insn = decode(&[0x0F, 0x1F, 0x00]);
    assert_eq!(insn.opcode, Opcode::Nop);
    assert_eq!(insn.size, 3);
}

#[test]
fn test_multibyte_nop_with_prefix() {
    // 66 0F 1F 44 00 00 = NOP WORD [RAX+RAX*1+0x0] (6-byte NOP with SIB)
    let insn = decode(&[0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]);
    assert_eq!(insn.opcode, Opcode::Nop);
    assert_eq!(insn.size, 6);
}

// ==========================================================================
// CALL indirect
// ==========================================================================

#[test]
fn test_call_indirect() {
    // FF D0 = CALL RAX (Group 5 /2, mod=11, rm=0)
    let insn = decode(&[0xFF, 0xD0]);
    assert_eq!(insn.opcode, Opcode::Call);
    assert_eq!(insn.flow, ControlFlow::Call);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0));
}

#[test]
fn test_jmp_indirect() {
    // FF E0 = JMP RAX (Group 5 /4, mod=11, rm=0)
    let insn = decode(&[0xFF, 0xE0]);
    assert_eq!(insn.opcode, Opcode::Jmp);
    assert_eq!(insn.flow, ControlFlow::Branch);
}

// ==========================================================================
// CMOVcc (conditional move, 0x0F 40-4F)
// ==========================================================================

#[test]
fn test_cmove_r64_rm64() {
    // 48 0F 44 C1 = CMOVE RAX, RCX (CMOVcc with cc=4 => E/Z)
    let insn = decode(&[0x48, 0x0F, 0x44, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Cmovcc);
    assert_eq!(insn.size, 4);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Eq))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(2), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

#[test]
fn test_cmovne_r32_rm32() {
    // 0F 45 D1 = CMOVNE EDX, ECX (cc=5 => NE/NZ)
    let insn = decode(&[0x0F, 0x45, 0xD1]);
    assert_eq!(insn.opcode, Opcode::Cmovcc);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Ne))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 2 && r.width == 32));
    assert!(matches!(insn.operand(2), Some(Operand::Reg(r)) if r.index == 1 && r.width == 32));
}

#[test]
fn test_cmovl_r64_mem() {
    // 48 0F 4C 45 F8 = CMOVL RAX, [RBP-8] (cc=0xC => L/NGE)
    let insn = decode(&[0x48, 0x0F, 0x4C, 0x45, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Cmovcc);
    assert_eq!(insn.size, 5);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Lt))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    match insn.operand(2) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -8);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

#[test]
fn test_cmovge_r32_rm32() {
    // 0F 4D C1 = CMOVGE EAX, ECX (cc=0xD => GE/NL)
    let insn = decode(&[0x0F, 0x4D, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Cmovcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Ge))));
}

#[test]
fn test_cmovb_r64_rm64() {
    // 48 0F 42 C1 = CMOVB RAX, RCX (cc=2 => B/C/NAE)
    let insn = decode(&[0x48, 0x0F, 0x42, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Cmovcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Cs))));
}

// ==========================================================================
// SETcc (set byte on condition, 0x0F 90-9F)
// ==========================================================================

#[test]
fn test_sete_r8() {
    // 0F 94 C0 = SETE AL (cc=4 => E/Z)
    let insn = decode(&[0x0F, 0x94, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Setcc);
    assert_eq!(insn.size, 3);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Eq))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 8));
}

#[test]
fn test_setne_r8() {
    // 0F 95 C1 = SETNE CL (cc=5 => NE/NZ)
    let insn = decode(&[0x0F, 0x95, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Setcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Ne))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8));
}

#[test]
fn test_setl_r8() {
    // 0F 9C C2 = SETL DL (cc=0xC => L/NGE)
    let insn = decode(&[0x0F, 0x9C, 0xC2]);
    assert_eq!(insn.opcode, Opcode::Setcc);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Lt))));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 2 && r.width == 8));
}

#[test]
fn test_setg_mem() {
    // 0F 9F 45 F0 = SETG [RBP-16] (cc=0xF => G/NLE)
    let insn = decode(&[0x0F, 0x9F, 0x45, 0xF0]);
    assert_eq!(insn.opcode, Opcode::Setcc);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Gt))));
    match insn.operand(1) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -16);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

// ==========================================================================
// MOVSXD (sign-extend dword to qword, 0x63)
// ==========================================================================

#[test]
fn test_movsxd_r64_r32() {
    // 48 63 C1 = MOVSXD RAX, ECX (REX.W + 0x63)
    let insn = decode(&[0x48, 0x63, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Movsxd);
    assert_eq!(insn.size, 3);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 32));
}

#[test]
fn test_movsxd_r64_mem() {
    // 48 63 45 FC = MOVSXD RAX, [RBP-4]
    let insn = decode(&[0x48, 0x63, 0x45, 0xFC]);
    assert_eq!(insn.opcode, Opcode::Movsxd);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    match insn.operand(1) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -4);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

#[test]
fn test_movsxd_r8_to_r15() {
    // 4C 63 C0 = MOVSXD R8, EAX (REX.WR)
    let insn = decode(&[0x4C, 0x63, 0xC0]);
    assert_eq!(insn.opcode, Opcode::Movsxd);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 8 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
}

// ==========================================================================
// Shift by CL (0xD3)
// ==========================================================================

#[test]
fn test_shl_cl() {
    // 48 D3 E0 = SHL RAX, CL (REX.W + 0xD3, /4)
    let insn = decode(&[0x48, 0xD3, 0xE0]);
    assert_eq!(insn.opcode, Opcode::Shl);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8)); // CL
}

#[test]
fn test_shr_cl() {
    // 48 D3 E8 = SHR RAX, CL (REX.W + 0xD3, /5)
    let insn = decode(&[0x48, 0xD3, 0xE8]);
    assert_eq!(insn.opcode, Opcode::Shr);
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8));
}

#[test]
fn test_sar_cl() {
    // D3 F8 = SAR EAX, CL (0xD3, /7)
    let insn = decode(&[0xD3, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Sar);
    assert_eq!(insn.size, 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 8));
}

// ==========================================================================
// CQO (0x99 with REX.W)
// ==========================================================================

#[test]
fn test_cqo() {
    // 48 99 = CQO (REX.W + CDQ)
    let insn = decode(&[0x48, 0x99]);
    assert_eq!(insn.opcode, Opcode::Cqo);
    assert_eq!(insn.size, 2);
}

#[test]
fn test_cdq_without_rexw() {
    // 99 = CDQ (without REX.W)
    let insn = decode(&[0x99]);
    assert_eq!(insn.opcode, Opcode::Cdq);
    assert_eq!(insn.size, 1);
}

// ==========================================================================
// CMPXCHG (0x0F B1)
// ==========================================================================

#[test]
fn test_cmpxchg_r64_r64() {
    // 48 0F B1 C8 = CMPXCHG RAX, RCX (REX.W + 0x0F B1)
    let insn = decode(&[0x48, 0x0F, 0xB1, 0xC8]);
    assert_eq!(insn.opcode, Opcode::Cmpxchg);
    assert_eq!(insn.size, 4);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

#[test]
fn test_cmpxchg_mem_r64() {
    // F0 48 0F B1 08 = LOCK CMPXCHG [RAX], RCX
    let insn = decode(&[0xF0, 0x48, 0x0F, 0xB1, 0x08]);
    assert_eq!(insn.opcode, Opcode::Cmpxchg);
    assert_eq!(insn.size, 5);
    match insn.operand(0) {
        Some(Operand::Mem(MemoryOperand::Base { base })) => {
            assert_eq!(base.index, 0); // RAX
        }
        other => panic!("expected Base, got: {other:?}"),
    }
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

// ==========================================================================
// BSF / BSR (0x0F BC/BD)
// ==========================================================================

#[test]
fn test_bsf_r64_r64() {
    // 48 0F BC C1 = BSF RAX, RCX
    let insn = decode(&[0x48, 0x0F, 0xBC, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Bsf);
    assert_eq!(insn.size, 4);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
}

#[test]
fn test_bsr_r32_r32() {
    // 0F BD C1 = BSR EAX, ECX
    let insn = decode(&[0x0F, 0xBD, 0xC1]);
    assert_eq!(insn.opcode, Opcode::Bsr);
    assert_eq!(insn.size, 3);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 32));
}

#[test]
fn test_bsf_r64_mem() {
    // 48 0F BC 45 F8 = BSF RAX, [RBP-8]
    let insn = decode(&[0x48, 0x0F, 0xBC, 0x45, 0xF8]);
    assert_eq!(insn.opcode, Opcode::Bsf);
    assert_eq!(insn.size, 5);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    match insn.operand(1) {
        Some(Operand::Mem(MemoryOperand::BaseOffset { base, offset })) => {
            assert_eq!(base.index, 5); // RBP
            assert_eq!(*offset, -8);
        }
        other => panic!("expected BaseOffset, got: {other:?}"),
    }
}

// ==========================================================================
// decode_all with new instructions
// ==========================================================================

#[test]
fn test_decode_all_with_new_insns() {
    let d = X86_64Decoder::new();
    // MOVSXD RAX, ECX; CQO; SHL RAX, CL; RET
    let bytes = [
        0x48, 0x63, 0xC1, // MOVSXD RAX, ECX
        0x48, 0x99, // CQO
        0x48, 0xD3, 0xE0, // SHL RAX, CL
        0xC3, // RET
    ];
    let results = d.decode_all(&bytes, 0x2000);
    assert_eq!(results.len(), 4);

    let insn0 = results[0].as_ref().expect("movsxd should decode");
    assert_eq!(insn0.opcode, Opcode::Movsxd);
    assert_eq!(insn0.address, 0x2000);
    assert_eq!(insn0.size, 3);

    let insn1 = results[1].as_ref().expect("cqo should decode");
    assert_eq!(insn1.opcode, Opcode::Cqo);
    assert_eq!(insn1.address, 0x2003);
    assert_eq!(insn1.size, 2);

    let insn2 = results[2].as_ref().expect("shl should decode");
    assert_eq!(insn2.opcode, Opcode::Shl);
    assert_eq!(insn2.address, 0x2005);
    assert_eq!(insn2.size, 3);

    let insn3 = results[3].as_ref().expect("ret should decode");
    assert_eq!(insn3.opcode, Opcode::Ret);
    assert_eq!(insn3.address, 0x2008);
}
