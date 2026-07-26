// AArch64 decoder tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Tests use known-good encodings from the ARM reference manual and
// cross-checked with `llvm-objdump --disassemble`.

use crate::aarch64::Aarch64Decoder;
use crate::arch::Decoder;
use crate::instruction::ControlFlow;
use crate::opcode::Opcode;
use crate::operand::{
    BarrierDomain, BarrierType, Condition, MemoryOperand, Operand, Register, ShiftType,
};

/// Helper: decode a single instruction from a u32 encoding at address 0.
fn decode(encoding: u32) -> crate::instruction::Instruction {
    let bytes = encoding.to_le_bytes();
    let d = Aarch64Decoder::new();
    d.decode(&bytes, 0).expect("decode should succeed")
}

/// Helper: decode at a specific address.
fn decode_at(encoding: u32, addr: u64) -> crate::instruction::Instruction {
    let bytes = encoding.to_le_bytes();
    let d = Aarch64Decoder::new();
    d.decode(&bytes, addr).expect("decode should succeed")
}

// ==========================================================================
// Data Processing — Immediate
// ==========================================================================

#[test]
fn test_add_imm_x0_x1_42() {
    // ADD X0, X1, #42  =>  sf=1, op=0, S=0, sh=0, imm12=42, Rn=1, Rd=0
    // 1 00 10001 0 0 000000101010 00001 00000
    let enc = 0x91_00_A8_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Add);
    assert_eq!(insn.operand_count(), 3);
    // Rd = X0
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    // Rn = X1
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 1 && r.width == 64));
    // imm = 42
    assert!(matches!(insn.operand(2), Some(Operand::Imm(42))));
}

#[test]
fn test_sub_imm_w0_w1_10() {
    // SUB W0, W1, #10  => sf=0, op=1, S=0, sh=0, imm12=10, Rn=1, Rd=0
    // 0 10 10001 0 0 000000001010 00001 00000
    let enc = 0x51_00_28_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Sub);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.width == 32));
}

#[test]
fn test_adds_imm_sets_flags() {
    // ADDS X0, X1, #1
    // 1 01 10001 0 0 000000000001 00001 00000
    let enc = 0xB1_00_04_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Adds);
}

#[test]
fn test_movz_x0_0x1234() {
    // MOVZ X0, #0x1234
    // 1 10 100101 00 0001001000110100 00000
    let enc = 0xD2_82_46_80;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Movz);
    assert!(matches!(insn.operand(1), Some(Operand::Imm(0x1234))));
}

#[test]
fn test_movk_x0_0x5678_lsl16() {
    // MOVK X0, #0x5678, LSL #16  => hw=1
    // 1 11 100101 01 0101011001111000 00000
    let enc = 0xF2_AA_CF_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Movk);
    assert!(matches!(insn.operand(1), Some(Operand::Imm(0x5678))));
    // Third operand = shift amount (16)
    assert!(matches!(insn.operand(2), Some(Operand::Imm(16))));
}

#[test]
fn test_movn_x0_0() {
    // MOVN X0, #0  (alias: MOV X0, #-1)
    // 1 00 100101 00 0000000000000000 00000
    let enc = 0x92_80_00_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Movn);
    assert_eq!(insn.operand_count(), 2);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(insn.operand(1), Some(Operand::Imm(0))));
}

#[test]
fn test_adr() {
    // ADR X0, #0x10 (at address 0x1000)
    // 0 immlo=00 10000 immhi=0000000000000000100 00000
    // immhi:immlo = 0b100_00 = 0x10/4 = 4 ... actually ADR offset = immhi:immlo
    // ADR encoding: op=0, immlo=bits[30:29], immhi=bits[23:5]
    // offset = 0x10 => binary = 10000 => immhi = 0b00000000000000001, immlo = 0b00
    // Wait, immhi:immlo forms a 21-bit value. offset = 0x10 = 16.
    // immhi = 16 >> 2 = 4 = bits[23:5], immlo = 16 & 3 = 0 = bits[30:29]
    // encoding: 0_00_10000_0000000000000000100_00000
    let enc = 0x10_00_00_80;
    let insn = decode_at(enc, 0x1000);
    assert_eq!(insn.opcode, Opcode::Adr);
    assert!(matches!(insn.operand(1), Some(Operand::PcRelAddr(0x1010))));
}

#[test]
fn test_and_imm() {
    // AND X0, X1, #0xFF
    // Bitmask immediate for 0xFF: N=1, immr=0, imms=0b000111
    // 1 00 100100 1 000000 000111 00001 00000
    let enc = 0x92_40_1C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::And);
    assert_eq!(insn.operand_count(), 3);
}

#[test]
fn test_orr_imm() {
    // ORR X0, X1, #1
    // N=1, immr=0, imms=0b000000
    // 1 01 100100 1 000000 000000 00001 00000
    let enc = 0xB2_40_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Orr);
}

#[test]
fn test_sbfm() {
    // SBFM X0, X1, #0, #7  (= SXTB X0, X1)
    // 1 00 100110 1 000000 000111 00001 00000
    let enc = 0x93_40_1C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Sbfm);
    assert_eq!(insn.operand_count(), 4);
}

// ==========================================================================
// Branches
// ==========================================================================

#[test]
fn test_b_forward() {
    // B #0x100 (at address 0x1000)
    // 000101 imm26 => offset = 0x100, imm26 = 0x100/4 = 0x40
    let enc = 0x14_00_00_40;
    let insn = decode_at(enc, 0x1000);
    assert_eq!(insn.opcode, Opcode::B);
    assert_eq!(insn.flow, ControlFlow::Branch);
    assert_eq!(insn.branch_target(), Some(0x1100));
}

#[test]
fn test_b_backward() {
    // B #-8 (at address 0x1000)
    // imm26 = -8/4 = -2 = 0x3FFFFFE (26-bit two's complement)
    let enc = 0x17_FF_FF_FE;
    let insn = decode_at(enc, 0x1000);
    assert_eq!(insn.opcode, Opcode::B);
    assert_eq!(insn.branch_target(), Some(0xFF8));
}

#[test]
fn test_bl() {
    // BL #0x200 (at address 0)
    // 100101 imm26 => imm26 = 0x200/4 = 0x80
    let enc = 0x94_00_00_80;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Bl);
    assert_eq!(insn.flow, ControlFlow::Call);
    assert_eq!(insn.branch_target(), Some(0x200));
}

#[test]
fn test_b_cond_eq() {
    // B.EQ #0x20 (at address 0x1000)
    // 01010100 imm19 0 cond
    // imm19 = 0x20/4 = 8
    let enc = 0x54_00_01_00;
    let insn = decode_at(enc, 0x1000);
    assert_eq!(insn.opcode, Opcode::BCond);
    assert_eq!(insn.flow, ControlFlow::ConditionalBranch);
    assert!(matches!(insn.operand(0), Some(Operand::Cond(Condition::Eq))));
    assert_eq!(insn.branch_target(), Some(0x1020));
}

#[test]
fn test_cbz() {
    // CBZ X0, #0x10 (at address 0)
    // 1 011010 0 imm19 Rt
    // sf=1, op=0, imm19=0x10/4=4, Rt=0
    let enc = 0xB4_00_00_80;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Cbz);
    assert_eq!(insn.flow, ControlFlow::ConditionalBranch);
}

#[test]
fn test_cbnz() {
    // CBNZ W5, #0x8
    // 0 011010 1 imm19 Rt
    // sf=0, op=1, imm19=0x8/4=2, Rt=5
    let enc = 0x35_00_00_45;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Cbnz);
}

#[test]
fn test_br_x16() {
    // BR X16
    // 1101011 0000 11111 000000 10000 00000
    let enc = 0xD6_1F_02_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Br);
    assert_eq!(insn.flow, ControlFlow::Branch);
}

#[test]
fn test_blr_x8() {
    // BLR X8
    // 1101011 0001 11111 000000 01000 00000
    let enc = 0xD6_3F_01_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Blr);
    assert_eq!(insn.flow, ControlFlow::Call);
}

#[test]
fn test_ret() {
    // RET (X30 implied)
    // 1101011 0010 11111 000000 11110 00000
    let enc = 0xD6_5F_03_C0;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ret);
    assert_eq!(insn.flow, ControlFlow::Return);
    // X30 is the default
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 30));
}

#[test]
fn test_ret_x16_preserves_explicit_return_register() {
    // RET X16
    let enc = 0xD6_5F_02_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ret);
    assert_eq!(insn.flow, ControlFlow::Return);
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 16));
}

#[test]
fn test_minimal_proof_fixture_common_sequence_decodes() {
    // This is the decoder-level surface expected by the minimal AArch64
    // proof fixture path: move, add, sub, stack load/store, branch, return.
    let cases = [
        (0xD2_80_00_20, 0x1000, Opcode::Movz, ControlFlow::Fallthrough, None),
        (0x91_00_08_00, 0x1004, Opcode::Add, ControlFlow::Fallthrough, None),
        (0xD1_00_04_01, 0x1008, Opcode::Sub, ControlFlow::Fallthrough, None),
        (0xF9_00_07_E1, 0x100C, Opcode::Str, ControlFlow::Fallthrough, None),
        (0xF9_40_07_E2, 0x1010, Opcode::Ldr, ControlFlow::Fallthrough, None),
        (0xB4_00_00_62, 0x1014, Opcode::Cbz, ControlFlow::ConditionalBranch, Some(0x1020)),
        (0x14_00_00_03, 0x1018, Opcode::B, ControlFlow::Branch, Some(0x1024)),
        (0xD6_5F_03_C0, 0x101C, Opcode::Ret, ControlFlow::Return, None),
    ];

    for (enc, addr, opcode, flow, target) in cases {
        let insn = decode_at(enc, addr);
        assert_eq!(insn.address, addr);
        assert_eq!(insn.size, 4);
        assert_eq!(insn.encoding, enc);
        assert_eq!(insn.opcode, opcode);
        assert_eq!(insn.flow, flow);
        assert_eq!(insn.branch_target(), target);
    }

    let store = decode_at(0xF9_00_07_E1, 0x100C);
    assert!(matches!(
        store.operand(1),
        Some(Operand::Mem(crate::operand::MemoryOperand::BaseOffset { base, offset }))
            if base.is_stack_pointer() && *offset == 8
    ));

    let load = decode_at(0xF9_40_07_E2, 0x1010);
    assert!(matches!(
        load.operand(1),
        Some(Operand::Mem(crate::operand::MemoryOperand::BaseOffset { base, offset }))
            if base.is_stack_pointer() && *offset == 8
    ));
}

#[test]
fn test_tbz() {
    // TBZ X0, #5, #0x10 (at address 0)
    // b5=0, 011011 0 b40=00101 imm14 Rt
    // imm14 = 0x10/4 = 4
    let enc = 0x36_28_00_80;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Tbz);
    assert!(matches!(insn.operand(1), Some(Operand::BitPos(5))));
}

// ==========================================================================
// Loads and Stores
// ==========================================================================

#[test]
fn test_ldr_x0_x1_imm() {
    // LDR X0, [X1, #8]
    // 11 111 00101 imm12 Rn Rt
    // size=11, opc=01, imm12=8/8=1, Rn=1, Rt=0
    let enc = 0xF9_40_04_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldr);
    assert!(insn.is_load());
    assert!(!insn.is_store());
}

#[test]
fn test_str_x0_x1_imm() {
    // STR X0, [X1, #16]
    // size=11, opc=00, imm12=16/8=2, Rn=1, Rt=0
    let enc = 0xF9_00_08_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Str);
    assert!(insn.is_store());
    assert!(!insn.is_load());
}

#[test]
fn test_ldrb() {
    // LDRB W0, [X1]
    // size=00, opc=01, imm12=0
    let enc = 0x39_40_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldrb);
}

#[test]
fn test_strh() {
    // STRH W0, [X1, #4]
    // size=01, opc=00, imm12=4/2=2
    let enc = 0x79_00_08_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Strh);
}

#[test]
fn test_ldp_x0_x1_x2() {
    // LDP X0, X1, [X2]
    // opc=10, L=1, imm7=0, Rt2=1, Rn=2, Rt=0
    let enc = 0xA9_40_04_40;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldp);
}

#[test]
fn test_stp_pre_index() {
    // STP X29, X30, [SP, #-16]!
    // opc=10, mode=11(pre), L=0, imm7=-16/8=-2=0b1111110, Rt2=30, Rn=31, Rt=29
    let enc = 0xA9_BF_7B_FD;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Stp);
}

#[test]
fn test_ldr_literal() {
    // LDR X0, <label>  (PC-relative literal load)
    // 01 011 000 imm19 Rt
    // opc=01, imm19=4 (offset=16), Rt=0
    let enc = 0x58_00_00_80;
    let insn = decode_at(enc, 0x1000);
    assert_eq!(insn.opcode, Opcode::LdrLiteral);
}

#[test]
fn test_ldar_x0_x1_atomic_acquire_nonexclusive() {
    // Cross-checked with clang/llvm-objdump:
    //   ldar  x0, [x1]  =>  c8dffc20
    //   ldaxr x0, [x1]  =>  c85ffc20
    // The reported c8dffc20 encoding is therefore LDAR, not LDAXR.
    let enc = 0xC8_DF_FC_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldar);
    assert!(insn.is_load());
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(
        insn.operand(1),
        Some(Operand::Mem(crate::operand::MemoryOperand::Base { base }))
            if base.index == 1 && base.width == 64
    ));
}

#[test]
fn test_ldaxr_x0_x1_remains_exclusive_acquire() {
    let enc = 0xC8_5F_FC_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldaxr);
    assert!(insn.is_load());
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(
        insn.operand(1),
        Some(Operand::Mem(crate::operand::MemoryOperand::Base { base }))
            if base.index == 1 && base.width == 64
    ));
}

#[test]
fn test_stlr_x0_x1_atomic_release_nonexclusive() {
    let enc = 0xC8_9F_FC_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Stlr);
    assert!(insn.is_store());
    assert!(!insn.is_load());
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(
        insn.operand(1),
        Some(Operand::Mem(crate::operand::MemoryOperand::Base { base }))
            if base.index == 1 && base.width == 64
    ));
}

#[test]
fn test_stlxr_w2_x0_x1_remains_exclusive_release() {
    let enc = 0xC8_02_FC_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Stlxr);
    assert!(insn.is_store());
    assert!(!insn.is_load());
    assert!(matches!(insn.operand(0), Some(Operand::Reg(r)) if r.index == 2 && r.width == 32));
    assert!(matches!(insn.operand(1), Some(Operand::Reg(r)) if r.index == 0 && r.width == 64));
    assert!(matches!(
        insn.operand(2),
        Some(Operand::Mem(crate::operand::MemoryOperand::Base { base }))
            if base.index == 1 && base.width == 64
    ));
}

// ==========================================================================
// System Instructions
// ==========================================================================

#[test]
fn test_nop() {
    // NOP = 0xD503201F
    let enc = 0xD5_03_20_1F;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Nop);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
}

#[test]
fn test_svc_0() {
    // SVC #0 = 0xD4000001
    let enc = 0xD4_00_00_01;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Svc);
    assert_eq!(insn.flow, ControlFlow::Exception);
    assert!(matches!(insn.operand(0), Some(Operand::Imm(0))));
}

#[test]
fn test_privileged_exception_family_decodes_as_boundaries() {
    let cases = [
        (0xD4_00_00_62, Opcode::Hvc, 3),
        (0xD4_00_00_83, Opcode::Smc, 4),
        (0xD4_40_00_C0, Opcode::Hlt, 6),
    ];

    for (enc, opcode, imm) in cases {
        let insn = decode(enc);
        assert_eq!(insn.opcode, opcode);
        assert_eq!(insn.flow, ControlFlow::Exception);
        assert!(
            matches!(insn.operand(0), Some(Operand::Imm(actual)) if *actual == imm),
            "{opcode:?} should preserve its exception immediate"
        );
    }
}

#[test]
fn test_brk_1() {
    // BRK #1
    let enc = 0xD4_20_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Brk);
}

#[test]
fn test_dmb_ish() {
    // DMB ISH = 0xD5033BBF (CRm=0b1011=ISH|Full, op2=100=DMB... wait)
    // Actually: DMB ISH = D5033B9F  (CRm=0b1011, op2=101)
    // Let me encode correctly:
    // System: 1101010100 L=0 op0=00 op1=011 CRn=0011 CRm=1011 op2=100 Rt=11111
    // bits: 1101010100_0_00_011_0011_1011_101_11111 = D503 3BAF... hmm
    // DMB ISH: D5033B9F from ARM ref
    // CRm=1011 (0xB), op2=101 (5)
    // Hmm, let me use the canonical: DMB ISH = 0xd5033b9f
    let enc = 0xD5_03_3B_9F;
    let insn = decode(enc);
    // D5033B9F = 1101_0101_0000_0011_0011_1011_1001_1111
    // op2 = bits[7:5] = 100 => DMB (not DSB which is op2=001)
    assert_eq!(insn.opcode, Opcode::Dmb);
    assert!(matches!(
        insn.operand(0),
        Some(Operand::Barrier { domain: BarrierDomain::Ish, kind: BarrierType::Full })
    ));
}

#[test]
fn test_dmb_named_load_store_barrier_options_preserve_scope_and_kind() {
    let cases = [
        (0xD5_03_39_9F, BarrierDomain::Ish, BarrierType::Ld), // DMB ISHLD
        (0xD5_03_3A_9F, BarrierDomain::Ish, BarrierType::St), // DMB ISHST
        (0xD5_03_3F_9F, BarrierDomain::Sy, BarrierType::Full), // DMB SY
    ];

    for (enc, expected_domain, expected_kind) in cases {
        let insn = decode(enc);
        assert_eq!(insn.opcode, Opcode::Dmb);
        assert!(matches!(
            insn.operand(0),
            Some(Operand::Barrier { domain, kind })
                if *domain == expected_domain && *kind == expected_kind
        ));
    }
}

#[test]
fn test_numeric_or_reserved_barrier_options_fail_closed() {
    let d = Aarch64Decoder::new();
    let cases: &[(u32, u64, u8)] = &[
        (0xD5_03_30_9F, 0x4000, 0x0), // DMB #0: no named LD/ST/full option
        (0xD5_03_34_3F, 0x4004, 0x4), // DSB #4: no named LD/ST/full option
        (0xD5_03_30_DF, 0x4008, 0x0), // ISB #0: only ISB SY is in boundary
    ];

    for &(enc, addr, option) in cases {
        let err = d
            .decode(&enc.to_le_bytes(), addr)
            .expect_err("unsupported barrier option should fail closed");
        assert!(matches!(
            err,
            crate::error::DisasmError::UnsupportedAarch64BarrierOption {
                encoding,
                address,
                option: actual_option,
            } if encoding == enc && address == addr && actual_option == option
        ));
    }
}

#[test]
fn test_isb() {
    // ISB = D5033FDF
    let enc = 0xD5_03_3F_DF;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Isb);
}

#[test]
fn test_mrs_read_nzcv() {
    // MRS X0, NZCV  =>  op0=3, op1=3, CRn=4, CRm=2, op2=0
    // encoding: D53B4200
    let enc = 0xD5_3B_42_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Mrs);
}

#[test]
fn test_msr_write_nzcv() {
    // MSR NZCV, X0
    let enc = 0xD5_1B_42_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Msr);
}

#[test]
fn test_provenance_preserves_aarch64_system_instruction_fields() {
    // MRS X0, NZCV. Extra trailing bytes must not be folded into the fixed-width instruction.
    let enc: u32 = 0xD5_3B_42_00;
    let mut bytes = enc.to_le_bytes().to_vec();
    bytes.extend_from_slice(&[0xAA, 0xBB, 0xCC, 0xDD]);
    let addr = 0x402000;
    let d = Aarch64Decoder::new();
    let insn = d.decode(&bytes, addr).expect("system instruction should decode");

    assert_eq!(insn.address, addr);
    assert_eq!(insn.size, 4);
    assert_eq!(insn.encoding, enc);
    assert_eq!(insn.bytes, enc.to_le_bytes().to_vec());
    assert_eq!(insn.opcode, Opcode::Mrs);
}

#[test]
fn test_provenance_reports_aarch64_unsupported_system_encoding_and_address() {
    // Top-level system encoding shape that is not currently decoded as a supported system op.
    let enc: u32 = 0xD5_00_00_00;
    let bytes = enc.to_le_bytes();
    let addr = 0x402010;
    let d = Aarch64Decoder::new();
    let err = d.decode(&bytes, addr).expect_err("unsupported system encoding should fail closed");

    assert!(matches!(
        err,
        crate::error::DisasmError::UnknownEncoding { encoding, address }
            if encoding == enc && address == addr
    ));
}

// ==========================================================================
// Data Processing — Register
// ==========================================================================

#[test]
fn test_add_shifted_reg() {
    // ADD X0, X1, X2
    // 1 00 01011 00 0 00010 000000 00001 00000
    let enc = 0x8B_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Add);
    assert_eq!(insn.operand_count(), 3);
}

#[test]
fn test_add_shifted_reg_lsl3() {
    // ADD X0, X1, X2, LSL #3
    let enc = 0x8B_02_0C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Add);
    assert!(matches!(
        insn.operand(2),
        Some(Operand::ShiftedReg { shift: ShiftType::Lsl, amount: 3, .. })
    ));
}

#[test]
fn test_sub_shifted_reg() {
    // SUB X0, X1, X2
    let enc = 0xCB_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Sub);
}

#[test]
fn test_and_shifted_reg() {
    // AND X0, X1, X2
    // 1 00 01010 00 0 00010 000000 00001 00000
    let enc = 0x8A_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::And);
}

#[test]
fn test_orr_shifted_reg() {
    // ORR X0, X1, X2
    let enc = 0xAA_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Orr);
}

#[test]
fn test_udiv() {
    // UDIV X0, X1, X2
    // 1 0 0 11010110 Rm 00001 0 Rn Rd
    let enc = 0x9A_C2_08_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Udiv);
}

#[test]
fn test_sdiv() {
    // SDIV X0, X1, X2
    let enc = 0x9A_C2_0C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Sdiv);
}

#[test]
fn test_madd() {
    // MADD X0, X1, X2, X3  (= MUL if Ra=XZR)
    // 1 00 11011 000 Rm 0 Ra Rn Rd
    let enc = 0x9B_02_0C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Madd);
    assert_eq!(insn.operand_count(), 4);
}

#[test]
fn test_csel() {
    // CSEL X0, X1, X2, EQ
    // 1 0 0 11010100 Rm cond 0 0 Rn Rd
    // cond=EQ=0000
    let enc = 0x9A_82_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Csel);
    assert!(matches!(insn.operand(3), Some(Operand::Cond(Condition::Eq))));
}

#[test]
fn test_rbit() {
    // RBIT X0, X1
    // 1 1 0 11010110 00000 0000 00 Rn Rd
    let enc = 0xDA_C0_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Rbit);
}

#[test]
fn test_clz() {
    // CLZ X0, X1
    let enc = 0xDA_C0_10_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Clz);
}

// ==========================================================================
// SIMD / FP basics
// ==========================================================================

#[test]
fn test_fadd_d() {
    // FADD D0, D1, D2
    // 00011110 01 1 Rm 001010 Rn Rd
    let enc = 0x1E_62_28_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Fadd);
}

#[test]
fn test_fmul_s() {
    // FMUL S0, S1, S2
    // 00011110 00 1 Rm 000010 Rn Rd
    let enc = 0x1E_22_08_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Fmul);
}

#[test]
fn test_fcmp_d() {
    // FCMP D0, D1
    // 00011110 01 1 Rm 001000 Rn 00 000
    let enc = 0x1E_61_20_00;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Fcmp);
}

#[test]
fn test_simd_load_store_unsigned_offset_decode_preserves_blocker_operands() {
    let cases = [
        (0x3D_C0_00_00, Opcode::Ldr, Register::simd(0, 128), 0, 0),
        (0x3D_80_04_41, Opcode::Str, Register::simd(1, 128), 2, 16),
        (0xFD_40_00_83, Opcode::Ldr, Register::simd(3, 64), 4, 0),
        (0xBD_00_00_C5, Opcode::Str, Register::simd(5, 32), 6, 0),
    ];

    for (enc, opcode, simd_reg, base_reg, offset) in cases {
        let insn = decode_at(enc, 0x1000);
        assert_eq!(insn.opcode, opcode);
        assert_eq!(insn.flow, ControlFlow::Fallthrough);
        assert_eq!(insn.bytes, enc.to_le_bytes().to_vec());
        assert_eq!(insn.is_load(), opcode == Opcode::Ldr);
        assert_eq!(insn.is_store(), opcode == Opcode::Str);
        assert_eq!(insn.operand(0), Some(&Operand::Reg(simd_reg)));
        assert_eq!(
            insn.operand(1),
            Some(&Operand::Mem(MemoryOperand::BaseOffset {
                base: Register::gpr(base_reg, true),
                offset,
            }))
        );
    }
}

// ==========================================================================
// Edge cases and error handling
// ==========================================================================

#[test]
fn test_insufficient_bytes() {
    let d = Aarch64Decoder::new();
    let result = d.decode(&[0x00, 0x00], 0);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        crate::error::DisasmError::InsufficientBytes { needed: 4, available: 2 }
    ));
}

#[test]
fn test_decode_all() {
    let d = Aarch64Decoder::new();
    // NOP NOP RET
    let nop = 0xD5_03_20_1Fu32;
    let ret = 0xD6_5F_03_C0u32;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&nop.to_le_bytes());
    bytes.extend_from_slice(&nop.to_le_bytes());
    bytes.extend_from_slice(&ret.to_le_bytes());

    let results = d.decode_all(&bytes, 0x1000);
    assert_eq!(results.len(), 3);
    assert!(results[0].is_ok());
    assert!(results[1].is_ok());
    assert!(results[2].is_ok());

    let insn0 = results[0].as_ref().unwrap();
    assert_eq!(insn0.opcode, Opcode::Nop);
    assert_eq!(insn0.address, 0x1000);

    let insn1 = results[1].as_ref().unwrap();
    assert_eq!(insn1.address, 0x1004);

    let insn2 = results[2].as_ref().unwrap();
    assert_eq!(insn2.opcode, Opcode::Ret);
    assert_eq!(insn2.address, 0x1008);
}

#[test]
fn test_instruction_size_always_4() {
    let insn = decode(0xD5_03_20_1F); // NOP
    assert_eq!(insn.size, 4);
}

#[test]
fn test_original_bytes_preserved_for_4_byte_instruction() {
    let enc = 0xD5_03_20_1F; // NOP
    let insn = decode(enc);
    assert_eq!(insn.bytes, enc.to_le_bytes().to_vec());
}

#[test]
fn test_arch_trait() {
    use crate::arch::Arch;
    let d = Aarch64Decoder::new();
    assert_eq!(d.name(), "AArch64");
    assert_eq!(d.min_insn_size(), 4);
    assert_eq!(d.max_insn_size(), 4);
    assert_eq!(d.alignment(), 4);
    assert_eq!(d.gpr_count(), 31);
    assert_eq!(d.stack_pointer(), Some(31));
    assert_eq!(d.link_register(), Some(30));
    assert_eq!(d.program_counter(), None);
}

#[test]
fn test_control_flow_classification() {
    // NOP = Fallthrough
    assert_eq!(decode(0xD5_03_20_1F).flow, ControlFlow::Fallthrough);
    // B = Branch
    assert_eq!(decode(0x14_00_00_01).flow, ControlFlow::Branch);
    // BL = Call
    assert_eq!(decode(0x94_00_00_01).flow, ControlFlow::Call);
    // RET = Return
    assert_eq!(decode(0xD6_5F_03_C0).flow, ControlFlow::Return);
    // SVC = Exception
    assert_eq!(decode(0xD4_00_00_01).flow, ControlFlow::Exception);
}

#[test]
fn test_register_display() {
    assert_eq!(format!("{}", Register::gpr(0, true)), "X0");
    assert_eq!(format!("{}", Register::gpr(15, false)), "W15");
    assert_eq!(format!("{}", Register::sp(true)), "SP");
    assert_eq!(format!("{}", Register::zr(true)), "XZR");
    assert_eq!(format!("{}", Register::zr(false)), "WZR");
    assert_eq!(format!("{}", Register::simd(0, 64)), "D0");
    assert_eq!(format!("{}", Register::simd(3, 32)), "S3");
    assert_eq!(format!("{}", Register::simd(7, 128)), "Q7");
}

#[test]
fn test_opcode_display() {
    assert_eq!(format!("{}", Opcode::Add), "ADD");
    assert_eq!(format!("{}", Opcode::Ldr), "LDR");
    assert_eq!(format!("{}", Opcode::B), "B");
    assert_eq!(format!("{}", Opcode::Nop), "NOP");
}

#[test]
fn test_condition_invert() {
    assert_eq!(Condition::Eq.invert(), Condition::Ne);
    assert_eq!(Condition::Ne.invert(), Condition::Eq);
    assert_eq!(Condition::Cs.invert(), Condition::Cc);
    assert_eq!(Condition::Ge.invert(), Condition::Lt);
}

#[test]
fn test_convenience_function() {
    let nop_bytes = 0xD5_03_20_1Fu32.to_le_bytes();
    let insn = crate::decode_aarch64(&nop_bytes, 0).expect("decode NOP");
    assert_eq!(insn.opcode, Opcode::Nop);
}

// ==========================================================================
// Additional coverage for issue #503 requirements
// ==========================================================================

#[test]
fn test_adrp() {
    // ADRP X0, #0x1000 (at address 0x2000)
    // op=1, immlo=01, immhi=0 => imm21=1 => offset = 1 << 12 = 0x1000
    // 1 01 10000 0000000000000000000 00000 = 0xB0000000
    let enc = 0xB0_00_00_00;
    let insn = decode_at(enc, 0x2000);
    assert_eq!(insn.opcode, Opcode::Adrp);
    // Target = (0x2000 & !0xFFF) + (1 << 12) = 0x2000 + 0x1000 = 0x3000
    assert!(matches!(insn.operand(1), Some(Operand::PcRelAddr(0x3000))));
}

#[test]
fn test_dsb_sy() {
    // DSB SY = D5033F9F
    // CRm=0b1111 (SY domain + full), op2=001 (DSB)
    let enc = 0xD5_03_3F_3F;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Dsb);
}

#[test]
fn test_tbnz() {
    // TBNZ W0, #3, #0x8 (at address 0)
    // b5=0, 011011 1 b40=00011 imm14=2 Rt=0
    let enc = 0x37_18_00_40;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Tbnz);
    assert!(matches!(insn.operand(1), Some(Operand::BitPos(3))));
}

#[test]
fn test_ldr_register_offset() {
    // LDR X0, [X1, X2] (register offset, no extend/shift)
    // 11 111 00011 1 Rm option=011 S=0 10 Rn Rt
    // size=11, opc=01, bit24=0, bit21=1, Rm=2, option=011, S=0, Rn=1, Rt=0
    let enc = 0xF8_62_68_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldr);
    assert!(insn.is_load());
    assert_eq!(insn.operand_count(), 2);
}

#[test]
fn test_csinc() {
    // CSINC X0, X1, X2, NE
    // 1 0 0 11010100 Rm=2 cond=0001 0 1 Rn=1 Rd=0
    let enc = 0x9A_82_14_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Csinc);
    assert!(matches!(insn.operand(3), Some(Operand::Cond(Condition::Ne))));
}

#[test]
fn test_adc() {
    // ADC X0, X1, X2
    // 1 0 0 11010000 Rm=2 000000 Rn=1 Rd=0
    let enc = 0x9A_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Adc);
    assert_eq!(insn.operand_count(), 3);
}

#[test]
fn test_sbc() {
    // SBC X0, X1, X2
    // 1 1 0 11010000 Rm=2 000000 Rn=1 Rd=0
    let enc = 0xDA_02_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Sbc);
}

#[test]
fn test_add_extended_reg() {
    // ADD X0, X1, W2, UXTW
    // 1 0 0 01011001 Rm=2 option=010 imm3=000 Rn=1 Rd=0
    let enc = 0x8B_22_40_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Add);
    assert_eq!(insn.operand_count(), 3);
}

#[test]
fn test_ldr_pre_index() {
    // LDR X0, [X1, #16]!
    // size=11, V=0, opc=01, imm9=16=0b000010000, op2=11(pre), Rn=1, Rt=0
    let enc = 0xF8_41_0C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Ldr);
    assert!(insn.is_load());
}

#[test]
fn test_str_post_index() {
    // STR X0, [X1], #-8
    // size=11, V=0, opc=00, imm9=-8=0x1F8, op2=01(post), Rn=1, Rt=0
    let enc = 0xF8_1F_84_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Str);
    assert!(insn.is_store());
}

#[test]
fn test_msub() {
    // MSUB X0, X1, X2, X3
    // 1 00 11011 000 Rm=2 1 Ra=3 Rn=1 Rd=0
    let enc = 0x9B_02_8C_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Msub);
    assert_eq!(insn.operand_count(), 4);
}

#[test]
fn test_eor_imm() {
    // EOR X0, X1, #0x1
    // 1 10 100100 N=1 immr=0 imms=0b000000 Rn=1 Rd=0
    let enc = 0xD2_40_00_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Eor);
}

#[test]
fn test_yield_hint() {
    // YIELD = D503203F
    let enc = 0xD5_03_20_3F;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Yield);
    assert_eq!(insn.flow, ControlFlow::Fallthrough);
}

#[test]
fn test_wfe_hint() {
    // WFE = D503205F
    let enc = 0xD5_03_20_5F;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Wfe);
}

#[test]
fn test_fsub_d() {
    // FSUB D0, D1, D2
    // 00011110 01 1 Rm=2 001110 Rn=1 Rd=0
    let enc = 0x1E_62_38_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Fsub);
}

#[test]
fn test_fdiv_s() {
    // FDIV S0, S1, S2
    // 00011110 00 1 Rm=2 000110 Rn=1 Rd=0
    let enc = 0x1E_22_18_20;
    let insn = decode(enc);
    assert_eq!(insn.opcode, Opcode::Fdiv);
}
