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
    // SOUNDNESS: `decode_dp_imm` routes bits[25:23] ∈ {010, 011} here, but only
    // 010 is "Add/subtract (immediate)". 011 is a DIFFERENT, POPULATED group —
    // ADDG/SUBG (FEAT_MTE, which also write a logical address TAG) and the
    // FEAT_CSSC min/max immediates. Measured against `objdump` over the sweep,
    // bit 23 = 1 produced 84,954 words this function decoded as a plain
    // ADD/SUB that no instruction encodes, plus 23,102 that ARE real
    // instructions and are NOT add/sub:
    //
    //   11c00020  smax w0, w1, #0   -> decoded as `Add`
    //   b1800000  subg              -> decoded as `Add`  (tagged add/subtract)
    //
    // `sh` is bit 22 alone; bit 23 was simply never read. A tagged add
    // presented to the gate as an untagged one models a register write the
    // hardware does not perform, and `smax` presented as `add` is arithmetic
    // that is wrong for every input where the operands differ.
    if bit(enc, 23) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

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

    let Some(imm_val) = decode_bitmask_immediate(n, imms, immr, sf) else {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    };

    // Rd is SP for AND/ORR/EOR, ZR for ANDS
    let rd_reg = if opc == 0b11 { gpr_or_zr(rd, sf) } else { gpr_or_sp(rd, sf) };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(rd_reg));
    insn.push_operand(Operand::Reg(gpr_or_zr(rn, sf)));
    insn.push_operand(Operand::Imm(imm_val));
    Ok(insn)
}

/// Decode a bitmask immediate (used by logical immediate instructions).
/// ARM DDI 0487 section C6.2, `DecodeBitMasks`.
///
/// Returns `None` for an encoding the architecture leaves UNDEFINED. That is a
/// REFUSAL, not a value: this decoder feeds the output gate's machine model, and
/// an unallocated encoding silently decoded as some plausible immediate lets the
/// model disagree with the hardware while still looking well-formed.
///
/// TWO OVERFLOWS USED TO LIVE HERE, and their consequences were not symmetric.
/// `1u64 << (s + 1)` with `s == 63`, and `1u64 << esize` with `esize == 64`,
/// both overflow — i.e. EVERY 64-bit logical immediate with a non-zero rotate.
/// With debug assertions ON that panics (aborting the compiler, which is not
/// fail-closed); with them OFF — which is how the shipped `trustc` is built —
/// it silently produced `#0`. So `eor x0, x0, #0x8000000000000000` decoded as
/// the IDENTITY, and the output gate certified it `Proven` with a
/// kernel-re-checkable grade against an identity spec, on machine code that is
/// wrong for every input. Measured: 27 such words in the 599-crate corpus.
fn decode_bitmask_immediate(n: u32, imms: u32, immr: u32, is_64: bool) -> Option<u64> {
    let reg_size = if is_64 { 64u32 } else { 32 };

    // Determine element size
    let len = highest_set_bit((n << 6) | (!imms & 0x3F), 7);
    if len < 1 {
        return None; // UNDEFINED: no element size is encoded.
    }
    let esize = 1u32 << len;
    let levels = esize - 1;

    let s = imms & levels;
    let r = immr & levels;

    // `S == levels` (an all-ones element) is UNDEFINED for the immediate forms:
    // that pattern is already expressible with a smaller element size, so the
    // encoding is reserved rather than redundant.
    if s == levels {
        return None;
    }

    // Create the element pattern. `s + 1` reaches 64 at `esize == 64`, where the
    // shift would overflow; the pattern there is every bit set.
    let ones = |count: u32| if count >= 64 { u64::MAX } else { (1u64 << count) - 1 };
    let welem = ones(s + 1);

    // Rotate right by r WITHIN the element.
    let elem = if r == 0 {
        welem
    } else {
        let mask = ones(esize);
        ((welem >> r) | (welem << (esize - r))) & mask
    };

    // Replicate to fill register width
    Some(replicate(elem, esize, reg_size))
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

    // `immr` and `imms` are 6-bit fields, but in the 32-bit form (sf=0/N=0) the
    // architecture fixes their top bit at 0: a bit position of 32..63 does not
    // exist in a W register. `objdump` answers `<unknown>` for all 23,816 such
    // words in the sweep; the CPU answers SIGILL.
    //
    // SOUNDNESS: this is the decode-side half of the `width - immr` underflow in
    // `trust-machine-sem`'s `sem_ubfm` / `sem_sbfm` / `sem_bfm`. With `width ==
    // 32` and `immr > 32` that subtraction wraps, and in a RELEASE build — how
    // `trustc` ships — it wraps SILENTLY to a huge shift amount rather than
    // panicking. The semantics now refuses that case outright as well; refusing
    // HERE is what keeps it unreachable in the first place.
    if !sf && (immr >= 32 || imms >= 32) {
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

    // EXTR is `sf op21(30:29) 100111 N o0(21) Rm imms Rn Rd` with op21 and o0
    // both FIXED at zero, and `imms<5>` fixed at zero in the 32-bit form. This
    // function read none of the three: 51,430 words in the sweep decoded as
    // `Extr` and are `<unknown>` to `objdump`.
    if bits(enc, 30, 29) != 0 || bit(enc, 21) != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }
    if !sf && imms >= 32 {
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
    // `decode_branch_sys` routes on bits[31:25] == 0101010 and never looks at
    // bit 24 or at `o0` (bit 4). B.cond is `0101 0100 imm19 0 cond`; both of
    // those are fixed fields.
    //
    // bit 24 = 1 is not a conditional branch at all (it is where `retaasppc`
    // and friends live): 39,538 ghost words plus 5,849 real, different
    // instructions in the sweep.
    if bit(enc, 24) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    // SOUNDNESS: `o0` = 1 is BC.cond (FEAT_HBC), a REAL and DIFFERENT branch —
    // 14,238 words, every one of which `objdump` names `bc.<cond>` and this
    // function used to hand back as `BCond`. It branches on the same condition,
    // so the two look interchangeable in a control-flow graph, but BC.cond is a
    // *consistent* branch: it carries an architectural hint that the branch is
    // not to be speculated, which is exactly the property a caller reasoning
    // about speculation-sensitive code would be relying on. This decoder cannot
    // represent that, so it must not present the word as the branch it is not.
    if bit(enc, 4) != 0 {
        return Err(DisasmError::UnmodeledAarch64Instruction {
            encoding: enc,
            address: addr,
            mnemonic: "BC.cond (consistent conditional branch)",
            reason: "FEAT_HBC's BC.cond is a distinct instruction from B.cond with the same \
                     condition and target; this decoder carries no representation for its \
                     speculation behaviour, so it cannot distinguish it from the B.cond it \
                     would otherwise decode to",
        });
    }

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

    // BR/BLR/RET are `1101011 opc op2(20:16) op3(15:10) Rn op4(4:0)` with
    // op2 = 11111, op3 = 000000 and op4 = 00000 all FIXED. This function read
    // only `opc` and `Rn`: of the 128,828 words that reach it, exactly 96 are
    // real BR/BLR/RET and 44,053 were decoded as one anyway.
    //
    // op2 != 11111 is unallocated outright (34,999 words, all `<unknown>`).
    if bits(enc, 20, 16) != 0b11111 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }
    // op3/op4 select the pointer-authentication branches — BRAA/BLRAB/RETAA and
    // the `retaasppcr` family. Those AUTHENTICATE the target address and fault
    // if authentication fails, so decoding one as a plain indirect branch drops
    // a check the hardware performs. Mixed space: mostly unallocated, 22 words
    // in the sweep are real.
    if bits(enc, 15, 10) != 0 || bits(enc, 4, 0) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

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
    // Exception generation is `11010100 opc imm16 op2(4:2) LL`, with op2 a FIXED
    // 000. Only `opc` and `LL` were read, so all eight op2 values decoded as the
    // same exception: 27,951 words in the sweep, every one `<unknown>` to
    // `objdump`. `d4000005` decoded as `Svc` — an unallocated word presented as
    // a system call.
    if bits(enc, 4, 2) != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

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
    // `op2` selects the barrier. Assembler-derived across ten variants (`clang
    // --target=aarch64-none-elf` + `objdump -d`), reading bits[7:5]:
    //
    //   dmb sy d5033fbf / dmb ld d5033dbf / dmb st d5033ebf / dmb ish d5033bbf
    //   dmb ishld d50339bf                                       -> op2 = 101
    //   dsb sy d5033f9f / dsb ld d5033d9f / dsb st d5033e9f / dsb ish d5033b9f
    //   dsb ishst d5033a9f                                       -> op2 = 100
    //   isb  d5033fdf -> op2 = 110      clrex d5033f5f -> op2 = 010
    //
    // SOUNDNESS: this table used to read `0b001 => Dsb, 0b100 => Dmb`. Both
    // entries were wrong, and the first one is the dangerous kind of wrong:
    //
    //   * `0b100` is DSB, so EVERY data synchronization barrier decoded as
    //     `Opcode::Dmb` and was modeled as a DataMemoryBarrier — a STRICTLY
    //     WEAKER barrier. DSB waits for completion; DMB only orders. That is a
    //     real instruction silently presented to the model as a different real
    //     instruction, the same class as LDPSW-as-LDP and FCMPE-as-FCMP.
    //   * `0b001` is not a barrier at all, and `0b101` (the real DMB) had no
    //     arm, so genuine DMBs fell to `UnknownEncoding` — fail-closed, but it
    //     meant DMB was never actually modeled despite the arm that claimed to.
    //
    // SOUNDNESS: every barrier fixes Rt = 11111. `decode_system`'s HINT route
    // one arm above tests `rt == 31`; the BARRIER route did not, so the whole
    // Rt != 31 space — which `objdump` names `msr` for all 840 words the sweep
    // found, e.g. `d5033043` = `msr S0_3_C3_C3_2, x3` — decoded as `Clrex`. A
    // SYSTEM REGISTER WRITE presented as an exclusive-monitor clear: the model
    // sees a barrier where the hardware mutates system state.
    if bits(enc, 4, 0) != 31 {
        return Err(DisasmError::UnmodeledAarch64Instruction {
            encoding: enc,
            address: addr,
            mnemonic: "MSR/SYS (system register or system instruction, Rt != 31)",
            reason: "every barrier encoding fixes Rt = 11111; with Rt naming a real register \
                     this word is a system-register write in the op0=00 space, whose effect on \
                     system state this decoder does not model",
        });
    }

    let opcode = match op2 {
        0b010 => {
            // CLREX
            let mut insn = Instruction::new(addr, enc, Opcode::Clrex, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Imm(crm as u64));
            return Ok(insn);
        }
        0b100 => Opcode::Dsb,
        0b101 => Opcode::Dmb,
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
    // SOUNDNESS: `o1` (bit 21) selects the PAIR and COMPARE-AND-SWAP forms —
    // LDXP/STXP/LDAXP/STLXP and the whole CAS/CASP family. This function never
    // read it, so it decoded them as their single-register neighbours: 3,655
    // words in the sweep, of which 3,296 are real instructions. `casal w0,w1,[x2]`
    // is a read-modify-write of memory conditional on a comparison; decoded as
    // `Ldxr` it becomes a plain load, and the store half vanishes from the model.
    if bit(enc, 21) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    let size = bits(enc, 31, 30);
    let l = bit(enc, 22);
    let o0 = bit(enc, 15);
    let o2 = bit(enc, 23);
    let rs = bits(enc, 20, 16) as u8;
    let rt2 = bits(enc, 14, 10) as u8;
    let rt = bits(enc, 4, 0) as u8;
    let rn = bits(enc, 9, 5) as u8;

    // SOUNDNESS: `size` is the ACCESS WIDTH, and this function used it for one
    // thing only — `is_64 = size == 0b11` — so size=00 (byte) and size=01
    // (halfword) both produced a 32-bit `Ldxr`/`Stxr`/`Ldar`/`Stlr`. That is
    // 2,710 words in the sweep, every one a REAL instruction: `ldxrb w0,[x1]`
    // decoded as `ldxr w0,[x1]`, i.e. a ONE-BYTE exclusive load presented to the
    // model as a FOUR-BYTE one. The three bytes past the end are read by the
    // model and not by the CPU, and the exclusive-monitor granule differs too.
    //
    // The opcode set carries no byte/halfword exclusive variants, so there is
    // nothing here to decode them AS. Refuse.
    if size < 0b10 {
        return Err(DisasmError::UnmodeledAarch64Instruction {
            encoding: enc,
            address: addr,
            mnemonic: "LDXRB/LDXRH/STXRB/STXRH/LDARB/LDARH/STLRB/STLRH (sub-word exclusive)",
            reason: "the byte and halfword exclusive/acquire-release forms access 1 or 2 bytes; \
                     this opcode set has only the 32/64-bit variants, so decoding them would \
                     model an access three or two bytes wider than the hardware performs",
        });
    }

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

    // SOUNDNESS: CONSTRAINED UNPREDICTABLE — the store-exclusive STATUS
    // register aliases the transfer register or the address register. The ARM
    // ARM raises `Unpredictable_DATAOVERLAP` for `s == t || (s == n && n != 31)`.
    //
    // This one is DIFFERENT IN KIND from the load/store families above, and the
    // difference is recorded rather than smoothed over. Native execution does
    // NOT fault: all four measured words EXECUTE on this implementation.
    //
    //   c8007c40  stxr w0,x0,[x2]     Rs==Rt   EXECUTED   (not SIGILL)
    //   c8007c01  stxr w0,x1,[x0]     Rs==Rn   EXECUTED   (not SIGILL)
    //   8803fca3  stlxr w3,w3,[x5]    Rs==Rt   EXECUTED   (not SIGILL)
    //   c81f7c5f  stxr wzr,xzr,[x2]   Rs==Rt   EXECUTED   (not SIGILL)
    //
    // So the refusal is NOT "the CPU rejects it". It is that ONE register is
    // given TWO values and the architecture does not say which survives.
    // Measured directly, with a live monitor reservation and the value read
    // back afterwards:
    //
    //   c8007c41  stxr w0,x1,[x2]  (control)  status=0  mem=1122334455667788
    //   c8007c40  stxr w0,x0,[x2]  Rs==Rt     x0=0      mem=1122334455667788
    //   c8007c01  stxr w0,x1,[x0]  Rs==Rn     x0=0      mem=1122334455667788
    //
    // This implementation resolves it as "transfer first, then overwrite the
    // register with the status" — so the aliased word DESTROYS the value in
    // the Rs==Rt case and the BASE POINTER in the Rs==Rn case. That is one of
    // the four resolutions the architecture allows (`Constraint_NONE`); the
    // others are `Constraint_UNKNOWN`, `Constraint_NOP` and `Constraint_UNDEF`,
    // and nothing entitles a checker to assume this chip's choice. The
    // assembler agrees the word is out of bounds: all four are "unpredictable
    // STXR instruction, status is also a source".
    //
    // The two exemptions are real and both are exercised by the tests:
    // `stxr w0,x1,[sp]` (c8007fe1) is legal because n==31 is SP, not the status
    // register; `stxr wzr,x1,[x0]` (c81f7c01) is legal because s==31 aliases
    // neither t nor n here. Both assemble, both execute, both still decode.
    //
    // Reachability, stated plainly: `trust-machine-sem` today returns
    // `UnsupportedAtomic` for every exclusive form, so none of these 7,940
    // words can currently reach a Proven verdict through the model. Refusing
    // at decode anyway is deliberate — being saved by a downstream refusal is
    // the "protected by ordering, not construction" pattern the rest of this
    // file exists to remove.
    if matches!(opcode, Opcode::Stxr | Opcode::Stlxr) && (rs == rt || (rs == rn && rn != 31)) {
        return Err(DisasmError::ConstrainedUnpredictableOperands {
            encoding: enc,
            address: addr,
            mnemonic: "store exclusive (STXR/STLXR)",
            constraint: "the status register Rs is also the transfer register Rt or the \
                         address register Rn (Unpredictable_DATAOVERLAP); one register \
                         receives both the status and the other value, and the architecture \
                         does not define which survives",
        });
    }

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
    // SOUNDNESS: "Load register (literal)" is `opc 011 V 00 imm19 Rt` —
    // bits[25:24] are a FIXED 00. `decode_load_store` routes here on
    // bits[29:27]==011 and V==0 alone; bit 25 is already 0 by the top-level
    // dispatch, but bit 24 was never tested by anyone. That one unread bit is
    // the single largest defect in this decoder: 140,862 words in the sweep,
    // 44,111 of them REAL instructions from a completely different group.
    //
    //   19000000  stlurb w0,[x0]     -> decoded `LdrLiteral`  (a STORE as a LOAD)
    //   99000040  stlur  w0,[x2]     -> decoded `Ldrsw`       (a STORE as a LOAD)
    //   d92089b0  stg    x16,[x13,#0x80] -> decoded `Prfm`, whose operand shape
    //                                       carries NO destination at all, so the
    //                                       store modeled as doing NOTHING
    //
    // The bit-24 space is "Load/store memory tags" (STG/STZG/LDG) and the
    // LDAPUR/STLUR unscaled acquire-release forms. None of them is a
    // PC-relative literal load, and half of them write memory.
    if bit(enc, 24) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    let opc = bits(enc, 31, 30);
    let imm19 = bits(enc, 23, 5);
    let rt = bits(enc, 4, 0) as u8;
    let offset = sign_extend(imm19, 19) << 2;

    // Trust: the transfer width comes from the SELECTED OPCODE, not from a
    // separate test of `opc`. `is_64 = opc == 0b01` was false for `opc == 0b10`
    // (LDRSW), so `ldrsw x0, <label>` decoded a **W** destination: the 32-bit
    // write path never builds a `BvSignExt`, and the register was then
    // zero-extended to 64. Measured: the literal 0xffffffff loaded as
    // 0x00000000ffffffff instead of 0xffffffffffffffff. ARM DDI 0487, LDRSW
    // (literal): "X[t] = SignExtend(data, 64)". The base+offset encoding at
    // `decode.rs:1193` already pairs `(Opcode::Ldrsw, true)` correctly.
    let (opcode, is_64) = match opc {
        0b00 => (Opcode::LdrLiteral, false),
        0b01 => (Opcode::LdrLiteral, true),
        0b10 => (Opcode::Ldrsw, true),
        0b11 => (Opcode::Prfm, false),
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

    // `opc` picks the element class; `L` picks load vs store. The register
    // width and the ELEMENT size are independent — LDPSW loads 4-byte elements
    // into 64-bit registers — so they are decoded separately.
    //
    //   opc=00          32-bit LDP/STP  — W registers, 4-byte elements
    //   opc=01, L=1     LDPSW           — X registers, 4-byte elements, SIGN-extended
    //   opc=01, L=0     STGP (FEAT_MTE) — not modeled
    //   opc=10          64-bit LDP/STP  — X registers, 8-byte elements
    //   opc=11          unallocated
    //
    // SOUNDNESS: `is_64 = opc == 0b10` alone put opc=01 and opc=11 on the
    // 32-bit LDP/STP path. LDPSW then decoded as a plain 32-bit LDP whose
    // semantics ZERO-extend, giving it effects identical to `ldp w,w,[x]` —
    // the two words are byte-distinct but the model could not tell them apart.
    // Refusing is the floor; approximating a reserved encoding as a real
    // instruction is not.
    let (opcode, is_64, scale) = match (opc, l) {
        (0b00, 1) => (Opcode::Ldp, false, 2),
        (0b00, 0) => (Opcode::Stp, false, 2),
        (0b01, 1) => (Opcode::Ldpsw, true, 2),
        (0b10, 1) => (Opcode::Ldp, true, 3),
        (0b10, 0) => (Opcode::Stp, true, 3),
        // opc=01/L=0 is STGP; opc=11 is unallocated.
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };
    let offset = sign_extend(imm7, 7) << scale;

    let base = gpr_or_sp(rn, true);

    // The addressing mode is validated FIRST. `mode == 0b00` is the
    // no-allocate pair (LDNP/STNP), which this decoder does not decode at all;
    // reporting a CONSTRAINED UNPREDICTABLE operand combination for a word we
    // refuse on other grounds would name a constraint on an encoding we never
    // reach, which is a false diagnostic even when the verdict is the same.
    let mem = match mode {
        0b01 => MemoryOperand::PostIndex { base, offset },
        0b10 => MemoryOperand::BaseOffset { base, offset },
        0b11 => MemoryOperand::PreIndex { base, offset },
        _ => return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr }),
    };

    // SOUNDNESS: CONSTRAINED UNPREDICTABLE — a LOAD pair that names the same
    // register for both halves. The ARM ARM raises `Unpredictable_LDPOVERLAP`
    // for `memop == MemOp_LOAD && t == t2`, and the permitted resolutions
    // include `Constraint_UNDEF`. Two writes are directed at one register and
    // the architecture does not say which one lands — so this decoder's operand
    // list, which shows two independent destinations, describes an instruction
    // that does not exist.
    //
    // Assembler: `ldp x0,x0,[x2,#-72]` is "unpredictable LDP instruction,
    // Rt2==Rt". NATIVE EXECUTION:
    //
    //   a97b8040  ldp x0,x0,[x2,#-72]      Rt1==Rt2   SIGILL
    //   a97b8440  ldp x0,x1,[x2,#-72]      control    executes
    //   29400040  ldp w0,w0,[x2]           Rt1==Rt2   SIGILL
    //   a9417c5f  ldp xzr,xzr,[x2,#16]     Rt1==Rt2   SIGILL
    //   69c50541  ldpsw x1,x1,[x10,#40]!   Rt1==Rt2   SIGILL
    //
    // There is NO `t != 31` exception here, unlike the writeback rules below:
    // `ldp xzr,xzr,[x2,#16]` names ZR twice and still SIGILLs, and the
    // assembler still refuses it. The constraint is on the register field, and
    // ZR is a register field value like any other.
    //
    // LDPSW is worth naming separately because it is the one case where the
    // ASSEMBLER is not a reliable oracle: clang refuses `ldpsw x0,x0,[x2,#8]`
    // but ACCEPTS the pre-indexed `ldpsw x1,x1,[x10,#40]!` (69c50541). Native
    // execution answers SIGILL for it regardless, and the ARM ARM applies
    // LDPOVERLAP to LDPSW in all three addressing modes. The hardware, not the
    // assembler, settles it.
    //
    // A STORE pair may legitimately name one register twice — `stp x0,x0,[x2,#16]`
    // (a9010040) assembles, executes, and must keep decoding.
    if l == 1 && rt == rt2 {
        return Err(DisasmError::ConstrainedUnpredictableOperands {
            encoding: enc,
            address: addr,
            mnemonic: "load pair (LDP/LDPSW)",
            constraint: "both transfer registers are the same register \
                         (Unpredictable_LDPOVERLAP); the architecture directs two loads at \
                         one destination without defining which result survives, and permits \
                         the encoding to be treated as UNDEFINED",
        });
    }

    // SOUNDNESS: CONSTRAINED UNPREDICTABLE — a pair access with writeback whose
    // base register is also one of the two transfer registers. The ARM ARM
    // raises `Unpredictable_WBOVERLAPLD` / `Unpredictable_WBOVERLAPST` for
    // `wback && (t == n || t2 == n) && n != 31`.
    //
    // Assembler: "unpredictable STP instruction, writeback base is also a
    // source" / "unpredictable LDP instruction, writeback base is also a
    // destination". NATIVE EXECUTION:
    //
    //   a9890442  stp x2,x1,[x2,#144]!     Rt==Rn     SIGILL
    //   a9890443  stp x3,x1,[x2,#144]!     control    executes
    //   a8a56301  stp x1,x24,[x24],#-432   Rt2==Rn    SIGILL
    //   a8a55f01  stp x1,x23,[x24],#-432   control    executes
    //   a9c79eb5  ldp x21,x7,[x21,#120]!   Rt==Rn     SIGILL
    //   a9c79eb1  ldp x17,x7,[x21,#120]!   control    executes
    //   28c10c61  ldp w1,w3,[x3],#8        Rt2==Rn    SIGILL
    //   28c10861  ldp w1,w2,[x3],#8        control    executes
    //
    // `n == 31` is exempt — the base is SP, which is not the same register as
    // the ZR that a transfer field of 31 names. `ldp x0,x1,[sp,#16]!`
    // (a9c107e0) is legal and must keep decoding. So is the non-writeback
    // `ldp x0,x2,[x0]` (a9400800): with mode 0b10 there is no base update, so
    // nothing overlaps.
    if matches!(mode, 0b01 | 0b11) && rn != 31 && (rt == rn || rt2 == rn) {
        return Err(DisasmError::ConstrainedUnpredictableOperands {
            encoding: enc,
            address: addr,
            mnemonic: "load/store pair (pre/post-indexed)",
            constraint: "the writeback base register Rn is also a transfer register \
                         (Unpredictable_WBOVERLAPLD / Unpredictable_WBOVERLAPST); the \
                         architecture permits the implementation to leave the result UNKNOWN, \
                         suppress the writeback, or treat the encoding as UNDEFINED, so no \
                         definite effect exists to model",
        });
    }

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
        // SOUNDNESS: the register-offset form is `.. 1 Rm option S 10 Rn Rt` —
        // bits[11:10] are a FIXED 10. Everything else in that slot is the ATOMIC
        // memory-operation space (LDADD/LDUMAX/SWP/...), the LDAPR/STLR
        // register forms, and the pointer-authenticated loads. This function
        // dispatched on bit 21 alone, so all of it decoded as a plain
        // register-offset load or store: 26,372 words in the sweep, 12,443 of
        // them real instructions.
        //
        //   b8606000  ldumaxl w0,w0,[x0] -> decoded `Ldr`  — an atomic RMW that
        //                                   WRITES MEMORY, presented as a load
        //   f820666b  ldraa x11,[x19,#0x30] -> decoded `Str` — a LOAD as a STORE
        //
        // "Atomic RMW modeled as a load" is the worst shape in this family: the
        // gate then reasons about a memory state the hardware does not produce.
        if bits(enc, 11, 10) != 0b10 {
            return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
        }

        // Register offset
        let rm = bits(enc, 20, 16) as u8;
        let option = bits(enc, 15, 13);
        let s = bit(enc, 12);
        let shift = if s == 1 { size as u8 } else { 0 };

        // FEAT_RPRFM's range prefetch shares the PRFM (register) encoding and is
        // selected by `Rt<4:3> == 11`. Assembler-derived, sweeping Rt over the
        // whole field with everything else fixed (`f8a068<rt>`): objdump answers
        // `prfm <prfop>, [x1, x0]` for Rt ≤ 23 and `rprfm #<n>, x0, [x1]` for
        // Rt ≥ 24. RPRFM reads `Xm` as a RANGE DESCRIPTOR — stride, count and
        // type — not as an index register to be added to the base, so the
        // memory operand this function builds is not the address it touches.
        if opcode == Opcode::Prfm && rt >= 24 {
            return Err(DisasmError::UnmodeledAarch64Instruction {
                encoding: enc,
                address: addr,
                mnemonic: "RPRFM (range prefetch)",
                reason: "Rt<4:3> == 11 in the PRFM (register) slot selects the range prefetch, \
                         whose Rm is a range descriptor rather than an index register; the \
                         base+index memory operand this decoder would build names a different \
                         address than the instruction reads",
            });
        }

        // The load/store register-offset form defines only four `option`
        // values; the ARM ARM makes the encoding UNDEFINED when `option<1> ==
        // 0`, i.e. for 000, 001, 100 and 101.
        //
        // SOUNDNESS: the old `_ => None` mapped every reserved value onto LSL.
        // Two of the four then became genuinely indistinguishable from a real
        // instruction: 001 and 101 also produced a 64-bit index register
        // (`option & 1 == 1`), which is byte-for-byte the `extend: None,
        // 64-bit index` shape that a legitimate `lsl` decodes to. A reserved
        // word therefore modeled EXACTLY as `ldr w0,[x1,x2,lsl#n]` and the gate
        // could certify a function containing it. (000 and 100 produced a
        // 32-bit index with no extend — a combination no architectural form
        // emits — which `extended_index_value` now rejects downstream, but
        // relying on a downstream width check to catch a decoder that invented
        // an instruction is exactly the "protected by ordering, not
        // construction" pattern this pass exists to remove.)
        let extend = match option {
            0b010 => Some(ExtendType::Uxtw),
            0b011 => None, // LSL
            0b110 => Some(ExtendType::Sxtw),
            0b111 => Some(ExtendType::Sxtx),
            _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
        };

        // UXTW/SXTW name the 32-bit W register; LSL and SXTX name the 64-bit X.
        let index = Register::gpr(rm, matches!(option, 0b011 | 0b111));

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

        // PRFM exists in the unsigned-offset and UNSCALED (PRFUM) forms only:
        // there is no pre- or post-indexed prefetch, because there is no
        // register to write the updated base into — `Rt` is the prefetch
        // OPERATION, not a destination. This arm reached the pre/post-index
        // paths for the PRFM opcode regardless, producing 2,353 words the
        // architecture does not allocate, each carrying a base-register update
        // effect that no instruction performs.
        if opcode == Opcode::Prfm && op2 != 0b00 {
            return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
        }

        // SOUNDNESS: CONSTRAINED UNPREDICTABLE — the writeback base register is
        // also the transfer register. Every FIELD in this word is valid, so no
        // field check can catch it; it is the coincidence of two register
        // NUMBERS that puts it out of bounds. The ARM ARM raises
        // `Unpredictable_WBOVERLAPLD` / `Unpredictable_WBOVERLAPST` for
        // `t == n && n != 31`, and the permitted resolutions include
        // `Constraint_UNDEF`.
        //
        // This is not a theoretical corner. The assembler refuses to encode it
        // — `str x30,[x30],#-21` is "unpredictable STR instruction, writeback
        // base is also a source" — and NATIVE EXECUTION answers SIGILL:
        //
        //   f81eb7de  str x30,[x30],#-21     Rt==Rn    SIGILL
        //   f81eb7dd  str x29,[x30],#-21     control   executes
        //   7843dd8c  ldrh w12,[x12,#61]!    Rt==Rn    SIGILL
        //   7843dd8b  ldrh w11,[x12,#61]!    control   executes
        //
        // Before this check the decoder answered `Str`/`Ldrh` for both members
        // of each pair, the semantics built a full effect list from it, and the
        // output gate reached PROVEN at the kernel-re-checkable grade on a word
        // the CPU refuses to run.
        //
        // `n == 31` is NOT the constraint: there Rn is SP and Rt is ZR, two
        // different registers. `ldr xzr,[sp],#8` (f84087ff) is legal, the
        // assembler encodes it, and it must keep decoding.
        //
        // The unscaled form (op2 == 0b00, LDUR/STUR) has no writeback and so no
        // constraint: `ldur x0,[x0,#8]` is legal and still decodes.
        if matches!(op2, 0b01 | 0b11) && rt == rn && rn != 31 {
            return Err(DisasmError::ConstrainedUnpredictableOperands {
                encoding: enc,
                address: addr,
                mnemonic: "load/store register (immediate, pre/post-indexed)",
                constraint: "the writeback base register Rn is also the transfer register Rt \
                             (Unpredictable_WBOVERLAPLD / Unpredictable_WBOVERLAPST); the \
                             architecture permits the implementation to leave the result \
                             UNKNOWN, suppress the writeback, or treat the encoding as \
                             UNDEFINED, so no definite effect exists to model",
            });
        }

        let mem = match op2 {
            0b00 => {
                // Unscaled immediate (LDUR/STUR) - treat as base offset
                MemoryOperand::BaseOffset { base, offset }
            }
            0b01 => MemoryOperand::PostIndex { base, offset },
            0b11 => MemoryOperand::PreIndex { base, offset },
            // SOUNDNESS: `op2 == 0b10` is the UNPRIVILEGED form (LDTR/STTR and
            // their sign-extending/sub-word siblings), and this used to say
            // "Unprivileged - treat as base offset", producing an
            // `Opcode::Ldr`/`Str` with a plain `BaseOffset` — i.e. effects
            // BYTE-IDENTICAL to the ordinary LDUR/STUR at the same offset.
            // Measured with the assembler: `ldtr w0,[x1,#4]` is b8404820 and
            // `ldur w0,[x1,#4]` is b8404020, two distinct words that the model
            // could not tell apart.
            //
            // They are not the same instruction. LDTR/STTR perform the access
            // with EL0 privilege regardless of the current exception level, so
            // whether the access faults depends on the unprivileged
            // permissions; at EL1 with unequal EL0/EL1 permissions the two
            // genuinely differ. Modeling that needs a privilege level and a
            // translation regime this semantics does not have, so the honest
            // answer is to refuse the encoding rather than silently promote it
            // to a privileged access that always succeeds.
            0b10 => {
                return Err(DisasmError::UnmodeledAarch64Instruction {
                    encoding: enc,
                    address: addr,
                    mnemonic: "LDTR/STTR (unprivileged load/store)",
                    reason: "the access is performed with EL0 privilege regardless of the \
                             current exception level; this decoder models no privilege level \
                             or translation regime, so it cannot distinguish it from the \
                             ordinary LDUR/STUR it would otherwise decode to",
                });
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

        // op2 = 1 shift(23:22) bit21. Bit 21 alone separates the SHIFTED form
        // from the EXTENDED one; bits[23:22] are the shift type, not part of the
        // selector.
        //
        // COMPLETENESS: this used to read `op2 == 0b1000`, which admits only
        // `shift == LSL`. `add w3,w1,w1,lsr #31` (`0b417c23`, the signed
        // divide-by-two idiom) has op2 = 1010 and so never reached
        // `decode_add_sub_shifted_reg` at all — it fell out of `decode_dp_reg`
        // as `UnknownEncoding`. That is fail-closed rather than unsound, but it
        // is the same missing predicate as the rest of this pass, and the
        // emitted corpus contains 6 distinct such words / 44 occurrences that
        // the gate could not verify for no reason other than this.
        if bit(enc, 21) == 0 {
            return decode_add_sub_shifted_reg(enc, addr);
        }
        // Add/subtract extended register: op2 = 1 opt(23:22) 1, `opt` fixed 00.
        if bits(enc, 23, 22) == 0b00 {
            return decode_add_sub_extended_reg(enc, addr);
        }
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
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

    // SOUNDNESS: `imm6` is a 6-bit shift amount, but in the 32-bit form (sf=0)
    // its top bit is a FIXED 0 — you cannot shift a W register by 32..63 and the
    // architecture leaves `imm6<5> == 1` UNDEFINED there.
    //
    // This is the reported exemplar, ground-truthed by native execution:
    // `0a098129` is `and w9,w9,w9,lsl #32` with sf=0. `objdump` answers
    // `<unknown>`; running it answers SIGILL (exit 132). This decoder answered
    // `Opcode::And` with `ShiftedReg { Lsl, amount: 32 }`, the semantics built a
    // complete [RegWrite, PcUpdate] effect list from it, and the output gate
    // certified the containing object `Proven` at the kernel-re-checkable grade
    // — on a word the CPU refuses to execute. 47,968 words in the sweep.
    if !sf && imm6 >= 32 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

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

    // Same fixed field as the logical form: `imm6<5>` is 0 when sf=0. 6,187
    // words in the sweep, all `<unknown>` to `objdump`.
    if !sf && imm6 >= 32 {
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

    // `imm3` is the left-shift applied to the extended operand and the
    // architecture allows 0..4 only; 5, 6 and 7 are UNDEFINED. 8,756 words in
    // the sweep decoded as an ADD/SUB with a shift the hardware rejects.
    if imm3 > 4 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let opcode = match (op, s) {
        (0, 0) => Opcode::Add,
        (0, 1) => Opcode::Adds,
        (1, 0) => Opcode::Sub,
        (1, 1) => Opcode::Subs,
        _ => unreachable!("(op, s) are single-bit fields: all 4 values handled"),
    };

    let extend = decode_extend_type(option);
    // Which register `Rm` names is decided by the extend option, and ONLY the
    // two "X" forms name a 64-bit register:
    //
    //   000 UXTB  001 UXTH  010 UXTW  011 UXTX
    //   100 SXTB  101 SXTH  110 SXTW  111 SXTX
    //
    // Assembler-derived (`clang --target=aarch64` + `objdump -d`), all eight
    // with `add x0, x1, ..`: 8b220020 `w2,uxtb`, 8b222020 `w2,uxth`,
    // 8b224020 `w2,uxtw`, 8b226020 `x2,uxtx`, 8b228020 `w2,sxtb`,
    // 8b22a020 `w2,sxth`, 8b22c020 `w2,sxtw`, 8b22e020 `x2,sxtx`.
    //
    // This used to read `option >= 0b100`, commented "SXTB..SXTX operate on
    // 64-bit view". That is wrong in BOTH directions and for FOUR of the eight
    // options: it gave UXTX a 32-bit `Rm` (it is the one unsigned form that
    // takes X), and gave SXTB/SXTH/SXTW 64-bit ones (all three take W, exactly
    // like their unsigned partners). Currently masked — `operand_to_formula`
    // refuses `Operand::ExtendedReg` outright, measured: decoding 8b226020 and
    // asking for effects yields `InvalidOperand { opcode: Add, index: 2 }` — so
    // no formula is built from the wrong width today. Fixed anyway: the mask is
    // a property of a consumer that is expected to grow support, not of this
    // decoder, and a decoder that names the wrong register is wrong regardless
    // of who currently declines to look.
    let rm_is_64 = matches!(option, 0b011 | 0b111);

    let rd_reg = if s == 0 { gpr_or_sp(rd, sf) } else { gpr_or_zr(rd, sf) };

    let mut insn = Instruction::new(addr, enc, opcode, ControlFlow::Fallthrough);
    insn.push_operand(Operand::Reg(rd_reg));
    insn.push_operand(Operand::Reg(gpr_or_sp(rn, sf)));
    insn.push_operand(Operand::ExtendedReg { reg: gpr_or_zr(rm, rm_is_64), extend, shift: imm3 });
    Ok(insn)
}

fn decode_add_sub_carry(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // SOUNDNESS: add/subtract with carry is `sf op S 11010000 Rm 000000 Rn Rd` —
    // bits[15:10] are a FIXED 000000. This function read `Rm`, `Rn`, `Rd`, `op`
    // and `S` and nothing else, so the entire 63/64 of the slot where those six
    // bits are non-zero decoded as ADC/ADCS/SBC/SBCS: 62,398 words, 3,730 of
    // them real and different instructions.
    //
    //   ba000420  rmif x1,#0,#0  -> decoded `Adcs` (RMIF writes NZCV from a
    //                               rotated register; nothing like an add)
    //   9a002000  addpt x0,x0,x0 -> decoded `Adc`  (checked pointer arithmetic)
    //
    // The same slot holds SETF8/SETF16, which also write flags from a value
    // rather than from an addition.
    if bits(enc, 15, 10) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

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

    // Conditional compare is `sf op S 11010010 ..` — `S` is a FIXED 1 and
    // bits[24:21] are a fixed 0010. `decode_dp_reg` routes both 0010 and 0011
    // here and neither this function nor the dispatch ever tested `S`. 47,295
    // words in the sweep decoded as CCMN/CCMP, all `<unknown>` to `objdump`:
    // 33,827 with S=0 and 13,468 with bit 21 = 1.
    if bit(enc, 29) != 1 || bit(enc, 21) != 0 {
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

    // Conditional select is bits[24:21] == 0100; `decode_dp_reg` also routes
    // 0101 here, which is not a conditional select. 14,450 words, all
    // `<unknown>` to `objdump`, decoded as CSEL/CSINC/CSINV/CSNEG.
    if bit(enc, 21) != 0 {
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

    // `S` (bit 29) is a fixed 0 here — `decode_dp_2source` checks it but jumps
    // to this function BEFORE that check, on bit 30. 1,543 words in the sweep,
    // all `<unknown>`.
    if bit(enc, 29) != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    // SOUNDNESS: `opcode2` (bits[20:16]) is a fixed 00000 for RBIT/REV/CLZ/CLS.
    // Non-zero is the POINTER AUTHENTICATION space — PACIA/PACIB/PACDA/AUTIA/…
    // — which this function decoded as bit-manipulation of the same registers:
    //
    //   dac10000  pacia x0,x0  -> decoded `Rbit`
    //
    // PACIA writes a signed pointer; RBIT writes the bit reversal. 17,375 words,
    // 1,068 of them real.
    if bits(enc, 20, 16) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

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
        // `opcode = 000011` is REV of a full 64-bit register and exists only in
        // the sf=1 form; the 32-bit REV is `000010`. 178 words with sf=0
        // decoded as a `Rev` no instruction encodes.
        0b000011 if sf => Opcode::Rev,
        0b000011 => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
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
    // Data-processing (3 source) is `sf op54(30:29) 11011 op31 Rm o0 Ra Rn Rd`
    // with `op54` a FIXED 00. Three quarters of the slot went unread: 91,519
    // words in the sweep decoded as MADD/MSUB/SMULH/…, every one `<unknown>`
    // to `objdump`.
    if bits(enc, 30, 29) != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

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
            // bits[11:10]=00: FP compare, FP immediate, FP 1-source, or FP<->int
            // conversion. With bits[11:10] already 00 the four are separated by
            // bits 12, 13 and 14 ALONE, and they are disjoint:
            //
            //   bit12=1                    FP immediate      (bits[12:10] = 100)
            //   bit12=0 bit13=1            FP compare        (bits[13:10] = 1000)
            //   bit12=0 bit13=0 bit14=1    FP 1-source       (bits[14:10] = 10000)
            //   bit12=0 bit13=0 bit14=0    FP <-> int conv   (bits[15:10] = 000000)
            //
            // SOUNDNESS: this used to select FP immediate with `bits[13:10] ==
            // 0b0100`, but BIT 13 IS `imm8<0>` — part of the immediate, not part
            // of the selector. Every FMOV-immediate with an ODD `imm8` therefore
            // failed the test and fell through to `decode_fp_int_conv`, where
            // `rmode`/`opcode` are read out of `imm8`'s other bits. Measured:
            // `1ee77007` is `fmov h7, #27.0` and decoded as `FmovReg` — a
            // CONSTANT MATERIALIZATION presented as a register-to-register move,
            // so the model propagates whatever was in the source register
            // instead of the constant. 84 words in the sweep.
            0b00 => {
                if bit(enc, 12) == 1 {
                    // FP immediate also fixes `imm5` (bits[9:5]) at 00000.
                    if bits(enc, 9, 5) != 0 {
                        return Err(DisasmError::UnallocatedEncoding {
                            encoding: enc,
                            address: addr,
                        });
                    }
                    return decode_fp_imm(enc, addr);
                }
                if bit(enc, 13) == 1 {
                    return decode_fp_compare(enc, addr);
                }
                if bit(enc, 14) == 1 {
                    return decode_fp_dp_1source(enc, addr);
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

    // Advanced SIMD three-same, `ORR (vector, register)` — decoded ONLY in its
    // `Rn == Rm` form, which is the architectural `MOV Vd.<T>, Vn.<T>` alias.
    //
    // This is not a general SIMD lane: trust-cg emits exactly this word for a
    // full-width FPR-to-FPR copy, and without it every float body stops at
    // `UnknownEncoding` before any semantics run. Verified against the system
    // assembler: `mov v0.16b, v2.16b` and `orr v0.16b, v2.16b, v2.16b` both
    // assemble to 0x4EA21C40, and it disassembles back as `mov.16b v0, v2`.
    //
    // FAIL-CLOSED ON PURPOSE: when `Rn != Rm` this word is a genuine bitwise OR
    // of two DIFFERENT registers, which is a different instruction with
    // different semantics. Decoding that as a move would be a silent
    // mistranslation, so it is left unknown until real vector-OR semantics
    // exist. Sibling encodings in the same family are likewise untouched —
    // size=00 AND, 01 BIC, 11 ORN, and U=1 EOR all still reject.
    if bit(enc, 31) == 0
        && bits(enc, 28, 24) == 0b01110
        && bit(enc, 29) == 0            // U = 0
        && bits(enc, 23, 22) == 0b10    // size = 10 selects ORR within the family
        && bit(enc, 21) == 1
        && bits(enc, 15, 11) == 0b00011 // opcode = ORR
        && bit(enc, 10) == 1
    {
        let rm = bits(enc, 20, 16) as u8;
        let rn = bits(enc, 9, 5) as u8;
        let rd = bits(enc, 4, 0) as u8;
        if rn == rm {
            // Q selects the arrangement: 1 => 16B (the whole 128-bit register),
            // 0 => 8B (low 64 bits; the architecture zeroes bits 127:64).
            let width: u16 = if bit(enc, 30) == 1 { 128 } else { 64 };
            let mut insn = Instruction::new(addr, enc, Opcode::SimdMov, ControlFlow::Fallthrough);
            insn.push_operand(Operand::Reg(Register::simd(rd, width)));
            insn.push_operand(Operand::Reg(Register::simd(rn, width)));
            return Ok(insn);
        }
    }

    Err(DisasmError::UnknownEncoding { encoding: enc, address: addr })
}

fn decode_fp_int_conv(enc: u32, addr: u64) -> Result<Instruction, DisasmError> {
    // SOUNDNESS: "Conversion between floating-point and integer" is
    // `sf 0 S 11110 ftype 1 rmode opcode 000000 Rn Rd` — bits[15:10] are a FIXED
    // 000000. `decode_simd_fp` reaches this function from two arms that do not
    // guarantee that (`bits[11:10] == 01` and the sf=1 prefix path), and the
    // function itself never checked, so it decoded FCCMP, FCSEL and the
    // conditional-compare space as conversions:
    //
    //   1e220420  fccmp s1,s2,#0,eq -> decoded `Scvtf`
    //
    // FCCMP writes NZCV and touches no register; SCVTF writes a register and
    // touches no flags. 31,192 words in the sweep, 4,966 of them real.
    if bits(enc, 15, 10) != 0 {
        return Err(DisasmError::UnknownEncoding { encoding: enc, address: addr });
    }

    let sf = is_64bit(enc);
    let ftype = bits(enc, 23, 22);
    let rmode = bits(enc, 20, 19);
    let opcode_field = bits(enc, 18, 16);
    let rn = bits(enc, 9, 5) as u8;
    let rd = bits(enc, 4, 0) as u8;

    // FMOV between a GPR and an FP register moves BITS, so the two widths must
    // agree, and `sf` and `ftype` name them independently. The allocated pairs
    // with `rmode == 00` are (sf=0, S), (sf=1, D) and either `sf` with H; the
    // top-half form (sf=1, ftype=10) needs `rmode == 01` and is refused below by
    // the `fp_width` match anyway. Reading the two fields without relating them
    // produced 711 words — e.g. a "64-bit GPR to 32-bit S" move — that decoded
    // as `FmovReg` and are `<unknown>` to `objdump`.
    if rmode == 0b00
        && (opcode_field == 0b110 || opcode_field == 0b111)
        && !matches!((sf, ftype), (false, 0b00) | (true, 0b01) | (_, 0b11))
    {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

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

    // For FCVT, destination width differs from source. `opcode<1:0>` IS the
    // destination `ftype`, so the source and destination formats are named by
    // two independent fields and the architecture requires them to DIFFER —
    // `ftype == opcode<1:0>` is unallocated (a "convert to my own format"
    // encoding does not exist; FMOV is the register-to-register move).
    // Assembler-derived: `fcvt d0,s0` = 1e22c000 (ftype=00, opcode=000101) and
    // `fcvt s0,d0` = 1e624000 (ftype=01, opcode=000100).
    //
    // SOUNDNESS: the old `_ => fp_width` swept the two unallocated pairs this
    // function can reach — (ftype=00, opcode=000100) and (ftype=01,
    // opcode=000101) — into a same-width "conversion", i.e. it decoded a
    // reserved word as an FCVT whose destination format equals its source. That
    // is an IDENTITY conversion: a reserved encoding presented to the gate as a
    // real, and trivially provable, instruction.
    let dst_width = if opcode == Opcode::Fcvt {
        match (ftype, opcode_field) {
            (0b00, 0b000101) => 64u16, // S -> D
            (0b01, 0b000100) => 32,    // D -> S
            _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
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
    // FP compare is `M 0 S 11110 ftype 1 Rm op(15:14) 1000 Rn opc(4:3) 000`.
    // `op` and the low three bits of the `opcode2` field are FIXED zeros and
    // were never read: 7,278 words in the sweep decoded as `Fcmp`, all
    // `<unknown>` to `objdump`.
    if bits(enc, 15, 14) != 0 || bits(enc, 2, 0) != 0 {
        return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr });
    }

    let ftype = bits(enc, 23, 22);
    let rm = bits(enc, 20, 16) as u8;
    let rn = bits(enc, 9, 5) as u8;
    let opc = bits(enc, 4, 3);

    let fp_width: u16 = match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => return Err(DisasmError::UnallocatedEncoding { encoding: enc, address: addr }),
    };

    // `opc<0>` selects compare-with-zero; `opc<1>` selects the SIGNALING form,
    // FCMPE. Assembler-derived: `fcmp s0,s1` = 1e212000 vs `fcmpe s0,s1` =
    // 1e212010, and `fcmp s0,#0.0` = 1e202008 vs `fcmpe s0,#0.0` = 1e202018 —
    // the pairs differ only in bit 4.
    //
    // SOUNDNESS: `opc<1>` used to be ignored entirely, so FCMPE decoded as
    // Opcode::Fcmp and the two words produced identical effects. They are
    // different instructions: FCMP raises Invalid Operation only for a
    // SIGNALING NaN, FCMPE raises it for ANY NaN including a quiet one, so they
    // differ in FPSR.IOC and, with the exception unmasked, in whether they trap.
    // This semantics models neither FPSR nor FP exceptions, so it cannot
    // represent the difference — and the effect of "cannot represent" must be a
    // refusal, not a silent aliasing onto the non-signaling instruction.
    if opc & 0b10 != 0 {
        return Err(DisasmError::UnmodeledAarch64Instruction {
            encoding: enc,
            address: addr,
            mnemonic: "FCMPE",
            reason: "the signaling compare raises Invalid Operation for a QUIET NaN as well \
                     as a signaling one; this semantics models neither FPSR nor FP exceptions, \
                     so it cannot distinguish it from the FCMP it would otherwise decode to",
        });
    }

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

#[cfg(test)]
mod bitmask_immediate_tests {
    use crate::decode_aarch64;
    use crate::error::DisasmError;
    use crate::operand::Operand;

    fn imm_of(enc: u32) -> Result<u64, DisasmError> {
        let insn = decode_aarch64(&enc.to_le_bytes(), 0)?;
        for op in insn.operands() {
            if let Operand::Imm(v) = op {
                return Ok(*v as u64);
            }
        }
        panic!("logical-immediate decode produced no immediate operand: {insn:?}");
    }

    /// 64-bit logical immediates with a NON-ZERO ROTATE must decode to their
    /// architectural value.
    ///
    /// `1u64 << (s + 1)` and `1u64 << esize` both overflow at `esize == 64`,
    /// which is every 64-bit encoding with `r != 0`. With debug assertions off —
    /// how the shipped `trustc` is built — the decoder silently yielded `#0`, so
    /// `eor x0, x0, #0x8000000000000000` read as the identity and the output
    /// gate certified that miscompile `Proven` with a kernel-re-checkable grade.
    ///
    /// These assert the VALUE, not merely that decoding succeeds: a test that
    /// only checked for absence of a panic would still have passed while the
    /// decoder returned zero.
    #[test]
    fn rotated_64_bit_logical_immediates_decode_to_their_value() {
        // Words taken from the assembler, not hand-encoded.
        for (enc, want, asm) in [
            (0xD241_0000u32, 0x8000_0000_0000_0000u64, "eor x0,x0,#0x8000000000000000"),
            (0xB27F_0000u32, 0x0000_0000_0000_0002u64, "orr x0,x0,#2"),
            (0x9260_7C00u32, 0xFFFF_FFFF_0000_0000u64, "and x0,x0,#0xffffffff00000000"),
        ] {
            match imm_of(enc) {
                Ok(got) => assert_eq!(
                    got, want,
                    "{asm}: decoded {got:#x}, architecture says {want:#x} \
                     (a zero here is the shift-overflow silently returning 0)"
                ),
                Err(e) => panic!("{asm} must decode, got {e:?}"),
            }
        }
    }

    /// The unrotated controls were always correct and must stay correct.
    #[test]
    fn unrotated_logical_immediates_are_unchanged() {
        assert_eq!(imm_of(0xB240_1C00).ok(), Some(0xff), "orr x0,x0,#0xff");
        assert_eq!(imm_of(0x1218_1C00).ok(), Some(0xff00), "and w0,w0,#0xff00");
    }

    /// An element of all ones is UNDEFINED for the immediate forms, and an
    /// encoding with no element size is too. Both used to yield an immediate —
    /// `0` — rather than a refusal, which is how an unallocated word became a
    /// plausible instruction the machine model would then reason about.
    #[test]
    fn undefined_logical_immediate_encodings_are_refused() {
        // imms = 0b111111 with N=1: len==0 after the NOT, no element size.
        let no_element = 0xB200_FC00u32;
        assert!(
            matches!(imm_of(no_element), Err(DisasmError::UnallocatedEncoding { .. })),
            "an encoding with no element size must be refused, not decoded to an immediate"
        );
    }
}

/// Reserved and unallocated encodings must be REFUSED, never decoded into a
/// plausible neighbouring instruction.
///
/// Every word here is assembler-derived (`clang --target=aarch64-none-elf` on
/// `.inst` directives, read back with `objdump -d`) or derived by mutating a
/// single named field of one that is; none is hand-encoded. The `objdump`
/// rendering is recorded per case, because "unallocated" and "allocated but
/// unmodeled" are different claims and this decoder now reports them
/// differently.
#[cfg(test)]
mod unallocated_encoding_tests {
    use crate::decode_aarch64;
    use crate::error::DisasmError;
    use crate::opcode::Opcode;
    use crate::operand::{ExtendType, MemoryOperand, Operand};

    fn decode(enc: u32) -> Result<crate::instruction::Instruction, DisasmError> {
        decode_aarch64(&enc.to_le_bytes(), 0x1000)
    }

    fn assert_unallocated(enc: u32, what: &str) {
        match decode(enc) {
            Err(DisasmError::UnallocatedEncoding { .. }) => {}
            other => panic!("{what} ({enc:#010x}) must be UnallocatedEncoding, got {other:?}"),
        }
    }

    fn assert_unmodeled(enc: u32, mnemonic: &str) {
        match decode(enc) {
            Err(DisasmError::UnmodeledAarch64Instruction { mnemonic: m, .. }) => {
                assert!(m.contains(mnemonic), "{enc:#010x} refused as the wrong instruction: {m}");
            }
            other => {
                panic!(
                    "{mnemonic} ({enc:#010x}) must be UnmodeledAarch64Instruction, got {other:?}"
                )
            }
        }
    }

    /// Load/store register offset allocates only `option` ∈ {010, 011, 110,
    /// 111}; `option<1> == 0` is UNDEFINED. Derived from the assembler's
    /// `ldr w0,[x1,x2,lsl#2]` = b8627820 by rewriting bits[15:13]; `objdump`
    /// renders all four as `<unknown>`.
    ///
    /// 001 and 101 are the dangerous pair: the old `_ => None` arm gave them
    /// `extend: None` AND a 64-bit index (`option & 1 == 1`), which is exactly
    /// what a real `lsl` form decodes to, so they modeled as a genuine
    /// instruction rather than merely an odd one.
    #[test]
    fn reserved_load_store_register_offset_options_are_refused() {
        assert_unallocated(0xB862_1820, "register offset option=000");
        assert_unallocated(0xB862_3820, "register offset option=001");
        assert_unallocated(0xB862_9820, "register offset option=100");
        assert_unallocated(0xB862_B820, "register offset option=101");
    }

    /// ... and the four ALLOCATED options still decode, with the index register
    /// width the architecture assigns: W for UXTW/SXTW, X for LSL/SXTX.
    #[test]
    fn allocated_load_store_register_offset_options_still_decode() {
        // (encoding, expected extend, expected index width) — assembler-derived.
        let cases: &[(u32, Option<ExtendType>, u16)] = &[
            (0xB862_5820, Some(ExtendType::Uxtw), 32), // ldr w0,[x1,w2,uxtw #2]
            (0xB862_7820, None, 64),                   // ldr w0,[x1,x2,lsl #2]
            (0xB862_D820, Some(ExtendType::Sxtw), 32), // ldr w0,[x1,w2,sxtw #2]
            (0xB862_F820, Some(ExtendType::Sxtx), 64), // ldr w0,[x1,x2,sxtx #2]
        ];
        for (enc, want_extend, want_width) in cases {
            let insn = decode(*enc).unwrap_or_else(|e| panic!("{enc:#010x} must decode: {e:?}"));
            let mem = insn
                .operands()
                .find_map(|o| if let Operand::Mem(m) = o { Some(m) } else { None })
                .unwrap_or_else(|| panic!("{enc:#010x} has no memory operand"));
            match mem {
                MemoryOperand::BaseRegister { index, extend, .. } => {
                    assert_eq!(extend, want_extend, "{enc:#010x} extend");
                    assert_eq!(index.width, *want_width, "{enc:#010x} index register width");
                }
                other => panic!("{enc:#010x} is not a register-offset form: {other:?}"),
            }
        }
    }

    /// LDTR/STTR are REAL instructions (`objdump`: `ldtr w0, [x1, #0x4]`), so
    /// they are refused as UNMODELED rather than unallocated. They used to
    /// decode as the ordinary LDUR/STUR, whose effects are byte-identical.
    #[test]
    fn unprivileged_load_store_is_refused_as_unmodeled() {
        assert_unmodeled(0xB840_4820, "LDTR/STTR"); // ldtr w0,[x1,#4]
        assert_unmodeled(0xB800_4820, "LDTR/STTR"); // sttr w0,[x1,#4]

        // The privileged neighbours they were aliased onto must still decode:
        // ldur w0,[x1,#4] = b8404020, stur w0,[x1,#4] = b8004020.
        assert_eq!(decode(0xB840_4020).expect("ldur must decode").opcode, Opcode::Ldr);
        assert_eq!(decode(0xB800_4020).expect("stur must decode").opcode, Opcode::Str);
    }

    /// FCMPE is a REAL instruction (`objdump`: `fcmpe s0, s1`) that differs from
    /// FCMP only in FPSR/exception behaviour this semantics does not model, so
    /// it is refused as unmodeled. `opc<1>` used to be ignored entirely.
    #[test]
    fn fcmpe_is_refused_as_unmodeled() {
        assert_unmodeled(0x1E21_2010, "FCMPE"); // fcmpe s0,s1
        assert_unmodeled(0x1E20_2018, "FCMPE"); // fcmpe s0,#0.0
        assert_unmodeled(0x1E61_2010, "FCMPE"); // fcmpe d0,d1

        // The non-signaling forms it was aliased onto still decode.
        for enc in [0x1E21_2000u32, 0x1E20_2008, 0x1E61_2000] {
            assert_eq!(
                decode(enc).unwrap_or_else(|e| panic!("{enc:#010x}: {e:?}")).opcode,
                Opcode::Fcmp
            );
        }
    }

    /// `FCVT`'s `opcode<1:0>` IS the destination `ftype`, and the architecture
    /// requires it to differ from the source `ftype`. The two same-format pairs
    /// this decoder can reach used to fall through to `_ => fp_width`, i.e. an
    /// IDENTITY conversion — a reserved word presented as a trivially provable
    /// real instruction. `objdump` renders both as `<unknown>`.
    #[test]
    fn unallocated_fcvt_pairs_are_refused() {
        // Derived from fcvt d0,s0 = 1e22c000 (ftype=00, opcode=000101) and
        // fcvt s0,d0 = 1e624000 (ftype=01, opcode=000100) by flipping bit 15.
        assert_unallocated(0x1E22_4000, "fcvt S->S");
        assert_unallocated(0x1E62_C000, "fcvt D->D");

        // The two allocated conversions still decode, with DIFFERING widths.
        for (enc, src, dst) in [(0x1E22_C000u32, 32u16, 64u16), (0x1E62_4000, 64, 32)] {
            let insn = decode(enc).unwrap_or_else(|e| panic!("{enc:#010x}: {e:?}"));
            assert_eq!(insn.opcode, Opcode::Fcvt);
            let widths: Vec<u16> = insn
                .operands()
                .filter_map(|o| if let Operand::Reg(r) = o { Some(r.width) } else { None })
                .collect();
            assert_eq!(widths, vec![dst, src], "{enc:#010x} (dst, src) widths");
        }
    }

    /// Add/sub extended register: only the two "X" options name a 64-bit `Rm`.
    /// The old `option >= 0b100` test was wrong for FOUR of the eight options —
    /// it gave UXTX a W register and gave SXTB/SXTH/SXTW X registers.
    ///
    /// All eight words are assembler-derived (`add x0, x1, <rm>, <ext>`).
    #[test]
    fn extended_register_operand_names_the_architectural_register_width() {
        let cases: &[(u32, ExtendType, u16)] = &[
            (0x8B22_0020, ExtendType::Uxtb, 32),
            (0x8B22_2020, ExtendType::Uxth, 32),
            (0x8B22_4020, ExtendType::Uxtw, 32),
            (0x8B22_6020, ExtendType::Uxtx, 64),
            (0x8B22_8020, ExtendType::Sxtb, 32),
            (0x8B22_A020, ExtendType::Sxth, 32),
            (0x8B22_C020, ExtendType::Sxtw, 32),
            (0x8B22_E020, ExtendType::Sxtx, 64),
        ];
        for (enc, want_extend, want_width) in cases {
            let insn = decode(*enc).unwrap_or_else(|e| panic!("{enc:#010x}: {e:?}"));
            let (reg, extend) = insn
                .operands()
                .find_map(|o| match o {
                    Operand::ExtendedReg { reg, extend, .. } => Some((reg, extend)),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("{enc:#010x} has no extended-register operand"));
            assert_eq!(extend, want_extend, "{enc:#010x} extend type");
            assert_eq!(
                reg.width, *want_width,
                "{enc:#010x} ({want_extend:?}) names the wrong Rm width"
            );
        }
    }
}

/// The barrier `op2` table decides WHICH barrier a word is, and it used to map
/// DSB onto `Opcode::Dmb` — a strictly weaker barrier — while leaving the real
/// DMB undecodable.
///
/// All ten words are assembler-derived.
#[cfg(test)]
mod barrier_selector_tests {
    use crate::decode_aarch64;
    use crate::opcode::Opcode;

    fn opcode_of(enc: u32) -> Opcode {
        decode_aarch64(&enc.to_le_bytes(), 0x1000)
            .unwrap_or_else(|e| panic!("{enc:#010x} must decode: {e:?}"))
            .opcode
    }

    #[test]
    fn dmb_and_dsb_are_not_confused() {
        // op2 = 101
        for (enc, what) in [
            (0xD503_3FBFu32, "dmb sy"),
            (0xD503_3DBF, "dmb ld"),
            (0xD503_3EBF, "dmb st"),
            (0xD503_3BBF, "dmb ish"),
            (0xD503_39BF, "dmb ishld"),
        ] {
            assert_eq!(opcode_of(enc), Opcode::Dmb, "{what} ({enc:#010x})");
        }
        // op2 = 100 — every one of these used to decode as Opcode::Dmb.
        for (enc, what) in [
            (0xD503_3F9Fu32, "dsb sy"),
            (0xD503_3D9F, "dsb ld"),
            (0xD503_3E9F, "dsb st"),
            (0xD503_3B9F, "dsb ish"),
            (0xD503_3A9F, "dsb ishst"),
        ] {
            assert_eq!(opcode_of(enc), Opcode::Dsb, "{what} ({enc:#010x})");
        }
        assert_eq!(opcode_of(0xD503_3FDF), Opcode::Isb, "isb");
        assert_eq!(opcode_of(0xD503_3F5F), Opcode::Clrex, "clrex");
    }
}
