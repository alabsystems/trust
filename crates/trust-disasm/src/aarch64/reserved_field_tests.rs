// AArch64 reserved / fixed / sf-dependent field validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
//! THE DECODER MUST REFUSE WHAT THE ARCHITECTURE DOES NOT ALLOCATE, AND MUST
//! NEVER RESOLVE ONE ALLOCATED ENCODING ONTO ANOTHER.
//!
//! Every word in this file came out of the CLANG TOOLCHAIN and was read back
//! with `objdump` (Apple LLVM 21); none is hand-encoded. Two derivations are
//! used, and each case records which:
//!
//!   * ASSEMBLED — written as source (`add w3, w1, w1, lsr #31`), assembled, and
//!     the word read out of `__text`.
//!   * DERIVED — an assembled word with ONE named field rewritten, then fed back
//!     through the same toolchain (`.incbin` into `__text`, so the assembler
//!     never re-encodes it) to record what `objdump` answers. The recorded
//!     answer is quoted in each case.
//!
//! `objdump` decodes with the full feature set — it prints `stg`, `ldraa`,
//! `addpt`, `ldumaxl`, `rprfm`, `bc.eq` — so a word it answers `<unknown>` is
//! not an allocated instruction under any current architectural extension.
//!
//! Each test pairs the REFUSAL with a CONTROL: the neighbouring real instruction
//! that the broken decoder used to answer with, which must still decode. A
//! refusal that also breaks the legal encoding is not a fix.

use crate::decode_aarch64;
use crate::error::DisasmError;
use crate::instruction::Instruction;
use crate::opcode::Opcode;
use crate::operand::{Operand, ShiftType};

fn decode(enc: u32) -> Result<Instruction, DisasmError> {
    decode_aarch64(&enc.to_le_bytes(), 0x1000)
}

/// The word must be REFUSED. Which refusal variant is a diagnostic choice;
/// that a plausible instruction comes back is the defect.
#[track_caller]
fn refused(enc: u32, objdump_says: &str) {
    match decode(enc) {
        Err(_) => {}
        Ok(insn) => panic!(
            "{enc:08x} (objdump: {objdump_says}) decoded as {:?} {:?} — a word the \
             architecture does not allocate here, presented to the machine model as a \
             real instruction",
            insn.opcode,
            insn.operands().collect::<Vec<_>>()
        ),
    }
}

/// The word must decode, and to the named opcode.
#[track_caller]
fn decodes_as(enc: u32, want: Opcode, asm: &str) -> Instruction {
    let insn = decode(enc).unwrap_or_else(|e| panic!("{asm} ({enc:08x}) must decode: {e:?}"));
    assert_eq!(insn.opcode, want, "{asm} ({enc:08x}) decoded as the wrong opcode");
    insn
}

// ===========================================================================
// sf-dependent shift amounts — the reported exemplar
// ===========================================================================

/// `imm6<5>` is a fixed 0 in the 32-bit shifted-register forms: a W register has
/// no bit 32..63 to shift by.
///
/// ASSEMBLED: `and x9,x9,x9,lsl #32` = 8a098129, `and w9,w9,w9,lsl #31` =
/// 0a097d29, `adds x0,x1,x2,lsr #40` = ab42a020.
/// DERIVED: 8a098129 with sf cleared = 0a098129, objdump `<unknown>`;
/// ab42a020 with sf cleared = 2b42a020, objdump `<unknown>`.
///
/// 0a098129 is the word this whole pass started from: NATIVE EXECUTION answers
/// SIGILL (exit 132), `objdump` answers `<unknown>`, and this decoder answered
/// `And` with `ShiftedReg { Lsl, amount: 32 }` — from which the semantics built a
/// full effect list and the output gate certified the containing object `Proven`
/// at the kernel-re-checkable grade.
#[test]
fn thirty_two_bit_shifted_register_rejects_shift_amounts_above_31() {
    refused(0x0A09_8129, "<unknown> — and w9,w9,w9,lsl #32");
    refused(0x2B42_A020, "<unknown> — adds w0,w1,w2,lsr #40");

    // The 64-bit sibling and the legal 32-bit shift must still decode.
    let insn = decodes_as(0x8A09_8129, Opcode::And, "and x9,x9,x9,lsl #32");
    assert!(
        insn.operands()
            .any(|o| matches!(o, Operand::ShiftedReg { shift: ShiftType::Lsl, amount: 32, .. })),
        "the 64-bit form must keep its shift of 32"
    );
    decodes_as(0x0A09_7D29, Opcode::And, "and w9,w9,w9,lsl #31");
    decodes_as(0xAB42_A020, Opcode::Adds, "adds x0,x1,x2,lsr #40");
}

/// Same fixed field in the bitfield and extract groups: `immr` and `imms` name
/// bit positions, so their top bit is 0 when the register is 32 bits wide.
///
/// ASSEMBLED: `ubfx w0,w1,#3,#4` = 53031820, `ubfx x0,x1,#40,#4` = d368ac20,
/// `extr w0,w1,w2,#31` = 13827c20.
/// DERIVED: 53031820 with `immr<5>` set = 53231820 and with `imms<5>` set =
/// 53039820; 13827c20 with `imms<5>` set = 1382fc20. objdump: all `<unknown>`.
///
/// This is the DECODE-SIDE half of the `width - immr` underflow in
/// `trust-machine-sem`'s `sem_ubfm` / `sem_sbfm` / `sem_bfm` and of
/// `width - field_width` on their other path. With `width == 32` both wrap, and
/// in a release build — how `trustc` ships — they wrap SILENTLY.
#[test]
fn thirty_two_bit_bitfield_and_extract_reject_positions_above_31() {
    refused(0x5323_1820, "<unknown> — ubfx w0,w1 with immr=35");
    refused(0x5303_9820, "<unknown> — ubfx w0,w1 with imms=38");
    refused(0x1382_FC20, "<unknown> — extr w0,w1,w2 with imms=63");

    decodes_as(0x5303_1820, Opcode::Ubfm, "ubfx w0,w1,#3,#4");
    decodes_as(0xD368_AC20, Opcode::Ubfm, "ubfx x0,x1,#40,#4");
    decodes_as(0x1382_7C20, Opcode::Extr, "extr w0,w1,w2,#31");
}

// ===========================================================================
// Fixed fields the decoder simply never read
// ===========================================================================

/// EXTR fixes `op21` (bits[30:29]) and `o0` (bit 21) at zero.
///
/// DERIVED from `extr w0,w1,w2,#31` = 13827c20: bit 21 set = 13a27c20,
/// bits[30:29] = 01 = 33827c20. objdump: both `<unknown>`.
#[test]
fn extract_rejects_nonzero_fixed_fields() {
    refused(0x13A2_7C20, "<unknown> — extr with o0=1");
    refused(0x3382_7C20, "<unknown> — extr with op21=01");
    decodes_as(0x1382_7C20, Opcode::Extr, "extr w0,w1,w2,#31");
}

/// Data-processing (3 source) fixes `op54` (bits[30:29]) at 00. Three quarters
/// of the slot decoded as MADD/MSUB/SMULH.
///
/// DERIVED from `madd w0,w1,w2,w3` = 1b020c20 with bits[30:29]=01 = 3b020c20,
/// objdump `<unknown>`.
#[test]
fn dp_three_source_rejects_nonzero_op54() {
    refused(0x3B02_0C20, "<unknown> — madd shape with op54=01");
    decodes_as(0x1B02_0C20, Opcode::Madd, "madd w0,w1,w2,w3");
    decodes_as(0x9B42_7C20, Opcode::Smulh, "smulh x0,x1,x2");
}

/// Add/subtract with carry fixes bits[15:10] at 000000. That slot holds RMIF,
/// ADDPT/SUBPT and SETF8/SETF16 — none of them an add.
///
/// ASSEMBLED: `adc x0,x1,x2` = 9a020020, `sbcs w0,w1,w2` = 7a020020.
/// DERIVED: 9a020020 with bit 10 set = 9a020420, objdump `<unknown>`.
/// FROM THE SWEEP (objdump-confirmed): 9a002000 `addpt x0,x0,x0`,
/// ba000420 `rmif`.
#[test]
fn add_sub_with_carry_rejects_nonzero_opcode2() {
    refused(0x9A02_0420, "<unknown> — adc shape with bits[15:10]=000001");
    refused(0x9A00_2000, "addpt x0,x0,x0");
    refused(0xBA00_0420, "rmif");

    decodes_as(0x9A02_0020, Opcode::Adc, "adc x0,x1,x2");
    decodes_as(0x7A02_0020, Opcode::Sbcs, "sbcs w0,w1,w2");
}

/// Add/subtract (extended register) allows `imm3` ∈ 0..=4 only.
///
/// DERIVED from `add x0,x1,x2,uxtx #4` = 8b227020 with imm3=5 = 8b227420,
/// objdump `<unknown>`.
#[test]
fn extended_register_rejects_shift_amounts_above_four() {
    refused(0x8B22_7420, "<unknown> — add x0,x1,x2,uxtx with imm3=5");
    decodes_as(0x8B22_7020, Opcode::Add, "add x0,x1,x2,uxtx #4");
    decodes_as(0x0B22_0020, Opcode::Add, "add w0,w1,w2,uxtb");
}

/// Conditional compare fixes `S` (bit 29) at 1 and bits[24:21] at 0010;
/// `decode_dp_reg` routes 0011 here as well.
///
/// DERIVED from `ccmp x0,x1,#0,eq` = fa410000: S cleared = da410000, bit 21 set
/// = fa610000. objdump: both `<unknown>`.
#[test]
fn conditional_compare_rejects_cleared_s_and_bit21() {
    refused(0xDA41_0000, "<unknown> — ccmp shape with S=0");
    refused(0xFA61_0000, "<unknown> — ccmp shape with bits[24:21]=0011");
    decodes_as(0xFA41_0000, Opcode::Ccmp, "ccmp x0,x1,#0,eq");
    decodes_as(0x3A43_1802, Opcode::Ccmn, "ccmn w0,#3,#2,ne");
}

/// Conditional select is bits[24:21] == 0100; `decode_dp_reg` also routed 0101.
///
/// DERIVED from `csel x0,x1,x2,eq` = 9a820020 with bit 21 set = 9aa20020,
/// objdump `<unknown>`.
#[test]
fn conditional_select_rejects_bit21() {
    refused(0x9AA2_0020, "<unknown> — csel shape with bits[24:21]=0101");
    decodes_as(0x9A82_0020, Opcode::Csel, "csel x0,x1,x2,eq");
    decodes_as(0x5A82_4420, Opcode::Csneg, "csneg w0,w1,w2,mi");
}

/// Data-processing (1 source) fixes `S` at 0 and `opcode2` (bits[20:16]) at
/// 00000, and `opcode == 000011` (REV of a full register) exists only for sf=1.
/// The `opcode2` space is POINTER AUTHENTICATION.
///
/// ASSEMBLED: `rbit w0,w1` = 5ac00020, `rev x0,x1` = dac00c20,
/// `rev w0,w1` = 5ac00820, `clz w0,w1` = 5ac01020.
/// DERIVED: 5ac00020 with opcode2=1 = 5ac10020 (`<unknown>`), with S set =
/// 7ac00020 (`<unknown>`); dac00c20 with sf cleared = 5ac00c20 (`<unknown>`).
/// FROM THE SWEEP: dac10000 `pacia x0,x0`.
#[test]
fn dp_one_source_rejects_pointer_auth_and_reserved_fields() {
    refused(0xDAC1_0000, "pacia x0,x0");
    refused(0x5AC1_0020, "<unknown> — rbit shape with opcode2=00001");
    refused(0x7AC0_0020, "<unknown> — rbit shape with S=1");
    refused(0x5AC0_0C20, "<unknown> — 64-bit REV opcode with sf=0");

    decodes_as(0x5AC0_0020, Opcode::Rbit, "rbit w0,w1");
    decodes_as(0xDAC0_0C20, Opcode::Rev, "rev x0,x1");
    decodes_as(0x5AC0_0820, Opcode::Rev, "rev w0,w1");
    decodes_as(0xDAC0_0820, Opcode::Rev32, "rev32 x0,x1");
    decodes_as(0x5AC0_1020, Opcode::Clz, "clz w0,w1");
}

/// Exception generation fixes bits[4:2] at 000; all eight values decoded as the
/// same exception, so `d4000005` came back as `Svc` — an unallocated word
/// presented as a system call.
///
/// DERIVED from `svc #0` = d4000001 with bits[4:2]=001 = d4000005,
/// objdump `<unknown>`.
#[test]
fn exception_generation_rejects_nonzero_op2() {
    refused(0xD400_0005, "<unknown> — svc shape with op2=001");
    decodes_as(0xD400_0001, Opcode::Svc, "svc #0");
    decodes_as(0xD420_0020, Opcode::Brk, "brk #1");
    decodes_as(0xD440_0040, Opcode::Hlt, "hlt #2");
}

/// FP compare fixes `op` (bits[15:14]) and the low three bits of `opcode2`.
///
/// DERIVED from `fcmp s0,s1` = 1e212000: bit 14 set = 1e216000, bit 0 set =
/// 1e212001. objdump: both `<unknown>`.
#[test]
fn fp_compare_rejects_nonzero_fixed_fields() {
    refused(0x1E21_6000, "<unknown> — fcmp shape with op=01");
    refused(0x1E21_2001, "<unknown> — fcmp shape with opcode2<2:0>=001");
    decodes_as(0x1E21_2000, Opcode::Fcmp, "fcmp s0,s1");
    decodes_as(0x1E60_2008, Opcode::Fcmp, "fcmp d0,#0.0");
}

// ===========================================================================
// One allocated encoding resolved onto a DIFFERENT allocated encoding
// ===========================================================================

/// Load register (literal) is `opc 011 V 00 imm19 Rt`: bits[25:24] are a fixed
/// 00 and NOBODY tested bit 24. The bit-24 space is the memory-tagging
/// (STG/STZG/LDG) and LDAPUR/STLUR groups — half of which WRITE MEMORY.
///
/// FROM THE SWEEP (objdump-confirmed): 190000c0 `stlurb w0,[x6]`,
/// 99000040 `stlur w0,[x2]`, d92089b0 `stg x16,[x13,#128]`,
/// 19000400 `<unknown>`.
///
/// `stg` decoded as `Prfm`, whose operand shape has no destination at all: a
/// STORE presented to the model as an instruction that does nothing.
#[test]
fn load_literal_rejects_the_bit24_space() {
    refused(0x1900_00C0, "stlurb w0,[x6] — a STORE decoded as LdrLiteral");
    refused(0x9900_0040, "stlur w0,[x2] — a STORE decoded as Ldrsw");
    refused(0xD920_89B0, "stg x16,[x13,#128] — a STORE decoded as Prfm, effects EMPTY");
    refused(0x1900_0400, "<unknown>");

    // ASSEMBLED literal loads must all still decode.
    decodes_as(0x5800_00C0, Opcode::LdrLiteral, "ldr x0,<label>");
    decodes_as(0x1800_00A1, Opcode::LdrLiteral, "ldr w1,<label>");
    decodes_as(0x9800_0082, Opcode::Ldrsw, "ldrsw x2,<label>");
    decodes_as(0xD800_0060, Opcode::Prfm, "prfm pldl1keep,<label>");
}

/// Add/subtract (immediate) is bits[25:23] == 010. `decode_dp_imm` also routes
/// 011, which is ADDG/SUBG (tagged add/subtract) and the FEAT_CSSC min/max
/// immediates.
///
/// FROM THE SWEEP: 11c00020 `smax w0,w1,#0`, 11800000 `<unknown>`.
#[test]
fn add_sub_immediate_rejects_the_tagged_and_minmax_space() {
    refused(0x11C0_0020, "smax w0,w1,#0 — decoded as Add");
    refused(0x1180_0000, "<unknown>");
    decodes_as(0x9100_1020, Opcode::Add, "add x0,x1,#4");
}

/// B.cond fixes bit 24 at 0 and `o0` (bit 4) at 0. `o0 == 1` is BC.cond
/// (FEAT_HBC), a real and DIFFERENT branch that this decoder answered `BCond`
/// for — 14,238 words in the sweep.
///
/// ASSEMBLED: `b.eq .` = 54000000.
/// FROM THE SWEEP: 54000010 `bc.eq`, 55000000 `<unknown>`.
#[test]
fn b_cond_rejects_bc_cond_and_the_bit24_space() {
    match decode(0x5400_0010) {
        Err(DisasmError::UnmodeledAarch64Instruction { mnemonic, .. }) => {
            assert!(mnemonic.contains("BC.cond"), "refused as the wrong instruction: {mnemonic}");
        }
        other => panic!("bc.eq (54000010) must be refused as unmodeled, got {other:?}"),
    }
    refused(0x5500_0000, "<unknown>");
    decodes_as(0x5400_0000, Opcode::BCond, "b.eq .");
}

/// BR/BLR/RET fix `op2` = 11111, `op3` = 000000 and `op4` = 00000. Only `opc`
/// and `Rn` were read: of 128,828 words reaching this function in the sweep,
/// exactly 96 are real BR/BLR/RET and 44,053 decoded as one. `op3`/`op4` select
/// the pointer-authenticated branches, which AUTHENTICATE the target.
///
/// ASSEMBLED: `br x0` = d61f0000, `blr x1` = d63f0020, `ret` = d65f03c0,
/// `ret x5` = d65f00a0.
/// DERIVED: op2=11110 = d61e0000, op3=000001 = d61f0400, op4=00001 = d61f0001;
/// objdump `<unknown>` for all three.
/// FROM THE SWEEP: d65f0be0 `retaasppcr x0`.
#[test]
fn branch_register_rejects_nonzero_op2_op3_op4() {
    refused(0xD61E_0000, "<unknown> — br shape with op2=11110");
    refused(0xD61F_0400, "<unknown> — br shape with op3=000001");
    refused(0xD61F_0001, "<unknown> — br shape with op4=00001");
    refused(0xD65F_0BE0, "retaasppcr x0 — an AUTHENTICATED return decoded as Ret");

    decodes_as(0xD61F_0000, Opcode::Br, "br x0");
    decodes_as(0xD63F_0020, Opcode::Blr, "blr x1");
    decodes_as(0xD65F_03C0, Opcode::Ret, "ret");
    decodes_as(0xD65F_00A0, Opcode::Ret, "ret x5");
}

/// Every barrier encoding fixes `Rt` at 11111. The HINT route one arm above
/// tests that; the BARRIER route did not, so the whole `Rt != 31` space — which
/// objdump names `msr` — decoded as `Clrex`. A SYSTEM REGISTER WRITE presented
/// as an exclusive-monitor clear.
///
/// ASSEMBLED: `dmb ish` = d5033bbf, `dsb sy` = d5033f9f, `isb` = d5033fdf,
/// `clrex` = d5033f5f.
/// DERIVED: d5033bbf with Rt=3 = d5033ba3, objdump `msr S0_3_C3_C11_5, x3`.
/// FROM THE SWEEP: d50333af `msr S0_3_C3_C3_5, x15`.
#[test]
fn barrier_rejects_system_register_writes() {
    refused(0xD503_3BA3, "msr S0_3_C3_C11_5, x3 — decoded as a barrier");
    refused(0xD503_33AF, "msr S0_3_C3_C3_5, x15 — decoded as Clrex");

    decodes_as(0xD503_3BBF, Opcode::Dmb, "dmb ish");
    decodes_as(0xD503_3F9F, Opcode::Dsb, "dsb sy");
    decodes_as(0xD503_3FDF, Opcode::Isb, "isb");
    decodes_as(0xD503_3F5F, Opcode::Clrex, "clrex");
}

/// The exclusive group: `o1` (bit 21) selects the PAIR and COMPARE-AND-SWAP
/// forms, and `size` is the ACCESS WIDTH. Neither was validated, so `ldxp`
/// decoded as `Ldxr` (half the register file silently dropped) and `ldxrb`
/// decoded as `Ldxr` — a ONE-BYTE access modeled as FOUR.
///
/// ASSEMBLED: `ldxr w0,[x1]` = 885f7c20, `stxr w0,w1,[x2]` = 88007c41,
/// `ldar x0,[x1]` = c8dffc20, `stlr x3,[x4]` = c89ffc83,
/// `ldaxr x0,[x1]` = c85ffc20, `stlxr w0,x1,[x2]` = c800fc41.
/// DERIVED: 885f7c20 with bit 21 set = 887f7c20, objdump `ldxp w0, wzr, [x1]`;
/// with size=00 = 085f7c20, objdump `ldxrb w0, [x1]`.
/// FROM THE SWEEP: 08007c01 `stxrb w0,w1,[x0]`.
#[test]
fn exclusive_rejects_pair_cas_and_sub_word_widths() {
    refused(0x887F_7C20, "ldxp w0,wzr,[x1] — a PAIR load decoded as Ldxr");
    refused(0x085F_7C20, "ldxrb w0,[x1] — a 1-byte access decoded as a 4-byte Ldxr");
    refused(0x0800_7C01, "stxrb w0,w1,[x0] — a 1-byte store decoded as a 4-byte Stxr");

    decodes_as(0x885F_7C20, Opcode::Ldxr, "ldxr w0,[x1]");
    decodes_as(0x8800_7C41, Opcode::Stxr, "stxr w0,w1,[x2]");
    decodes_as(0xC8DF_FC20, Opcode::Ldar, "ldar x0,[x1]");
    decodes_as(0xC89F_FC83, Opcode::Stlr, "stlr x3,[x4]");
    decodes_as(0xC85F_FC20, Opcode::Ldaxr, "ldaxr x0,[x1]");
    decodes_as(0xC800_FC41, Opcode::Stlxr, "stlxr w0,x1,[x2]");
}

/// The load/store register-offset form fixes bits[11:10] at 10. Everything else
/// in that slot is the ATOMIC memory-operation space, the LDAPR/STLR register
/// forms and the pointer-authenticated loads — dispatched on bit 21 alone, all
/// of it decoded as a plain load or store.
///
/// FROM THE SWEEP: b8606000 `ldumaxl w0,w0,[x0]` (an atomic READ-MODIFY-WRITE
/// decoded as `Ldr`, so the write vanishes) and f820666b `ldraa x11,[x19,#48]`
/// (a LOAD decoded as `Str`).
///
/// FEAT_RPRFM's range prefetch shares the PRFM (register) slot and is selected
/// by `Rt<4:3> == 11`; its `Rm` is a range descriptor, not an index register.
/// DERIVED by sweeping Rt over `f8a068<rt>`: objdump answers `prfm <prfop>` for
/// Rt ≤ 23 and `rprfm #<n>, x0, [x1]` for Rt ≥ 24.
///
/// PRFM has no pre/post-indexed form — `Rt` is the prefetch operation, not a
/// destination, so there is nothing to write an updated base into.
/// DERIVED from `prfum pldl1keep,[x1,#-8]` = f89f8020 with bits[11:10]=01 =
/// f89f8420, objdump `<unknown>`.
#[test]
fn load_store_register_rejects_atomics_rprfm_and_indexed_prefetch() {
    refused(0xB860_6000, "ldumaxl w0,w0,[x0] — an atomic RMW decoded as Ldr");
    refused(0xF820_666B, "ldraa x11,[x19,#48] — a LOAD decoded as Str");
    refused(0xF8A0_6838, "rprfm #16, x0, [x1]");
    refused(0xF8A0_4A1B, "rprfm #3, x0, [x16]");
    refused(0xF89F_8420, "<unknown> — post-indexed PRFM");

    decodes_as(0xF8A2_6820, Opcode::Prfm, "prfm pldl1keep,[x1,x2]");
    decodes_as(0xF980_0420, Opcode::Prfm, "prfm pldl1keep,[x1,#8]");
    decodes_as(0xF89F_8020, Opcode::Prfm, "prfum pldl1keep,[x1,#-8]");
    decodes_as(0xB862_7820, Opcode::Ldr, "ldr w0,[x1,x2,lsl #2]");
    decodes_as(0xF840_8C20, Opcode::Ldr, "ldr x0,[x1,#8]!");
    decodes_as(0xB800_4420, Opcode::Str, "str w0,[x1],#4");
}

/// FP↔integer conversion fixes bits[15:10] at 000000, and FMOV (general) needs
/// `sf` and `ftype` to name the SAME width — it moves bits.
///
/// ASSEMBLED: `scvtf s0,w0` = 1e220000, `fmov w0,s0` = 1e260000,
/// `fmov x0,d0` = 9e660000, `fcvtzs w0,s0` = 1e380000.
/// DERIVED: 1e220000 with bit 10 set = 1e220400, objdump `fccmp s0, s2, #0, eq`;
/// 1e260000 with sf set = 9e260000, objdump `<unknown>` (a 64-bit GPR paired
/// with a 32-bit S register).
/// FROM THE SWEEP: 1e220420 `fccmp s1,s2,#0,eq`.
///
/// FCCMP writes NZCV and no register; SCVTF writes a register and no flags.
#[test]
fn fp_int_conversion_rejects_fccmp_and_mismatched_fmov_widths() {
    refused(0x1E22_0400, "fccmp s0,s2,#0,eq — decoded as Scvtf");
    refused(0x1E22_0420, "fccmp s1,s2,#0,eq — decoded as Scvtf");
    refused(0x9E26_0000, "<unknown> — fmov pairing a 64-bit GPR with a 32-bit S");

    decodes_as(0x1E22_0000, Opcode::Scvtf, "scvtf s0,w0");
    decodes_as(0x9E63_0020, Opcode::Ucvtf, "ucvtf d0,x1");
    decodes_as(0x1E26_0000, Opcode::FmovReg, "fmov w0,s0");
    decodes_as(0x9E66_0000, Opcode::FmovReg, "fmov x0,d0");
    decodes_as(0x1E27_0000, Opcode::FmovReg, "fmov s0,w0");
    decodes_as(0x9E67_0000, Opcode::FmovReg, "fmov d0,x0");
    decodes_as(0x1E38_0000, Opcode::Fcvtzs, "fcvtzs w0,s0");
    decodes_as(0x9E79_0000, Opcode::Fcvtzu, "fcvtzu x0,d0");
}

// ===========================================================================
// Dispatch bugs: a real instruction routed to the wrong decoder
// ===========================================================================

/// FMOV (immediate) is selected by bits[12:10] == 100. `decode_simd_fp` tested
/// bits[13:10] == 0100 — but BIT 13 IS `imm8<0>`. Every FMOV-immediate with an
/// ODD `imm8` therefore missed the test and fell through to
/// `decode_fp_int_conv`, which read `rmode`/`opcode` out of the immediate's
/// other bits and answered `FmovReg`: a CONSTANT MATERIALIZATION presented as a
/// register-to-register move, so the model propagates whatever was in the
/// source register.
///
/// ASSEMBLED, with `imm8` = bits[20:13] of the assembled word: `fmov s0,#1.0` =
/// 1e2e1000 (imm8 = 112, EVEN — the case that always worked),
/// `fmov s0,#1.0625` = 1e2e3000 (imm8 = 113, ODD), `fmov d1,#-1.0625` =
/// 1e7e3001 (241), `fmov s4,#17.0` = 1e263004 (49), `fmov s3,#-13.0` =
/// 1e355003 (170), `fmov d0,#2.0` = 1e601000 (0).
#[test]
fn fp_immediate_with_an_odd_imm8_is_not_a_register_move() {
    for (enc, imm8, asm) in [
        (0x1E2E_1000u32, 112u64, "fmov s0,#1.0"),
        (0x1E2E_3000, 113, "fmov s0,#1.0625"),
        (0x1E7E_3001, 241, "fmov d1,#-1.0625"),
        (0x1E26_3004, 49, "fmov s4,#17.0"),
        (0x1E35_5003, 170, "fmov s3,#-13.0"),
        (0x1E60_1000, 0, "fmov d0,#2.0"),
    ] {
        let insn = decodes_as(enc, Opcode::FmovImm, asm);
        let got = insn
            .operands()
            .find_map(|o| if let Operand::Imm(v) = o { Some(*v) } else { None })
            .unwrap_or_else(|| panic!("{asm} ({enc:08x}) has no immediate operand"));
        assert_eq!(got, imm8, "{asm} ({enc:08x}) decoded the wrong imm8");
    }
}

/// COMPLETENESS: add/subtract (shifted register) is selected by bit 21 alone;
/// bits[23:22] are the SHIFT TYPE. `decode_dp_reg` tested `op2 == 0b1000`, which
/// admits only LSL, so every add/sub with an LSR or ASR shift fell out of the
/// dispatch as `UnknownEncoding` and no function could verify.
///
/// `add w3,w1,w1,lsr #31` is the signed divide-by-two idiom; the emitted corpus
/// contains 6 distinct such words across 44 occurrences.
///
/// ASSEMBLED: `add w3,w1,w1,lsr #31` = 0b417c23, `add w3,w1,w1,asr #5` =
/// 0b811423, `sub w0,w1,w2,asr #7` = 4b821c20, `adds x0,x1,x2,lsr #40` =
/// ab42a020, `add x3,x1,x1,lsl #3` = 8b010c23.
#[test]
fn add_sub_shifted_register_accepts_lsr_and_asr() {
    for (enc, op, shift, amount, asm) in [
        (0x0B41_7C23u32, Opcode::Add, ShiftType::Lsr, 31u8, "add w3,w1,w1,lsr #31"),
        (0x0B81_1423, Opcode::Add, ShiftType::Asr, 5, "add w3,w1,w1,asr #5"),
        (0x4B82_1C20, Opcode::Sub, ShiftType::Asr, 7, "sub w0,w1,w2,asr #7"),
        (0xAB42_A020, Opcode::Adds, ShiftType::Lsr, 40, "adds x0,x1,x2,lsr #40"),
        (0x8B01_0C23, Opcode::Add, ShiftType::Lsl, 3, "add x3,x1,x1,lsl #3"),
    ] {
        let insn = decodes_as(enc, op, asm);
        let found = insn.operands().any(|o| {
            matches!(o, Operand::ShiftedReg { shift: s, amount: a, .. }
                if *s == shift && *a == amount)
        });
        assert!(
            found,
            "{asm} ({enc:08x}) lost its shift: {:?}",
            insn.operands().collect::<Vec<_>>()
        );
    }
}
