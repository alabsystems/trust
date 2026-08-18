// AArch64 CONSTRAINED UNPREDICTABLE operand-constraint validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
//! THE DECODER MUST REFUSE OPERAND COMBINATIONS THE ARCHITECTURE LEAVES
//! UNDEFINED, NOT ONLY FIELD PATTERNS IT DOES NOT ALLOCATE.
//!
//! `reserved_field_tests` closed the FIELD family: words whose fixed, reserved
//! or `sf`-dependent bits are wrong. This file closes the family that survived
//! it. Here every field is valid — the words are architecturally well-formed
//! and objdump NAMES them, so a mnemonic-level differential against the
//! reference classes them OK — and the CPU still refuses them. What is out of
//! bounds is the coincidence of two register NUMBERS.
//!
//! Four constraints, all from the ARM ARM (DDI 0487) `ConstrainUnpredictable`
//! calls in the relevant instruction pseudocode:
//!
//!   R1  load/store register, immediate pre/post-indexed
//!       `t == n && n != 31`            Unpredictable_WBOVERLAPLD / …ST
//!   R2  load pair (LDP, LDPSW)
//!       `t == t2`                      Unpredictable_LDPOVERLAP
//!   R3  load/store pair, pre/post-indexed
//!       `(t == n || t2 == n) && n != 31`
//!                                      Unpredictable_WBOVERLAPLD / …ST
//!   R4  store exclusive (STXR, STLXR)
//!       `s == t || (s == n && n != 31)` Unpredictable_DATAOVERLAP
//!
//! DERIVATION. Every word here came out of the CLANG TOOLCHAIN; none is
//! hand-encoded. Each case records both halves:
//!
//!   * ASSEMBLED — the CONTROL. Written as source, assembled, and the word read
//!     back out of `__text` with objdump.
//!   * DERIVED   — the ALIASED word. Exactly ONE register field of the
//!     assembled control is rewritten, and the result fed back through the same
//!     toolchain by `.incbin` (so the assembler never re-encodes it) to record
//!     objdump's answer. That answer is quoted in each case.
//!
//! THE CONTROL IS PART OF THE TEST. A refusal that also breaks the neighbouring
//! legal encoding is not a fix, so every aliased word is paired with the word
//! that differs from it in ONE register and must still decode. The BOUNDARY
//! cases go further: they pin the exemptions (`n == 31`, store pair, no
//! writeback) that a slightly-too-wide rule would swallow.
//!
//! TWO INDEPENDENT ORACLES agree with each refusal, and where they disagree
//! that is recorded rather than hidden:
//!
//!   * the ASSEMBLER refuses to encode the source form ("unpredictable LDR
//!     instruction, writeback base is also a source"), for 15 of the 16 aliased
//!     words. The exception is `ldpsw x1,x1,[x10,#40]!`. clang applies its
//!     `Rt2==Rt` check UNEVENLY across addressing modes — it catches
//!     `ldp w0,w0,[x2]` and `ldpsw x6,x6,[x9],#8` but encodes
//!     `ldp w0,w0,[x2],#8` and `ldpsw x1,x1,[x10,#40]!` — so the assembler is
//!     corroboration here, never the authority. Eight such clang-accepted words
//!     were executed: all eight SIGILL, all eight one-register controls run. An
//!     assembler gap, not an architectural permission.
//!   * NATIVE EXECUTION, each word alone in its own process with every GPR
//!     pointing at a mapped page-aligned buffer, answers SIGILL for all twelve
//!     R1/R2/R3 words while every control executes. The four R4 words EXECUTE
//!     rather than faulting; see `store_exclusive_*` below for why they are
//!     refused anyway and what was measured instead.

use crate::decode_aarch64;
use crate::error::DisasmError;
use crate::instruction::Instruction;
use crate::opcode::Opcode;
use crate::operand::{MemoryOperand, Operand};

fn decode(enc: u32) -> Result<Instruction, DisasmError> {
    decode_aarch64(&enc.to_le_bytes(), 0x1000)
}

/// The word must be refused, and refused AS a constrained-unpredictable operand
/// combination. The variant matters here: `UnallocatedEncoding` would claim the
/// architecture does not allocate the encoding, which is false — objdump names
/// it — and would misdirect anyone reading the diagnostic.
#[track_caller]
fn refused_as_constrained(enc: u32, objdump_says: &str) {
    match decode(enc) {
        Err(DisasmError::ConstrainedUnpredictableOperands { encoding, .. }) => {
            assert_eq!(encoding, enc, "the error must carry the word it refused");
        }
        Err(other) => panic!(
            "{enc:08x} (objdump: {objdump_says}) was refused as {other:?} — it IS an allocated \
             encoding; refusing it as anything but a CONSTRAINED UNPREDICTABLE operand \
             combination misstates why the CPU will not run it"
        ),
        Ok(insn) => panic!(
            "{enc:08x} (objdump: {objdump_says}) decoded as {:?} {:?} — an operand combination \
             the architecture leaves CONSTRAINED UNPREDICTABLE, handed to the machine model as \
             an instruction with a definite effect",
            insn.opcode,
            insn.operands().collect::<Vec<_>>()
        ),
    }
}

/// The word must decode, and to the named opcode. Used for every control and
/// every boundary case.
#[track_caller]
fn decodes_as(enc: u32, want: Opcode, asm: &str) -> Instruction {
    let insn = decode(enc).unwrap_or_else(|e| panic!("{asm} ({enc:08x}) must decode: {e:?}"));
    assert_eq!(insn.opcode, want, "{asm} ({enc:08x}) decoded as the wrong opcode");
    insn
}

/// Register indexes the decoded instruction carries, transfer registers first.
fn regs(insn: &Instruction) -> Vec<u8> {
    insn.operands()
        .filter_map(|o| match o {
            Operand::Reg(r) => Some(r.index),
            _ => None,
        })
        .collect()
}

fn writeback_base(insn: &Instruction) -> Option<u8> {
    insn.operands().find_map(|o| match o {
        Operand::Mem(MemoryOperand::PreIndex { base, .. })
        | Operand::Mem(MemoryOperand::PostIndex { base, .. }) => Some(base.index),
        _ => None,
    })
}

// ===========================================================================
// R1 — load/store register, immediate pre/post-indexed: Rt == Rn, Rn != 31
// ===========================================================================

/// The reported exemplar. ASSEMBLED: `str x29,[x30],#-21` = f81eb7dd.
/// DERIVED: Rt[4:0] rewritten 29 -> 30 = f81eb7de, objdump `str x30, [x30], #-21`.
///
/// NATIVE: f81eb7de SIGILL, f81eb7dd executes. clang refuses to assemble the
/// aliased source form: "unpredictable STR instruction, writeback base is also
/// a source".
#[test]
fn post_indexed_store_rejects_transfer_register_aliasing_the_writeback_base() {
    refused_as_constrained(0xF81E_B7DE, "str x30, [x30], #-21");

    let insn = decodes_as(0xF81E_B7DD, Opcode::Str, "str x29,[x30],#-21");
    assert_eq!(writeback_base(&insn), Some(30), "the control keeps its post-index writeback");
    assert_eq!(regs(&insn), vec![29], "the control transfers x29, not the base");
}

/// The transfer register is a W register and the base an X register — the same
/// register NUMBER. A check that compared print-names instead of indexes would
/// let this through.
///
/// ASSEMBLED: `ldrh w11,[x12,#61]!` = 7843dd8b.
/// DERIVED: Rt 11 -> 12 = 7843dd8c, objdump `ldrh w12, [x12, #61]!`.
/// NATIVE: 7843dd8c SIGILL, 7843dd8b executes.
#[test]
fn pre_indexed_load_rejects_aliasing_across_register_widths() {
    refused_as_constrained(0x7843_DD8C, "ldrh w12, [x12, #61]!");

    let insn = decodes_as(0x7843_DD8B, Opcode::Ldrh, "ldrh w11,[x12,#61]!");
    assert_eq!(writeback_base(&insn), Some(12));
    assert_eq!(regs(&insn), vec![11]);
}

/// ASSEMBLED: `ldrsw x17,[x16,#-255]!` = b8901e11.
/// DERIVED: Rt 17 -> 16 = b8901e10, objdump `ldrsw x16, [x16, #-255]!`.
/// NATIVE: b8901e10 SIGILL, b8901e11 executes.
#[test]
fn pre_indexed_sign_extending_load_rejects_aliasing() {
    refused_as_constrained(0xB890_1E10, "ldrsw x16, [x16, #-255]!");
    decodes_as(0xB890_1E11, Opcode::Ldrsw, "ldrsw x17,[x16,#-255]!");
}

/// The sub-word store form. ASSEMBLED: `strb w5,[x6,#3]!` = 38003cc5.
/// DERIVED: Rt 5 -> 6 = 38003cc6, objdump `strb w6, [x6, #3]!`.
/// NATIVE: 38003cc6 SIGILL, 38003cc5 executes.
#[test]
fn pre_indexed_byte_store_rejects_aliasing() {
    refused_as_constrained(0x3800_3CC6, "strb w6, [x6, #3]!");
    decodes_as(0x3800_3CC5, Opcode::Strb, "strb w5,[x6,#3]!");
}

/// BOUNDARY — `n == 31` is NOT the constraint. Rn 31 is SP and Rt 31 is ZR: two
/// different registers, nothing overlaps.
///
/// ASSEMBLED: `ldr x0,[sp],#8` = f84087e0 and `ldr xzr,[sp],#8` = f84087ff —
/// clang encodes BOTH. NATIVE: both execute.
#[test]
fn post_indexed_load_keeps_the_stack_pointer_base_with_a_zero_register_transfer() {
    let insn = decodes_as(0xF840_87FF, Opcode::Ldr, "ldr xzr,[sp],#8");
    assert_eq!(writeback_base(&insn), Some(31), "SP is still the writeback base");
    decodes_as(0xF840_87E0, Opcode::Ldr, "ldr x0,[sp],#8");
}

/// BOUNDARY — the unscaled form has no writeback, so `Rt == Rn` is ordinary.
///
/// ASSEMBLED: `ldur x1,[x0,#8]` = f8408001, `ldur x0,[x0,#8]` = f8408000 —
/// clang encodes both. NATIVE: both execute.
#[test]
fn unscaled_load_keeps_transfer_equal_to_base_because_there_is_no_writeback() {
    let insn = decodes_as(0xF840_8000, Opcode::Ldr, "ldur x0,[x0,#8]");
    assert_eq!(writeback_base(&insn), None, "LDUR must not carry a writeback");
    decodes_as(0xF840_8001, Opcode::Ldr, "ldur x1,[x0,#8]");
}

// ===========================================================================
// R2 — load pair: Rt == Rt2
// ===========================================================================

/// ASSEMBLED: `ldp x0,x1,[x2,#-72]` = a97b8440.
/// DERIVED: Rt2[14:10] 1 -> 0 = a97b8040, objdump `ldp x0, x0, [x2, #-72]`.
/// NATIVE: a97b8040 SIGILL, a97b8440 executes.
/// clang: "unpredictable LDP instruction, Rt2==Rt".
#[test]
fn load_pair_rejects_naming_one_register_for_both_halves() {
    refused_as_constrained(0xA97B_8040, "ldp x0, x0, [x2, #-72]");

    let insn = decodes_as(0xA97B_8440, Opcode::Ldp, "ldp x0,x1,[x2,#-72]");
    assert_eq!(regs(&insn), vec![0, 1], "the control keeps two distinct destinations");
}

/// The 32-bit pair. ASSEMBLED: `ldp w0,w1,[x2]` = 29400440.
/// DERIVED: Rt2 1 -> 0 = 29400040, objdump `ldp w0, w0, [x2]`.
/// NATIVE: 29400040 SIGILL, 29400440 executes.
#[test]
fn thirty_two_bit_load_pair_rejects_naming_one_register_for_both_halves() {
    refused_as_constrained(0x2940_0040, "ldp w0, w0, [x2]");
    decodes_as(0x2940_0440, Opcode::Ldp, "ldp w0,w1,[x2]");
}

/// LDPSW — the case where the ASSEMBLER IS NOT A RELIABLE ORACLE. clang refuses
/// `ldpsw x0,x0,[x2,#8]` (the offset form) but ACCEPTS this pre-indexed one.
/// The hardware settles it.
///
/// ASSEMBLED: `ldpsw x1,x2,[x10,#40]!` = 69c50941.
/// DERIVED: Rt2 2 -> 1 = 69c50541, objdump `ldpsw x1, x1, [x10, #40]!`.
/// NATIVE: 69c50541 SIGILL, 69c50941 executes.
#[test]
fn ldpsw_rejects_naming_one_register_for_both_halves_even_though_clang_encodes_it() {
    refused_as_constrained(0x69C5_0541, "ldpsw x1, x1, [x10, #40]!");
    decodes_as(0x69C5_0941, Opcode::Ldpsw, "ldpsw x1,x2,[x10,#40]!");
}

/// LDPOVERLAP has NO `!= 31` exception, so naming ZR twice is still out of
/// bounds — unlike the writeback rules, where 31 means SP and is exempt.
///
/// ASSEMBLED: `ldp xzr,x1,[x2,#16]` = a941045f.
/// DERIVED: Rt2 1 -> 31 = a9417c5f, objdump `ldp xzr, xzr, [x2, #16]`.
/// NATIVE: a9417c5f SIGILL, a941045f executes.
/// clang: "unpredictable LDP instruction, Rt2==Rt".
#[test]
fn load_pair_rejects_the_zero_register_named_twice() {
    refused_as_constrained(0xA941_7C5F, "ldp xzr, xzr, [x2, #16]");
    decodes_as(0xA941_045F, Opcode::Ldp, "ldp xzr,x1,[x2,#16]");
}

/// LDPOVERLAP applies to the INDEXED modes too, and this is the pair clang
/// encodes without complaint — so only the hardware settles it.
///
/// ASSEMBLED: `ldp x3, x3, [x5], #16` = a8c10ca3 and `ldp x3, x4, [x5], #16` =
/// a8c110a3 — clang encodes BOTH.
/// NATIVE: a8c10ca3 SIGILL, a8c110a3 executes.
#[test]
fn post_indexed_load_pair_rejects_naming_one_register_for_both_halves() {
    refused_as_constrained(0xA8C1_0CA3, "ldp x3, x3, [x5], #16 — clang encodes this one");
    decodes_as(0xA8C1_10A3, Opcode::Ldp, "ldp x3,x4,[x5],#16");
}

/// The strongest single case for "LDPOVERLAP has no register-31 exception":
/// `ldp wzr,wzr,[sp],#0` writes NOTHING and adds zero to SP, clang encodes it
/// happily — and the CPU still refuses to execute it.
///
/// ASSEMBLED: `ldp wzr, wzr, [sp], #0` = 28c07fff and `ldp wzr, w1, [sp], #0` =
/// 28c007ff — clang encodes both.
/// NATIVE: 28c07fff SIGILL, 28c007ff executes.
#[test]
fn post_indexed_load_pair_rejects_two_zero_registers_even_with_a_stack_pointer_base() {
    refused_as_constrained(0x28C0_7FFF, "ldp wzr, wzr, [sp], #0 — clang encodes it, CPU SIGILLs");

    // The Rn==31 exemption belongs to the WRITEBACK rule, not to LDPOVERLAP:
    // the same instruction with distinct transfer registers is fine.
    let insn = decodes_as(0x28C0_07FF, Opcode::Ldp, "ldp wzr,w1,[sp],#0");
    assert_eq!(writeback_base(&insn), Some(31), "SP is still the writeback base");
    assert_eq!(regs(&insn), vec![31, 1]);
}

/// BOUNDARY — LDPOVERLAP is a LOAD constraint. A store pair may name one
/// register twice: there is one value and two copies of it, nothing undefined.
///
/// ASSEMBLED: `stp x0,x1,[x2,#16]` = a9010440, `stp x0,x0,[x2,#16]` = a9010040
/// — clang encodes both. NATIVE: both execute.
#[test]
fn store_pair_keeps_one_register_named_twice() {
    let insn = decodes_as(0xA901_0040, Opcode::Stp, "stp x0,x0,[x2,#16]");
    assert_eq!(regs(&insn), vec![0, 0], "the store pair genuinely names x0 twice");
    decodes_as(0xA901_0440, Opcode::Stp, "stp x0,x1,[x2,#16]");
}

// ===========================================================================
// R3 — load/store pair with writeback: Rt == Rn or Rt2 == Rn, Rn != 31
// ===========================================================================

/// ASSEMBLED: `stp x3,x1,[x2,#144]!` = a9890443.
/// DERIVED: Rt[4:0] 3 -> 2 = a9890442, objdump `stp x2, x1, [x2, #144]!`.
/// NATIVE: a9890442 SIGILL, a9890443 executes.
/// clang: "unpredictable STP instruction, writeback base is also a source".
#[test]
fn pre_indexed_store_pair_rejects_first_transfer_aliasing_the_base() {
    refused_as_constrained(0xA989_0442, "stp x2, x1, [x2, #144]!");

    let insn = decodes_as(0xA989_0443, Opcode::Stp, "stp x3,x1,[x2,#144]!");
    assert_eq!(writeback_base(&insn), Some(2));
    assert_eq!(regs(&insn), vec![3, 1]);
}

/// The SECOND transfer register aliasing the base — a rule that only tested Rt
/// would miss this.
///
/// ASSEMBLED: `stp x1,x23,[x24],#-432` = a8a55f01.
/// DERIVED: Rt2[14:10] 23 -> 24 = a8a56301, objdump `stp x1, x24, [x24], #-432`.
/// NATIVE: a8a56301 SIGILL, a8a55f01 executes.
#[test]
fn post_indexed_store_pair_rejects_second_transfer_aliasing_the_base() {
    refused_as_constrained(0xA8A5_6301, "stp x1, x24, [x24], #-432");

    let insn = decodes_as(0xA8A5_5F01, Opcode::Stp, "stp x1,x23,[x24],#-432");
    assert_eq!(writeback_base(&insn), Some(24));
    assert_eq!(regs(&insn), vec![1, 23]);
}

/// The load side of the same rule; clang words it differently ("writeback base
/// is also a destination") which is why both are exercised.
///
/// ASSEMBLED: `ldp x17,x7,[x21,#120]!` = a9c79eb1.
/// DERIVED: Rt 17 -> 21 = a9c79eb5, objdump `ldp x21, x7, [x21, #120]!`.
/// NATIVE: a9c79eb5 SIGILL, a9c79eb1 executes.
#[test]
fn pre_indexed_load_pair_rejects_first_transfer_aliasing_the_base() {
    refused_as_constrained(0xA9C7_9EB5, "ldp x21, x7, [x21, #120]!");
    decodes_as(0xA9C7_9EB1, Opcode::Ldp, "ldp x17,x7,[x21,#120]!");
}

/// ASSEMBLED: `ldp w1,w2,[x3],#8` = 28c10861.
/// DERIVED: Rt2 2 -> 3 = 28c10c61, objdump `ldp w1, w3, [x3], #8`.
/// NATIVE: 28c10c61 SIGILL, 28c10861 executes.
#[test]
fn post_indexed_load_pair_rejects_second_transfer_aliasing_the_base() {
    refused_as_constrained(0x28C1_0C61, "ldp w1, w3, [x3], #8");
    decodes_as(0x28C1_0861, Opcode::Ldp, "ldp w1,w2,[x3],#8");
}

/// BOUNDARY — writeback onto SP. Rn 31 is SP; the transfer fields are 0 and 1,
/// so nothing overlaps and the encoding is ordinary.
///
/// ASSEMBLED: `ldp x0,x1,[x2,#16]!` = a9c10440, `ldp x0,x1,[sp,#16]!` = a9c107e0
/// — clang encodes both. NATIVE: both execute.
#[test]
fn pre_indexed_load_pair_keeps_the_stack_pointer_as_writeback_base() {
    let insn = decodes_as(0xA9C1_07E0, Opcode::Ldp, "ldp x0,x1,[sp,#16]!");
    assert_eq!(writeback_base(&insn), Some(31), "SP is still the writeback base");
    decodes_as(0xA9C1_0440, Opcode::Ldp, "ldp x0,x1,[x2,#16]!");
}

/// BOUNDARY — the signed-offset mode has no writeback, so a transfer register
/// may equal the base.
///
/// ASSEMBLED: `ldp x1,x2,[x0]` = a9400801, `ldp x0,x2,[x0]` = a9400800 — clang
/// encodes both. NATIVE: both execute.
#[test]
fn offset_load_pair_keeps_transfer_equal_to_base_because_there_is_no_writeback() {
    let insn = decodes_as(0xA940_0800, Opcode::Ldp, "ldp x0,x2,[x0]");
    assert_eq!(writeback_base(&insn), None, "the offset form must not carry a writeback");
    decodes_as(0xA940_0801, Opcode::Ldp, "ldp x1,x2,[x0]");
}

// ===========================================================================
// R4 — store exclusive: Rs == Rt, or Rs == Rn with Rn != 31
// ===========================================================================
//
// DIFFERENT IN KIND, and the difference is recorded rather than smoothed over.
// Native execution does NOT fault here: all four aliased words EXECUTE. The
// refusal rests on what they DO, measured with a live monitor reservation and
// the result read back:
//
//   c8007c41  stxr w0,x1,[x2]  (control)  status=0  mem=1122334455667788
//   c8007c40  stxr w0,x0,[x2]  Rs==Rt     x0=0      mem=1122334455667788
//   c8007c01  stxr w0,x1,[x0]  Rs==Rn     x0=0      mem=1122334455667788
//
// One register is given two values. This implementation resolves it as
// "transfer first, then overwrite with the status", so the aliased word
// DESTROYS the stored value's register in the Rs==Rt case and the BASE POINTER
// in the Rs==Rn case. That is `Constraint_NONE`, one of the four resolutions
// the ARM ARM permits for `Unpredictable_DATAOVERLAP`; the others are
// `Constraint_UNKNOWN`, `Constraint_NOP` and `Constraint_UNDEF`. Nothing
// entitles a checker to assume this chip's choice, and the decoded operand list
// — two independent registers that happen to have the same index — cannot
// express the collision at all. clang refuses all four: "unpredictable STXR
// instruction, status is also a source".

/// ASSEMBLED: `stxr w0,x1,[x2]` = c8007c41.
/// DERIVED: Rt[4:0] 1 -> 0 = c8007c40, objdump `stxr w0, x0, [x2]`.
/// NATIVE: EXECUTES (does not fault) and leaves x0 = 0, destroying the value.
#[test]
fn store_exclusive_rejects_status_register_aliasing_the_transfer_register() {
    refused_as_constrained(0xC800_7C40, "stxr w0, x0, [x2]");

    let insn = decodes_as(0xC800_7C41, Opcode::Stxr, "stxr w0,x1,[x2]");
    assert_eq!(regs(&insn), vec![0, 1], "the control keeps status and transfer distinct");
}

/// DERIVED from the same control: Rn[9:5] 2 -> 0 = c8007c01, objdump
/// `stxr w0, x1, [x0]`.
/// NATIVE: EXECUTES and leaves x0 = 0, destroying the BASE POINTER.
#[test]
fn store_exclusive_rejects_status_register_aliasing_the_address_register() {
    refused_as_constrained(0xC800_7C01, "stxr w0, x1, [x0]");
    decodes_as(0xC800_7C41, Opcode::Stxr, "stxr w0,x1,[x2]");
}

/// The release-store variant, 32-bit, so the rule is not tied to STXR or to the
/// 64-bit size.
///
/// ASSEMBLED: `stlxr w3,w4,[x5]` = 8803fca4.
/// DERIVED: Rt 4 -> 3 = 8803fca3, objdump `stlxr w3, w3, [x5]`.
#[test]
fn store_release_exclusive_rejects_status_register_aliasing_the_transfer_register() {
    refused_as_constrained(0x8803_FCA3, "stlxr w3, w3, [x5]");

    let insn = decodes_as(0x8803_FCA4, Opcode::Stlxr, "stlxr w3,w4,[x5]");
    assert_eq!(regs(&insn), vec![3, 4]);
}

/// The `s == t` half of DATAOVERLAP has no `!= 31` exception, so WZR named as
/// both status and transfer is still out of bounds — and clang refuses it.
///
/// ASSEMBLED: `stxr wzr,x1,[x2]` = c81f7c41.
/// DERIVED: Rt 1 -> 31 = c81f7c5f, objdump `stxr wzr, xzr, [x2]`.
#[test]
fn store_exclusive_rejects_the_zero_register_as_both_status_and_transfer() {
    refused_as_constrained(0xC81F_7C5F, "stxr wzr, xzr, [x2]");
    decodes_as(0xC81F_7C41, Opcode::Stxr, "stxr wzr,x1,[x2]");
}

/// BOUNDARY — `s == n` IS exempted at n == 31: the base is SP, which is not the
/// register the status is written to.
///
/// ASSEMBLED: `stxr w0,x1,[sp]` = c8007fe1 — clang encodes it. NATIVE: executes.
#[test]
fn store_exclusive_keeps_the_stack_pointer_base_with_status_register_zero() {
    decodes_as(0xC800_7FE1, Opcode::Stxr, "stxr w0,x1,[sp]");
}

/// BOUNDARY — Rs == 31 is WZR, and here it aliases neither Rt (1) nor Rn (0),
/// so no constraint applies. A rule written as "Rs == 31 is always suspect"
/// would break this.
///
/// ASSEMBLED: `stxr w4,x1,[x0]` = c8047c01, `stxr wzr,x1,[x0]` = c81f7c01 —
/// clang encodes both. NATIVE: both execute.
#[test]
fn store_exclusive_keeps_a_zero_status_register_that_aliases_nothing() {
    let insn = decodes_as(0xC81F_7C01, Opcode::Stxr, "stxr wzr,x1,[x0]");
    assert_eq!(regs(&insn), vec![31, 1], "status is WZR, transfer is x1");
    decodes_as(0xC804_7C01, Opcode::Stxr, "stxr w4,x1,[x0]");
}

/// The non-status exclusive forms fix Rs to 11111 and have no writeback, so no
/// operand constraint applies to them at all. `ldxr x0,[x0]` (c85f7c00) and
/// `ldar x0,[x0]` (c8dffc00) both assemble and must keep decoding — a rule that
/// keyed on "Rt equals Rn in an exclusive" rather than on the STATUS register
/// would wrongly refuse them.
#[test]
fn load_exclusive_and_acquire_keep_transfer_equal_to_base() {
    decodes_as(0xC85F_7C00, Opcode::Ldxr, "ldxr x0,[x0]");
    decodes_as(0xC8DF_FC00, Opcode::Ldar, "ldar x0,[x0]");
}

// ===========================================================================
// The refusal must not leak into neighbouring encodings
// ===========================================================================

/// The no-allocate pair (LDNP/STNP, `mode == 0b00`) is refused for a different
/// reason — this decoder does not decode it — and must keep saying so. A word
/// we never decode must not be reported as a constrained-unpredictable operand
/// combination: that would name a constraint on an encoding the decoder never
/// reaches, which is a false diagnostic even though the verdict is the same.
///
/// ASSEMBLED: `ldnp x0,x0,[x2]` = a8400040 — clang encodes it (LLVM applies no
/// LDPOVERLAP check to the no-allocate form).
#[test]
fn no_allocate_pair_is_still_refused_as_an_encoding_this_decoder_does_not_decode() {
    match decode(0xA840_0040) {
        Err(DisasmError::ConstrainedUnpredictableOperands { .. }) => panic!(
            "a8400040 (ldnp x0,x0,[x2]) was refused as a CONSTRAINED UNPREDICTABLE operand \
             combination, but this decoder does not decode the no-allocate pair at all — the \
             diagnostic names a constraint on a path never taken"
        ),
        Err(_) => {}
        Ok(insn) => panic!("a8400040 (ldnp) must not decode, got {:?}", insn.opcode),
    }
}

/// The register-offset load/store form has no writeback, so `Rt == Rn` there is
/// ordinary and the R1 rule must not reach it.
///
/// ASSEMBLED: `ldr x0,[x0,x1]` = f8616800.
#[test]
fn register_offset_load_keeps_transfer_equal_to_base() {
    let insn = decodes_as(0xF861_6800, Opcode::Ldr, "ldr x0,[x0,x1]");
    assert_eq!(writeback_base(&insn), None, "the register-offset form has no writeback");
}
