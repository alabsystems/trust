// trust-machine-sem: value-pinned regressions for the three model/hardware
// divergences found by the NATIVE SEMANTIC DIFFERENTIAL
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! THE THREE DIVERGENCES, PINNED TO THE HARDWARE'S ANSWER.
//!
//! The native semantic differential
//! (`crates/trust-disasm/harness/native-semantic/`) executes a candidate word on
//! the CPU between a prologue that loads the whole register file and a trapping
//! epilogue that reads it back, and compares the result against replaying
//! `Aarch64Semantics::effects`. Over 499,529 comparisons it reported 11,385
//! disagreements in exactly three families. Each test here reproduces one, at a
//! word that came out of `clang` and was read back with `objdump`, and asserts
//! the VALUE the hardware produced — not merely that something changed.
//!
//! Asserting the value is the point. A test that only checks "the formula now
//! mentions V13" passes against a second wrong model; a test that says the
//! stored word is `0x0102030405060708` fails against every model but the right
//! one. Where a case was confirmed on silicon by the differential, the confirmed
//! number is quoted in the test.
//!
//! Each test FAILED before the corresponding fix. The observed failures are
//! recorded in the doc comment of each test, so a later reader can tell a test
//! that guards something from a test that never could.

use trust_disasm::operand::{Operand, Register};
use trust_disasm::{Opcode, decode_aarch64};

use super::Aarch64Semantics;
use super::helpers::operand_to_formula;
use crate::concrete::ConcreteState;
use crate::effect::Effect;
use crate::semantics::Semantics;
use crate::state::MachineState;

/// Where every candidate here is placed. Any address works; a fixed one keeps
/// the PC-relative arithmetic out of the comparison.
const PC: u64 = 0x1000;

/// Pointer-shaped and far from zero, so a base register cannot be confused with
/// an offset or with a small value that happened to be lying around.
const BASE: u64 = 0x0000_0004_0002_0000;

fn effects_of(word: u32) -> Vec<Effect> {
    let insn = decode_aarch64(&word.to_le_bytes(), PC)
        .unwrap_or_else(|e| panic!("decode {word:08x}: {e}"));
    Aarch64Semantics
        .effects(&MachineState::symbolic(), &insn)
        .unwrap_or_else(|e| panic!("effects {word:08x}: {e}"))
}

/// Replay one word's modeled effects concretely, exactly the way the native
/// differential's model side does: every formula is evaluated against the
/// PRE-state, and results land in the post-state.
fn replay(word: u32, pre: &ConcreteState) -> ConcreteState {
    let effects = effects_of(word);
    let mut post = pre.clone();
    post.pc = pre.pc.wrapping_add(4);
    for effect in &effects {
        post.apply_effect_with_eval_state(pre, effect)
            .unwrap_or_else(|e| panic!("replay {word:08x} effect {effect:?}: {e}"));
    }
    post
}

fn poke(state: &mut ConcreteState, addr: u64, value: u128, bytes: u32) {
    for i in 0..u64::from(bytes) {
        state.memory.insert(addr + i, ((value >> (i * 8)) & 0xff) as u8);
    }
}

fn peek(state: &ConcreteState, addr: u64, bytes: u32) -> u128 {
    let mut value = 0u128;
    for i in 0..u64::from(bytes) {
        let byte = *state
            .memory
            .get(&(addr + i))
            .unwrap_or_else(|| panic!("no byte stored at {:#x}", addr + i));
        value |= u128::from(byte) << (i * 8);
    }
    value
}

// ---------------------------------------------------------------------------
// FAMILY 1 — Ldr/Str SIMD&FP (V=1). 5,721 divergences.
//
// `operand_to_formula` matched `Operand::Reg(r)` and called `read_gpr(r.index)`
// without ever consulting `r.kind`. The decoder records `RegKind::Simd`
// correctly; the semantics discarded it, so `str d13,[…]` stored the GPR X13
// and `ldr d11,[…]` wrote the GPR x11.
// ---------------------------------------------------------------------------

/// `str d13,[x28,#0xa0]` (fd00538d) must store V13, not X13.
///
/// BEFORE THE FIX this stored `0xdeadbeefdeadbeef` — the GPR of the same
/// number — and failed:
///   `assertion `left == right` failed: str d13 stored the wrong register file
///     left: 0xdeadbeefdeadbeef
///    right: 0x102030405060708`
#[test]
fn str_simd_d_stores_the_fp_register_not_the_gpr_of_the_same_number() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[28] = BASE;
    pre.gpr[13] = 0xdead_beef_dead_beef;
    pre.fpr[13] = 0x1122_3344_5566_7788_0102_0304_0506_0708;

    let post = replay(0xfd00_538d, &pre);

    assert_eq!(
        peek(&post, BASE + 0xa0, 8),
        0x0102_0304_0506_0708,
        "str d13 stored the wrong register file"
    );
}

/// `str q1,[x2,#0x10]` (3d800441) stores the WHOLE 128-bit register.
#[test]
fn str_simd_q_stores_all_sixteen_bytes_of_the_fp_register() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[2] = BASE;
    pre.gpr[1] = 0xdead_beef_dead_beef;
    pre.fpr[1] = 0x0f0e_0d0c_0b0a_0908_0706_0504_0302_0100;

    let post = replay(0x3d80_0441, &pre);

    assert_eq!(
        peek(&post, BASE + 0x10, 16),
        0x0f0e_0d0c_0b0a_0908_0706_0504_0302_0100,
        "str q1 stored the wrong register file"
    );
}

/// `str b3,[x4]` (3d000083) and `str h2,[x5,#4]` (7d0008a2): the byte and
/// halfword lanes take the LOW bits of V, not of X.
#[test]
fn str_simd_narrow_lanes_take_the_low_bits_of_the_fp_register() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[4] = BASE;
    pre.gpr[5] = BASE + 0x100;
    pre.gpr[3] = 0xdead_beef_dead_beef;
    pre.gpr[2] = 0xdead_beef_dead_beef;
    pre.fpr[3] = 0xaabb_ccdd_eeff_0011_2233_4455_6677_8899;
    pre.fpr[2] = 0xaabb_ccdd_eeff_0011_2233_4455_6677_8899;

    let post_b = replay(0x3d00_0083, &pre);
    assert_eq!(peek(&post_b, BASE, 1), 0x99, "str b3 stored the wrong register file");

    let post_h = replay(0x7d00_08a2, &pre);
    assert_eq!(peek(&post_h, BASE + 0x100 + 4, 2), 0x8899, "str h2 stored the wrong register file");
}

/// `ldr d11,[x11,#0x50]` (fd40296b) must write V11 and LEAVE X11 ALONE.
///
/// BEFORE THE FIX the loaded value landed in the GPR, and both halves of this
/// failed: `x11` had been overwritten with `0x1122334455667788` and `v11` was
/// still its pre-value.
#[test]
fn ldr_simd_d_writes_the_fp_register_and_leaves_the_gpr_untouched() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[11] = BASE;
    // All-ones, so the architectural zeroing of the upper lane is OBSERVED
    // rather than coinciding with a zero-initialized field.
    pre.fpr[11] = u128::MAX;
    poke(&mut pre, BASE + 0x50, 0x1122_3344_5566_7788, 8);

    let post = replay(0xfd40_296b, &pre);

    assert_eq!(
        post.fpr[11], 0x1122_3344_5566_7788,
        "ldr d11 must write V11 with the loaded doubleword AND zero the upper lane"
    );
    assert_eq!(post.gpr[11], BASE, "ldr d11 must not write the GPR x11");
}

/// `ldr s0,[x1]` (bd400020) zeroes bits 127:32; `ldr q7,[x9]` (3dc00127) fills
/// the whole register.
#[test]
fn ldr_simd_s_and_q_write_the_fp_register_with_architectural_zeroing() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[1] = BASE;
    pre.gpr[9] = BASE + 0x40;
    pre.fpr[0] = u128::MAX;
    pre.fpr[7] = u128::MAX;
    poke(&mut pre, BASE, 0xaabb_ccdd, 4);
    poke(&mut pre, BASE + 0x40, 0x0f0e_0d0c_0b0a_0908_0706_0504_0302_0100, 16);

    let post_s = replay(0xbd40_0020, &pre);
    assert_eq!(post_s.fpr[0], 0xaabb_ccdd, "ldr s0 must zero bits 127:32 of V0");
    assert_eq!(post_s.gpr[0], 0, "ldr s0 must not write the GPR x0");

    let post_q = replay(0x3dc0_0127, &pre);
    assert_eq!(
        post_q.fpr[7], 0x0f0e_0d0c_0b0a_0908_0706_0504_0302_0100,
        "ldr q7 must write all 128 bits of V7"
    );
}

/// THE DISCARD ITSELF, at the site that made it: a SIMD register handed to the
/// INTEGER operand reader is refused, never silently read as the GPR of the
/// same number.
///
/// This is the property the family-1 fix actually rests on. `sem_ldr`/`sem_str`
/// now route SIMD operands to the FP file, but the ~60 other callers of
/// `operand_to_formula` are integer data-processing paths for which no correct
/// SIMD reading exists — so the answer there is REFUSAL. Approximating onto the
/// neighbouring register file is what produced 5,721 wrong answers.
///
/// BEFORE THE FIX this returned `Ok(X13)`:
///   `assertion failed: a SIMD operand handed to the integer reader must be
///    refused, not read as X13`
#[test]
fn a_simd_operand_in_an_integer_path_is_refused_rather_than_read_as_a_gpr() {
    let state = MachineState::symbolic();

    for (kind_name, operand) in [
        ("plain", Operand::Reg(Register::simd(13, 64))),
        (
            "shifted",
            Operand::ShiftedReg {
                reg: Register::simd(13, 64),
                shift: trust_disasm::operand::ShiftType::Lsl,
                amount: 3,
            },
        ),
    ] {
        let got = operand_to_formula(&state, Some(&operand), Opcode::Add, 2, 64);
        assert!(
            got.is_err(),
            "a {kind_name} SIMD operand handed to the integer reader must be refused, \
             not read as X13 — got {got:?}"
        );
    }

    // The GPR/SP/ZR forms must still be read, or the refusal above is just a
    // broken function.
    for (what, operand) in [
        ("gpr", Operand::Reg(Register::gpr(13, true))),
        ("sp", Operand::Reg(Register::sp(true))),
        ("zr", Operand::Reg(Register::zr(true))),
    ] {
        assert!(
            operand_to_formula(&state, Some(&operand), Opcode::Add, 2, 64).is_ok(),
            "the {what} operand form must still be read"
        );
    }
}

// ---------------------------------------------------------------------------
// FAMILY 2 — Ubfm/Sbfm with imms < immr. 5,208 divergences.
//
// The `imms < immr` arm shifted the WHOLE register left by `width - immr` and
// never masked the source to `imms + 1` bits; SBFM additionally never
// sign-extended from bit `imms`. Observable whenever `immr - imms >= 2`.
// ---------------------------------------------------------------------------

/// `ubfiz w15,w4,#28,#1` (5304008f) — THE WORD THE DIFFERENTIAL CONFIRMED ON
/// SILICON: model said `0x80000000`, hardware said `0`.
///
/// `UBFIZ Wd, Wn, #28, #1` is `Wd = ZeroExtend(Wn<0:0>) << 28`. With `w4 = 8`
/// bit 0 is CLEAR, so the answer is 0; the unmasked model shifted bit 3 into
/// bit 31.
///
/// BEFORE THE FIX:
///   `assertion `left == right` failed: ubfiz w15,w4,#28,#1 must mask the
///     source to imms+1 = 1 bit
///     left: 0x80000000
///    right: 0x0`
#[test]
fn ubfiz_masks_the_source_to_imms_plus_one_bits() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[4] = 0x8;

    let post = replay(0x5304_008f, &pre);
    assert_eq!(post.gpr[15], 0, "ubfiz w15,w4,#28,#1 must mask the source to imms+1 = 1 bit");

    // And the bit that IS in the field still arrives.
    pre.gpr[4] = 0x9;
    let post = replay(0x5304_008f, &pre);
    assert_eq!(
        post.gpr[15], 0x1000_0000,
        "ubfiz w15,w4,#28,#1 must place bit 0 of the source at bit 28"
    );
}

/// `ubfiz x9,x10,#60,#2` (d3440549) — the 64-bit form: `Xd = (Xn & 3) << 60`.
///
/// BEFORE THE FIX: left `0xc000000000000000`, right `0x0`.
#[test]
fn ubfiz_masks_the_source_in_the_sixty_four_bit_form() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[10] = 0b1100;

    let post = replay(0xd344_0549, &pre);
    assert_eq!(post.gpr[9], 0, "ubfiz x9,x10,#60,#2 must mask the source to 2 bits");

    pre.gpr[10] = 0b1101;
    let post = replay(0xd344_0549, &pre);
    assert_eq!(
        post.gpr[9], 0x1000_0000_0000_0000,
        "ubfiz x9,x10,#60,#2 must place bit 0 of the source at bit 60"
    );
}

/// `sbfiz w0,w1,#24,#4` (13080c20) — `Wd = SignExtend(Wn<3:0>) << 24`.
///
/// This pins BOTH halves of the SBFM fix at once. With `w1 = 0x18` the field is
/// `0x8`, which is NEGATIVE as a 4-bit value, so bits 31:28 fill with ones:
/// `0xf8000000`. The unmasked model produced `0x18000000` — wrong in the field
/// (bit 4 leaked in) and wrong above it (no sign extension).
///
/// BEFORE THE FIX:
///   `assertion `left == right` failed: sbfiz w0,w1,#24,#4 must mask to imms+1
///     bits AND sign-extend from bit imms
///     left: 0x18000000
///    right: 0xf8000000`
#[test]
fn sbfiz_masks_and_sign_extends_the_extracted_field() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[1] = 0x18;

    let post = replay(0x1308_0c20, &pre);
    assert_eq!(
        post.gpr[0], 0xf800_0000,
        "sbfiz w0,w1,#24,#4 must mask to imms+1 bits AND sign-extend from bit imms"
    );

    // A non-negative field must NOT sign-extend.
    pre.gpr[1] = 0x17;
    let post = replay(0x1308_0c20, &pre);
    assert_eq!(
        post.gpr[0], 0x0700_0000,
        "sbfiz w0,w1,#24,#4 with a positive field must zero the bits above it"
    );
}

/// `sbfiz x9,x10,#56,#4` (93480d49) — the 64-bit form.
///
/// BEFORE THE FIX: left `0x1800000000000000`, right `0xf800000000000000`.
#[test]
fn sbfiz_masks_and_sign_extends_in_the_sixty_four_bit_form() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[10] = 0x18;

    let post = replay(0x9348_0d49, &pre);
    assert_eq!(
        post.gpr[9], 0xf800_0000_0000_0000,
        "sbfiz x9,x10,#56,#4 must mask to imms+1 bits AND sign-extend from bit imms"
    );
}

/// The canonical `LSL` alias — `immr - imms == 1` — must be UNCHANGED.
///
/// This is why the corpus was never wrong: all 29 `imms < immr` words in the
/// emitted output are this shape, where the unmasked shift is EQUIVALENT
/// because the field reaches exactly to the top of the register. A fix that
/// broke it would be a regression in the only sub-case that ships.
/// `lsl w0,w1,#4` = 531c6c20 — clang-assembled and read back with objdump, like
/// every other word here. (A hand-guessed 531c1b20 was tried first and is a
/// DIFFERENT instruction; assembling is not a formality.)
#[test]
fn the_canonical_lsl_alias_is_unchanged() {
    let word = 0x531c_6c20u32;
    let insn = decode_aarch64(&word.to_le_bytes(), PC).expect("decode lsl w0,w1,#4");
    assert_eq!(insn.opcode, Opcode::Ubfm, "lsl is the UBFM alias");

    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[1] = 0x1234_5678;
    let post = replay(word, &pre);
    assert_eq!(post.gpr[0], 0x2345_6780, "lsl w0,w1,#4 must still be a plain left shift");
}

/// THE REWRITTEN FORMULAS MUST STILL SORT-CHECK.
///
/// This is the corpus-cost guard. The three fixes are value-preserving for the
/// only shape the emitted corpus actually contains — the canonical `LSL` alias —
/// but they change the FORMULA the output gate discharges: `BvShl(rn, n)` became
/// `BvShl(BvZeroExt(BvExtract(rn)), n)`, and the ADCS/SBCS carry became an
/// `Or`/`And` over `BvULt` and `Eq`. A width-inconsistent term does not produce
/// a wrong answer, it makes the SMT translation fail — which is how a Proven
/// becomes an error rather than a refutation, and is exactly the failure the
/// `BvZeroExt` "amount, not target width" comments elsewhere in this file record.
///
/// Checked with `trust_types::check_formula_sort`, the authority the discharge
/// itself uses, over every effect of every word touched by the three fixes.
#[test]
fn every_rewritten_formula_is_sort_consistent() {
    for (word, what) in [
        (0x531c_6c20u32, "lsl w0,w1,#4 (the alias the corpus contains)"),
        (0xd37c_ec20, "lsl x0,x1,#4"),
        (0x5304_008f, "ubfiz w15,w4,#28,#1"),
        (0xd344_0549, "ubfiz x9,x10,#60,#2"),
        (0x1308_0c20, "sbfiz w0,w1,#24,#4"),
        (0x9348_0d49, "sbfiz x9,x10,#56,#4"),
        (0x3a03_0005, "adcs w5,w0,w3"),
        (0xba03_0005, "adcs x5,x0,x3"),
        (0x7a03_0005, "sbcs w5,w0,w3"),
        (0xfa03_0005, "sbcs x5,x0,x3"),
        (0xfd00_538d, "str d13,[x28,#0xa0]"),
        (0xfd40_296b, "ldr d11,[x11,#0x50]"),
        (0x3d80_0441, "str q1,[x2,#0x10]"),
        (0x3dc0_0127, "ldr q7,[x9]"),
    ] {
        for effect in effects_of(word) {
            for formula in effect_formulas(&effect) {
                trust_types::check_formula_sort(formula).unwrap_or_else(|e| {
                    panic!("{what} ({word:08x}) produced a formula that does not sort-check: {e}")
                });
            }
        }
    }
}

/// Every `Formula` an effect carries.
///
/// EXHAUSTIVE, WITH NO WILDCARD. `Effect` is `#[non_exhaustive]` but this test
/// lives in the crate that defines it, where that attribute is inert — so a
/// fourteenth variant is E0004 here rather than a formula that silently goes
/// unchecked. A wildcard was written first and the compiler reported it
/// unreachable, which is the same guarantee arriving as a warning; taking it
/// out converts the guarantee into a hard failure.
fn effect_formulas(effect: &Effect) -> Vec<&trust_types::Formula> {
    match effect {
        Effect::RegWrite { value, .. }
        | Effect::SpWrite { value }
        | Effect::FpRegWrite { value, .. }
        | Effect::PcUpdate { value } => vec![value],
        Effect::MemWrite { address, value, .. } => vec![address, value],
        Effect::MemRead { address, .. } => vec![address],
        Effect::FlagUpdate { n, z, c, v } => vec![n, z, c, v],
        Effect::Branch { target } | Effect::Return { target } => vec![target],
        Effect::ConditionalBranch { target, fallthrough, .. } => vec![target, fallthrough],
        Effect::Call { target, return_addr } => vec![target, return_addr],
        Effect::Aarch64AtomicAccess { address, .. } => vec![address],
        // Carries no formula.
        Effect::Aarch64SyncBoundary { .. } => vec![],
    }
}

// ---------------------------------------------------------------------------
// FAMILY 3 — Adcs/Sbcs flags. 456 divergences.
//
// The RESULT carried the carry-in, but the flags came from
// `compute_nzcv(rn, rm, result)`, which never saw it — so the carry-OUT was
// computed as though the carry-IN were zero.
// ---------------------------------------------------------------------------

fn nzcv(state: &ConcreteState) -> String {
    let f = state.flags;
    format!(
        "{}{}{}{}",
        if f.n { 'N' } else { 'n' },
        if f.z { 'Z' } else { 'z' },
        if f.c { 'C' } else { 'c' },
        if f.v { 'V' } else { 'v' }
    )
}

/// `adcs w5,w0,w3` (3a030005) with C=1 — the family's confirmed shape.
///
/// `0 + 0xffffffff + 1 = 0x100000000`: the result is 0 and the carry OUT is 1.
/// The old `C = result <u lhs` reads `0 <u 0` = false and loses it. This is the
/// case `result <u lhs` cannot express: with a carry-in, a result EQUAL to the
/// left operand is still a carry.
///
/// BEFORE THE FIX:
///   `assertion `left == right` failed: adcs must compute the carry-out FROM
///     the carry-in
///     left: "nZcv"
///    right: "nZCv"`
#[test]
fn adcs_carry_out_accounts_for_the_carry_in() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0;
    pre.gpr[3] = 0xffff_ffff;
    pre.flags.c = true;

    let post = replay(0x3a03_0005, &pre);
    assert_eq!(post.gpr[5], 0, "adcs result");
    assert_eq!(nzcv(&post), "nZCv", "adcs must compute the carry-out FROM the carry-in");
}

/// The same, 64-bit: `adcs x5,x0,x3` (ba030005).
#[test]
fn adcs_carry_out_accounts_for_the_carry_in_at_sixty_four_bits() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0;
    pre.gpr[3] = u64::MAX;
    pre.flags.c = true;

    let post = replay(0xba03_0005, &pre);
    assert_eq!(post.gpr[5], 0, "adcs result");
    assert_eq!(nzcv(&post), "nZCv", "adcs must compute the carry-out FROM the carry-in");
}

/// With C=0 the carry-out must be the ordinary one — a fix that always sets C
/// would pass the test above and be just as wrong.
#[test]
fn adcs_with_no_carry_in_is_an_ordinary_add() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0;
    pre.gpr[3] = 0xffff_ffff;
    pre.flags.c = false;

    let post = replay(0x3a03_0005, &pre);
    assert_eq!(post.gpr[5], 0xffff_ffff, "adcs result with no carry-in");
    assert_eq!(nzcv(&post), "Nzcv", "adcs with C=0 must not invent a carry-out");
}

/// `sbcs w5,w0,w3` (7a030005) with C=0 (a BORROW in).
///
/// `SBCS` is `AddWithCarry(Rn, NOT(Rm), C)`: `0xffffffff + 0x00000000 + 0` does
/// not carry, so C=0 — the subtraction borrowed. The old `C = NOT(lhs <u rhs)`
/// answers the question for a borrow-free subtract and reports C=1.
///
/// BEFORE THE FIX:
///   `assertion `left == right` failed: sbcs must compute the carry-out FROM
///     the carry-in
///     left: "NzCv"
///    right: "Nzcv"`
#[test]
fn sbcs_carry_out_accounts_for_the_borrow_in() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0xffff_ffff;
    pre.gpr[3] = 0xffff_ffff;
    pre.flags.c = false;

    let post = replay(0x7a03_0005, &pre);
    assert_eq!(post.gpr[5], 0xffff_ffff, "sbcs result is rn - rm - 1");
    assert_eq!(nzcv(&post), "Nzcv", "sbcs must compute the carry-out FROM the carry-in");
}

/// The same, 64-bit: `sbcs x5,x0,x3` (fa030005).
#[test]
fn sbcs_carry_out_accounts_for_the_borrow_in_at_sixty_four_bits() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = u64::MAX;
    pre.gpr[3] = u64::MAX;
    pre.flags.c = false;

    let post = replay(0xfa03_0005, &pre);
    assert_eq!(post.gpr[5], u64::MAX, "sbcs result is rn - rm - 1");
    assert_eq!(nzcv(&post), "Nzcv", "sbcs must compute the carry-out FROM the carry-in");
}

/// With C=1 SBCS is a plain subtract and must keep the plain answer.
#[test]
fn sbcs_with_carry_in_set_is_an_ordinary_subtract() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0xffff_ffff;
    pre.gpr[3] = 0xffff_ffff;
    pre.flags.c = true;

    let post = replay(0x7a03_0005, &pre);
    assert_eq!(post.gpr[5], 0, "sbcs result is rn - rm");
    assert_eq!(nzcv(&post), "nZCv", "rn >= rm, so no borrow");
}

/// ADCS/SBCS N, Z and V are computed from the WITH-CARRY result and were
/// already right; this pins them so the carry fix cannot quietly disturb them.
/// `0x7fffffff + 0 + 1 = 0x80000000` is a signed overflow with no carry out.
#[test]
fn adcs_overflow_and_sign_come_from_the_with_carry_result() {
    let mut pre = ConcreteState::new();
    pre.pc = PC;
    pre.gpr[0] = 0x7fff_ffff;
    pre.gpr[3] = 0;
    pre.flags.c = true;

    let post = replay(0x3a03_0005, &pre);
    assert_eq!(post.gpr[5], 0x8000_0000, "adcs result");
    assert_eq!(nzcv(&post), "NzcV", "the carry-in pushed the sum over the signed edge");
}
