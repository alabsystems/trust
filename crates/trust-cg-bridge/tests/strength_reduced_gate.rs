// tests/strength_reduced_gate.rs — the call-event gate over objects trust-cg ships at O2 whose
// multiplies by a constant were strength-reduced to shifts and adds, proved through the
// kernel-checked `Trust.BVS` rewrite family (`verify_output_instantiate/strength.rs`).
//
// At O2 trust-cg emits `x * 3 + 7` as `(x + 7) + (x << 1)`, `a * 7 + 3` (u32) as
// `(3 + (a << 3)) - a`, and `x * 2` as `ubfm x, x, #63, #62`. Before the strength route each was
// [VALIDATED]: no wrapper strip or operand order joins those cores to the source's.
//
// POSITIVES (T-G1..T-G3): each must be kernel-[PROVED] on BOTH object formats, its evidence
// label naming exactly the rewrite theorems used, with the strength-reduced words present in
// the object. MUTANTS (T-G4): each patches one word, found by its encoding mask and asserted
// unique, and must be Refuted; each has its unmutated object proved in the same test, so a
// mutant cannot pass by the harness being broken. Each mutant is refuted at step (4), by ay's
// counterexample, before the step-(5) kernel retry where the strength route runs, so these
// mutants do not exercise the route: they would still pass if it accepted a wrong object. The
// evidence that the KERNEL refuses a wrong strength-reduced object is the route's unit test
// `wrong_objects_are_rejected_by_the_kernel` (T-U5, filter off), in
// `src/verify_output_instantiate/strength_route_tests.rs`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Compiled only with `kernel-recheck` (which implies `ay-proofs`): the positives assert the
// clean kernel's [PROVED] grade, which no other build can award. Run: `targo --unverified test
// -p trust-cg-bridge --features kernel-recheck,test-hooks --test strength_reduced_gate`.
#![cfg(feature = "kernel-recheck")]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::CerReport;
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::BinOp;
use trust_ir::{Linkage, Module, Ty};

// ===========================================================================
// helpers
// ===========================================================================

/// The `trust-direct-lane-structural` producer's mangled name for the ladder's `fn h`.
const H: &str = "_RNvCs77DEPyZbqkJ_4rung1h";

/// What every strength-route label ends with (`strength::LABEL_TAIL`).
const TAIL: &str = "Clean.BVC congruence (O(1) add@N, strength-reduced multiply)";
const SHL_MUL: &str = "Trust.BVS.shl_mul";
const SHL_HI_OUT: &str = "Trust.BVS.shl_hi_out";
const COLLECT_ADD: &str = "Trust.BVS.collect_add";
const COLLECT_SUB: &str = "Trust.BVS.collect_sub";
const ADD_REC_M_COMM: &str = "Trust.BVC.addRecM_comm";

/// The label the strength route gives an obligation that used `theorems`, in order.
fn strength_label(theorems: &[&str]) -> String {
    let mut parts = theorems.to_vec();
    parts.push(TAIL);
    parts.join("+")
}

#[track_caller]
fn assert_kernel_proved(fx: &Fixture, report: &CerReport, symbol: &str) {
    assert!(
        report.certificate(symbol).is_some_and(|c| c.is_kernel_proved()),
        "{}: `{symbol}` is not kernel-[PROVED]\n{}\n{}",
        fx.triple,
        explain(report),
        disassemble(&fx.object)
    );
}

#[track_caller]
fn assert_refuted(fx: &Fixture, symbol: &str, what: &str) {
    let report = fx.report();
    let c = report.certificate(symbol).expect("certificate");
    assert!(
        matches!(c.verdict, OutputVerdict::Refuted { .. }),
        "{}: MUTANT `{what}` of `{symbol}` is not Refuted\n{}\n{}",
        fx.triple,
        explain(&report),
        disassemble(&fx.object)
    );
}

/// `symbol` is kernel-[PROVED] by an instantiation whose label is exactly `label` and names no
/// strength theorem it did not use.
#[track_caller]
fn assert_strength_proved(fx: &Fixture, report: &CerReport, symbol: &str, label: &str) {
    assert_kernel_proved(fx, report, symbol);
    let theorem = match &report.certificate(symbol).expect("certificate").verdict {
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { theorem, .. } } => {
            theorem.clone()
        }
        other => panic!("{}: `{symbol}` is not a kernel instantiation: {other:?}", fx.triple),
    };
    assert_eq!(theorem, label, "{}: `{symbol}`'s label\n{}", fx.triple, explain(report));
    for name in [SHL_MUL, SHL_HI_OUT, COLLECT_ADD, COLLECT_SUB, ADD_REC_M_COMM] {
        assert_eq!(
            theorem.contains(name),
            label.contains(name),
            "{}: `{symbol}`: {name} in {theorem}",
            fx.triple
        );
    }
}

/// The words of `symbol` matching `pred`, in order.
fn words_where(fx: &Fixture, symbol: &str, pred: impl Fn(u32) -> bool) -> Vec<(u64, u32)> {
    function_words(&fx.object, symbol).into_iter().filter(|(_, w)| pred(*w)).collect()
}

/// The one word of `symbol` matching `pred` (`what` names it), asserted unique.
#[track_caller]
fn the_one(fx: &Fixture, symbol: &str, what: &str, pred: impl Fn(u32) -> bool) -> (u64, u32) {
    let hits = words_where(fx, symbol, pred);
    assert_eq!(
        hits.len(),
        1,
        "{}: exactly one `{what}` expected in `{symbol}`\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    hits[0]
}

/// Any data-processing (3 source) word: `madd`, `msub`, `mul`, `smulh`, `umaddl`, ...
fn is_multiply(w: u32) -> bool {
    w & 0x1f00_0000 == 0x1b00_0000
}

/// `add Xd, Xn, Xm, lsl #imm` (64-bit, LSL) when `x64`, else the 32-bit `add Wd, Wn, Wm, ...`.
fn is_add_lsl(w: u32, x64: bool, imm: u32) -> bool {
    let op = if x64 { 0x8b00_0000 } else { 0x0b00_0000 };
    w & 0xffe0_0000 == op && (w >> 10) & 0x3f == imm
}

/// `sub Wd, Wn, Wm` (32-bit, unshifted register).
fn is_sub_w(w: u32) -> bool {
    w & 0xffe0_fc00 == 0x4b00_0000
}

/// `movz` of the 16-bit immediate `imm` (either register width, no shift).
fn is_movz(w: u32, imm: u32) -> bool {
    w & 0x7fe0_0000 == 0x5280_0000 && (w >> 5) & 0xffff == imm
}

/// `ubfm Xd, Xn, #63, #62` (`lsl Xd, Xn, #1`).
fn is_ubfm_lsl1(w: u32) -> bool {
    w & 0xffff_fc00 == 0xd37f_f800
}

/// `eor Xd, Xn, Xm, lsl #imm` (64-bit, LSL, any amount).
fn is_eor_x(w: u32) -> bool {
    w & 0xffe0_0000 == 0xca00_0000
}

/// `w` with its shifted-register `imm6` field set to `imm`.
fn with_imm6(w: u32, imm: u32) -> u32 {
    (w & !(0x3f << 10)) | (imm << 10)
}

/// `w` (a UBFM) with its `immr` and `imms` fields set.
fn with_immr_imms(w: u32, immr: u32, imms: u32) -> u32 {
    (w & !0x003f_fc00) | (immr << 16) | (imms << 10)
}

/// The rung as trust-cg receives it: the lane folds a check whose condition is a constant
/// true out of the codegen module (an unsited `Assert` never reaches trust-cg), while the
/// producer the gate reads keeps it.
fn folded(body: &str) -> String {
    body.lines().filter(|l| !l.trim_start().starts_with("assert ")).collect::<Vec<_>>().join("\n")
}

/// The gate's fixture for a whole producer module in text: bytes from the folded module,
/// compiled under the fixture license with the producer's own body-gate authority recognized,
/// and the producer IR as written.
fn producer_fixture(text: &str, triple: &str, opt: OptLevel) -> Fixture {
    let parse =
        |t: &str| trust_ir::parser::parse_module(t).unwrap_or_else(|e| panic!("{e:?}\n{t}"));
    let license = fixture_license().with_recognized_authority("trust-direct-lane-structural");
    let object = compile_under(&parse(&folded(text)), triple, opt, license)
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"));
    Fixture::with_object(targeted(&parse(text), triple), object, triple)
}

// ===========================================================================
// T-G1: s02 `x * 3 + 7`
// ===========================================================================

/// Ladder rung s02 (`tests/trust-f1-ladder/micro/s02_mul_add.rs`): `rung(x) = x * 3 + 7`.
fn s02_module() -> Module {
    let mut mb = ModBuilder::new("cer_strength_s02");
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    mb.define("rung", s, Linkage::External, |fb| {
        let three = fb.konst(Ty::U64, 3);
        let product = fb.bin(BinOp::Mul, Ty::U64, fb.p(0), three);
        let seven = fb.konst(Ty::U64, 7);
        let out = fb.bin(BinOp::Add, Ty::U64, product, seven);
        fb.ret(out);
    });
    mb.finish()
}

/// s02 at O2 is `movz x1, #7; add x2, x0, x1; add x0, x2, x0, lsl #1`: no multiply.
fn s02_fixture(triple: &str) -> Fixture {
    let fx = Fixture::new(s02_module(), triple, OptLevel::O2);
    assert!(
        words_where(&fx, "rung", is_multiply).is_empty(),
        "{triple}: s02 at O2 multiplies\n{}",
        disassemble(&fx.object)
    );
    fx
}

/// POSITIVE T-G1: s02 at O2 is kernel-[PROVED] through `shl_mul` then `collect_add`, with no
/// Add commutation. FAILS without the strength route: the grade is [VALIDATED].
#[test]
fn s02_strength_reduced_mul_add_is_kernel_proved() {
    for triple in BOTH {
        let fx = s02_fixture(triple);
        the_one(&fx, "rung", "add x, x, x, lsl #1", |w| is_add_lsl(w, true, 1));
        assert_strength_proved(&fx, &fx.report(), "rung", &strength_label(&[SHL_MUL, COLLECT_ADD]));
    }
}

// ===========================================================================
// T-G2: s09 `h(x as u32) as u64`, `h(a) = a * 7 + 3`
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung s09
/// (`tests/trust-f1-ladder/micro/s09_u32.rs`), the whole two-function module, with the `#loc`
/// comments and the `target` and `file` lines dropped so [`targeted`] stamps each triple.
const S09_IR: &str = r#"; TrustIr text format v1
module "rung"

functy.0 = (u32) -> (u32)

functy.1 = (u64) -> (u64)

rustcc fn @_RNvCs77DEPyZbqkJ_4rung1h(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "h"
    ; #names: %0="a"
bb0(%0: u32):
    %1 = const u32 7
    %2 = mul u32 %0, %1
    %3 = const u32 3
    %4 = add u32 %2, %3
    ret %4
}

fn @rung(functy.1) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = trunc u64 %0 to u32
    %2 = call @func.0(%1)
    %3 = zext u32 %2 to u64
    ret %3
}
"#;

/// s09 at O2: `h` is `movz w1, #3; add w2, w1, w0, lsl #3; sub w0, w2, w0`, and `rung` inlines
/// the same three words between two zero-extending `orr`s. Neither multiplies.
fn s09_fixture(triple: &str) -> Fixture {
    let fx = producer_fixture(S09_IR, triple, OptLevel::O2);
    for symbol in [H, "rung"] {
        assert!(
            words_where(&fx, symbol, is_multiply).is_empty(),
            "{triple}: s09 `{symbol}` at O2 multiplies\n{}",
            disassemble(&fx.object)
        );
        the_one(&fx, symbol, "add w, w, w, lsl #3", |w| is_add_lsl(w, false, 3));
        the_one(&fx, symbol, "sub w, w, w", is_sub_w);
    }
    fx
}

/// POSITIVE T-G2: both functions of s09 at O2 are kernel-[PROVED] through `shl_mul` then
/// `collect_sub`, with one Add commutation (`3 + x*8` to `x*8 + 3`). `rung`'s obligation is
/// the 64-bit zero extension of `h`'s, under the `orr` wrappers.
#[test]
fn s09_strength_reduced_u32_mul_add_is_kernel_proved() {
    let label = strength_label(&[SHL_MUL, COLLECT_SUB, ADD_REC_M_COMM]);
    for triple in BOTH {
        let fx = s09_fixture(triple);
        let report = fx.report();
        assert_strength_proved(&fx, &report, H, &label);
        assert_strength_proved(&fx, &report, "rung", &label);
    }
}

// ===========================================================================
// T-G3: s14 / s15 `(x + 1) ^ (x * 2)` through an aggregate, and its scalar twin
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rungs s14 and s15 (trustc ac76a2c1a,
/// `-Ztrust-ir-lower=on -Coverflow-checks=off`), `#loc`/`#scope` comments and the `target` line
/// dropped so [`targeted`] stamps each triple. Copied from `call_event_gate.rs`.
const AGG_HEAD: &str = "module \"rung\"\nstruct @P { a: u64 @0, b: u64 @8 } size=16 align=8 id=0\n\
                        enum @E repr(u64) { A = 0, B(u64) = 1 } layout(direct tag@0 size=16 \
                        align=8 offsets=[[], [8]]) id=0\n\
                        functy.0 = (u64) -> (u64)\ntype ty.0 = u64\n";

/// The gate's fixture for a rung: bytes from the folded module, the producer IR as written.
fn rung_fixture(body: &str, triple: &str, opt: OptLevel) -> Fixture {
    let object = Fixture::new(rung_ir(&folded(body)), triple, opt).object;
    Fixture::with_object(targeted(&rung_ir(body), triple), object, triple)
}

fn rung_ir(body: &str) -> Module {
    let text = format!(
        "{AGG_HEAD}\nfn @rung(functy.0) {{\n    ; #producer: trust\nbb0(%0: u64):\n{body}\n}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

const S14_IR: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %5 = const (u64, u64) { 0, 0 }
    %6 = insertfield (u64, u64) %5, 0, %2
    %7 = insertfield (u64, u64) %6, 1, %4
    %8 = extractfield u64 %7, 0
    %9 = extractfield u64 %7, 1
    %10 = xor u64 %8, %9
    ret %10";

const S15_IR: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %5 = const struct.0 { 0, 0 }
    %6 = insertfield struct.0 %5, 0, %2
    %7 = insertfield struct.0 %6, 1, %4
    %8 = extractfield u64 %7, 0
    %9 = extractfield u64 %7, 1
    %10 = xor u64 %8, %9
    ret %10";

/// `(x+1) ^ (x*2)` without an aggregate: the scalar twin of s14/s15.
const S14_TWIN: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %10 = xor u64 %2, %4
    ret %10";

/// `rung` at O2 computes `x * 2` with `ubfm x, x, #63, #62` and joins with an `eor`; no
/// multiply.
fn assert_ubfm_eor(fx: &Fixture) -> (u64, u32) {
    assert!(
        words_where(fx, "rung", is_multiply).is_empty(),
        "{}: O2 multiplies\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    the_one(fx, "rung", "eor x, x, x", is_eor_x);
    the_one(fx, "rung", "ubfm x, x, #63, #62", is_ubfm_lsl1)
}

/// POSITIVE T-G3: s14 (tuple) and s15 (struct) at O2 are kernel-[PROVED] through `shl_hi_out`
/// (the UBFM's zero-extended low 63 bits shifted by one equal the whole register shifted by
/// one) then `shl_mul`. Their scalar twin is kernel-[PROVED] too, through `shl_mul` alone:
/// trust-cg fuses its shift into the `eor` (`eor x0, x1, x0, lsl #1`), with no UBFM.
#[test]
fn s14_s15_ubfm_doubling_is_kernel_proved() {
    for triple in BOTH {
        for body in [S14_IR, S15_IR] {
            let fx = rung_fixture(body, triple, OptLevel::O2);
            assert_ubfm_eor(&fx);
            let label = strength_label(&[SHL_HI_OUT, SHL_MUL]);
            assert_strength_proved(&fx, &fx.report(), "rung", &label);
        }
        let twin = rung_fixture(S14_TWIN, triple, OptLevel::O2);
        assert!(
            words_where(&twin, "rung", is_multiply).is_empty()
                && words_where(&twin, "rung", is_ubfm_lsl1).is_empty(),
            "{triple}: the twin at O2 multiplies or keeps a UBFM\n{}",
            disassemble(&twin.object)
        );
        the_one(&twin, "rung", "eor x, x, x, lsl #1", |w| is_eor_x(w) && (w >> 10) & 0x3f == 1);
        assert_strength_proved(&twin, &twin.report(), "rung", &strength_label(&[SHL_MUL]));
    }
}

// ===========================================================================
// s08: `h(x, 3)`, `h(a, b) = a * b + a`
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung s08
/// (`tests/trust-f1-ladder/micro/s08_two_args.rs`), the whole two-function module, with the
/// `#loc` comments and the `target` and `file` lines dropped so [`targeted`] stamps each triple.
const S08_IR: &str = r#"; TrustIr text format v1
module "rung"

functy.0 = (u64, u64) -> (u64)

functy.1 = (u64) -> (u64)

rustcc fn @_RNvCs77DEPyZbqkJ_4rung1h(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "h"
    ; #names: %0="a", %1="b"
bb0(%0: u64, %1: u64):
    %2 = mul u64 %0, %1
    %3 = add u64 %2, %0
    ret %3
}

fn @rung(functy.1) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = const u64 3
    %2 = call @func.0(%0, %1)
    ret %2
}
"#;

/// POSITIVE (s08): at O2 `rung` inlines `h(x, 3)` as `add x1, x0, x0; add x0, x1, x0, lsl #1`,
/// an S3 instance with the addend `x` after `shl_mul`: kernel-[PROVED] through `shl_mul` then
/// `collect_add`. `h` keeps its `madd` and is proved by the Add commutation alone.
#[test]
fn s08_inlined_constant_argument_is_kernel_proved() {
    for triple in BOTH {
        let fx = producer_fixture(S08_IR, triple, OptLevel::O2);
        assert!(
            words_where(&fx, "rung", is_multiply).is_empty(),
            "{triple}: s08 `rung` at O2 multiplies\n{}",
            disassemble(&fx.object)
        );
        the_one(&fx, "rung", "add x, x, x, lsl #1", |w| is_add_lsl(w, true, 1));
        let report = fx.report();
        assert_strength_proved(&fx, &report, "rung", &strength_label(&[SHL_MUL, COLLECT_ADD]));
        assert_kernel_proved(&fx, &report, H);
    }
}

// ===========================================================================
// T-G4: mutants
// ===========================================================================

/// MUTANT (s02): `add x0, x2, x0, lsl #1` made `lsl #2`, so the object computes `x * 5 + 7`.
#[test]
fn mutant_s02_shift_by_two() {
    for triple in BOTH {
        let fx = s02_fixture(triple);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (at, w) = the_one(&fx, "rung", "add x, x, x, lsl #1", |w| is_add_lsl(w, true, 1));
        let m = fx.patched(|o| patch_word(o, at, with_imm6(w, 2)));
        assert_refuted(&m, "rung", "x * 3 + 7 specified, x + 7 + (x << 2) computed");
    }
}

/// MUTANT (s02): `movz x1, #7` made `#8`, so the object computes `x * 3 + 8`.
#[test]
fn mutant_s02_addend_eight() {
    for triple in BOTH {
        let fx = s02_fixture(triple);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (at, w) = the_one(&fx, "rung", "movz #7", |w| is_movz(w, 7));
        let m = fx.patched(|o| patch_word(o, at, (w & !(0xffff << 5)) | (8 << 5)));
        assert_refuted(&m, "rung", "x * 3 + 7 specified, x + 8 + (x << 1) computed");
    }
}

/// MUTANT (s09, in `h` and in `rung` separately): the `sub` made `add` (bit 30), so the
/// function computes `a * 9 + 3`.
#[test]
fn mutant_s09_sub_made_add() {
    for triple in BOTH {
        let fx = s09_fixture(triple);
        let report = fx.report();
        for symbol in [H, "rung"] {
            assert_kernel_proved(&fx, &report, symbol);
            let (at, w) = the_one(&fx, symbol, "sub w, w, w", is_sub_w);
            let m = fx.patched(|o| patch_word(o, at, w & !0x4000_0000));
            assert_refuted(&m, symbol, "a * 7 + 3 specified, (3 + (a << 3)) + a computed");
        }
    }
}

/// MUTANT (s09, in `h` and in `rung` separately): `add w, w, w, lsl #3` made `lsl #2`, so the
/// function computes `a * 3 + 3`.
#[test]
fn mutant_s09_shift_by_two() {
    for triple in BOTH {
        let fx = s09_fixture(triple);
        let report = fx.report();
        for symbol in [H, "rung"] {
            assert_kernel_proved(&fx, &report, symbol);
            let (at, w) = the_one(&fx, symbol, "add w, w, w, lsl #3", |w| is_add_lsl(w, false, 3));
            let m = fx.patched(|o| patch_word(o, at, with_imm6(w, 2)));
            assert_refuted(&m, symbol, "a * 7 + 3 specified, (3 + (a << 2)) - a computed");
        }
    }
}

/// MUTANT (s14): the UBFM's `immr/imms` `63/62` (`lsl #1`) made `62/61` (`lsl #2`), so the
/// object computes `(x + 1) ^ (x * 4)`.
#[test]
fn mutant_s14_ubfm_shift_by_two() {
    for triple in BOTH {
        let fx = rung_fixture(S14_IR, triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (at, w) = assert_ubfm_eor(&fx);
        let m = fx.patched(|o| patch_word(o, at, with_immr_imms(w, 62, 61)));
        assert_refuted(&m, "rung", "(x + 1) ^ (x * 2) specified, (x + 1) ^ (x << 2) computed");
    }
}

/// MUTANT (s14): the UBFM's `imms` made 7 (`ubfiz x, x, #1, #8`), so the object doubles only
/// the low byte: `(x + 1) ^ ((x & 0xff) << 1)`. `shl_hi_out` declines a zero extension that
/// drops live bits, and the obligation is Refuted.
#[test]
fn mutant_s14_ubfm_made_ubfiz() {
    for triple in BOTH {
        let fx = rung_fixture(S14_IR, triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (at, w) = assert_ubfm_eor(&fx);
        let m = fx.patched(|o| patch_word(o, at, with_immr_imms(w, 63, 7)));
        assert_refuted(&m, "rung", "(x + 1) ^ (x * 2) specified, ubfiz #1, #8 computed");
    }
}
