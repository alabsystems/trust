// tests/constdiv_gate.rs — the call-event gate over the ladder's constant divisions, decided at
// step (4) on the kernel-certified CONSTDIV rewrite and kernel-proved at step (5) by the CONSTDIV
// conjunction route (DECISION_QUEUE CONSTDIV-1; `verify_output_instantiate/const_div.rs`,
// `step4_rewrite` and `try_conjunction`, the latter reached through `branch_dispatch.rs`).
//
// trust-cg divides by a constant with the AArch64 magic multiply-high: `x / 3` is
// `umulh(x, 0xAAAAAAAAAAAAAAAB) >> 1`, and s20's `x % 7` is the add-back quotient
// `(t + ((x - t) >> 1)) >> 2` with `t = umulh(x, 0x2492492492492493)`, then `x - q * 7`. Before
// the hook, step (4) handed ay the multiply-high against the spec's `bvudiv`, a CDCL miter it
// cannot close: every cell ran its whole per-query budget and was Unknown ("value(return) did
// not conclude"; 120 s on the stage-1 ladder, `docs/STATUS.md`). With the hook, each magic
// quotient of the machine side is replaced by `x / d` under a kernel-admitted certificate
// `R(core) = R(x / d)` (`Trust.BVD.magic_noadd` / `magic_addback`), and ay decides the rewritten
// item, which shares the spec's division. Stage B2: step (5) then hands the ORIGINAL conjunction
// (the 128-bit product, never the rewrite) to the branch routes, where, after the branch split and
// the division split decline, the CONSTDIV route proves it in the kernel; step (5)'s CONSTDIV-1
// filter keeps that kernel evidence, so the cell is kernel-[PROVED] with the route's label, and O4
// still names the step-(4) rewrite.
//
// POSITIVES: s20 (`x % 7`) and the standalone `x / 3`, at O0 and O2 on both triples, are Proven
// by `KernelInstantiated` with the exact CONSTDIV label, each gate run timed against a bound far
// below the 120 s budget; the hook is handed each item's left side once (never the right side)
// and rewrites exactly once, on `value(return)`, whose left side carries the multiply-high and no
// division; step (5) calls the branch routes once and they return kernel evidence.
//
// THE ROUTE OFF: with the CONSTDIV conjunction route off (`without_const_div_conjunction`), every
// positive cell is Proven [VALIDATED] (`AyValidated`) with the rewrite named, as at stage B1: the
// branch routes are called once and decline.
//
// THE OLD PATH: with the hook off (`without_const_div_rewrite`), every positive cell is Unknown
// at step (4), ended on one of ay's deterministic counts (`[stop:effort]`, DECISION_QUEUE
// BUDGET-1; the gate's `:rlimit` among them), exactly as before the hook, and step (5) is never
// reached.
//
// R01 (`x / 3 + (x ^ 0x55) * 2`, shifted, or-ed, …): measured and pinned as observed: Proven
// [VALIDATED] on the rewrite, the branch routes called once and declining (the CONSTDIV walk
// refuses the producer's shift amounts, `(sext i32 3 to u64) & 63 & 63` and a non-literal `lshr`
// amount: `const_div.rs`'s walk has no sign-extension arm and shifts right only by a literal;
// `const_div/tests.rs` `r01_declines_at_the_shift_amounts_only`).
//
// MUTANTS: a wrong magic constant (the `movz` low half-word plus 2: outside the band, so the
// search declines it before any kernel work, `const_div/tests.rs`
// `magic_plus_two_is_declined_at_the_band`, and ay refutes the old miter), a wrong final shift,
// and an off-by-one divisor in the IR (bytes for 3 or 7 against IR for 2 / 4 or 6 / 8): each is
// asserted Refuted (at step (4): step (5)'s routes are never called), and each has its unmutated
// twin kernel-proved in the same test. The shift and
// divisor mutants are asserted rewritten and then Refuted by ay on the rewritten item, so a
// miscompile stays caught through the hook; the magic + 2 mutants are asserted not rewritten.
//
// BUDGET: every gate query runs under its effort count (`:rlimit`, sized to the query) and a
// wall-clock backstop the gate reads from `TCG_TRUST_IR_GATE_TIMEOUT_MS` (the build refuses
// `TCG_*` in its own environment, and the frozen gate's thread-local seam is `cfg(test)` only),
// so [`init`] sets the backstop once for this binary before any test does anything else.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Compiled only with `kernel-recheck` (the hook's certificate is the clean kernel's) and
// `test-hooks` (the hook's calls are read, and turned off, through its test hooks). Run:
// `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks --test
// constdiv_gate`.
#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]

mod cer_common;

use std::time::Instant;

use cer_common::*;
use trust_cg_bridge::call_event::{CerInput, CerReport, verify_compiled_module};
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_instantiate::{
    HookCall, record_branch_split_calls, record_const_div_rewrites, without_const_div_conjunction,
    without_const_div_rewrite,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::Module;
use trust_types::Formula;
use trust_types::determinism::StopCause;

// ===========================================================================
// helpers
// ===========================================================================

/// The per-query wall-clock backstop of every gate solver in this binary, in ms: the
/// production value. The old-path cells end on their effort count (3.6 to 8.3 s each in a debug
/// build, measured 2026-11-15), so a shorter clock would let the machine's load decide which
/// stop they report.
const GATE_BUDGET_MS: u64 = 120_000;

/// The bound on one positive gate run (debug build), far below the production budget and
/// the ladder's timeout (both 120 s).
const POSITIVE_BOUND_MS: u128 = 20_000;

const OPTS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// What the hook's note opens with for the function's return value.
const NOTE: &str = "; value(return) was decided by ay on its CONSTDIV rewrite (1 magic quotient(s)";
const MAGIC_NOADD: &str = "Trust.BVD.magic_noadd";
const MAGIC_ADDBACK: &str = "Trust.BVD.magic_addback";
const REM_TAIL: &str = "Trust.BVD.rem_tail";
const TAIL: &str = "Trust.BVD constant division (magic multiply-high, kernel-checked)";

/// The exact labels of the CONSTDIV conjunction route on the gate's step-(5) conjunctions (the
/// same strings `const_div/tests.rs` pins on the hand-built conjunctions, which it pins equal to
/// these cells' own): s20 at O0 (UBFM halving, the `orr` move), s20 at O2 (`lsr #1` halving), and
/// `x / 3` (one conjunction at O0 and O2).
const LABEL_S20_O0: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+\
Clean.BVC.bvf_div_cong+Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
Clean.BVC.bvf_shl_cong+Clean.BVC.bvf_sub_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVD.magic_addback+Trust.BVD.rem_tail+\
Trust.BVD.ubfm_k+Trust.BVV.len_natToBv+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";
const LABEL_S20_O2: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+\
Clean.BVC.bvf_div_cong+Clean.BVC.bvf_lshr_cong+Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+\
Clean.BVC.bvf_shl_cong+Clean.BVC.bvf_sub_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVD.lshr_k+Trust.BVD.magic_addback+\
Trust.BVD.rem_tail+Trust.BVV.len_natToBv+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";
const LABEL_DIV3: &str = "Clean.BVC.bvf_and_cong+Clean.BVC.bvf_div_cong+\
Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVD.magic_noadd+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";

/// Set the gate budget for this process, once, before anything else runs.
fn init() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        // SAFETY: every test in this binary calls `init` first, and `Once` holds every other
        // caller until this returns, so no thread of this process reads the environment while
        // it is written.
        // The one blessed write: set once, never restored, read only after this returns.
        #[allow(env_mutation)]
        unsafe {
            std::env::set_var("TCG_TRUST_IR_GATE_TIMEOUT_MS", GATE_BUDGET_MS.to_string());
        }
    });
}

/// The rung as trust-cg receives it: the lane folds a check whose condition is a constant
/// true out of the codegen module, while the producer the gate reads keeps it.
fn folded(body: &str) -> String {
    body.lines().filter(|l| !l.trim_start().starts_with("assert ")).collect::<Vec<_>>().join("\n")
}

fn parse(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

/// The gate's fixture for a whole producer module in text: bytes from the folded module,
/// compiled under the fixture license with the producer's own body-gate authority recognized,
/// and the producer IR as written (`branch_split_gate.rs`'s configuration).
fn producer_fixture(text: &str, triple: &str, opt: OptLevel) -> Fixture {
    let license = fixture_license().with_recognized_authority("trust-direct-lane-structural");
    let object = compile_under(&parse(&folded(text)), triple, opt, license)
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"));
    Fixture::with_object(targeted(&parse(text), triple), object, triple)
}

/// `fx`'s bytes read against the producer IR `text` instead (an IR mutant).
fn against(fx: &Fixture, text: &str) -> Fixture {
    Fixture::with_object(targeted(&parse(text), &fx.triple), fx.object.clone(), &fx.triple)
}

/// `text` with `from` replaced by `to`, asserted to occur exactly once.
#[track_caller]
fn replace_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "`{from}` is not unique in the IR");
    text.replacen(from, to, 1)
}

/// What a gate run turns off.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Off {
    /// Nothing: the gate as it ships.
    Nothing,
    /// The step-(4) hook (`without_const_div_rewrite`).
    Hook,
    /// The step-(5) CONSTDIV conjunction route (`without_const_div_conjunction`).
    Route,
}

/// One gate run on the 8 MiB gate thread, the hook's calls and the step-(5) branch-route calls
/// recorded (`true` where the routes returned kernel evidence).
struct Run {
    report: CerReport,
    calls: Vec<HookCall>,
    routes: Vec<bool>,
    ms: u128,
}

fn run(fx: &Fixture, off: Off) -> Run {
    init();
    let t = Instant::now();
    let ((report, calls), routes) = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                let gate = || {
                    verify_compiled_module(&CerInput {
                        m_cg: &fx.m_cg,
                        producers: &fx.producers,
                        bodies: &fx.bodies,
                        placements: &fx.placements,
                        object: &fx.object,
                        relocation_model: fx.model,
                    })
                };
                record_branch_split_calls(|| {
                    record_const_div_rewrites(|| match off {
                        Off::Nothing => gate(),
                        Off::Hook => without_const_div_rewrite(gate),
                        Off::Route => without_const_div_conjunction(gate),
                    })
                })
            })
            .expect("spawn the gate thread")
            .join()
            .expect("the gate thread panicked")
    });
    let ms = t.elapsed().as_millis();
    let report = report.unwrap_or_else(|e| {
        panic!("{}: object refused: {e}\n{}", fx.triple, disassemble(&fx.object))
    });
    Run { report, calls, routes, ms }
}

/// Does `f` mention a division or a remainder (the spec's `value(return)` does; the magic
/// bytes have none)?
fn has_division(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |n| {
        if matches!(n, Formula::BvUDiv(..) | Formula::BvURem(..)) {
            found = true;
        }
    });
    found
}

/// Does `f` hold a 64-bit multiply-high (`umulh`, bits 127..64 of a 128-bit product: the
/// machine side's; no spec side has one)?
fn has_umulh(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |n| {
        if let Formula::BvExtract { inner, high: 127, low: 64 } = n
            && matches!(**inner, Formula::BvMul(_, _, 128))
        {
            found = true;
        }
    });
    found
}

/// The hook was handed each item once (a call on a right side too would repeat a name), and
/// rewrote exactly once, on `value(return)`, whose recorded input is the machine side: it holds
/// the multiply-high and no division (the right side, the spec's, holds the division and no
/// multiply-high).
#[track_caller]
fn assert_hook_calls(r: &Run, what: &str) {
    let names: Vec<&str> = r.calls.iter().map(|(n, _, _)| n.as_str()).collect();
    let mut unique = names.clone();
    unique.sort_unstable();
    unique.dedup();
    assert_eq!(
        unique.len(),
        names.len(),
        "{what}: an item was handed to the hook twice: {names:?}"
    );
    let rewrote: Vec<&(String, Formula, Option<String>)> =
        r.calls.iter().filter(|(_, _, note)| note.is_some()).collect();
    assert_eq!(
        rewrote.iter().map(|(n, _, _)| n.as_str()).collect::<Vec<_>>(),
        ["value(return)"],
        "{what}: the hook did not rewrite exactly once, on value(return): {names:?}"
    );
    let (_, m, _) = rewrote[0];
    assert!(
        has_umulh(m) && !has_division(m),
        "{what}: the hook was not handed value(return)'s machine side"
    );
}

/// `rung` is kernel-[PROVED] by the CONSTDIV conjunction route: `KernelInstantiated` with exactly
/// `label`, O4 still naming the step-(4) rewrite and every theorem in `want`; the hook calls are
/// [`assert_hook_calls`]', and step (5) called the branch routes once, which returned kernel
/// evidence.
#[track_caller]
fn assert_kernel_proved(fx: &Fixture, r: &Run, what: &str, want: &[&str], label: &str) {
    let c = r.report.certificate("rung").expect("certificate");
    assert!(
        matches!(&c.verdict, OutputVerdict::Proven {
            evidence: ProvenEvidence::KernelInstantiated { theorem, original: None }
        } if theorem == label)
            && c.is_kernel_proved(),
        "{what}: not kernel-[PROVED] with the CONSTDIV label {label}: {:?}\n{}\n{}",
        c.verdict,
        explain(&r.report),
        disassemble(&fx.object)
    );
    assert!(label.contains("Trust.BVD.") && label.ends_with(TAIL), "{what}: {label}");
    let o4 = &c.obligations.o4_return.detail;
    assert!(
        o4.contains(NOTE) && o4.ends_with(&format!("{TAIL})")),
        "{what}: O4 does not name the rewrite: {o4}"
    );
    for t in want {
        assert!(o4.contains(t), "{what}: O4 does not name {t}: {o4}");
    }
    assert_hook_calls(r, what);
    assert_eq!(r.routes, [true], "{what}: step (5)'s branch routes");
}

/// `rung` is Proven [VALIDATED] on the rewrite: `AyValidated`, not kernel-proved, O4 naming
/// the rewrite and every theorem in `want`; the hook calls are [`assert_hook_calls`]', and step
/// (5) called the branch routes once, which declined.
#[track_caller]
fn assert_rewrite_validated(fx: &Fixture, r: &Run, what: &str, want: &[&str]) {
    let c = r.report.certificate("rung").expect("certificate");
    assert!(
        matches!(c.verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated })
            && !c.is_kernel_proved(),
        "{what}: not Proven [VALIDATED] on the rewrite: {:?}\n{}\n{}",
        c.verdict,
        explain(&r.report),
        disassemble(&fx.object)
    );
    let o4 = &c.obligations.o4_return.detail;
    assert!(
        o4.contains(NOTE) && o4.ends_with(&format!("{TAIL})")),
        "{what}: O4 does not name the rewrite: {o4}"
    );
    for t in want {
        assert!(o4.contains(t), "{what}: O4 does not name {t}: {o4}");
    }
    assert_hook_calls(r, what);
    assert_eq!(r.routes, [false], "{what}: step (5)'s branch routes");
}

/// Refuted by ay's counterexample on `value(return)`, the hook having rewritten that item first
/// exactly when `rewritten` (so a refutation on the rewritten item is what is shown, or, for a
/// mutant the search declines, one on the old miter), at step (4), so step (5)'s branch routes are
/// never called. Returns the verdict's account.
#[track_caller]
fn assert_refuted(fx: &Fixture, what: &str, rewritten: bool) -> String {
    let r = run(fx, Off::Nothing);
    let c = r.report.certificate("rung").expect("certificate");
    let detail = &c.obligations.o4_return.detail;
    assert!(
        matches!(c.verdict, OutputVerdict::Refuted { .. })
            && !c.is_kernel_proved()
            && detail.ends_with("violate value(return): ay found a counterexample input"),
        "MUTANT `{what}` is not Refuted on value(return): {:?} {detail}\n{}\n{}",
        c.verdict,
        explain(&r.report),
        disassemble(&fx.object)
    );
    let notes: Vec<&str> =
        r.calls.iter().filter(|(_, _, n)| n.is_some()).map(|(n, _, _)| n.as_str()).collect();
    let want: &[&str] = if rewritten { &["value(return)"] } else { &[] };
    assert_eq!(notes, want, "MUTANT `{what}`: rewritten {notes:?}, expected {want:?}");
    assert!(r.routes.is_empty(), "MUTANT `{what}`: step (5) was reached: {:?}", r.routes);
    format!("{what}: {} in {} ms (rewritten: {rewritten}): {detail}", c.grade, r.ms)
}

/// The one word of `rung` matching `pred` (`what` names it), asserted unique.
#[track_caller]
fn the_one(fx: &Fixture, what: &str, pred: impl Fn(u32) -> bool) -> (u64, u32) {
    let hits: Vec<(u64, u32)> =
        function_words(&fx.object, "rung").into_iter().filter(|(_, w)| pred(*w)).collect();
    assert_eq!(
        hits.len(),
        1,
        "{}: exactly one `{what}` expected in `rung`\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    hits[0]
}

/// `umulh Xd, Xn, Xm`.
fn is_umulh(w: u32) -> bool {
    w & 0xffe0_fc00 == 0x9bc0_7c00
}

/// `udiv` / `sdiv` (either width).
fn is_hw_div(w: u32) -> bool {
    w & 0x7fe0_f800 == 0x1ac0_0800
}

/// `movz Xd, #imm` (64-bit, half-word 0).
fn is_movz64(w: u32, imm: u32) -> bool {
    w & 0xffe0_0000 == 0xd280_0000 && (w >> 5) & 0xffff == imm
}

/// `ubfm Xd, Xn, #k, #63` (`lsr Xd, Xn, #k`).
fn is_lsr_imm(w: u32, k: u32) -> bool {
    w & 0xffc0_fc00 == 0xd340_fc00 && (w >> 16) & 0x3f == k
}

fn with_immr(w: u32, k: u32) -> u32 {
    (w & !(0x3f << 16)) | (k << 16)
}

fn with_imm16(w: u32, imm: u32) -> u32 {
    (w & !(0xffff << 5)) | (imm << 5)
}

/// The magic sequence, not a hardware divide.
#[track_caller]
fn assert_magic_bytes(fx: &Fixture) {
    let words = function_words(&fx.object, "rung");
    assert!(
        words.iter().any(|(_, w)| is_umulh(*w)) && !words.iter().any(|(_, w)| is_hw_div(*w)),
        "{}: not the umulh sequence\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
}

// ===========================================================================
// the rungs
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung s20
/// (`tests/trust-f1-ladder/micro/s20_rem_const.rs`; stage-1 trustc 3bea2f1d41,
/// `-Ztrust-verify=off -Ztrust-ir-lower=on -Coverflow-checks=off`, identical at O0 and O2),
/// the `target` line dropped so [`targeted`] stamps each triple.
const S20_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s20_rem_const.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = const u64 7
    %2 = const u64 0
    %3 = icmp ne u64 %1, %2
    assert %3, rem_by_zero  ; #proof: div_nonzero
    %4 = urem u64 %0, %1
    ret %4
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L1C53 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C53#rem_by_zero#o0" range 0 1 53 1 58 site f0/bb0#3
"#;

/// The standalone `x / 3`: s20 with `udiv` by 3 (the producer's shape for a `/` by a
/// literal; the same text the stage-A capture compiled).
fn d3_ir() -> String {
    S20_IR
        .replace("urem u64 %0, %1", "udiv u64 %0, %1")
        .replace("const u64 7", "const u64 3")
        .replace("rem_by_zero", "div_by_zero")
}

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung r01
/// (`tests/trust-f1-ladder/programs/r01_arith.rs`; same trustc and flags as [`S20_IR`]).
const R01_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/programs/r01_arith.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = const u64 3
    %2 = const u64 0
    %3 = icmp ne u64 %1, %2
    assert %3, div_by_zero  ; #proof: div_nonzero
    %4 = udiv u64 %0, %1
    %5 = const u64 85
    %6 = xor u64 %0, %5
    %7 = const u64 2
    %8 = mul u64 %6, %7
    %9 = add u64 %4, %8
    %10 = const i32 3
    %11 = const u64 63
    %12 = sext i32 %10 to u64
    %13 = and u64 %12, %11
    %14 = shl u64 %9, %13
    %15 = const u64 7
    %16 = and u64 %0, %15
    %17 = or u64 %14, %16
    %18 = const i32 1
    %19 = const u64 63
    %20 = sext i32 %18 to u64
    %21 = and u64 %20, %19
    %22 = lshr u64 %0, %21
    %23 = sub u64 %17, %22
    %24 = const u64 11
    %25 = add u64 %23, %24
    ret %25
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L1C61 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C61#div_by_zero#o0" range 0 1 61 1 66 site f0/bb0#3
"#;

/// `(label, IR, theorems the O4 note must name)` of the two positives.
fn positives() -> [(&'static str, String, Vec<&'static str>); 2] {
    [("s20", S20_IR.to_string(), vec![MAGIC_ADDBACK]), ("x/3", d3_ir(), vec![MAGIC_NOADD])]
}

/// The exact CONSTDIV label of a positive cell.
fn label_of(rung: &str, opt: OptLevel) -> &'static str {
    match (rung, opt) {
        ("s20", OptLevel::O0) => LABEL_S20_O0,
        ("s20", _) => LABEL_S20_O2,
        _ => LABEL_DIV3,
    }
}

// ===========================================================================
// positives
// ===========================================================================

/// POSITIVE: s20 (`x % 7`) and `x / 3`, at O0 and O2 on both triples, are kernel-[PROVED] by
/// the CONSTDIV conjunction route with its exact label, the O4 detail still naming the step-(4)
/// rewrite and its theorems, each gate run under [`POSITIVE_BOUND_MS`]. FAILS without the route
/// (every cell [VALIDATED], `constant_divisions_are_validated_on_the_rewrite`) and without the hook
/// (every cell Unknown at step (4), `without_the_hook_the_old_path_is_taken`).
#[test]
fn constant_divisions_are_kernel_proved() {
    let mut times = Vec::new();
    for (label, ir, want) in positives() {
        for triple in BOTH {
            for opt in OPTS {
                let fx = producer_fixture(&ir, triple, opt);
                assert_magic_bytes(&fx);
                let r = run(&fx, Off::Nothing);
                let what = format!("{label} {triple} {opt:?}");
                assert_kernel_proved(&fx, &r, &what, &want, label_of(label, opt));
                assert!(
                    r.ms < POSITIVE_BOUND_MS,
                    "{what}: the gate took {} ms (bound {POSITIVE_BOUND_MS} ms)",
                    r.ms
                );
                times.push(format!("{what}: {} ms", r.ms));
            }
        }
    }
    println!("constdiv gate, positive cells (debug): {times:#?}");
    assert_eq!(times.len(), 8);
}

/// The step-(4) note names the remainder tail's theorem only where the item has one: never,
/// since the rewrite certifies the magic quotients alone and ay decides the tail (`x - q * 7`) on
/// the rewritten item. The step-(5) kernel proof is the whole conjunction's: its label names the
/// tail (`Trust.BVD.rem_tail`). Pins that the step-(4) certificate is the quotient's, not a
/// whole-function proof, and that the grade rests on the conjunction's.
#[test]
fn the_rewrite_certifies_the_quotient_only() {
    let fx = producer_fixture(S20_IR, DARWIN, OptLevel::O2);
    let r = run(&fx, Off::Nothing);
    assert_kernel_proved(&fx, &r, "s20 darwin O2", &[MAGIC_ADDBACK], LABEL_S20_O2);
    let o4 = &r.report.certificate("rung").expect("certificate").obligations.o4_return.detail;
    assert!(!o4.contains(REM_TAIL), "the rewrite claims the remainder tail: {o4}");
    assert!(LABEL_S20_O2.contains(REM_TAIL) && LABEL_S20_O2.contains(MAGIC_ADDBACK));
}

// ===========================================================================
// the route off
// ===========================================================================

/// With the CONSTDIV conjunction route off (the name is stage B1's, which the call_event.rs
/// waiver row cites for that stage's step-(4) behaviour), every positive cell is what stage B1
/// made it: Proven
/// [VALIDATED] (`AyValidated`) on the step-(4) rewrite, O4 naming the rewrite and its theorems,
/// step (5)'s branch routes called once and declining (the branch split's walk refuses the
/// 128-bit product and no divisor has a variable), so CONSTDIV-1's step-(5) filter grades it
/// [VALIDATED].
#[test]
fn constant_divisions_are_validated_on_the_rewrite() {
    let mut seen = Vec::new();
    for (label, ir, want) in positives() {
        for triple in BOTH {
            for opt in OPTS {
                let fx = producer_fixture(&ir, triple, opt);
                let r = run(&fx, Off::Route);
                let what = format!("{label} {triple} {opt:?} (route off)");
                assert_rewrite_validated(&fx, &r, &what, &want);
                seen.push(format!("{what}: {} ms", r.ms));
            }
        }
    }
    println!("{seen:#?}");
    assert_eq!(seen.len(), 8);
}

// ===========================================================================
// the old path
// ===========================================================================

/// With the hook off, the gate is what it was before the hook: each positive cell is Unknown at
/// step (4), its O4 detail ay's own (`value(return) did not conclude: …`) with no rewrite
/// named, after the budget ran out. Split by rung so the two halves run side by side.
fn old_path(label: &str, ir: &str) {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(ir, triple, opt);
            let r = run(&fx, Off::Hook);
            let c = r.report.certificate("rung").expect("certificate");
            let o4 = &c.obligations.o4_return.detail;
            assert!(
                matches!(c.verdict, OutputVerdict::Unknown { .. })
                    && o4.starts_with("value(return) did not conclude")
                    && !o4.contains("CONSTDIV"),
                "{label} {triple} {opt:?}: with the hook off: {:?} {o4}",
                c.verdict
            );
            assert!(
                r.calls.iter().all(|(_, _, n)| n.is_none()) && !r.calls.is_empty(),
                "{label} {triple} {opt:?}: the hook was not consulted, or rewrote while off"
            );
            assert_eq!(
                StopCause::from_reason(o4),
                Some(StopCause::Effort),
                "{label} {triple} {opt:?}: Unknown, but not on its effort count: {o4}"
            );
            assert!(r.routes.is_empty(), "{label}: step (5) was reached: {:?}", r.routes);
            seen.push(format!("{label} {triple} {opt:?}: Unknown in {} ms: {o4}", r.ms));
        }
    }
    println!("{seen:#?}");
}

#[test]
fn without_the_hook_the_old_path_is_taken_s20() {
    old_path("s20", S20_IR);
}

#[test]
fn without_the_hook_the_old_path_is_taken_div3() {
    old_path("x/3", &d3_ir());
}

// ===========================================================================
// r01
// ===========================================================================

/// r01 (`x / 3 + (x ^ 0x55) * 2`, then `<< 3`, `| x & 7`, `- (x >> 1)`, `+ 11`) at O0 and O2 on
/// both triples: its division is rewritten, and its value item gets past step (4); measured and
/// pinned as observed: Proven [VALIDATED] on the rewrite, NOT kernel-proved. Step (5) calls the
/// branch routes once and all three decline: the branch split's walk refuses the 128-bit product,
/// no divisor has a variable, and the CONSTDIV route's own walk refuses `value(return)`'s shift
/// amounts, the producer's `(sext i32 3 to u64) & 63 & 63` for `<< 3` and a non-literal amount for
/// `>> 1` (`const_div.rs`'s walk is the branch walk before s10: no sign-extension arm, `lshr` by a
/// literal only; `const_div/tests.rs` `r01_declines_at_the_shift_amounts_only` pins that these are
/// the only refusals).
#[test]
fn r01_gets_past_step_4_on_the_rewrite() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(R01_IR, triple, opt);
            assert_magic_bytes(&fx);
            let r = run(&fx, Off::Nothing);
            let what = format!("r01 {triple} {opt:?}");
            let c = r.report.certificate("rung").expect("certificate");
            seen.push(format!(
                "{what}: {} {:?} in {} ms: {}",
                c.grade, c.verdict, r.ms, c.obligations.o4_return.detail
            ));
            assert_rewrite_validated(&fx, &r, &what, &[MAGIC_NOADD]);
            assert!(r.ms < POSITIVE_BOUND_MS, "{what}: the gate took {} ms", r.ms);
        }
    }
    println!("{seen:#?}");
}

// ===========================================================================
// mutants
// ===========================================================================

/// MUTANTS, each Refuted on `value(return)` at step (4) (step (5)'s routes never called), each
/// with its unmutated twin kernel-[PROVED] in the same test:
/// - the magic constant's low half-word plus 2 (`movz`): outside the Granlund-Montgomery band,
///   so not rewritten (asserted), and ay refutes the old miter (a counterexample exists only
///   for large `x`);
/// - the final shift one more (`lsr #1` -> `#2` for x / 3, `#2` -> `#3` for s20): rewritten
///   (asserted; the bytes are then a correct magic for another divisor, 6 or 14), and Refuted
///   on the rewritten item;
/// - the IR's divisor one less and one more than the bytes' (3 -> 2, 4; 7 -> 6, 8): rewritten
///   (asserted) and Refuted on the rewritten item.
#[test]
fn constdiv_mutants_are_never_proven() {
    let mut seen = Vec::new();
    for (label, ir, want) in positives() {
        let s20 = label == "s20";
        let (mk_lo, shift, d) = if s20 { (0x2493, 2, 7) } else { (0xaaab, 1, 3) };
        for triple in BOTH {
            for opt in OPTS {
                let fx = producer_fixture(&ir, triple, opt);
                let twin = run(&fx, Off::Nothing);
                assert_kernel_proved(&fx, &twin, label, &want, label_of(label, opt));
                let cell = format!("{label} {triple} {opt:?}");
                let (at, w) = the_one(&fx, "the magic movz", |w| is_movz64(w, mk_lo));
                let m = fx.patched(|o| patch_word(o, at, with_imm16(w, mk_lo + 2)));
                seen.push(assert_refuted(&m, &format!("{cell} magic + 2"), false));
                let (at, w) = the_one(&fx, "the final lsr", |w| is_lsr_imm(w, shift));
                let m = fx.patched(|o| patch_word(o, at, with_immr(w, shift + 1)));
                seen.push(assert_refuted(
                    &m,
                    &format!("{cell} lsr #{shift} -> #{}", shift + 1),
                    true,
                ));
                for e in [d - 1, d + 1] {
                    let wrong =
                        replace_once(&ir, &format!("const u64 {d}"), &format!("const u64 {e}"));
                    seen.push(assert_refuted(
                        &against(&fx, &wrong),
                        &format!("{cell} IR / {e}"),
                        true,
                    ));
                }
            }
        }
    }
    println!("{seen:#?}");
    assert_eq!(seen.len(), 2 * 2 * 2 * 4);
}
