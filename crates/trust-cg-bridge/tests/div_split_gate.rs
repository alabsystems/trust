// tests/div_split_gate.rs — the call-event gate over ladder rung s21_div_var
// (`if x != 0 { 1000 / x } else { 0 }` over `u64`), proved through the guarded symbolic division
// split (`verify_output_instantiate/div_split.rs`, DECISION_QUEUE DIV-SPLIT-1): one kernel-checked
// deep atom case split against the branching reflection of the whole conjunction, tried by the
// step-(5) branch routes (`verify_output_instantiate/branch_dispatch.rs`) only after the branch
// split declines.
//
// Before the route s21 was [VALIDATED] (`AyValidated`) at O0 and O2 on both aarch64 triples, the
// branch split called once and declining at its walk ("a side is outside the width walk": the
// divisor `x` has a variable), calls `[false]` (measured 2026-11-15 by the design probe,
// <home>/trust-cp-logs/s3-design/run1.log to run4.log).
//
// POSITIVE: s21 at O0 and O2, both triples, kernel-[PROVED] as `KernelInstantiated` with the
// DIV-SPLIT-1 label, calls `[true]`. The fixture configuration is `branch_split_gate.rs`'s:
// trust-cg compiles the producer IR with the unsited `assert` folded out (as the compiler lane
// folds it), and the gate reads the producer IR as written. The IR is the producer's own
// `-Ztrust-dump=ir:` text (stage-1 trustc 80c41bb667, `-Copt-level=2`, identical at 0), with the
// `#loc` comments and the `target` line dropped.
//
// PRECISION PIN, the raw-udiv all-ones twin: bytes that return all-ones at x = 0 and `1000 / x`
// elsewhere (trust-cg's compile of `if x != 0 { 1000 / x } else { u64::MAX }`) read against a
// spec that divides with no guard and no check (`udiv 1000, x`). They agree everywhere under
// SMT-LIB `bvudiv` (all-ones at a zero divisor), and trust-ir makes an unsigned division by zero
// undefined behaviour (`ub("unsigned division by zero")`), so any value there refines it: a
// [PROVED] grade would be sound. Measured 2026-11-15: it stays [VALIDATED] (`AyValidated`), the
// routes called once and declining, both at the walk (`TRUST_GATE_TRACE=1`, all four cells: the
// machine writes its all-ones as `BvOr(0, BvNot(0))`, and `BvNot` is outside the frozen walk).
// Past the walk the unguarded spec division would still be stuck on `bvIsZero` in the x = 0
// leaf (unit mutant 7's shape). Flip this pin if a route proves it.
// LIVE DIVISION BY ZERO: the same bytes against a spec that keeps the division's check
// (`assert x != 0`) are Unknown at O4 ("the unsited check … can fail on a reached path"): the
// route is never reached.
//
// MUTANTS (Refuted beside the unmutated twin): bytes `cbnz`/`b.ne` flipped, `movz #1000` made
// `#1001`, the `udiv` operands swapped, `udiv` made `sdiv`; IR `icmp ne` made `eq`, the `udiv`
// operands swapped. ay refutes each at step (4), before the step-(5) routes run (each asserts the
// recorder empty): harness controls. The KERNEL's refusals of wrong division splits are the route's unit tests with the
// Rust checks bypassed (`div_split/tests.rs` `mutants_are_refused_by_the_kernel`).
//
// UNSIGNED REMAINDER BY A VARIABLE (PKG-C5c-S3c, the `rem_var_` tests): `if y != 0 { x % y } else
// { 0 }` over `u64`. No `BvURem` reaches the gate: the spec states `x % y` as the AArch64 lowering
// `x - ite(y == 0, 0, x / y) * y` (`verify_output::eval_binop`'s `Rem` arm) and the machine's
// `udiv` + `msub` lift to the same tree, so DIV-SPLIT-1 proves it unchanged (its pre-filter fires
// on the quotient's `BvUDiv(X0, X1)`). Measured 2026-11-15: kernel-[PROVED] at O0 and O2 on both
// triples, calls `[true]`, the branch split declining at its walk (`TRUST_GATE_TRACE=1`). Its
// byte and IR mutants are not Proven, their verdicts pinned as measured; the raw twin and the live
// remainder by zero are pinned beside them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Run: `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks --test
// div_split_gate`.
#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::{CerInput, CerReport, verify_compiled_module};
use trust_cg_bridge::compiled_object::ObjectRefusal;
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_instantiate::record_branch_split_calls;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::Module;

/// What every division-split label ends with (`div_split::LABEL_TAIL`).
const TAIL: &str = "kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";
/// The arm selection every case split uses.
const ITE_CONG: &str = "Trust.BVB.ite_cong";

const OPTS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

fn folded(body: &str) -> String {
    body.lines().filter(|l| !l.trim_start().starts_with("assert ")).collect::<Vec<_>>().join("\n")
}

fn parse(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

/// Bytes from the folded `machine` module, the producer IR `spec` as written.
fn fixture_of(machine: &str, spec: &str, triple: &str, opt: OptLevel) -> Fixture {
    let license = fixture_license().with_recognized_authority("trust-direct-lane-structural");
    let object = compile_under(&parse(&folded(machine)), triple, opt, license)
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"));
    Fixture::with_object(targeted(&parse(spec), triple), object, triple)
}

fn producer_fixture(text: &str, triple: &str, opt: OptLevel) -> Fixture {
    fixture_of(text, text, triple, opt)
}

fn against(fx: &Fixture, text: &str) -> Fixture {
    Fixture::with_object(targeted(&parse(text), &fx.triple), fx.object.clone(), &fx.triple)
}

fn verify_recording(fx: &Fixture) -> (Result<CerReport, ObjectRefusal>, Vec<bool>) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                record_branch_split_calls(|| {
                    verify_compiled_module(&CerInput {
                        m_cg: &fx.m_cg,
                        producers: &fx.producers,
                        bodies: &fx.bodies,
                        placements: &fx.placements,
                        object: &fx.object,
                        relocation_model: fx.model,
                    })
                })
            })
            .expect("spawn the gate thread")
            .join()
            .expect("the gate thread panicked")
    })
}

#[track_caller]
fn report_recording(fx: &Fixture) -> (CerReport, Vec<bool>) {
    let (report, calls) = verify_recording(fx);
    let report = report.unwrap_or_else(|e| {
        panic!("{}: object refused: {e}\n{}", fx.triple, disassemble(&fx.object))
    });
    (report, calls)
}

#[track_caller]
fn replace_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "`{from}` is not unique in the IR");
    text.replacen(from, to, 1)
}

/// The label of `rung`'s division-split proof, or a panic naming what it was instead.
#[track_caller]
fn div_label(fx: &Fixture, report: &CerReport) -> String {
    let c = report.certificate("rung").expect("certificate");
    assert!(
        c.is_kernel_proved(),
        "{}: `rung` is not kernel-[PROVED]\n{}\n{}",
        fx.triple,
        explain(report),
        disassemble(&fx.object)
    );
    match &c.verdict {
        OutputVerdict::Proven {
            evidence: ProvenEvidence::KernelInstantiated { theorem, original: None },
        } if theorem.ends_with(TAIL)
            && theorem.contains(ITE_CONG)
            && !theorem.contains("BRANCH-SPLIT-1") =>
        {
            theorem.clone()
        }
        other => panic!(
            "{}: `rung` is not a division-split instantiation: {other:?}\n{}",
            fx.triple,
            explain(report)
        ),
    }
}

/// Refuted, with the step-(5) branch routes never called (ay refutes at step (4)).
#[track_caller]
fn assert_refuted(fx: &Fixture, what: &str) -> String {
    let (report, calls) = verify_recording(fx);
    let report = report.unwrap_or_else(|refusal| {
        panic!("{}: MUTANT `{what}`: object refused: {refusal}", fx.triple)
    });
    let c = report.certificate("rung").expect("certificate");
    assert!(
        matches!(c.verdict, OutputVerdict::Refuted { .. }) && !c.is_kernel_proved(),
        "{}: MUTANT `{what}` is not Refuted\n{}\n{}",
        fx.triple,
        explain(&report),
        disassemble(&fx.object)
    );
    assert!(calls.is_empty(), "{}: MUTANT `{what}`: the routes were called: {calls:?}", fx.triple);
    format!("{}: {:?}", c.grade, c.verdict)
}

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

/// `movz` of the 16-bit immediate `imm` (either register width, no shift).
fn is_movz(w: u32, imm: u32) -> bool {
    w & 0x7fe0_0000 == 0x5280_0000 && (w >> 5) & 0xffff == imm
}

/// `cbz` / `cbnz` (either width).
fn is_cb(w: u32) -> bool {
    w & 0x7e00_0000 == 0x3400_0000
}

/// `b.cond`.
fn is_bcond(w: u32) -> bool {
    w & 0xff00_0010 == 0x5400_0000
}

/// 64-bit `udiv`.
fn is_udiv(w: u32) -> bool {
    w & 0xffe0_fc00 == 0x9ac0_0800
}

/// The branch on `x != 0` with its sense flipped: `cbnz` <-> `cbz`, or a `b.cond` with the
/// condition's low bit flipped (`ne` <-> `eq`).
fn flipped_branch(w: u32) -> u32 {
    if is_cb(w) { w ^ (1 << 24) } else { w ^ 1 }
}

// ===========================================================================
// the rung
// ===========================================================================

/// Ladder rung s21 (`tests/trust-f1-ladder/micro/s21_div_var.rs`): the producer's own
/// `-Ztrust-dump=ir:` text (stage-1 trustc 80c41bb667, `-Copt-level=2`; identical at `0`), the
/// `#loc` comments and the `target` line dropped so `targeted` stamps each triple.
const S21_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s21_div_var.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %2 = const u64 0
    %3 = icmp ne u64 %0, %2
    condbr %3, bb1, bb2
bb1:
    %4 = const u64 1000
    %5 = const u64 0
    %6 = icmp ne u64 %0, %5
    assert %6, div_by_zero  ; #proof: div_nonzero
    %7 = udiv u64 %4, %0
    br bb3(%7)
bb2:
    %8 = const u64 0
    br bb3(%8)
bb3(%1: u64):
    ret %1
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L1C65 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C65#div_by_zero#o0" range 0 1 65 1 73 site f0/bb1#3
"#;

/// The machine of the all-ones twins: s21 with `u64::MAX` for the `else` arm.
fn ones_ir() -> String {
    replace_once(S21_IR, "%8 = const u64 0", "%8 = const u64 18446744073709551615")
}

/// `1000 / x` with no guard and no check: trust-ir makes `udiv` by zero undefined behaviour.
const RAW_UDIV_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s21_div_var.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %2 = const u64 1000
    %3 = udiv u64 %2, %0
    ret %3
}
"#;

/// `1000 / x` with the division's check kept as the lowering records it, and no guard: a live
/// division by zero at x = 0.
const ASSERTED_UDIV_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s21_div_var.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %2 = const u64 1000
    %3 = const u64 0
    %4 = icmp ne u64 %0, %3
    assert %4, div_by_zero  ; #proof: div_nonzero
    %5 = udiv u64 %2, %0
    ret %5
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L1C65 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C65#div_by_zero#o0" range 0 1 65 1 73 site f0/bb0#3
"#;

// ===========================================================================
// positive
// ===========================================================================

/// POSITIVE: s21 at O0 and O2, on both triples, is kernel-[PROVED] by the division split, its
/// route called once (`[true]`). FAILS without the route (or without the dispatch's fallback):
/// [VALIDATED] with calls `[false]`.
#[test]
fn s21_div_var_is_kernel_proved_by_the_div_split() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S21_IR, triple, opt);
            let t = std::time::Instant::now();
            let (report, calls) = report_recording(&fx);
            let ms = t.elapsed().as_millis();
            let label = div_label(&fx, &report);
            assert_eq!(calls, [true], "{triple} {opt:?}: the route's calls");
            let want = if opt == OptLevel::O0 { S21_O0_LABEL } else { S21_O2_LABEL };
            assert_eq!(label, want, "{triple} {opt:?}");
            seen.push(format!("{triple} {opt:?}: {ms} ms (whole gate): {label}"));
        }
    }
    println!("{seen:#?}");
}

/// The measured labels (2026-11-15, both triples).
const S21_O2_LABEL: &str = "Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+Trust.BVB.ite_cong+\
Trust.BVB.ite_false+Trust.BVB.ite_true+kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";
const S21_O0_LABEL: &str = "Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+Clean.BVC.bvf_sub_cong+\
Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+Trust.BVB.sub_zero+kernel atom case split, \
guarded symbolic division (DIV-SPLIT-1)";

// ===========================================================================
// the all-ones twins
// ===========================================================================

/// PRECISION PIN: the all-ones bytes against the raw `udiv 1000, x` (no guard, no check). Under
/// SMT-LIB `bvudiv` the two agree at every x (all-ones at 0), and trust-ir makes `udiv` by zero
/// undefined behaviour, so the bytes refine the spec: a [PROVED] grade here would not be a false
/// accept. Pinned as measured: Proven [VALIDATED], calls `[false]` (both routes decline at the
/// walk: the machine's all-ones is `BvNot(0)`).
#[test]
fn raw_udiv_all_ones_twin() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = fixture_of(&ones_ir(), RAW_UDIV_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            seen.push(format!("{triple} {opt:?}: {} {:?} calls {calls:?}", c.grade, c.verdict));
            assert!(c.verdict.is_proven(), "{triple} {opt:?}\n{}", explain(&report));
            raw_twin_expectation(&fx, &report, &calls);
        }
    }
    println!("{seen:#?}");
}

/// LIVE DIVISION BY ZERO: the all-ones bytes against `1000 / x` with its check kept: Unknown at O4
/// (the check can fail on a reached path), never Proven; the route is never called.
#[test]
fn asserted_live_division_by_zero_is_unknown_at_o4() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = fixture_of(&ones_ir(), ASSERTED_UDIV_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            match &c.verdict {
                OutputVerdict::Unknown { reason } if reason.contains("O4") => {}
                other => {
                    panic!("{triple} {opt:?}: not Unknown at O4: {other:?}\n{}", explain(&report))
                }
            }
            assert!(calls.is_empty(), "{triple} {opt:?}: the route was called: {calls:?}");
        }
    }
}

// ===========================================================================
// mutants
// ===========================================================================

/// MUTANTS of s21 at O0 and O2 on both triples, each Refuted after the unmutated twin is
/// kernel-[PROVED] by the division split. Bytes: the branch on `x != 0` flipped (`cbnz`/`cbz` at
/// O2, `b.ne`/`b.eq` at O0); `movz #1000` made `#1001`; the `udiv` operands swapped; `udiv` made
/// `sdiv`. IR, against the original bytes: `icmp ne` made `eq`; the `udiv` operands swapped.
#[test]
fn s21_mutants_are_refuted() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S21_IR, triple, opt);
            div_label(&fx, &fx.report());
            let mut refuted = |m: &Fixture, what: &str| {
                let got = assert_refuted(m, &format!("s21 {opt:?} {what}"));
                seen.push(format!("s21 {triple} {opt:?} {what}: {got}"));
            };
            let (at, w) = the_one(&fx, "the branch on x != 0", |w| is_cb(w) || is_bcond(w));
            refuted(&fx.patched(|o| patch_word(o, at, flipped_branch(w))), "branch flipped");
            let (at, w) = the_one(&fx, "movz #1000", |w| is_movz(w, 1000));
            let m1001 = (w & !(0xffff << 5)) | (1001 << 5);
            refuted(&fx.patched(|o| patch_word(o, at, m1001)), "movz #1000 -> #1001");
            let (at, w) = the_one(&fx, "udiv", is_udiv);
            let (rn, rm) = ((w >> 5) & 31, (w >> 16) & 31);
            let swapped = (w & !((31 << 5) | (31 << 16))) | (rm << 5) | (rn << 16);
            refuted(&fx.patched(|o| patch_word(o, at, swapped)), "udiv operands swapped");
            refuted(&fx.patched(|o| patch_word(o, at, w | (1 << 10))), "udiv -> sdiv");
            let eqm = replace_once(S21_IR, "%3 = icmp ne", "%3 = icmp eq");
            refuted(&against(&fx, &eqm), "IR icmp ne -> eq");
            let swap = replace_once(S21_IR, "udiv u64 %4, %0", "udiv u64 %0, %4");
            refuted(&against(&fx, &swap), "IR udiv operands swapped");
        }
    }
    assert_eq!(seen.len(), 2 * 2 * 6, "{seen:#?}");
    println!("{seen:#?}");
}

/// The raw twin as measured (2026-11-15, all four cells): Proven [VALIDATED] (`AyValidated`), the
/// step-(5) branch routes called once and declining (`[false]`).
fn raw_twin_expectation(fx: &Fixture, report: &CerReport, calls: &[bool]) {
    match &report.certificate("rung").expect("certificate").verdict {
        OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated } => {}
        other => panic!(
            "{}: the raw all-ones twin moved (flip this pin if a route now proves it): {other:?}\n{}",
            fx.triple,
            explain(report)
        ),
    }
    assert_eq!(calls, [false], "{}: the raw twin's route calls", fx.triple);
}

// ===========================================================================
// PKG-C5c-S3c: unsigned remainder by a variable (RemByZero)
// ===========================================================================

/// 64-bit `msub` (`madd` with o0 = 1): `Rd = Ra - Rn * Rm`.
fn is_msub(w: u32) -> bool {
    w & 0xffe0_8000 == 0x9b00_8000
}

/// `w` with the 5-bit register field at `at` set to `r`.
fn with_field(w: u32, at: u32, r: u32) -> u32 {
    (w & !(31 << at)) | (r << at)
}

/// `if y != 0 { x % y } else { 0 }` over `u64` (`rem_var.rs`, `#[no_mangle] pub extern "C" fn
/// rung(x: u64, y: u64) -> u64`): the producer's own `-Ztrust-dump=ir:` text (stage-1 trustc
/// 80c41bb667, `-Ztrust-dump=ir: -Ztrust-ir-lower=on -Ztrust-verify=off -Coverflow-checks=off`,
/// `-Copt-level=2`; byte-identical at `0`; dumped 2026-11-15), the `#loc` comments and the
/// `target` line dropped so `targeted` stamps each triple. The spec evaluates `urem` as the
/// AArch64 lowering `x - ite(y == 0, 0, x / y) * y` (`verify_output::eval_binop`'s `Rem` arm),
/// and trust-cg lowers it to `udiv` then `msub`, so no `BvURem` reaches the gate: DIV-SPLIT-1
/// admits the conjunction as written (its pre-filter fires on the quotient's `BvUDiv(X0, X1)`).
const REM_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "rem_var.rs"

functy.0 = (u64, u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: u64, %1: u64):
    %3 = const u64 0
    %4 = icmp ne u64 %1, %3
    condbr %4, bb1, bb2
bb1:
    %5 = const u64 0
    %6 = icmp ne u64 %1, %5
    assert %6, rem_by_zero  ; #proof: div_nonzero
    %7 = urem u64 %0, %1
    br bb3(%7)
bb2:
    %8 = const u64 0
    br bb3(%8)
bb3(%2: u64):
    ret %2
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L3C16 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#rem_by_zero#o0" range 0 3 16 3 21 site f0/bb1#2
"#;

/// `x % y` with no guard and no check: trust-ir makes `urem` by zero undefined behaviour.
/// Hand-shaped in the producer's form, not a dump.
const RAW_UREM_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "rem_var.rs"

functy.0 = (u64, u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: u64, %1: u64):
    %2 = urem u64 %0, %1
    ret %2
}
"#;

/// `x % y` with the remainder's check kept as the lowering records it, and no guard: a live
/// remainder by zero at y = 0. Hand-shaped in the producer's form, not a dump.
const ASSERTED_UREM_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "rem_var.rs"

functy.0 = (u64, u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: u64, %1: u64):
    %2 = const u64 0
    %3 = icmp ne u64 %1, %2
    assert %3, rem_by_zero  ; #proof: div_nonzero
    %4 = urem u64 %0, %1
    ret %4
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L3C16 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#rem_by_zero#o0" range 0 3 16 3 21 site f0/bb0#2
"#;

/// The measured labels (2026-11-15, both triples): the remainder's `msub` adds `bvf_mul_cong` and
/// `bvf_sub_cong` to s21's set (at O2 too); O0's `subs` guard adds `sub_zero`.
const REM_O2_LABEL: &str = "Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+kernel atom case \
split, guarded symbolic division (DIV-SPLIT-1)";
const REM_O0_LABEL: &str = "Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+\
Trust.BVB.sub_zero+kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";

/// POSITIVE (PKG-C5c-S3c exit): `if y != 0 { x % y } else { 0 }` at O0 and O2, on both triples,
/// is kernel-[PROVED] by the division split unchanged, its route called once (`[true]`), with the
/// measured label (which cites the `msub`'s multiply and subtract congruences), and its object
/// lowers the remainder as exactly one `udiv` and one `msub`.
#[test]
fn rem_var_is_kernel_proved_by_the_div_split() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(REM_IR, triple, opt);
            the_one(&fx, "udiv", is_udiv);
            the_one(&fx, "msub", is_msub);
            let t = std::time::Instant::now();
            let (report, calls) = report_recording(&fx);
            let ms = t.elapsed().as_millis();
            let label = div_label(&fx, &report);
            assert_eq!(calls, [true], "{triple} {opt:?}: the route's calls");
            let want = if opt == OptLevel::O0 { REM_O0_LABEL } else { REM_O2_LABEL };
            assert_eq!(label, want, "{triple} {opt:?}");
            for t in ["Clean.BVC.bvf_mul_cong", "Clean.BVC.bvf_sub_cong"] {
                assert!(label.contains(t), "{triple} {opt:?}: the label does not cite {t}");
            }
            seen.push(format!("{triple} {opt:?}: {ms} ms (whole gate): {label}"));
        }
    }
    println!("{seen:#?}");
}

/// Not proved, the step-(5) routes never answering `true`; returns the verdict for the pin.
#[track_caller]
fn assert_not_proved(fx: &Fixture, what: &str) -> (String, Vec<bool>) {
    let (report, calls) = verify_recording(fx);
    let report = report.unwrap_or_else(|refusal| {
        panic!("{}: MUTANT `{what}`: object refused: {refusal}", fx.triple)
    });
    let c = report.certificate("rung").expect("certificate");
    assert!(
        !c.verdict.is_proven() && !c.is_kernel_proved(),
        "{}: MUTANT `{what}` is proved\n{}\n{}",
        fx.triple,
        explain(&report),
        disassemble(&fx.object)
    );
    assert!(!calls.contains(&true), "{}: MUTANT `{what}`: a route proved it: {calls:?}", fx.triple);
    let kind = match &c.verdict {
        OutputVerdict::Refuted { .. } => "Refuted",
        OutputVerdict::Unknown { .. } => "Unknown",
        other => panic!("{}: MUTANT `{what}`: {other:?}", fx.triple),
    };
    (kind.to_string(), calls)
}

/// MUTANTS of the remainder at O0 and O2 on both triples, each not Proven (and no route answering
/// `true`) after the unmutated twin is kernel-[PROVED] by the division split; then each verdict is
/// pinned as measured ([`REM_MUTANT_PIN`]). Bytes: the branch on `y != 0` flipped; `msub` made
/// `madd`; `msub`'s Ra set to its Rm (`y - q*y`); its Rm set to its Ra (`x - q*x`); its Ra and Rn
/// swapped (`q - x*y`); the `udiv` operands swapped; `udiv` made `sdiv`. IR, against the original
/// bytes: the guard's `icmp ne` made `eq`; `urem` made `udiv`; `urem` made `srem`; the `urem`
/// operands swapped.
#[test]
fn rem_var_mutants_are_not_proved() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(REM_IR, triple, opt);
            div_label(&fx, &fx.report());
            let mut not_proved = |m: &Fixture, what: &str| {
                let (kind, calls) = assert_not_proved(m, &format!("rem {opt:?} {what}"));
                seen.push((triple, opt, what.to_string(), kind, calls));
            };
            let (at, w) = the_one(&fx, "the branch on y != 0", |w| is_cb(w) || is_bcond(w));
            not_proved(&fx.patched(|o| patch_word(o, at, flipped_branch(w))), "branch flipped");
            let (at, w) = the_one(&fx, "msub", is_msub);
            let (rn, ra, rm) = ((w >> 5) & 31, (w >> 10) & 31, (w >> 16) & 31);
            not_proved(&fx.patched(|o| patch_word(o, at, w & !(1 << 15))), "msub -> madd");
            not_proved(&fx.patched(|o| patch_word(o, at, with_field(w, 10, rm))), "msub Ra := Rm");
            not_proved(&fx.patched(|o| patch_word(o, at, with_field(w, 16, ra))), "msub Rm := Ra");
            let swapped = with_field(with_field(w, 10, rn), 5, ra);
            not_proved(&fx.patched(|o| patch_word(o, at, swapped)), "msub Ra <-> Rn");
            let (at, w) = the_one(&fx, "udiv", is_udiv);
            let (rn, rm) = ((w >> 5) & 31, (w >> 16) & 31);
            let swapped = with_field(with_field(w, 5, rm), 16, rn);
            not_proved(&fx.patched(|o| patch_word(o, at, swapped)), "udiv operands swapped");
            not_proved(&fx.patched(|o| patch_word(o, at, w | (1 << 10))), "udiv -> sdiv");
            let ir = |from: &str, to: &str| against(&fx, &replace_once(REM_IR, from, to));
            not_proved(&ir("%4 = icmp ne", "%4 = icmp eq"), "IR icmp ne -> eq");
            not_proved(&ir("urem u64 %0, %1", "udiv u64 %0, %1"), "IR urem -> udiv");
            not_proved(&ir("urem u64 %0, %1", "srem u64 %0, %1"), "IR urem -> srem");
            not_proved(&ir("urem u64 %0, %1", "urem u64 %1, %0"), "IR urem operands swapped");
        }
    }
    assert_eq!(seen.len(), 2 * 2 * 11, "{seen:#?}");
    let got: Vec<String> = seen
        .iter()
        .map(|(t, o, what, kind, calls)| format!("{t} {o:?} {what}: {kind} calls {calls:?}"))
        .collect();
    println!("{got:#?}");
    for (t, o, what, kind, calls) in &seen {
        let pinned = REM_MUTANT_PIN
            .iter()
            .find(|(w, _)| w == what)
            .unwrap_or_else(|| panic!("no pin for `{what}`"))
            .1;
        assert_eq!(format!("{kind} calls {calls:?}"), pinned, "{t} {o:?} {what}: the pin moved");
    }
}

/// The remainder mutants' measured verdicts (2026-11-15, all four cells alike): each Refuted by ay
/// at step (4), the step-(5) routes never called (the s21 precedent).
const REM_MUTANT_PIN: [(&str, &str); 11] = [
    ("branch flipped", "Refuted calls []"),
    ("msub -> madd", "Refuted calls []"),
    ("msub Ra := Rm", "Refuted calls []"),
    ("msub Rm := Ra", "Refuted calls []"),
    ("msub Ra <-> Rn", "Refuted calls []"),
    ("udiv operands swapped", "Refuted calls []"),
    ("udiv -> sdiv", "Refuted calls []"),
    ("IR icmp ne -> eq", "Refuted calls []"),
    ("IR urem -> udiv", "Refuted calls []"),
    ("IR urem -> srem", "Refuted calls []"),
    ("IR urem operands swapped", "Refuted calls []"),
];

/// PRECISION PIN, the raw remainder twin: bytes of an unguarded `x % y` (`udiv` then `msub`)
/// against the same spec (no guard, no check). Both sides are the composite
/// `x - ite(y == 0, 0, x / y) * y` with no top-level `Ite`, so the split closes by `Eq.refl`
/// (`div_split.rs` `split`, `rl == rr`); sound either way (both sides are SMT `bvurem`, and
/// trust-ir `urem` by zero is undefined behaviour). Pinned as measured: kernel-[PROVED] by the
/// division split at O0 and O2 on both triples.
#[test]
fn rem_var_raw_twin() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = fixture_of(RAW_UREM_IR, RAW_UREM_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            seen.push(format!("{triple} {opt:?}: {} {:?} calls {calls:?}", c.grade, c.verdict));
            assert!(c.verdict.is_proven(), "{triple} {opt:?}\n{}", explain(&report));
            raw_urem_expectation(&fx, &report, &calls, opt);
        }
    }
    println!("{seen:#?}");
}

/// The raw remainder twin as measured (2026-11-15, all four cells): kernel-[PROVED] by the
/// division split, its route called once (`[true]`), the label citing `ite_cong` (the quotient
/// `Ite`'s congruence proof inside the core: no split happens).
fn raw_urem_expectation(fx: &Fixture, report: &CerReport, calls: &[bool], opt: OptLevel) {
    let label = div_label(fx, report);
    assert_eq!(calls, [true], "{}: the raw remainder twin's route calls", fx.triple);
    let want = if opt == OptLevel::O0 { RAW_UREM_O0_LABEL } else { RAW_UREM_O2_LABEL };
    assert_eq!(label, want, "{} {opt:?}: the raw remainder twin's label", fx.triple);
}

/// The raw remainder twin's measured labels (2026-11-15, both triples).
const RAW_UREM_O0_LABEL: &str = "Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+\
Clean.BVC.bvf_or_zero_id+Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+kernel atom case split, guarded \
symbolic division (DIV-SPLIT-1)";
const RAW_UREM_O2_LABEL: &str = "Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+\
kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";

/// LIVE REMAINDER BY ZERO: the raw remainder bytes against `x % y` with its check kept: Unknown at
/// O4 (the check can fail on a reached path), never Proven; the route is never called.
#[test]
fn rem_var_live_by_zero_is_unknown_at_o4() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = fixture_of(RAW_UREM_IR, ASSERTED_UREM_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            match &c.verdict {
                OutputVerdict::Unknown { reason } if reason.contains("O4") => {}
                other => {
                    panic!("{triple} {opt:?}: not Unknown at O4: {other:?}\n{}", explain(&report))
                }
            }
            assert!(calls.is_empty(), "{triple} {opt:?}: the route was called: {calls:?}");
        }
    }
}
