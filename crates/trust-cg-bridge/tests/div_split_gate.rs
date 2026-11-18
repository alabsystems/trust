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
// routes called once and declining (`TRUST_GATE_TRACE=1`, all four cells): the branch split at its
// walk (the machine writes its all-ones as `BvOr(0, BvNot(0))`, and `BvNot` is outside the frozen
// walk); since PKG-C5c-S3d the division split's walk admits a complemented literal (its `BvXor`
// view), so the division split now declines at a leaf ("the arms of a case differ"): the
// unguarded spec division is stuck on `bvIsZero ⟦x⟧` in the x = 0 leaf (unit mutant 7's shape;
// PKG-C5c-S3e). Flip this pin if a route proves it.
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
// SIGNED DIVISION AND REMAINDER: the complete original S3d inputs,
// checked overflow/zero twins, live conjunctions and mutation denominator stay.
// New Rust-only signed/complement goal construction has been withdrawn pending
// an original-operation semantic relation checked in Lean. These objects must
// not obtain kernel evidence or ship under StrictProvenOnly.
//
// THE SITED CONFIGURATION (PKG-C5c-S3b, the `s21_sited_` tests): the proving arms
// carry the copied guard/divisor in the retained conjunction's unit proof. The
// Rust-only S2a tail allowance is withdrawn, so the actual O0 object and both
// byte mutations retain the complete O1 Unknown record and cannot ship strict.
// These cells check refusal before proof routing; they do not assert a semantic
// refutation of mutations hidden behind an unlicensed address materialization.
// Tail-free O2 positives and raw-conjunction kernel controls remain separate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Run: `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks --test
// div_split_gate`.
#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::{CerInput, CerReport, Grade, verify_compiled_module};
use trust_cg_bridge::compiled_object::ObjectRefusal;
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_instantiate::{
    RecordedConjunction, record_branch_split_calls, record_branch_split_conjunctions,
};
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
    let (report, calls) = verify_recording_conjunctions(fx);
    (report, calls.into_iter().map(|(proved, _)| proved).collect())
}

/// [`verify_recording`] with the items of each call to the route, as the gate passed them.
fn verify_recording_conjunctions(
    fx: &Fixture,
) -> (Result<CerReport, ObjectRefusal>, Vec<RecordedConjunction>) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                record_branch_split_conjunctions(|| {
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
/// accept. Pinned as measured: Proven [VALIDATED], calls `[false]`: the branch split declines at
/// its walk (the machine's all-ones is `BvNot(0)`); the division split, whose walk admits a
/// complemented literal since PKG-C5c-S3d, declines at a leaf ("the arms of a case differ": the
/// unguarded division is stuck on `bvIsZero` at x = 0, PKG-C5c-S3e).
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

// ===========================================================================
// PKG-C5c-S3b: the sited configuration (a divisor and its guard read through a copy)
// ===========================================================================

/// `orr Xd, xzr, Xm` (the 64-bit `mov Xd, Xm`): `(d, m)`.
fn mov_reg(w: u32) -> Option<(u32, u32)> {
    (w & 0xffe0_ffe0 == 0xaa00_03e0).then_some((w & 31, (w >> 16) & 31))
}

/// The `udiv` of `rung`, and the last `mov x<Rm>, x0` before it (the copy its divisor reads).
#[track_caller]
fn udiv_and_copy(fx: &Fixture) -> ((u64, u32), (u64, u32)) {
    let (at, w) = the_one(fx, "udiv", is_udiv);
    let rm = (w >> 16) & 31;
    let copy = function_words(&fx.object, "rung")
        .into_iter()
        .filter(|(o, c)| *o < at && mov_reg(*c) == Some((rm, 0)))
        .last()
        .unwrap_or_else(|| {
            panic!(
                "{}: no `mov x{rm}, x0` before the `udiv`\n{}",
                fx.triple,
                disassemble(&fx.object)
            )
        });
    ((at, w), copy)
}

/// The entire retained address pair must remain Unknown until a Lean-checked
/// bridge licenses its semantics. A proof of a separate conjunction cannot
/// promote this machine-input refusal.
#[track_caller]
fn assert_sited_o1_unknown(fx: &Fixture, report: &CerReport, calls: &[bool]) {
    use trust_cg_bridge::compiled_object::{CompiledObject, ObjectExpectations, ObjectLayout};
    let object = CompiledObject::parse(&fx.object).expect("parses");
    let expected =
        ObjectExpectations::from_module(&fx.m_cg, object.format, fx.model).expect("expectations");
    let layout = ObjectLayout::bind(object, &expected).expect("binds");
    let window = &layout.windows["rung"];
    assert!(!window.unknown.is_empty(), "{}: no reader Unknowns", fx.triple);
    assert_eq!(
        report.certificate("rung").expect("certificate").obligations.o1_binding.detail,
        window.unknown.join("; "),
        "{}: original reader account changed",
        fx.triple
    );
    let c = report.certificate("rung").expect("certificate");
    assert_eq!(
        c.obligations.o1_binding.grade,
        Grade::Unknown,
        "{}: {}",
        fx.triple,
        explain(report)
    );
    assert_eq!(
        c.obligations.o1_binding.detail.matches("address materialization").count(),
        2,
        "{}: {}",
        fx.triple,
        explain(report)
    );
    assert!(
        matches!(&c.verdict, OutputVerdict::Unknown { .. }) && !c.is_kernel_proved(),
        "{}: {}",
        fx.triple,
        explain(report)
    );
    assert!(calls.is_empty(), "{}: unlicensed tail reached proof routing: {calls:?}", fx.triple);
    assert!(
        report.ships(EmitPolicy::StrictProvenOnly).is_err(),
        "{}: {}",
        fx.triple,
        explain(report)
    );
    assert!(report.ships(EmitPolicy::AllowUnknown).is_ok(), "{}: {}", fx.triple, explain(report));
}

/// All original sited O0 baseline cells remain present, with the actual copied
/// operand checked in the bytes. S2a withdrawal requires precise O1 refusal;
/// raw S3b conjunction proof positives do not grant whole-object admission.
#[test]
fn s21_sited_o0_copy_keeps_the_unlicensed_tail_unknown() {
    let mut seen = Vec::new();
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        let ((at, _), (copy_at, _)) = udiv_and_copy(&fx);
        let (report, calls) = report_recording(&fx);
        assert_sited_o1_unknown(&fx, &report, &calls);
        seen.push(format!(
            "{triple} O0 sited: copy at {copy_at:#x}, udiv at {at:#x}: Unknown calls {calls:?}"
        ));
    }
    assert_eq!(seen.len(), BOTH.len(), "every original baseline cell must run");
    println!("{seen:#?}");
}

/// Both original byte mutations remain: copied operand x0 -> x2 and the
/// quotient divisor -> dividend. The earlier unlicensed O1 pair remains the
/// blocker, so these cells claim Unknown, not a decided value refutation.
#[test]
fn s21_sited_o0_copy_mutants_are_not_proved() {
    let mut seen = Vec::new();
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        let (report, calls) = report_recording(&fx);
        assert_sited_o1_unknown(&fx, &report, &calls);
        let ((at, w), (copy_at, cw)) = udiv_and_copy(&fx);
        let rn = (w >> 5) & 31;
        for (what, m) in [
            ("copy reads x2", fx.patched(|o| patch_word(o, copy_at, with_field(cw, 16, 2)))),
            ("udiv Rm := Rn", fx.patched(|o| patch_word(o, at, with_field(w, 16, rn)))),
        ] {
            let (report, calls) = report_recording(&m);
            assert_sited_o1_unknown(&m, &report, &calls);
            let grade = &report.certificate("rung").unwrap().obligations.o1_binding.grade;
            seen.push((triple, what, format!("{grade:?} calls {calls:?}")));
        }
    }
    assert_eq!(
        seen.len(),
        BOTH.len() * SITED_MUTANT_PIN.len(),
        "every original mutation cell must run"
    );
    println!("{seen:#?}");
    for (triple, what, got) in &seen {
        let pinned = SITED_MUTANT_PIN
            .iter()
            .find(|(w, _)| w == what)
            .unwrap_or_else(|| panic!("no pin for `{what}`"))
            .1;
        assert_eq!(got, pinned, "{triple} {what}: the pin moved");
    }
}

/// Current refusal policy, with all historical mutation identities retained.
const SITED_MUTANT_PIN: [(&str, &str); 2] =
    [("copy reads x2", "Unknown calls []"), ("udiv Rm := Rn", "Unknown calls []")];

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

// ===========================================================================
// PKG-C5c-S3d: signed `/` and `%` by a variable, and `MIN / -1`
// ===========================================================================

/// The signed machine module: the producer IR with its unsited `assert`s folded out (as the
/// compiler lane folds them) and its obligation records dropped. The fold moves every later
/// instruction's index, so the records' sites no longer name their checks (s21's single check is
/// the last instruction before its `udiv`, so its moved site happens to land on an arithmetic
/// instruction; the signed checks' do not, and trust-ir's validation refuses the module). The
/// bytes do not read the records; the gate reads them from the producer IR as written.
fn signed_machine(body: &str) -> String {
    folded(body).lines().filter(|l| !l.starts_with("obligation ")).collect::<Vec<_>>().join("\n")
}

/// Bytes from the signed machine module of `machine`, the producer IR `spec` as written.
fn signed_fixture(machine: &str, spec: &str, triple: &str, opt: OptLevel) -> Fixture {
    let license = fixture_license().with_recognized_authority("trust-direct-lane-structural");
    let object = compile_under(&parse(&signed_machine(machine)), triple, opt, license)
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"));
    Fixture::with_object(targeted(&parse(spec), triple), object, triple)
}

/// 64-bit `sdiv`.
fn is_sdiv(w: u32) -> bool {
    w & 0xffe0_fc00 == 0x9ac0_0c00
}

/// 64-bit `movn xd, #0` (-1).
fn is_movn0(w: u32) -> bool {
    w & 0xffff_ffe0 == 0x9280_0000
}

/// 64-bit `movz xd, #0`.
fn is_movz0_64(w: u32) -> bool {
    w & 0xffff_ffe0 == 0xd280_0000
}

/// 64-bit `movk xd, #0x8000, lsl #48` (with a `movz xd, #0`: `i64::MIN`).
fn is_movk_8000_48(w: u32) -> bool {
    w & 0xffff_ffe0 == 0xf2f0_0000
}

/// 64-bit `subs xzr, xn, xm` (`cmp xn, xm`) with `xn = x0`: the compare against `i64::MIN`.
fn is_cmp_x0_reg(w: u32) -> bool {
    w & 0xff20_03ff == 0xeb00_001f
}

/// Every word of `rung` matching `pred`, in address order.
fn all_of(fx: &Fixture, pred: impl Fn(u32) -> bool) -> Vec<(u64, u32)> {
    function_words(&fx.object, "rung").into_iter().filter(|(_, w)| pred(*w)).collect()
}

/// The first word of `rung` matching `pred` (after `after`, if given).
#[track_caller]
fn first_of(fx: &Fixture, what: &str, after: u64, pred: impl Fn(u32) -> bool) -> (u64, u32) {
    all_of(fx, pred).into_iter().find(|(o, _)| *o >= after).unwrap_or_else(|| {
        panic!("{}: no `{what}` in `rung`\n{}", fx.triple, disassemble(&fx.object))
    })
}

/// The signed guard's materialized constants, as measured (2026-11-15, every cell): `-1` is
/// `movn xd, #0` and `i64::MIN` is `movz xd, #0; movk xd, #0x8000, lsl #48` (no single
/// `movz #0x8000, lsl #48`); each is compared by `subs xzr, xn, xd`. The lifter states them as
/// `BvNot(0)` and `BvOr(BvAnd(0, !(0xffff << 48)), 1 << 63)`, which the route's compare
/// canonicalization meets with the spec's `-1` and `MIN` literals.
#[track_caller]
fn assert_signed_guard_constants(fx: &Fixture, opt: OptLevel) {
    let (movn, _) = first_of(fx, "movn #0", 0, is_movn0);
    let (movk, _) = first_of(fx, "movk #0x8000, lsl #48", 0, is_movk_8000_48);
    let movz: Vec<u64> = all_of(fx, is_movz0_64).into_iter().map(|(o, _)| o).collect();
    assert!(movz.contains(&(movk - 4)), "{} {opt:?}: no `movz #0` before the `movk`", fx.triple);
    assert!(movn < movk, "{} {opt:?}: the -1 constant is not first", fx.triple);
    first_of(fx, "cmp x0, xd", movk, is_cmp_x0_reg);
}

/// Complete guarded signed-division objects require a Lean-checked semantic
/// relation before the output gate may promote them to kernel evidence.
#[test]
fn sdiv_var_requires_lean_semantics_before_strict_admission() {
    signed_requires_lean_semantics(SDIV_IR, "sdiv_var", false);
}

/// Keep the complete signed-remainder population and strict refusal too.
#[test]
fn srem_var_requires_lean_semantics_before_strict_admission() {
    signed_requires_lean_semantics(SREM_IR, "srem_var", true);
}

/// Exact original conjunctions remain tied to the live gate subjects. The
/// unit test now refuses their proposed semantic goal; no fixture is retagged
/// as an admitted proof after withdrawal of the Rust-only goal constructor.
fn unit_fixture(subject: &str, opt: OptLevel) -> Vec<(trust_types::Formula, trust_types::Formula)> {
    let text = match (subject, opt) {
        ("sdiv_var", OptLevel::O0) => {
            include_str!("../src/verify_output_instantiate/div_split/fixtures/sdiv_var-O0.json")
        }
        ("sdiv_var", OptLevel::O2) => {
            include_str!("../src/verify_output_instantiate/div_split/fixtures/sdiv_var-O2.json")
        }
        ("srem_var", OptLevel::O0) => {
            include_str!("../src/verify_output_instantiate/div_split/fixtures/srem_var-O0.json")
        }
        ("srem_var", OptLevel::O2) => {
            include_str!("../src/verify_output_instantiate/div_split/fixtures/srem_var-O2.json")
        }
        other => panic!("no unit fixture {other:?}"),
    };
    serde_json::from_str(text).expect("the unit fixture parses")
}

fn signed_requires_lean_semantics(ir: &str, subject: &str, rem: bool) {
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(ir, ir, triple, opt);
            the_one(&fx, "sdiv", is_sdiv);
            if rem {
                the_one(&fx, "msub", is_msub);
            }
            assert_signed_guard_constants(&fx, opt);
            let (report, conjs) = verify_recording_conjunctions(&fx);
            let report = report.unwrap_or_else(|e| panic!("{triple}: object refused: {e}"));
            let calls: Vec<bool> = conjs.iter().map(|(proved, _)| *proved).collect();
            assert_eq!(calls, [false], "{subject} {triple} {opt:?}: signed evidence escaped");
            assert_eq!(
                conjs[0].1,
                unit_fixture(subject, opt),
                "{subject} {triple} {opt:?}: original conjunction changed"
            );
            assert!(
                report.ships(EmitPolicy::StrictProvenOnly).is_err(),
                "{subject} {triple} {opt:?}: signed object shipped without Lean semantics"
            );
        }
    }
}

/// THE MIN / -1 TWIN (`if y != 0 { x / y }`, no source guard against `MIN / -1`), and its `%`
/// sibling, at O0 and O2 on both triples: Unknown at O4, the producer's unconditional overflow
/// check (`assert %12, overflow`, the unsited check at `bb1[9]`) failing on a reached path at
/// `(MIN, -1)`; the routes are never called (`calls []`). Item 0 alone agrees there (the spec's
/// `BvSDiv` and the lifter's `sdiv` are both `MIN`): only (4b) separates the twin from Rust, which
/// panics. For `%` the twin's value agrees everywhere (`MIN % -1` is 0 either way) and the check
/// still makes it Unknown: Rust panics there too.
#[test]
fn min_neg_one_twin_is_unknown_at_o4() {
    for (what, ir) in [("/", SDIV_ZERO_GUARD_IR), ("%", SREM_ZERO_GUARD_IR)] {
        for triple in BOTH {
            for opt in OPTS {
                let fx = signed_fixture(ir, ir, triple, opt);
                let (report, calls) = report_recording(&fx);
                let c = report.certificate("rung").expect("certificate");
                match &c.verdict {
                    OutputVerdict::Unknown { reason }
                        if reason.contains("O4") && reason.contains("unsited check at bb1[9]") => {}
                    other => panic!(
                        "{what} {triple} {opt:?}: not Unknown at the overflow check: {other:?}\n{}",
                        explain(&report)
                    ),
                }
                assert!(
                    calls.is_empty(),
                    "{what} {triple} {opt:?}: the routes were called: {calls:?}"
                );
            }
        }
    }
}

/// The twin's IR with its overflow check (and that check's record) removed: the `MIN / -1` fence
/// is that check alone (DIV-SPLIT-1 S3d; design section 3.6). Without it the twin's bytes meet a
/// spec whose `MIN / -1` is SMT `bvsdiv`'s `MIN`, exactly what `sdiv` computes, so the route proves
/// the refinement: a [PROVED] grade here is sound for that (weaker) spec, and shows that nothing
/// in the route refuses `MIN / -1` on its own: the producer's unconditional overflow check and the
/// gate's (4b) step do.
fn unchecked_twin_ir() -> String {
    SDIV_ZERO_GUARD_IR
        .lines()
        .filter(|l| !l.contains("overflow div") && !l.starts_with("obligation 1 "))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

/// Removing a source overflow check cannot grant the missing signed semantic
/// relation or promote the object to strict evidence.
#[test]
fn an_unchecked_overflow_twin_still_requires_lean_semantics() {
    let spec = unchecked_twin_ir();
    assert_eq!(spec.lines().count() + 2, SDIV_ZERO_GUARD_IR.lines().count(), "the cut");
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(SDIV_ZERO_GUARD_IR, &spec, triple, opt);
            let (report, calls) = report_recording(&fx);
            assert_eq!(calls, [false], "{triple} {opt:?}: signed evidence escaped");
            assert!(
                report.ships(EmitPolicy::StrictProvenOnly).is_err(),
                "{triple} {opt:?}: unchecked signed twin shipped"
            );
        }
    }
}

/// LIVE SIGNED DIVISION BY ZERO AND OVERFLOW: the bytes of an unguarded `x / y` against the
/// producer's own IR for it (both checks kept): Unknown at O4 (the `div_by_zero` check at
/// `bb0[2]` can fail first), never Proven; the routes are never called.
#[test]
fn asserted_live_signed_division_is_unknown_at_o4() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(ASSERTED_SDIV_IR, ASSERTED_SDIV_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            match &c.verdict {
                OutputVerdict::Unknown { reason }
                    if reason.contains("O4") && reason.contains("unsited check at bb0[2]") => {}
                other => {
                    panic!("{triple} {opt:?}: not Unknown at O4: {other:?}\n{}", explain(&report))
                }
            }
            assert!(calls.is_empty(), "{triple} {opt:?}: the routes were called: {calls:?}");
        }
    }
}

/// `x % y` over `i64` with no guard and no check: hand-shaped in the producer's form, not a dump
/// (the producer always records both checks).
const RAW_SREM_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "srem_raw.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %2 = srem i64 %0, %1
    ret %2
}
"#;

/// Identical raw signed-remainder formulas also require the original-operation
/// relation: reflexivity of a proposed Rust goal supplies no semantic authority.
#[test]
fn a_raw_signed_remainder_twin_still_requires_lean_semantics() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(RAW_SREM_IR, RAW_SREM_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            assert_eq!(calls, [false], "{triple} {opt:?}: signed evidence escaped");
            assert!(
                report.ships(EmitPolicy::StrictProvenOnly).is_err(),
                "{triple} {opt:?}: raw signed remainder shipped"
            );
        }
    }
}

/// The `%` twin's bytes (`if y != 0 { x % y }`) against the guarded spec (`srem_var`): they agree
/// everywhere (at `(MIN, -1)` the bytes compute `MIN - MIN * -1 = 0`, the spec's `else` arm), so
/// any Proven grade is sound. Pinned as measured ([`ZERO_GUARD_REM_PIN`]).
#[test]
fn zero_guard_rem_bytes_against_the_guarded_spec() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(SREM_ZERO_GUARD_IR, SREM_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            let c = report.certificate("rung").expect("certificate");
            assert!(c.verdict.is_proven(), "{triple} {opt:?}\n{}", explain(&report));
            seen.push(format!("{} {:?} calls {calls:?}", c.grade, c.verdict));
        }
    }
    println!("{seen:#?}");
    for got in &seen {
        assert_eq!(got, ZERO_GUARD_REM_PIN, "the pin moved");
    }
}

/// Measured 2026-11-15, all four cells alike: ay validates it at step (4); the route declines
/// (the bytes' unguarded composite meets the spec's `else` arm at the leaf `x == MIN, y == -1`,
/// where the arms are equal only as values).
const ZERO_GUARD_REM_PIN: &str = "[VALIDATED] Proven { evidence: AyValidated } calls [false]";

/// MUTANTS of the signed subjects at O0 and O2 on both triples. The unmutated
/// twin requires Lean semantics before strict admission: each is not Proven (and no route answers `true`) but
/// the named equivalents ([`EQUIVALENT_SIGNED_MUTANTS`]), and each verdict is pinned as measured
/// ([`SIGNED_MUTANT_PIN`]). Bytes: the branch on `y != 0` flipped;
/// the guard's `movn #0` made `#1` (`-1` made `-2`); its `movk #0x8000` made `#0x4000` (`MIN` made
/// `2^62`); the `MIN` compare reading x1 for x0; the branch after the `-1` compare flipped;
/// `sdiv` made `udiv`; the `sdiv` operands swapped; for `%`, `msub` made `madd` and its Ra set to
/// its Rm. IR, against the original bytes: the guard's `-1` made `-2`; its `MIN` made `MIN + 1`;
/// the `-1` compare's `icmp ne` made `eq`; `sdiv`/`srem` made unsigned; the operands swapped.
fn visit_signed_mutants(
    fx: &Fixture,
    ir: &str,
    rem: bool,
    mut not_proved: impl FnMut(&Fixture, &str),
) {
    let (at, w) = first_of(fx, "the branch on y != 0", 0, |w| is_cb(w) || is_bcond(w));
    not_proved(&fx.patched(|o| patch_word(o, at, flipped_branch(w))), "zero guard flipped");
    let (movn, w) = first_of(fx, "movn #0", 0, is_movn0);
    not_proved(&fx.patched(|o| patch_word(o, movn, w | (1 << 5))), "movn #0 -> #1");
    let (at, w) = first_of(fx, "movk #0x8000", 0, is_movk_8000_48);
    let k = (w & !(0xffff << 5)) | (0x4000 << 5);
    not_proved(&fx.patched(|o| patch_word(o, at, k)), "movk #0x8000 -> #0x4000");
    let (at, w) = first_of(fx, "cmp x0, xd", 0, is_cmp_x0_reg);
    not_proved(&fx.patched(|o| patch_word(o, at, with_field(w, 5, 1))), "MIN cmp reads x1");
    let (at, w) = first_of(fx, "the branch after the -1 compare", movn, is_bcond);
    not_proved(&fx.patched(|o| patch_word(o, at, flipped_branch(w))), "-1 branch flipped");
    let (at, w) = the_one(fx, "sdiv", is_sdiv);
    not_proved(&fx.patched(|o| patch_word(o, at, w & !(1 << 10))), "sdiv -> udiv");
    let (rn, rm) = ((w >> 5) & 31, (w >> 16) & 31);
    let swapped = with_field(with_field(w, 5, rm), 16, rn);
    not_proved(&fx.patched(|o| patch_word(o, at, swapped)), "sdiv operands swapped");
    if rem {
        let (at, w) = the_one(fx, "msub", is_msub);
        let rm = (w >> 16) & 31;
        not_proved(&fx.patched(|o| patch_word(o, at, w & !(1 << 15))), "msub -> madd");
        not_proved(&fx.patched(|o| patch_word(o, at, with_field(w, 10, rm))), "msub Ra := Rm");
    }
    let op = if rem { "srem" } else { "sdiv" };
    let un = if rem { "urem" } else { "udiv" };
    let ir_m = |from: &str, to: &str| against(fx, &replace_once(ir, from, to));
    not_proved(&ir_m("%7 = const i64 -1", "%7 = const i64 -2"), "IR -1 -> -2");
    not_proved(
        &ir_m("%10 = const i64 -9223372036854775808", "%10 = const i64 -9223372036854775807"),
        "IR MIN -> MIN + 1",
    );
    not_proved(&ir_m("%8 = icmp ne", "%8 = icmp eq"), "IR -1 icmp ne -> eq");
    not_proved(
        &ir_m(&format!("{op} i64 %0, %1"), &format!("{un} i64 %0, %1")),
        "IR signed -> unsigned",
    );
    not_proved(
        &ir_m(&format!("{op} i64 %0, %1"), &format!("{op} i64 %1, %0")),
        "IR operands swapped",
    );
}

fn signed_mutants(ir: &str, subject: &str, rem: bool) -> Vec<(String, String)> {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = signed_fixture(ir, ir, triple, opt);
            let (baseline, baseline_calls) = report_recording(&fx);
            assert_eq!(
                baseline_calls,
                [false],
                "{subject} {triple} {opt:?}: signed baseline gained evidence"
            );
            assert!(
                baseline.ships(EmitPolicy::StrictProvenOnly).is_err(),
                "{subject} {triple} {opt:?}: signed baseline shipped"
            );
            let mut not_proved = |m: &Fixture, what: &str| {
                let (report, calls) = verify_recording(m);
                let report = report.unwrap_or_else(|refusal| {
                    panic!("{triple}: MUTANT `{subject} {what}`: object refused: {refusal}")
                });
                assert!(
                    report.ships(EmitPolicy::StrictProvenOnly).is_err(),
                    "{triple}: MUTANT `{subject} {what}` shipped without Lean semantics"
                );
                let c = report.certificate("rung").expect("certificate");
                let kind = match &c.verdict {
                    OutputVerdict::Refuted { .. } => "Refuted".to_string(),
                    OutputVerdict::Unknown { .. } => "Unknown".to_string(),
                    OutputVerdict::Proven { .. } => format!("Proven {}", c.grade),
                    other => panic!("{triple}: MUTANT `{subject} {what}`: {other:?}"),
                };
                seen.push((format!("{triple} {opt:?} {what}"), format!("{kind} calls {calls:?}")));
            };
            visit_signed_mutants(&fx, ir, rem, &mut not_proved);
        }
    }
    seen
}

/// Each mutant's verdict is pinned; only the named EQUIVALENT mutants may be Proven, and none
/// by a route (`calls` never holds `true` but for them).
#[track_caller]
fn check_signed_mutant_pin(subject: &str, seen: &[(String, String)], per_cell: usize) {
    assert_eq!(seen.len(), 2 * 2 * per_cell, "{subject}: {seen:#?}");
    println!("{subject} {seen:#?}");
    for (what, got) in seen {
        let name = what.splitn(3, ' ').nth(2).expect("cell name");
        if !EQUIVALENT_SIGNED_MUTANTS.contains(&(subject, name)) {
            assert!(
                !got.starts_with("Proven") && !got.contains("true"),
                "{subject} {what}: a mutant is proved: {got}"
            );
        }
        let pinned = SIGNED_MUTANT_PIN
            .iter()
            .find(|(s, w, _)| *s == subject && *w == name)
            .unwrap_or_else(|| panic!("no pin for {subject} `{name}`: {got}"))
            .2;
        assert_eq!(got, pinned, "{subject} {what}: the pin moved");
    }
}

#[test]
fn sdiv_var_mutants_are_not_proved() {
    let seen = signed_mutants(SDIV_IR, "sdiv_var", false);
    check_signed_mutant_pin("sdiv_var", &seen, 12);
}

#[test]
fn srem_var_mutants_are_not_proved() {
    let seen = signed_mutants(SREM_IR, "srem_var", true);
    check_signed_mutant_pin("srem_var", &seen, 14);
}

/// EQUIVALENT mutants, which a sound gate may prove: for `%` the `MIN / -1` guard is
/// semantically idle on these bytes (`sdiv` gives `MIN` there, so `msub` gives `MIN - MIN * -1 =
/// 0`, the guard's `else`), so moving its `-1` or `MIN` constant, or comparing the divisor with
/// `MIN`, changes no result.
const EQUIVALENT_SIGNED_MUTANTS: [(&str, &str); 3] = [
    ("srem_var", "movn #0 -> #1"),
    ("srem_var", "movk #0x8000 -> #0x4000"),
    ("srem_var", "MIN cmp reads x1"),
];

/// The signed mutants' measured verdicts (2026-11-15, all four cells alike). Every
/// non-equivalent byte and IR mutant is Refuted by ay at step (4), the step-(5) routes never called
/// (the s21 precedent: the route's kernel refusals are the unit tests'); for `%` the spec's guard
/// constants moved leave the producer's overflow check live at `(MIN, -1)` on a reached path
/// (Unknown at O4), and the three equivalent byte mutants are validated by ay, the route
/// declining.
const SIGNED_MUTANT_PIN: [(&str, &str, &str); 26] = [
    ("sdiv_var", "zero guard flipped", "Refuted calls []"),
    ("sdiv_var", "movn #0 -> #1", "Refuted calls []"),
    ("sdiv_var", "movk #0x8000 -> #0x4000", "Refuted calls []"),
    ("sdiv_var", "MIN cmp reads x1", "Refuted calls []"),
    ("sdiv_var", "-1 branch flipped", "Refuted calls []"),
    ("sdiv_var", "sdiv -> udiv", "Refuted calls []"),
    ("sdiv_var", "sdiv operands swapped", "Refuted calls []"),
    ("sdiv_var", "IR -1 -> -2", "Refuted calls []"),
    ("sdiv_var", "IR MIN -> MIN + 1", "Refuted calls []"),
    ("sdiv_var", "IR -1 icmp ne -> eq", "Refuted calls []"),
    ("sdiv_var", "IR signed -> unsigned", "Refuted calls []"),
    ("sdiv_var", "IR operands swapped", "Refuted calls []"),
    ("srem_var", "zero guard flipped", "Refuted calls []"),
    ("srem_var", "movn #0 -> #1", "Proven [VALIDATED] calls [false]"),
    ("srem_var", "movk #0x8000 -> #0x4000", "Proven [VALIDATED] calls [false]"),
    ("srem_var", "MIN cmp reads x1", "Proven [VALIDATED] calls [false]"),
    ("srem_var", "-1 branch flipped", "Refuted calls []"),
    ("srem_var", "sdiv -> udiv", "Refuted calls []"),
    ("srem_var", "sdiv operands swapped", "Refuted calls []"),
    ("srem_var", "msub -> madd", "Refuted calls []"),
    ("srem_var", "msub Ra := Rm", "Refuted calls []"),
    ("srem_var", "IR -1 -> -2", "Unknown calls []"),
    ("srem_var", "IR MIN -> MIN + 1", "Unknown calls []"),
    ("srem_var", "IR -1 icmp ne -> eq", "Refuted calls []"),
    ("srem_var", "IR signed -> unsigned", "Refuted calls []"),
    ("srem_var", "IR operands swapped", "Refuted calls []"),
];

/// `if y != 0 && (y != -1 || x != i64::MIN) { x / y } else { 0 }` over `i64` (`sdiv_var.rs`,
/// `#[no_mangle] pub extern "C" fn rung(x: i64, y: i64) -> i64`): the producer's own
/// `-Ztrust-dump=ir:` text (stage-1 trustc 52c2d5c509, `-Ztrust-dump=ir: -Ztrust-ir-lower=on
/// -Ztrust-verify=off -Coverflow-checks=off`, `-Copt-level=2`; byte-identical at `0`; dumped
/// 2026-11-15), the `#loc` comments and the `target` line dropped. The producer records both
/// signed checks unconditionally (`div_by_zero`, and `overflow` as `y != -1 || x != MIN`).
const SDIV_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "sdiv_var.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %5 = const i64 0
    %6 = icmp ne i64 %1, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i64 -1
    %8 = icmp ne i64 %1, %7
    condbr %8, bb5, bb4
bb2:
    %9 = const bool false
    br bb3(%9)
bb3(%2: bool):
    condbr %2, bb7, bb8
bb4:
    %10 = const i64 -9223372036854775808
    %11 = icmp ne i64 %0, %10
    br bb6(%11)
bb5:
    %12 = const bool true
    br bb6(%12)
bb6(%3: bool):
    br bb3(%3)
bb7:
    %13 = const i64 0
    %14 = icmp ne i64 %1, %13
    assert %14, div_by_zero  ; #proof: div_nonzero
    %15 = const i64 -1
    %16 = const i64 -9223372036854775808
    %17 = icmp ne i64 %1, %15
    %18 = icmp ne i64 %0, %16
    %19 = const bool true
    %20 = select bool %17, %19, %18
    assert %20, overflow div  ; #proof: no_overflow
    %21 = sdiv i64 %0, %1
    br bb9(%21)
bb8:
    %22 = const i64 0
    br bb9(%22)
bb9(%4: i64):
    ret %4
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L3C46 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C46#div_by_zero#o0" range 0 3 46 3 51 site f0/bb7#2

obligation 1 arithmetic_safety pending "direct THIR Assert (overflow) at L3C46 of `rung::rung`: arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C46#overflow#o0" range 0 3 46 3 51 site f0/bb7#9
"#;

/// The same with `x % y` (`srem_var.rs`), dumped alike. The spec states `x % y` as the composite
/// `x - ite(y == 0, 0, x /s y) * y` (`verify_output::eval_binop`'s signed `Rem` arm); trust-cg
/// lowers it to `sdiv` then `msub`.
const SREM_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "srem_var.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %5 = const i64 0
    %6 = icmp ne i64 %1, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i64 -1
    %8 = icmp ne i64 %1, %7
    condbr %8, bb5, bb4
bb2:
    %9 = const bool false
    br bb3(%9)
bb3(%2: bool):
    condbr %2, bb7, bb8
bb4:
    %10 = const i64 -9223372036854775808
    %11 = icmp ne i64 %0, %10
    br bb6(%11)
bb5:
    %12 = const bool true
    br bb6(%12)
bb6(%3: bool):
    br bb3(%3)
bb7:
    %13 = const i64 0
    %14 = icmp ne i64 %1, %13
    assert %14, rem_by_zero  ; #proof: div_nonzero
    %15 = const i64 -1
    %16 = const i64 -9223372036854775808
    %17 = icmp ne i64 %1, %15
    %18 = icmp ne i64 %0, %16
    %19 = const bool true
    %20 = select bool %17, %19, %18
    assert %20, overflow rem  ; #proof: no_overflow
    %21 = srem i64 %0, %1
    br bb9(%21)
bb8:
    %22 = const i64 0
    br bb9(%22)
bb9(%4: i64):
    ret %4
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L3C46 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C46#rem_by_zero#o0" range 0 3 46 3 51 site f0/bb7#2

obligation 1 arithmetic_safety pending "direct THIR Assert (overflow) at L3C46 of `rung::rung`: arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C46#overflow#o0" range 0 3 46 3 51 site f0/bb7#9
"#;

/// THE MIN / -1 TWIN: `if y != 0 { x / y } else { 0 }` over `i64` (`sdiv_zero_guard.rs`), dumped
/// alike: no source guard against `MIN / -1`, so the producer's unconditional overflow check is
/// live on a reached path.
const SDIV_ZERO_GUARD_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "sdiv_zero_guard.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %3 = const i64 0
    %4 = icmp ne i64 %1, %3
    condbr %4, bb1, bb2
bb1:
    %5 = const i64 0
    %6 = icmp ne i64 %1, %5
    assert %6, div_by_zero  ; #proof: div_nonzero
    %7 = const i64 -1
    %8 = const i64 -9223372036854775808
    %9 = icmp ne i64 %1, %7
    %10 = icmp ne i64 %0, %8
    %11 = const bool true
    %12 = select bool %9, %11, %10
    assert %12, overflow div  ; #proof: no_overflow
    %13 = sdiv i64 %0, %1
    br bb3(%13)
bb2:
    %14 = const i64 0
    br bb3(%14)
bb3(%2: i64):
    ret %2
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L3C16 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#div_by_zero#o0" range 0 3 16 3 21 site f0/bb1#2

obligation 1 arithmetic_safety pending "direct THIR Assert (overflow) at L3C16 of `rung::rung`: arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#overflow#o0" range 0 3 16 3 21 site f0/bb1#9
"#;

/// `if y != 0 { x % y } else { 0 }` over `i64` (`srem_zero_guard.rs`), dumped alike.
const SREM_ZERO_GUARD_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "srem_zero_guard.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %3 = const i64 0
    %4 = icmp ne i64 %1, %3
    condbr %4, bb1, bb2
bb1:
    %5 = const i64 0
    %6 = icmp ne i64 %1, %5
    assert %6, rem_by_zero  ; #proof: div_nonzero
    %7 = const i64 -1
    %8 = const i64 -9223372036854775808
    %9 = icmp ne i64 %1, %7
    %10 = icmp ne i64 %0, %8
    %11 = const bool true
    %12 = select bool %9, %11, %10
    assert %12, overflow rem  ; #proof: no_overflow
    %13 = srem i64 %0, %1
    br bb3(%13)
bb2:
    %14 = const i64 0
    br bb3(%14)
bb3(%2: i64):
    ret %2
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L3C16 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#rem_by_zero#o0" range 0 3 16 3 21 site f0/bb1#2

obligation 1 arithmetic_safety pending "direct THIR Assert (overflow) at L3C16 of `rung::rung`: arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C16#overflow#o0" range 0 3 16 3 21 site f0/bb1#9
"#;

/// `x / y` over `i64` with no guard (`asserted_sdiv.rs`), dumped alike: both checks live.
const ASSERTED_SDIV_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "asserted_sdiv.rs"

functy.0 = (i64, i64) -> (i64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x", %1="y"
bb0(%0: i64, %1: i64):
    %2 = const i64 0
    %3 = icmp ne i64 %1, %2
    assert %3, div_by_zero  ; #proof: div_nonzero
    %4 = const i64 -1
    %5 = const i64 -9223372036854775808
    %6 = icmp ne i64 %1, %4
    %7 = icmp ne i64 %0, %5
    %8 = const bool true
    %9 = select bool %6, %8, %7
    assert %9, overflow div  ; #proof: no_overflow
    %10 = sdiv i64 %0, %1
    ret %10
}

obligation 0 arithmetic_safety pending "direct THIR Assert (div_by_zero) at L3C4 of `rung::rung`: divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C4#div_by_zero#o0" range 0 3 4 3 9 site f0/bb0#2

obligation 1 arithmetic_safety pending "direct THIR Assert (overflow) at L3C4 of `rung::rung`: arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L3C4#overflow#o0" range 0 3 4 3 9 site f0/bb0#9
"#;

#[cfg(feature = "fmrel")]
#[path = "div_split_gate/fmrel.rs"]
mod fmrel;
