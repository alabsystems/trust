// tests/branch_split_gate.rs — the call-event gate over ladder rungs proved through the branch
// split (`verify_output_instantiate/branch_split.rs`, DECISION_QUEUE BRANCH-SPLIT-1), one
// kernel-checked term against the branching reflection of the whole conjunction (an atom case
// split when the conjunction has atoms). Step (5) of `call_event.rs` calls it at three sites: after
// `closed_branch::retry` declines, in place of a non-kernel first evidence, and inside the retry
// (`call_event/closed_branch.rs` `check`) on the folded items when the conjunction routes give no
// kernel value for them.
//
// Before the route, s05 (`if x < 2 { 10 } else if x & 1 == 0 { … } else { x * 3 }`) was
// [VALIDATED] with a wide-multiply StructuralCitation and r02 (the same chain on `x % 2`) was
// [VALIDATED]: no kernel route reflected a conjunction whose sides branch on `x`.
//
// POSITIVES: s05 and r02 at O0 and O2, on both object formats, are kernel-[PROVED] as
// `KernelInstantiated` with the branch label. The bytes are trust-cg's own compile of the
// producer IR with the unsited `assert` folded (as the compiler lane folds it), and the gate reads
// the producer IR as written: the configuration the route's fixtures were captured in
// (`src/verify_output_instantiate/branch_split/fixtures/HEADER.md`).
//
// ATOM-FREE: s07_local_call at O0 (two calls of a local `h`, the result their sum) has no Ite on
// a variable in its conjunction; the route proves it with no case split (each item closes by the
// congruence chains and `Eq.refl`), so the label names no arm selection.
//
// FOLDED: s23_enum_local at O2. The closed-branch retry folds its two ground tag tests (the
// untaken `E::A` arm reads an unwritten payload slot), and the folded value, `tbz` against the
// spec's `x & 1 == 0`, is over the bit-blast's refutation limit; the route proves it inside the
// retry, under the retry's three kernel-proved premises.
//
// NON-TARGETS: s04 keeps its bit-blast `KernelRecheckable` evidence and the route is never called
// for it (the route never replaces kernel evidence), and s23 at O0 keeps the closed-branch retry's
// four side conditions and the route is never called for it (the folded value's bit-blast is kernel
// evidence there, so neither the retry's call nor step (5)'s is reached). The calls are read
// through the `test-hooks` recorder (`verify_output_instantiate::record_branch_split_calls`), so
// these pin the call order whether or not the route would prove the conjunction.
//
// KERNEL-INELIGIBLE TWINS: s05, s07 and s23 (O2) with a dead `u16` shift, which gives the spec a
// modeling side condition, so step (5) is not kernel-eligible (`call_event.rs`,
// `kernel_eligible`). Each conj is its rung's, which the route proves; each twin must stay
// [VALIDATED] with the route never called, while the plain rung is kernel-[PROVED] by it.
//
// PRECISION PINS: s07 with its two call results added in the other order (`add x1, x0, x20`) is
// an equivalent mutant ay proves; the route is called and declines (no operand-order step on this
// path). `cmp #100`->`#101` is an equivalent mutant (the comparison is reached only for an
// even `x`, and there `x > 100` and `x > 101` agree). ay proves it [VALIDATED]; the route is
// called and declines (it does no infeasible-path reasoning, DECISION_QUEUE BRANCH-SPLIT-1
// "Revisit when"). It is pinned on its own, Proven and not kernel-[PROVED]: flip it to
// kernel-[PROVED] when infeasible-path reasoning lands.
//
// MUTANTS: byte mutants (`movz #10`→`#11`, `cmp #100`→`#99`, `hi`→`hs`, r02's `lsr #1`→`#2`;
// s07's `add #1`→`#2`, `add`→`sub`, `mov x20, x0`→`mov x20, x19`) and IR mutants (swapped arms,
// `x * 5`, `>= 100`, `& 3`, `% 4`; s07's `+ 2`, `-`), each Refuted, each with its
// unmutated twin kernel-[PROVED] by the route in the same test so a mutant cannot pass by the
// harness being broken. Each mutant changes the function's value on some input, so ay refutes it
// at step (4), before the step-(5) kernel step where the route runs: these mutants do not exercise
// the route, and would still pass if it accepted a wrong conjunction. The evidence that the
// KERNEL rejects a wrong branching conjunction is the route's unit tests with the Rust checks
// bypassed (`branch_split_proves_s04_s05_and_refuses_mutants`,
// `r02_is_proved_and_its_mutants_are_not`, `s07_mutants_are_refused_by_the_kernel`,
// `s23_folded_value_is_proved_and_its_mutants_are_not`, `atom_free_literal_condition_closes_by_selection`,
// in `src/verify_output_instantiate/branch_split/tests.rs`). Inside the retry,
// `s23_o2_mutants_reaching_the_branch_split_are_declined` (`src/call_event/closed_branch/tests.rs`)
// shows wrong folds declined on the production path, the filter on: (b), a false premise, by the
// premise bit-blast; (c), `tbz #1`, by the width walk, so it never reaches the kernel; (a) and (d)
// by the route, whose kernel refusal of those shapes with the Rust checks bypassed is the
// `branch_split` unit tests' (`arms 5, 5` and `spec arms swapped`).
// s23's O2 byte mutants (`mov #5`→`#6`, `add #1`→`#2`, `tbz #0`→`#1`, `tbz`→`tbnz`) are each not
// Proven: each is Unknown (ay's counterexample runs only through memory), not Refuted.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Compiled only with `kernel-recheck` (which implies `ay-proofs`) and `test-hooks`: the positives
// assert the clean kernel's [PROVED] grade, which no other build can award, and the call-order
// pins read the route's calls through the `test-hooks` recorder. Run: `targo --unverified test
// -p trust-cg-bridge --features kernel-recheck,test-hooks --test branch_split_gate`.
#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::{CerInput, CerReport, verify_compiled_module};
use trust_cg_bridge::compiled_object::ObjectRefusal;
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_instantiate::record_branch_split_calls;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::Module;

// ===========================================================================
// helpers
// ===========================================================================

/// What every branch-split label ends with (`branch_theory::LABEL_TAIL`).
const TAIL: &str = "kernel atom case split (O(1) branching conjunction, BRANCH-SPLIT-1)";
/// The arm selection every case split uses.
const ITE_CONG: &str = "Trust.BVB.ite_cong";
/// r02's `lsr #1` against the spec's `x / 2` (S4).
const ZEXT_DROP1_DIV2: &str = "Trust.BVS.zext_drop1_div2";

const OPTS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// The rung as trust-cg receives it: the lane folds a check whose condition is a constant
/// true out of the codegen module (an unsited `Assert` never reaches trust-cg), while the
/// producer the gate reads keeps it.
fn folded(body: &str) -> String {
    body.lines().filter(|l| !l.trim_start().starts_with("assert ")).collect::<Vec<_>>().join("\n")
}

fn parse(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

/// The gate's fixture for a whole producer module in text: bytes from the folded module,
/// compiled under the fixture license with the producer's own body-gate authority recognized,
/// and the producer IR as written.
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

/// [`Fixture::verify`] on the same 8 MiB gate thread, with the route's calls on that thread
/// recorded: one entry per call step (5) made to the branch split, `true` when it returned
/// kernel evidence.
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

/// The report and the route's calls, the object accepted.
#[track_caller]
fn report_recording(fx: &Fixture) -> (CerReport, Vec<bool>) {
    let (report, calls) = verify_recording(fx);
    let report = report.unwrap_or_else(|e| {
        panic!("{}: object refused: {e}\n{}", fx.triple, disassemble(&fx.object))
    });
    (report, calls)
}

/// `text` with `from` replaced by `to`, asserted to occur exactly once.
#[track_caller]
fn replace_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(text.matches(from).count(), 1, "`{from}` is not unique in the IR");
    text.replacen(from, to, 1)
}

/// The evidence of `symbol`'s Proven verdict, or a panic naming what it was instead.
#[track_caller]
fn evidence<'a>(fx: &Fixture, report: &'a CerReport, symbol: &str) -> &'a ProvenEvidence {
    match &report.certificate(symbol).expect("certificate").verdict {
        OutputVerdict::Proven { evidence } => evidence,
        other => panic!("{}: `{symbol}` is not Proven: {other:?}\n{}", fx.triple, explain(report)),
    }
}

/// `symbol` is kernel-[PROVED] by the branch split: `KernelInstantiated` with no retained
/// original, its label naming the arm selection and ending with the route's tail, and naming
/// `extra` when given.
#[track_caller]
fn assert_branch_proved(fx: &Fixture, report: &CerReport, symbol: &str, extra: Option<&str>) {
    let c = report.certificate(symbol).expect("certificate");
    assert!(
        c.is_kernel_proved(),
        "{}: `{symbol}` is not kernel-[PROVED]\n{}\n{}",
        fx.triple,
        explain(report),
        disassemble(&fx.object)
    );
    match evidence(fx, report, symbol) {
        ProvenEvidence::KernelInstantiated { theorem, original: None }
            if theorem.ends_with(TAIL)
                && theorem.contains(ITE_CONG)
                && extra.is_none_or(|t| theorem.contains(t)) => {}
        other => panic!(
            "{}: `{symbol}` is not a branch-split instantiation{}: {other:?}\n{}",
            fx.triple,
            extra.map(|t| format!(" naming {t}")).unwrap_or_default(),
            explain(report)
        ),
    }
}

/// A mutant that changes a result is Refuted (by ay at step (4)). Returns what it got.
#[track_caller]
fn assert_refuted(fx: &Fixture, symbol: &str, what: &str) -> String {
    let report = fx.verify().unwrap_or_else(|refusal| {
        panic!("{}: MUTANT `{what}` of `{symbol}`: object refused: {refusal}", fx.triple)
    });
    let c = report.certificate(symbol).unwrap_or_else(|| panic!("no `{symbol}`"));
    assert!(
        matches!(c.verdict, OutputVerdict::Refuted { .. }) && !c.is_kernel_proved(),
        "{}: MUTANT `{what}` of `{symbol}` is not Refuted\n{}\n{}",
        fx.triple,
        explain(&report),
        disassemble(&fx.object)
    );
    format!("{}: {:?}", c.grade, c.verdict)
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

/// `movz` of the 16-bit immediate `imm` (either register width, no shift).
fn is_movz(w: u32, imm: u32) -> bool {
    w & 0x7fe0_0000 == 0x5280_0000 && (w >> 5) & 0xffff == imm
}

/// `w` (a `movz`) with its immediate set to `imm`.
fn with_imm16(w: u32, imm: u32) -> u32 {
    (w & !(0xffff << 5)) | (imm << 5)
}

/// `subs Xd, Xn, #imm` (64-bit, unshifted immediate; `cmp` when `Xd` is `xzr`).
fn is_subs_imm(w: u32, imm: u32) -> bool {
    w & 0xffc0_0000 == 0xf100_0000 && (w >> 10) & 0xfff == imm
}

/// `w` (an add/sub immediate) with its `imm12` set to `imm`.
fn with_imm12(w: u32, imm: u32) -> u32 {
    (w & !(0xfff << 10)) | (imm << 10)
}

/// The condition field of a `b.cond` or a `csel`/`csinc`/`csinv`/`csneg`, if `w` is one.
fn cond_of(w: u32) -> Option<u32> {
    if w & 0xff00_0010 == 0x5400_0000 {
        Some(w & 0xf)
    } else if w & 0x1fe0_0000 == 0x1a80_0000 {
        Some((w >> 12) & 0xf)
    } else {
        None
    }
}

/// `w` (a `b.cond` or a conditional select) with its condition set to `cond`.
fn with_cond(w: u32, cond: u32) -> u32 {
    if w & 0xff00_0010 == 0x5400_0000 {
        (w & !0xf) | cond
    } else {
        (w & !(0xf << 12)) | (cond << 12)
    }
}

const HI: u32 = 8;
const LS: u32 = 9;
const HS: u32 = 2;
const LO: u32 = 3;

/// `ubfm Xd, Xn, #1, #63` (`lsr Xd, Xn, #1`).
fn is_lsr1(w: u32) -> bool {
    w & 0xffff_fc00 == 0xd341_fc00
}

// ===========================================================================
// the rungs
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung s05
/// (`tests/trust-f1-ladder/micro/s05_if_chain.rs`; trustc main 605f57d8cf,
/// `-Ztrust-ir-lower=on -Ztrust-verify=off -Coverflow-checks=off`, identical at `-Copt-level=0`
/// and `2`), with the `#loc` comments and the `target` line dropped so [`targeted`] stamps each
/// triple.
const S05_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s05_if_chain.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %4 = const u64 2
    %5 = icmp ult u64 %0, %4
    condbr %5, bb1, bb2
bb1:
    %6 = const u64 10
    br bb3(%6)
bb2:
    %7 = const u64 1
    %8 = and u64 %0, %7
    %9 = const u64 0
    %10 = icmp eq u64 %8, %9
    condbr %10, bb4, bb5
bb3(%1: u64):
    ret %1
bb4:
    %11 = const u64 100
    %12 = icmp ugt u64 %0, %11
    condbr %12, bb7, bb8
bb5:
    %13 = const u64 3
    %14 = mul u64 %0, %13
    br bb6(%14)
bb6(%2: u64):
    br bb3(%2)
bb7:
    %15 = const u64 100
    %16 = sub u64 %0, %15
    br bb9(%16)
bb8:
    %17 = const u64 1
    %18 = add u64 %0, %17
    br bb9(%18)
bb9(%3: u64):
    br bb6(%3)
}
"#;

/// The same for ladder rung r02 (`tests/trust-f1-ladder/programs/r02_branch.rs`): s05 with
/// `x % 2` for `x & 1`, its divisor check kept as the lowering recorded it.
const R02_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/programs/r02_branch.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %4 = const u64 2
    %5 = icmp ult u64 %0, %4
    condbr %5, bb1, bb2
bb1:
    %6 = const u64 10
    br bb3(%6)
bb2:
    %7 = const u64 2
    %8 = const u64 0
    %9 = icmp ne u64 %7, %8
    assert %9, rem_by_zero  ; #proof: div_nonzero
    %10 = urem u64 %0, %7
    %11 = const u64 0
    %12 = icmp eq u64 %10, %11
    condbr %12, bb4, bb5
bb3(%1: u64):
    ret %1
bb4:
    %13 = const u64 100
    %14 = icmp ugt u64 %0, %13
    condbr %14, bb7, bb8
bb5:
    %15 = const u64 3
    %16 = mul u64 %0, %15
    br bb6(%16)
bb6(%2: u64):
    br bb3(%2)
bb7:
    %17 = const u64 100
    %18 = sub u64 %0, %17
    br bb9(%18)
bb8:
    %19 = const u64 1
    %20 = add u64 %0, %19
    br bb9(%20)
bb9(%3: u64):
    br bb6(%3)
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L1C77 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C77#rem_by_zero#o0" range 0 1 77 1 82 site f0/bb2#3
"#;

/// Ladder rung s04 (`tests/trust-f1-ladder/micro/s04_if.rs`), the same producer and flags.
const S04_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s04_if.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %2 = const u64 5
    %3 = icmp ult u64 %0, %2
    condbr %3, bb1, bb2
bb1:
    %4 = const u64 1
    br bb3(%4)
bb2:
    %5 = const u64 2
    br bb3(%5)
bb3(%1: u64):
    ret %1
}
"#;

/// s23 `match if x & 1 == 0 { E::A } else { E::B(x) } { E::A => 5, E::B(y) => y + 1 }`, as
/// `call_event_gate.rs` states it (trustc ac76a2c1a, `-Ztrust-ir-lower=on -Coverflow-checks=off`).
const S23_IR: &str = "module \"rung\"
struct @P { a: u64 @0, b: u64 @8 } size=16 align=8 id=0
enum @E repr(u64) { A = 0, B(u64) = 1 } layout(direct tag@0 size=16 align=8 offsets=[[], [8]]) id=0
functy.0 = (u64) -> (u64)
type ty.0 = u64

fn @rung(functy.0) {
    ; #producer: trust
bb0(%0: u64):
    %3 = const u64 1
    %4 = and u64 %0, %3
    %5 = const u64 0
    %6 = icmp eq u64 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const enum.0 { 0 }
    br bb3(%7)
bb2:
    %8 = const enum.0 { 1, 0 }
    %9 = insertfield enum.0 %8, 1, %0
    br bb3(%9)
bb3(%1: enum.0):
    %10 = extractfield u64 %1, 0
    switch %10 [ 0: bb4 default: bb5 ]
bb4:
    %11 = const u64 5
    br bb6(%11)
bb5:
    %12 = extractfield u64 %1, 1
    %13 = const u64 1
    %14 = add u64 %12, %13
    br bb6(%14)
bb6(%2: u64):
    ret %2
}
";

/// Ladder rung s07 (`tests/trust-f1-ladder/micro/s07_local_call.rs`: `h(a) = a * 5 + 1`,
/// `rung(x) = h(x) + h(x + 1)`), the producer's own `-Ztrust-dump=ir:` text (stage-1 trustc
/// 80c41bb66, `-Ztrust-ir-lower=on -Ztrust-verify=off -Coverflow-checks=off`, identical at
/// `-Copt-level=0` and `2`), as [`S05_IR`].
const S07_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s07_local_call.rs"

functy.0 = (u64) -> (u64)

rustcc fn @_RNvCs7Vb4zyVTiud_4rung1h(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "h"
    ; #names: %0="a"
bb0(%0: u64):
    %1 = const u64 5
    %2 = mul u64 %0, %1
    %3 = const u64 1
    %4 = add u64 %2, %3
    ret %4
}

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = call @func.0(%0)
    %2 = const u64 1
    %3 = add u64 %0, %2
    %4 = call @func.0(%3)
    %5 = add u64 %1, %4
    ret %5
}
"#;

/// s07's label, measured (2026-11-14, both triples): the zero-wrapper strip (`bvf_or_cong` over
/// `bvf_or_zero_id`), `bvf_add_cong` above it, and `ite_cong` from `reflect_value`'s congruence
/// over the top-level reach indicators `Ite(true, 1, 0)`, which stay `Ite`s in both views; no
/// `ite_true` / `ite_false`, since each item's two views are equal and close by `Eq.refl`, with
/// no arm selection.
const S07_LABEL: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
                         Trust.BVB.ite_cong+kernel atom case split (O(1) branching conjunction, \
                         BRANCH-SPLIT-1)";

/// s23's folded O2 value's label, measured (2026-11-14, both triples): the `tbz` bridge and
/// `beq_and_lowbit` meet on bit 0 of `x`, one split, and each leaf selects its arms.
const S23_O2_LABEL: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+Trust.BVB.beq_and_lowbit+\
                            Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+kernel atom \
                            case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

/// s07's callee `h`, by its mangled symbol.
const S07_H: &str = "_RNvCs7Vb4zyVTiud_4rung1h";

/// A dead `u16` shift at the top of `rung`'s entry block (after `entry`), its values numbered from
/// `n`: the spec gets the modeling side condition `1 < 16` (`narrow_shift_side_condition`), so
/// step (5) is not kernel-eligible.
fn with_dead_u16_shift(text: &str, entry: &str, n: u32) -> String {
    let (t, k, r) = (n, n + 1, n + 2);
    replace_once(
        text,
        entry,
        &format!(
            "{entry}    %{t} = trunc u64 %0 to u16\n    %{k} = const u16 1\n    \
             %{r} = lshr u16 %{t}, %{k}\n"
        ),
    )
}

// ===========================================================================
// positives
// ===========================================================================

/// POSITIVE: s05 at O0 and O2, on both triples, is kernel-[PROVED] by the branch split.
/// FAILS without the route: the grade is [VALIDATED] (a wide-multiply StructuralCitation).
#[test]
fn s05_if_chain_is_kernel_proved_by_the_branch_split() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S05_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            assert_branch_proved(&fx, &report, "rung", None);
            assert_eq!(calls, [true], "{triple} {opt:?}: the route's calls");
        }
    }
}

/// POSITIVE: r02 at O0 and O2, on both triples, is kernel-[PROVED] by the branch split, its
/// label naming `zext_drop1_div2` (the machine's `lsr #1` against the spec's `x / 2`). FAILS
/// without the route: the grade is [VALIDATED].
#[test]
fn r02_branch_is_kernel_proved_by_the_branch_split() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(R02_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            assert_branch_proved(&fx, &report, "rung", Some(ZEXT_DROP1_DIV2));
            assert_eq!(calls, [true], "{triple} {opt:?}: the route's calls");
        }
    }
}

/// NON-TARGET: s04 keeps the bit-blast `KernelRecheckable` evidence it had before the route, and
/// the route is never called for it (kernel evidence is never replaced: the route proves s04's
/// conjunction too, `branch_split_proves_s04_s05_and_refuses_mutants`, so calling it first would
/// also move the evidence).
#[test]
fn s04_keeps_its_bit_blast_evidence() {
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S04_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            match evidence(&fx, &report, "rung") {
                ProvenEvidence::KernelRecheckable(_) => {}
                other => panic!("{triple} {opt:?}: s04's evidence moved: {other:?}"),
            }
            assert!(calls.is_empty(), "{triple} {opt:?}: the route was called for s04: {calls:?}");
        }
    }
}

/// NON-TARGET: s23 at O0 keeps the closed-branch retry's side-conditioned evidence, with its
/// four side conditions, and the route is never called for it (the retry runs before the route;
/// the recorder shows a swapped order whether or not the route would prove s23's conjunction).
#[test]
fn s23_o0_keeps_its_side_conditions() {
    for triple in BOTH {
        let fx = Fixture::new(parse(S23_IR), triple, OptLevel::O0);
        let (report, calls) = report_recording(&fx);
        match evidence(&fx, &report, "rung") {
            ProvenEvidence::KernelRecheckableWithSideConditions { side_conditions, .. } => {
                assert_eq!(side_conditions.len(), 4, "{triple}\n{}", explain(&report))
            }
            other => panic!("{triple}: s23 O0 is not side-conditioned evidence: {other:?}"),
        }
        assert!(calls.is_empty(), "{triple}: the route was called for s23 O0: {calls:?}");
    }
}

/// KERNEL-INELIGIBLE TWIN: s05 with a dead `u16` shift in its entry block. The shift is
/// narrower than a register, so the spec carries the modeling side condition `1 < 16`
/// (`narrow_shift_side_condition`), which step (2) discharges with ay but which is not in the
/// step-(5) conjunction; the step is therefore not kernel-eligible. The twin's conj is s05's
/// (the dead value is not in it), which the route proves, so a route called outside
/// `kernel_eligible` would grade the twin kernel-[PROVED] over a conjunction that leaves its
/// side condition out. The twin stays [VALIDATED] (`AyValidated`) with the route never called;
/// plain s05, the eligible twin, is kernel-[PROVED] by it in the same loop.
#[test]
fn a_kernel_ineligible_twin_never_reaches_the_route() {
    let ineligible = replace_once(
        S05_IR,
        "bb0(%0: u64):\n",
        "bb0(%0: u64):\n    %19 = trunc u64 %0 to u16\n    %20 = const u16 1\n    \
         %21 = lshr u16 %19, %20\n",
    );
    for triple in BOTH {
        for opt in OPTS {
            let eligible = producer_fixture(S05_IR, triple, opt);
            let (report, calls) = report_recording(&eligible);
            assert_branch_proved(&eligible, &report, "rung", None);
            assert_eq!(calls, [true], "{triple} {opt:?}: the eligible twin's route calls");

            let fx = producer_fixture(&ineligible, triple, opt);
            let (report, calls) = report_recording(&fx);
            match evidence(&fx, &report, "rung") {
                ProvenEvidence::AyValidated => {}
                other => panic!(
                    "{triple} {opt:?}: the kernel-ineligible twin is not [VALIDATED]: {other:?}\n{}",
                    explain(&report)
                ),
            }
            assert!(
                calls.is_empty(),
                "{triple} {opt:?}: the route was called outside `kernel_eligible`: {calls:?}"
            );
        }
    }
}

/// PRECISION PIN: s05 and r02 with `cmp x, #100` made `#101`, at O0 and O2 on both triples. It
/// changes nothing the function returns (the comparison is reached only for an even `x`, and for
/// an even `x`, `x > 100` and `x > 101` agree), so ay proves it [VALIDATED]: Proven, never
/// Refuted or Unknown. The route is called and declines ("the arms of a case differ"): it does
/// no infeasible-path reasoning. When that reasoning lands (DECISION_QUEUE BRANCH-SPLIT-1
/// "Revisit when"), this pin fails and is flipped to kernel-[PROVED].
#[test]
fn cmp_101_is_an_equivalent_twin_the_route_declines() {
    let mut seen = Vec::new();
    for text in [S05_IR, R02_IR] {
        for triple in BOTH {
            for opt in OPTS {
                let fx = producer_fixture(text, triple, opt);
                let (at, w) = the_one(&fx, "cmp x, #100", |w| is_subs_imm(w, 100));
                let cmp101 = fx.patched(|o| patch_word(o, at, with_imm12(w, 101)));
                let (report, calls) = report_recording(&cmp101);
                let c = report.certificate("rung").expect("certificate");
                assert!(
                    c.verdict.is_proven()
                        && !c.is_kernel_proved()
                        && !matches!(
                            &c.verdict,
                            OutputVerdict::Proven {
                                evidence: ProvenEvidence::KernelInstantiated { .. }
                            }
                        ),
                    "{triple} {opt:?}: `cmp #101` is not Proven at [VALIDATED] (flip this pin if \
                     the route now proves it)\n{}",
                    explain(&report)
                );
                assert_eq!(calls, [false], "{triple} {opt:?}: the route's calls for `cmp #101`");
                seen.push(format!("{triple} {opt:?}: {}: {:?}", c.grade, c.verdict));
            }
        }
    }
    assert_eq!(seen.len(), 2 * 2 * 2, "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

// ===========================================================================
// mutants
// ===========================================================================

/// MUTANTS of s05 and r02, at O0 and O2 on both triples: each is Refuted. Bytes: the `movz #10`
/// made `#11` (x < 2 gives 11); the `cmp x, #100` made `#99` (x = 100 takes the other arm); the
/// `hi` (or its inverse `ls`) condition made `hs` (`lo`) (x = 100 takes the other arm); r02's
/// `lsr #1` made `lsr #2` (x = 4 reads as odd). IR, against the original bytes: the `x > 100` arms
/// swapped; `x * 3` made `x * 5`; `>` made `>=`; s05's `& 1` made `& 3`; r02's `% 2` made `% 4`.
/// Each mutant's unmutated twin is kernel-[PROVED] by the route first. The equivalent `cmp #101`
/// is pinned separately (`cmp_101_is_an_equivalent_twin_the_route_declines`).
#[test]
fn branch_split_mutants_are_refuted() {
    let mut seen = Vec::new();
    for (rung, text) in [("s05", S05_IR), ("r02", R02_IR)] {
        let r02 = rung == "r02";
        let extra = r02.then_some(ZEXT_DROP1_DIV2);
        for triple in BOTH {
            for opt in OPTS {
                let fx = producer_fixture(text, triple, opt);
                assert_branch_proved(&fx, &fx.report(), "rung", extra);
                // Bytes.
                let movz10 = the_one(&fx, "movz #10", |w| is_movz(w, 10));
                let movz11 = fx.patched(|o| patch_word(o, movz10.0, with_imm16(movz10.1, 11)));
                let (at, w) = the_one(&fx, "cmp x, #100", |w| is_subs_imm(w, 100));
                let mut refuted = |m: &Fixture, what: &str| {
                    let got = assert_refuted(m, "rung", &format!("{rung} {opt:?} {what}"));
                    seen.push(format!("{rung} {triple} {opt:?} {what}: {got}"));
                };
                refuted(&fx.patched(|o| patch_word(o, at, with_imm12(w, 99))), "cmp #100 -> #99");
                refuted(&movz11, "movz #10 -> #11");
                let (at, w) = the_one(&fx, "an hi/ls condition", |w| {
                    cond_of(w).is_some_and(|c| c == HI || c == LS)
                });
                let flipped = if cond_of(w) == Some(HI) { HS } else { LO };
                refuted(&fx.patched(|o| patch_word(o, at, with_cond(w, flipped))), "hi -> hs");
                if r02 {
                    let (at, w) = the_one(&fx, "lsr x, x, #1", is_lsr1);
                    let lsr2 = (w & !(0x3f << 16)) | (2 << 16);
                    refuted(&fx.patched(|o| patch_word(o, at, lsr2)), "lsr #1 -> #2");
                }

                // IR, against the original bytes.
                let (gt, sub, add) = if r02 {
                    ("condbr %14, bb7, bb8", "%14 = icmp ugt", "%15 = const u64 3")
                } else {
                    ("condbr %12, bb7, bb8", "%12 = icmp ugt", "%13 = const u64 3")
                };
                let swapped = replace_once(text, gt, &gt.replace("bb7, bb8", "bb8, bb7"));
                refuted(&against(&fx, &swapped), "the x > 100 arms swapped");
                let times5 = replace_once(text, add, &add.replace("u64 3", "u64 5"));
                refuted(&against(&fx, &times5), "x * 3 -> x * 5");
                let ge = replace_once(text, sub, &sub.replace("ugt", "uge"));
                refuted(&against(&fx, &ge), "> 100 -> >= 100");
                if r02 {
                    let rem4 = replace_once(text, "%7 = const u64 2", "%7 = const u64 4");
                    refuted(&against(&fx, &rem4), "% 2 -> % 4");
                } else {
                    let and3 = replace_once(text, "%7 = const u64 1", "%7 = const u64 3");
                    refuted(&against(&fx, &and3), "& 1 -> & 3");
                }
            }
        }
    }
    // 2 rungs x 2 triples x 2 opts, with 7 mutants each for s05 and 8 for r02.
    assert_eq!(seen.len(), 2 * 2 * (7 + 8), "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

// ===========================================================================
// s07_local_call: a conjunction with no atoms
// ===========================================================================

/// The label of a `KernelInstantiated` with no retained original.
fn label<'a>(fx: &Fixture, report: &'a CerReport, symbol: &str) -> &'a str {
    match evidence(fx, report, symbol) {
        ProvenEvidence::KernelInstantiated { theorem, original: None } => theorem,
        other => panic!(
            "{}: `{symbol}` is not a kernel instantiation: {other:?}\n{}",
            fx.triple,
            explain(report)
        ),
    }
}

/// POSITIVE: s07 at O0, on both triples, is kernel-[PROVED] by the branch split with no case
/// split: its five items (two ground reach indicators, two call arguments, the result over the
/// call-result leaves) differ only by the machine's `mov` wrappers `BvOr(0, v)`, which the
/// zero-wrapper strip removes. The callee `h` keeps its own evidence (the add-commutation
/// route's). FAILS without the branch-split change, where the route declined a conjunction with no
/// Ite on a variable: measured 2026-11-14 with that precondition restored (mutant B1,
/// `scripts/frozen-waivers.txt`) on aarch64-apple-darwin, where the loop stops, the grade is
/// [VALIDATED] and the calls are `[false]` (`TRUST_GATE_TRACE=1`: the bit-blast is 2600
/// refutation steps, over the 2048 limit).
#[test]
fn s07_local_call_is_kernel_proved_without_atoms() {
    for triple in BOTH {
        let fx = producer_fixture(S07_IR, triple, OptLevel::O0);
        let (report, calls) = report_recording(&fx);
        let c = report.certificate("rung").expect("certificate");
        assert!(c.is_kernel_proved(), "{triple}: calls {calls:?}\n{}", explain(&report));
        assert_eq!(label(&fx, &report, "rung"), S07_LABEL, "{triple}");
        assert_eq!(calls, [true], "{triple}: the route's calls");
        let h = report.certificate(S07_H).expect("h");
        assert!(h.is_kernel_proved(), "{triple}: h\n{}", explain(&report));
        let h = label(&fx, &report, S07_H);
        assert!(h.contains("Trust.BVC.addRecM_comm") && !h.ends_with(TAIL), "{triple}: h {h}");
    }
}

/// PRECISION PIN: s07 with the two call results added in the other order (`add x1, x20, x0` made
/// `add x1, x0, x20`). The result is the same, so ay proves it; the route is called and declines,
/// since its reflection here has no operand-order step. Proven, not kernel-[PROVED]; flip it when
/// the route learns add commutation. This pins the grade and the call; why the route declines
/// (the arms of a case differ) is pinned on the captured commuted conj by the unit test
/// `s07_commuted_sum_is_declined_because_the_arms_differ`.
#[test]
fn s07_commuted_sum_is_an_equivalent_twin_the_route_declines() {
    for triple in BOTH {
        let fx = producer_fixture(S07_IR, triple, OptLevel::O0);
        let (at, _) = the_one(&fx, "add x1, x20, x0", |w| w == 0x8b00_0281);
        let commuted = fx.patched(|o| patch_word(o, at, 0x8b14_0001));
        let (report, calls) = report_recording(&commuted);
        let c = report.certificate("rung").expect("certificate");
        assert!(
            c.verdict.is_proven() && !c.is_kernel_proved(),
            "{triple}: the commuted sum is not Proven at [VALIDATED] (flip this pin if the route \
             now proves it)\n{}",
            explain(&report)
        );
        assert_eq!(calls, [false], "{triple}: the route's calls for the commuted sum");
    }
}

/// MUTANTS of s07 at O0 on both triples, each Refuted, after the unmutated twin is
/// kernel-[PROVED]. Bytes: `add x0, x19, #1` made `#2` (the second call's argument);
/// `add x1, x20, x0` made `sub`; `mov x20, x0` made `mov x20, x19` (the first call's result
/// replaced by `x`). IR, against the original bytes: `+ 1` made `+ 2`; the sum made a
/// difference. ay refutes each at step (4), before the route runs: these are harness controls,
/// and the kernel's refusals are the unit tests' (`s07_mutants_are_refused_by_the_kernel`).
#[test]
fn s07_mutants_are_refuted() {
    let mut seen = Vec::new();
    for triple in BOTH {
        let fx = producer_fixture(S07_IR, triple, OptLevel::O0);
        let (report, calls) = report_recording(&fx);
        assert!(report.certificate("rung").expect("rung").is_kernel_proved(), "{triple}");
        assert_eq!(calls, [true], "{triple}");
        let mut refuted = |m: &Fixture, what: &str| {
            let got = assert_refuted(m, "rung", &format!("s07 {what}"));
            seen.push(format!("s07 {triple} {what}: {got}"));
        };
        for (what, from, to) in [
            ("add x0, x19, #1 -> #2", 0x9100_0660, 0x9100_0a60),
            ("add x1, x20, x0 -> sub", 0x8b00_0281, 0xcb00_0281),
            ("mov x20, x0 -> mov x20, x19", 0xaa00_03f4, 0xaa13_03f4),
        ] {
            let (at, _) = the_one(&fx, what, |w| w == from);
            refuted(&fx.patched(|o| patch_word(o, at, to)), what);
        }
        let plus2 = replace_once(S07_IR, "%2 = const u64 1", "%2 = const u64 2");
        refuted(&against(&fx, &plus2), "IR x + 1 -> x + 2");
        let sub = replace_once(S07_IR, "%5 = add u64", "%5 = sub u64");
        refuted(&against(&fx, &sub), "IR h(x) + h(x + 1) -> h(x) - h(x + 1)");
    }
    assert_eq!(seen.len(), 2 * 5, "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

/// KERNEL-INELIGIBLE TWIN of s07: a dead `u16` shift gives the spec a side condition, so step (5)
/// is not kernel-eligible. The twin stays [VALIDATED] (`AyValidated`) with the route never called.
#[test]
fn s07_kernel_ineligible_twin_never_reaches_the_route() {
    let ineligible = with_dead_u16_shift(S07_IR, "; #names: %0=\"x\"\nbb0(%0: u64):\n", 6);
    for triple in BOTH {
        let fx = producer_fixture(&ineligible, triple, OptLevel::O0);
        let (report, calls) = report_recording(&fx);
        match evidence(&fx, &report, "rung") {
            ProvenEvidence::AyValidated => {}
            other => panic!(
                "{triple}: the kernel-ineligible s07 twin is not [VALIDATED]: {other:?}\n{}",
                explain(&report)
            ),
        }
        assert!(
            calls.is_empty(),
            "{triple}: the route was called outside `kernel_eligible`: {calls:?}"
        );
    }
}

// ===========================================================================
// s23_enum_local at O2: the closed-branch fold, then the branch split
// ===========================================================================

/// The step-(5) evidence of s23 at O2: the retry's side-conditioned evidence whose value is the
/// branch split's `KernelInstantiated`. Returns the value's label and the side-condition count.
fn folded_branch_value<'a>(fx: &Fixture, report: &'a CerReport) -> (&'a str, usize) {
    match evidence(fx, report, "rung") {
        ProvenEvidence::KernelRecheckableWithSideConditions { value, side_conditions } => {
            match &**value {
                ProvenEvidence::KernelInstantiated { theorem, original: None } => {
                    (theorem, side_conditions.len())
                }
                other => panic!(
                    "{}: s23 O2's value is not the branch split's: {other:?}\n{}",
                    fx.triple,
                    explain(report)
                ),
            }
        }
        other => panic!(
            "{}: s23 O2 is not side-conditioned evidence: {other:?}\n{}",
            fx.triple,
            explain(report)
        ),
    }
}

/// POSITIVE: s23 at O2, on both triples, is kernel-[PROVED]: the closed-branch retry folds the two
/// ground tag tests (the untaken `E::A` arm reads an unwritten payload slot) and canonicalizes the
/// spec's carrier, and the folded value (`tbz` against `x & 1 == 0`), over the bit-blast's
/// refutation limit, is the branch split's, under the retry's kernel-proved premises. The route
/// is called once, inside the retry, and proves; step (5) does not call it again. FAILS without
/// the branch split in `closed_branch::check`: measured 2026-11-14 with it stubbed to `None`
/// (mutant C1, `scripts/frozen-waivers.txt`) on aarch64-apple-darwin, where the loop stops, the
/// grade is [VALIDATED] and the calls are `[false]` (step (5)'s own call on the unfolded conj,
/// which reads memory, so the walk refuses it; the reason is read from the code).
#[test]
fn s23_o2_is_kernel_proved_through_the_fold_and_the_branch_split() {
    for triple in BOTH {
        let fx = Fixture::new(parse(S23_IR), triple, OptLevel::O2);
        let (report, calls) = report_recording(&fx);
        let c = report.certificate("rung").expect("certificate");
        assert!(c.is_kernel_proved(), "{triple}: calls {calls:?}\n{}", explain(&report));
        let (theorem, sides) = folded_branch_value(&fx, &report);
        assert_eq!(theorem, S23_O2_LABEL, "{triple}");
        assert_eq!(sides, 3, "{triple}\n{}", explain(&report));
        assert_eq!(calls, [true], "{triple}: the route's calls");
    }
}

/// MUTANTS of s23's O2 bytes on both triples, each not Proven, after the unmutated twin is
/// kernel-[PROVED]: `mov x0, #5` made `#6`; `add x0, x1, #1` made `#2`; `tbz w0, #0` made
/// `tbz w0, #1`; `tbz` made `tbnz`. Measured 2026-11-14: each is Unknown, not Refuted (ay's
/// counterexample runs only through memory, the unwritten payload slot), so these assert
/// not-Proven. ay decides each at step (4), before the retry: harness controls; the kernel's and
/// the route's refusals are the unit tests' (`s23_o2_mutants_reaching_the_branch_split_are_declined`
/// in `src/call_event/closed_branch/tests.rs`).
#[test]
fn s23_o2_mutants_are_not_proven() {
    let mut seen = Vec::new();
    for triple in BOTH {
        let fx = Fixture::new(parse(S23_IR), triple, OptLevel::O2);
        assert!(fx.report().certificate("rung").expect("rung").is_kernel_proved(), "{triple}");
        for (what, from, to) in [
            ("mov x0, #5 -> #6", 0xd280_00a0, 0xd280_00c0),
            ("add x0, x1, #1 -> #2", 0x9100_0420, 0x9100_0820),
            ("tbz w0, #0 -> #1", 0x3600_0200, 0x3608_0200),
            ("tbz -> tbnz", 0x3600_0200, 0x3700_0200),
        ] {
            let (at, _) = the_one(&fx, what, |w| w == from);
            let m = fx.patched(|o| patch_word(o, at, to));
            let report =
                m.verify().unwrap_or_else(|e| panic!("{triple}: {what}: object refused: {e}"));
            let c = report.certificate("rung").expect("rung");
            assert!(
                !c.verdict.is_proven(),
                "{triple}: MUTANT `{what}` of s23 O2 was PROVEN\n{}\n{}",
                explain(&report),
                disassemble(&m.object)
            );
            seen.push(format!("s23 O2 {triple} {what}: {}: {:?}", c.grade, c.verdict));
        }
    }
    assert_eq!(seen.len(), 2 * 4, "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

/// KERNEL-INELIGIBLE TWIN of s23 at O2: a dead `u16` shift gives the spec a side condition, so
/// step (5), and with it the retry and its branch split, is not reached. The twin stays
/// [VALIDATED] (`AyValidated`) with the route never called.
#[test]
fn s23_o2_kernel_ineligible_twin_never_reaches_the_route() {
    let ineligible = with_dead_u16_shift(S23_IR, "bb0(%0: u64):\n", 15);
    for triple in BOTH {
        let fx = Fixture::new(parse(&ineligible), triple, OptLevel::O2);
        let (report, calls) = report_recording(&fx);
        match evidence(&fx, &report, "rung") {
            ProvenEvidence::AyValidated => {}
            other => panic!(
                "{triple}: the kernel-ineligible s23 twin is not [VALIDATED]: {other:?}\n{}",
                explain(&report)
            ),
        }
        assert!(
            calls.is_empty(),
            "{triple}: the route was called outside `kernel_eligible`: {calls:?}"
        );
    }
}

// ===========================================================================
// s10_signed: the signed flags, the arithmetic shift and the sign extension
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung s10
/// (`tests/trust-f1-ladder/micro/s10_signed.rs`: `h(a: i64) -> i64 { if a < 100 { a - 200 }
/// else { a >> 2 } }`, called through `rung(x: u64) -> u64`), as the s05 rung's dump is taken,
/// with the `#loc` comments and the `target` line dropped. The shift amount is the lane's
/// `sext(2) & 63`.
const S10_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s10_signed.rs"

functy.0 = (i64) -> (i64)

functy.1 = (u64) -> (u64)

rustcc fn @_RNvCs7Vb4zyVTiud_4rung1h(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "h"
    ; #names: %0="a"
bb0(%0: i64):
    %2 = const i64 100
    %3 = icmp slt i64 %0, %2
    condbr %3, bb1, bb2
bb1:
    %4 = const i64 200
    %5 = sub i64 %0, %4
    br bb3(%5)
bb2:
    %6 = const i32 2
    %7 = const i64 63
    %8 = sext i32 %6 to i64
    %9 = and i64 %8, %7
    %10 = ashr i64 %0, %9
    br bb3(%10)
bb3(%1: i64):
    ret %1
}

fn @rung(functy.1) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = bitcast u64 %0 to i64
    %2 = call @func.0(%1)
    %3 = bitcast i64 %2 to u64
    ret %3
}
"#;

/// s10's callee `h`, by its mangled symbol.
const S10_H: &str = "_RNvCs7Vb4zyVTiud_4rung1h";

/// The signed flag bridge every s10 label names.
const SLT_FLAGS: &str = "Trust.BVB.slt_flags";

/// s10's label, measured (2026-11-14; the same for `h` at O0 and O2 and for the inlined `rung`
/// at O2, and on the captured conjs in `branch_split/tests.rs`): the signed flag bridge
/// `slt_flags`, the arm selection, the zero-wrapper strip (`bvf_or_cong` over `bvf_or_zero_id`),
/// `bvf_sub_cong` and `bvf_and_cong` over the arms and the amount, and `bvf_ashr_cong`, the
/// shift-amount fold to `Const 2`.
const S10_LABEL: &str = "Clean.BVC.bvf_and_cong+Clean.BVC.bvf_ashr_cong+Clean.BVC.bvf_or_cong+\
                         Clean.BVC.bvf_or_zero_id+Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+\
                         Trust.BVB.ite_false+Trust.BVB.ite_true+Trust.BVB.slt_flags+kernel atom \
                         case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

const LT: u32 = 11;
const LE: u32 = 13;

/// The one word of `symbol` matching `pred` (`what` names it), asserted unique.
#[track_caller]
fn the_one_in(fx: &Fixture, symbol: &str, what: &str, pred: impl Fn(u32) -> bool) -> (u64, u32) {
    let hits: Vec<(u64, u32)> =
        function_words(&fx.object, symbol).into_iter().filter(|(_, w)| pred(*w)).collect();
    assert_eq!(
        hits.len(),
        1,
        "{}: exactly one `{what}` expected in `{symbol}`\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    hits[0]
}

/// `sub Xd, Xn, #imm` (64-bit, unshifted immediate, flags not set).
fn is_sub_imm(w: u32, imm: u32) -> bool {
    w & 0xffc0_0000 == 0xd100_0000 && (w >> 10) & 0xfff == imm
}

/// `asrv Xd, Xn, Xm` (`asr` by a register).
fn is_asrv(w: u32) -> bool {
    w & 0xffe0_fc00 == 0x9ac0_2800
}

/// POSITIVE: s10 at O0 and O2, on both triples: `h` is kernel-[PROVED] by the branch split
/// through the signed flag bridge (`b.lt`'s `N != V` after `cmp x0, #100` against the spec's
/// `a <s 100`), the arithmetic-shift arm (the machine's `asr` by `sxtw(2) & 63` at O0, by
/// `#2` at O2, against the spec's `sext(2) & 63`, both folded to `Const 2`) and the zero
/// wrappers. At O2 `rung` inlines `h` and is kernel-[PROVED] the same way. FAILS without the
/// route's signed admission: measured 2026-11-14 with the route before this change (a local probe
/// of this IR on aarch64-apple-darwin), the calls were `[false]` at O0 and `[false, false]` at
/// O2, the grade [VALIDATED] (`AyValidated`), the decline "branch: a side is outside the width
/// walk".
#[test]
fn s10_signed_is_kernel_proved_by_the_branch_split() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S10_IR, triple, opt);
            let (report, calls) = report_recording(&fx);
            assert_branch_proved(&fx, &report, S10_H, Some(SLT_FLAGS));
            let mut labels = vec![label(&fx, &report, S10_H).to_string()];
            if opt == OptLevel::O2 {
                assert_branch_proved(&fx, &report, "rung", Some(SLT_FLAGS));
                labels.push(label(&fx, &report, "rung").to_string());
                assert_eq!(calls, [true, true], "{triple} {opt:?}: the route's calls");
            } else {
                assert_eq!(calls, [true], "{triple} {opt:?}: the route's calls");
            }
            for l in &labels {
                assert_eq!(l, S10_LABEL, "{triple} {opt:?}");
            }
            seen.push(format!("{triple} {opt:?}: {labels:?}"));
        }
    }
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

/// PRECISION PIN: s10's `cmp x0, #100; b.lt` made `cmp x0, #99; b.le`, at O0 and O2 on both
/// triples. `x <= 99` is `x < 100`, so ay proves `h` [VALIDATED]: Proven, never Refuted. The
/// route is called for `h` and declines. Measured 2026-11-14 (`TRUST_GATE_TRACE=1`, each of the
/// four): "the arms of a case differ". `b.le` is `Z | N != V`; the flag bridge rewrites its
/// `N != V` to `bvSLtReal x 99`, but the machine's atoms (`x - 99 == 0`, `x <s 99`) are not the
/// spec's (`x <s 100`), and the split, which does no infeasible-path reasoning (DECISION_QUEUE
/// BRANCH-SPLIT-1 "Revisit when"), meets cases no input reaches (`x <s 100` with both machine
/// atoms false) where the arms differ. At O2 `rung` (its own inlined copy, unpatched) stays
/// kernel-[PROVED], so the calls are `[false, true]`. Flip this pin when that reasoning lands.
#[test]
fn s10_cmp_99_le_is_an_equivalent_twin_the_route_declines() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S10_IR, triple, opt);
            let (cmp_at, cmp) = the_one_in(&fx, S10_H, "cmp x0, #100", |w| is_subs_imm(w, 100));
            let (lt_at, lt) = the_one_in(&fx, S10_H, "b.lt", |w| cond_of(w) == Some(LT));
            let twin = fx.patched(|o| {
                patch_word(o, cmp_at, with_imm12(cmp, 99));
                patch_word(o, lt_at, with_cond(lt, LE));
            });
            let (report, calls) = report_recording(&twin);
            let c = report.certificate(S10_H).expect("certificate");
            assert!(
                c.verdict.is_proven()
                    && !c.is_kernel_proved()
                    && !matches!(
                        &c.verdict,
                        OutputVerdict::Proven {
                            evidence: ProvenEvidence::KernelInstantiated { .. }
                        }
                    ),
                "{triple} {opt:?}: `cmp #99; b.le` is not Proven at [VALIDATED] (flip this pin if \
                 the route now proves it)\n{}",
                explain(&report)
            );
            if opt == OptLevel::O2 {
                assert_branch_proved(&twin, &report, "rung", Some(SLT_FLAGS));
                // The order is pinned: `h`'s call declines first, then `rung`'s proves
                // (measured 2026-11-14 on both triples, `TRUST_GATE_TRACE=1`).
                assert_eq!(calls, [false, true], "{triple} {opt:?}: the route's calls");
            } else {
                assert_eq!(calls, [false], "{triple} {opt:?}: the route's calls");
            }
            seen.push(format!("{triple} {opt:?}: {}: {:?} calls {calls:?}", c.grade, c.verdict));
        }
    }
    assert_eq!(seen.len(), 2 * 2, "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}

/// MUTANTS of s10's `h`, at O0 and O2 on both triples, each Refuted, after the unmutated twin is
/// kernel-[PROVED]. Bytes: `b.lt` made `b.le` (x = 100 takes the subtraction); `cmp x0, #100`
/// made `#101` (x = 100 likewise); `sub x1, x0, #200` made `#201`; `asr` made `lsl` (by the same
/// register). IR, against the original bytes: `slt` made `sle`; `200` made `201`. (`asr` made
/// `lsr` is not among them: under `x >= 100` the two agree.) ay refutes each at step (4), before
/// the route runs: harness controls; the kernel's refusals are the unit tests'
/// (`s10_signed_is_proved_and_its_mutants_are_refused_by_the_kernel`).
#[test]
fn s10_mutants_are_refuted() {
    let mut seen = Vec::new();
    for triple in BOTH {
        for opt in OPTS {
            let fx = producer_fixture(S10_IR, triple, opt);
            assert_branch_proved(&fx, &fx.report(), S10_H, Some(SLT_FLAGS));
            let mut refuted = |m: &Fixture, what: &str| {
                let got = assert_refuted(m, S10_H, &format!("s10 {opt:?} {what}"));
                seen.push(format!("s10 {triple} {opt:?} {what}: {got}"));
            };
            let (at, w) = the_one_in(&fx, S10_H, "b.lt", |w| cond_of(w) == Some(LT));
            refuted(&fx.patched(|o| patch_word(o, at, with_cond(w, LE))), "b.lt -> b.le");
            let (at, w) = the_one_in(&fx, S10_H, "cmp x0, #100", |w| is_subs_imm(w, 100));
            refuted(&fx.patched(|o| patch_word(o, at, with_imm12(w, 101))), "cmp #100 -> #101");
            let (at, w) = the_one_in(&fx, S10_H, "sub x1, x0, #200", |w| is_sub_imm(w, 200));
            refuted(&fx.patched(|o| patch_word(o, at, with_imm12(w, 201))), "sub #200 -> #201");
            let (at, w) = the_one_in(&fx, S10_H, "asr", is_asrv);
            refuted(&fx.patched(|o| patch_word(o, at, w & !(0x3 << 10))), "asr -> lsl");
            let sle = replace_once(S10_IR, "icmp slt", "icmp sle");
            refuted(&against(&fx, &sle), "IR a < 100 -> a <= 100");
            let k201 = replace_once(S10_IR, "%4 = const i64 200", "%4 = const i64 201");
            refuted(&against(&fx, &k201), "IR a - 200 -> a - 201");
        }
    }
    assert_eq!(seen.len(), 2 * 2 * 6, "{seen:#?}");
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("{seen:#?}");
    }
}
