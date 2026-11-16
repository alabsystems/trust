// tests/additive_cancel_gate.rs — the call-event gate over ladder rung r08_overflow at O2, proved
// through the kernel-checked additive cancellation `Trust.BVA.add_sub_cancel`
// (`verify_output_instantiate/cancel.rs`, DECISION_QUEUE CANCEL-1).
//
// r08 is `let big = u64::MAX - 1000; let y = big + x; y - big + 1`. At O2 trust-cg folds it to
// `x + 1` (docs/STATUS.md, the F1 ladder's O2 row), while the producer IR the gate reads keeps
// `((big + x) - big) + 1` with `big` the SSA value `MAX - 1000`, used twice. Without the cancel
// route the obligation is [VALIDATED]: no wrapper strip, operand order or strength rewrite joins
// `(c + x) - c` to `x`, and ay's bit-blast refutation of the add/sub chain is over the re-check
// limit (11,361 steps at 64 bits and 4,281 at 32, against 2,048; the unit test
// `cancel::tests::r08_is_validated_without_the_cancel_route`).
//
// POSITIVE: r08 at O2, on both object formats, is kernel-[PROVED] as `KernelInstantiated` with
// exactly the cancel label, its object is one `add` (immediate 1) and a `ret`, and the branch
// split (which step (5) runs after this route declines) is never called. The same holds for its
// `u32` twin (one 32-bit `add` and a `ret`), the 32-bit width the step is offered at.
//
// MUTANTS: the object's `add #1` made `#2` (at 64 and at 32 bits), and the producer IR with `big`
// off by one on the subtracted side (the object compiled from the unmutated IR). None is ever
// `KernelInstantiated`; each is Refuted, with its unmutated twin kernel-[PROVED] in the same test so
// a mutant cannot pass by the harness being broken. Each changes the function's value on some
// input, so ay refutes it at step (4), before the step-(5) kernel retry where the cancel route
// runs: these mutants do not exercise the route. The evidence that the KERNEL refuses a wrong
// cancellation is the route's unit tests with the filter off (`cancel.rs`,
// `wrong_cancellations_are_rejected_by_the_kernel` and
// `forged_instances_fail_in_the_kernel`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Compiled only with `kernel-recheck` (which implies `ay-proofs`) and `test-hooks`: the positive
// asserts the clean kernel's [PROVED] grade, which no other build can award, and reads the branch
// split's calls through the `test-hooks` recorder. Run: `targo --unverified test -p
// trust-cg-bridge --features kernel-recheck,test-hooks --test additive_cancel_gate`.
#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::CerReport;
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_instantiate::record_branch_split_calls;
use trust_cg_codegen::pipeline::OptLevel;

/// The label of an obligation the cancel route proves with one cancellation and nothing else
/// (`cancel::label`).
const CANCEL_LABEL: &str =
    "Trust.BVA.add_sub_cancel+Clean.BVC congruence (O(1) add@N, additive cancellation)";

/// The producer's own `-Ztrust-dump=ir:` text for ladder rung r08
/// (`tests/trust-f1-ladder/programs/r08_overflow.rs`), with the `#loc` and `#scope` comments and
/// the `target` and `file` lines dropped so [`targeted`] stamps each triple.
const R08_IR: &str = r#"; TrustIr text format v1
module "rung"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = const u64 18446744073709551615
    %2 = const u64 1000
    %3 = sub u64 %1, %2
    %4 = add u64 %3, %0
    %5 = sub u64 %4, %3
    %6 = const u64 1
    %7 = add u64 %5, %6
    ret %7
}
"#;

/// r08 on `u32` (`let big = u32::MAX - 1000; let y = big + x; y - big + 1`), written as the
/// producer writes a `u32` body (cf. s09's `h` in `strength_reduced_gate.rs`): the shape of the
/// 32-bit width the cancel step is offered at, with the W-register readout trust-cg's `u32`
/// objects produce.
const R08_U32_IR: &str = r#"; TrustIr text format v1
module "rung"

functy.0 = (u32) -> (u32)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u32):
    %1 = const u32 4294967295
    %2 = const u32 1000
    %3 = sub u32 %1, %2
    %4 = add u32 %3, %0
    %5 = sub u32 %4, %3
    %6 = const u32 1
    %7 = add u32 %5, %6
    ret %7
}
"#;

/// `ret` (to `x30`).
const RET: u32 = 0xd65f_03c0;

/// `add Xd, Xn, #imm12` (64-bit ADD immediate, no flags, either `sh`).
fn is_add_imm_x(w: u32) -> bool {
    w & 0xff80_0000 == 0x9100_0000
}

/// `add Wd, Wn, #imm12` (32-bit ADD immediate, no flags, either `sh`).
fn is_add_imm_w(w: u32) -> bool {
    w & 0xff80_0000 == 0x1100_0000
}

/// The ADD immediate's `imm12` and `sh` fields.
fn add_imm_fields(w: u32) -> (u32, u32) {
    ((w >> 10) & 0xfff, (w >> 22) & 1)
}

fn parse(text: &str) -> trust_ir::Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

/// The gate's fixture: bytes from `codegen` compiled under the fixture license with the
/// producer's own body-gate authority recognized, and `producer` as the IR the gate reads.
fn fixture(producer: &str, codegen: &str, triple: &str) -> Fixture {
    let license = fixture_license().with_recognized_authority("trust-direct-lane-structural");
    let object = compile_under(&parse(codegen), triple, OptLevel::O2, license)
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"));
    Fixture::with_object(targeted(&parse(producer), triple), object, triple)
}

/// r08 at O2: exactly one instruction besides `ret`, an `add` immediate of 1 (no `sub`, no
/// constant materialised). Returns the `add`'s offset and word.
fn r08_fixture(triple: &str) -> (Fixture, (u64, u32)) {
    r08_fixture_of(R08_IR, is_add_imm_x, triple)
}

/// [`r08_fixture`] for `ir`, the `add` recognised by `is_add`.
fn r08_fixture_of(ir: &str, is_add: fn(u32) -> bool, triple: &str) -> (Fixture, (u64, u32)) {
    let fx = fixture(ir, ir, triple);
    let words = function_words(&fx.object, "rung");
    let rets = words.iter().filter(|(_, w)| *w == RET).count();
    let adds: Vec<(u64, u32)> = words.iter().copied().filter(|(_, w)| is_add(*w)).collect();
    assert!(
        words.len() == 2 && rets == 1 && adds.len() == 1,
        "{triple}: r08 at O2 is not one `add` immediate and a `ret`\n{}",
        disassemble(&fx.object)
    );
    assert_eq!(add_imm_fields(adds[0].1), (1, 0), "{triple}: the add's immediate");
    (fx, adds[0])
}

/// The certificate's evidence, when it is a kernel instantiation.
fn instantiation(report: &CerReport, symbol: &str) -> Option<String> {
    match &report.certificate(symbol).expect("certificate").verdict {
        OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { theorem, .. } } => {
            Some(theorem.clone())
        }
        _ => None,
    }
}

#[track_caller]
fn assert_cancel_proved(fx: &Fixture, report: &CerReport) {
    let c = report.certificate("rung").expect("certificate");
    assert!(
        c.is_kernel_proved(),
        "{}: `rung` is not kernel-[PROVED]\n{}\n{}",
        fx.triple,
        explain(report),
        disassemble(&fx.object)
    );
    assert_eq!(
        instantiation(report, "rung").as_deref(),
        Some(CANCEL_LABEL),
        "{}: `rung`'s evidence\n{}",
        fx.triple,
        explain(report)
    );
}

#[track_caller]
fn assert_never_instantiated(fx: &Fixture, what: &str) {
    let report = fx.report();
    let c = report.certificate("rung").expect("certificate");
    assert_eq!(
        instantiation(&report, "rung"),
        None,
        "{}: MUTANT `{what}` is KernelInstantiated\n{}",
        fx.triple,
        explain(&report)
    );
    assert!(
        matches!(c.verdict, OutputVerdict::Refuted { .. }),
        "{}: MUTANT `{what}` is not Refuted: {:?}\n{}\n{}",
        fx.triple,
        c.verdict,
        explain(&report),
        disassemble(&fx.object)
    );
}

// ===========================================================================
// the exit test
// ===========================================================================

/// POSITIVE (CANCEL-1 exit test): r08 at O2 is kernel-[PROVED] through `add_sub_cancel` on both
/// triples, and step (5) never reaches the branch split. Without the cancel route the grade is
/// [VALIDATED] (`cancel::tests::r08_is_validated_without_the_cancel_route`).
#[test]
fn r08_overflow_folded_to_add_one_is_kernel_proved() {
    for triple in BOTH {
        let (fx, _) = r08_fixture(triple);
        let (report, calls) = record_branch_split_calls(|| fx.report());
        assert_cancel_proved(&fx, &report);
        assert!(calls.is_empty(), "{triple}: the branch split was called: {calls:?}");
    }
}

/// POSITIVE: r08 on `u32` at O2, on both triples, folds to one 32-bit `add` immediate of 1 and is
/// kernel-[PROVED] with exactly the cancel label: the 32-bit cancel step on a real object and its
/// W-register readout, not only on the unit tests' synthetic extract.
#[test]
fn r08_u32_folded_to_add_one_is_kernel_proved() {
    for triple in BOTH {
        let (fx, _) = r08_fixture_of(R08_U32_IR, is_add_imm_w, triple);
        let (report, calls) = record_branch_split_calls(|| fx.report());
        assert_cancel_proved(&fx, &report);
        assert!(calls.is_empty(), "{triple}: the branch split was called: {calls:?}");
    }
}

/// MUTANT: r08 on `u32` with its `add w0, w0, #1` made `#2`.
#[test]
fn mutant_r08_u32_add_two_is_never_kernel_instantiated() {
    for triple in BOTH {
        let (fx, (at, w)) = r08_fixture_of(R08_U32_IR, is_add_imm_w, triple);
        assert_cancel_proved(&fx, &fx.report());
        let m = fx.patched(|o| patch_word(o, at, (w & !(0xfff << 10)) | (2 << 10)));
        assert_never_instantiated(&m, "u32: x + 1 specified, x + 2 computed");
    }
}

// ===========================================================================
// mutants
// ===========================================================================

/// MUTANT: `add x0, x0, #1` made `#2`, so the object computes `x + 2`.
#[test]
fn mutant_r08_add_two_is_never_kernel_instantiated() {
    for triple in BOTH {
        let (fx, (at, w)) = r08_fixture(triple);
        assert_cancel_proved(&fx, &fx.report());
        let m = fx.patched(|o| patch_word(o, at, (w & !(0xfff << 10)) | (2 << 10)));
        assert_never_instantiated(&m, "x + 1 specified, x + 2 computed");
    }
}

/// MUTANT: the producer IR subtracts `big + 1` (`MAX - 999`) where it added `big`, so it
/// specifies `x`, while the object (from the unmutated IR) computes `x + 1`.
#[test]
fn mutant_r08_big_off_by_one_is_never_kernel_instantiated() {
    let mutant = R08_IR.replace(
        "    %5 = sub u64 %4, %3\n    %6 = const u64 1\n    %7 = add u64 %5, %6\n    ret %7\n",
        "    %5 = const u64 999\n    %6 = sub u64 %1, %5\n    %7 = sub u64 %4, %6\n    \
         %8 = const u64 1\n    %9 = add u64 %7, %8\n    ret %9\n",
    );
    assert_ne!(mutant, R08_IR, "the mutation applied");
    for triple in BOTH {
        let (fx, _) = r08_fixture(triple);
        assert_cancel_proved(&fx, &fx.report());
        let m = fixture(&mutant, R08_IR, triple);
        assert_never_instantiated(&m, "(big + x) - (big + 1) + 1 specified, x + 1 computed");
    }
}
