// tests/call_event_gate.rs — the call-event refinement (CER) gate over objects
// trust-cg's `Compiler::compile` ships (increment 5, step 5.2; design
// docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §5 and §8 5.2).
//
// POSITIVES: each must be kernel-[PROVED] on BOTH object formats (Mach-O for
// aarch64-apple-darwin, ELF for aarch64-unknown-linux-gnu); a conditional
// positive may be [VALIDATED], and says so. MUTANTS: each must be Refuted or
// Unknown (or refuse the object), never Proven; every mutant has an unmutated
// twin in the same test that is Proven, so a mutant cannot pass by the
// harness being broken. The withdrawn panic-tail roster below instead requires
// both the original and mutated objects to retain their complete Unknown account.
//
// Callees are External on Darwin: trust-cg refuses Internal/Private direct
// edges off AArch64 ELF until step 5.3 (design fact V4).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Compiled only with `kernel-recheck` (which implies `ay-proofs`): the
// positives assert the clean kernel's [PROVED] grade, which no other build can
// award. Run: `targo --unverified test -p trust-cg-bridge --features
// kernel-recheck,test-hooks --test call_event_gate`.
#![cfg(feature = "kernel-recheck")]

mod cer_common;

use std::sync::Arc;

use cer_common::*;
use trust_cg_bridge::call_event::{
    Assumption, CallSiteKind, CerReport, FnPlacement, Grade, ParamPlace, ProducerBody,
    ProducerModule, ReturnPlace, ScalarPlace,
};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict, ProvenEvidence};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::{CallingConv, Constant, Linkage, Module, Ty};

// ===========================================================================
// helpers
// ===========================================================================

fn kernel_proved(report: &CerReport, symbol: &str) -> bool {
    report.certificate(symbol).is_some_and(|c| c.is_kernel_proved())
}

#[track_caller]
fn assert_kernel_proved(fx: &Fixture, report: &CerReport, symbol: &str) {
    assert!(
        kernel_proved(report, symbol),
        "{}: `{symbol}` is not kernel-[PROVED]\n{}\n{}",
        fx.triple,
        explain(report),
        disassemble(&fx.object)
    );
}

/// A mutant must never be Proven: Refuted, Unknown, or the whole object refused.
#[track_caller]
fn assert_not_proven(fx: &Fixture, symbol: &str, what: &str) -> String {
    match fx.verify() {
        Err(refusal) => format!("object refused: {refusal}"),
        Ok(report) => {
            let c = report
                .certificate(symbol)
                .unwrap_or_else(|| panic!("no certificate for `{symbol}`"));
            assert!(
                !c.verdict.is_proven(),
                "{}: MUTANT `{what}` of `{symbol}` was PROVEN\n{}\n{}",
                fx.triple,
                explain(&report),
                disassemble(&fx.object)
            );
            format!("{}: {:?}", c.grade, c.verdict)
        }
    }
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

fn u64s(n: usize) -> Vec<Ty> {
    vec![Ty::U64; n]
}

/// `f(x) = g(x) + 1`, `g` an External declaration.
fn wrapper_module() -> Module {
    let mut mb = ModBuilder::new("cer_wrapper");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

// ===========================================================================
// POSITIVES
// ===========================================================================

#[test]
fn wrapper_g_plus_one_is_kernel_proved() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        let c = report.certificate("f").unwrap();
        assert_eq!(c.assumptions, vec![Assumption::External("g".into())], "{triple}");
        assert_eq!(c.call_sites.len(), 1, "{triple}");
        assert_eq!(c.call_sites[0].kind, CallSiteKind::Direct, "{triple}");
        assert_eq!(c.call_sites[0].symbol, "g");
        let reloc = c.call_sites[0].reloc.clone().expect("a relocated bl");
        assert_eq!(
            reloc,
            if triple == DARWIN { "ARM64_RELOC_BRANCH26" } else { "R_AARCH64_CALL26" }
        );
        for o in [
            &c.obligations.o0_abi,
            &c.obligations.o1_binding,
            &c.obligations.o2_pairing,
            &c.obligations.o3_events,
            &c.obligations.o4_return,
            &c.obligations.o5_frame,
        ] {
            assert_eq!(o.grade, Grade::Proven, "{triple}: {}", explain(&report));
        }
        // The certificate binds to the shipped object and records P digests.
        assert_eq!(report.object_sha256.len(), 64);
        assert!(c.placement_sha256.contains_key("f") && c.placement_sha256.contains_key("g"));
        let json = report.to_json();
        assert!(
            json.contains("trust-cg-bridge.call-refinement.v1") && json.contains("\"External\""),
            "{json}"
        );
        // `<stem>.trust-cg-certificates.json`, beside the object it binds to.
        let dir = tempfile::tempdir().expect("tempdir");
        let path = report.write_certificates(&dir.path().join("crate")).expect("write");
        assert!(path.to_string_lossy().ends_with("crate.trust-cg-certificates.json"));
        assert_eq!(std::fs::read_to_string(&path).unwrap(), json);
        assert!(json.contains(&report.object_sha256));
        report.ships(EmitPolicy::StrictProvenOnly).unwrap_or_else(|e| panic!("{triple}: {e}"));
    }
}

#[test]
fn self_and_mutual_recursion_proved() {
    let mut mb = ModBuilder::new("cer_recursion");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let rec = mb.reserve("rec", s, Linkage::External);
    let ping = mb.reserve("ping", s, Linkage::External);
    let pong = mb.reserve("pong", s, Linkage::External);
    // rec(x) = rec(x + 1) ^ 3 — the call is to the function's own symbol.
    mb.body(rec, |fb| {
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Add, Ty::U64, fb.p(0), one);
        let r = fb.call(rec, &[x1]);
        let k = fb.konst(Ty::U64, 3);
        let out = fb.bin(BinOp::Xor, Ty::U64, r, k);
        fb.ret(out);
    });
    // ping(x) = pong(x ^ 2) + 7 ; pong(x) = ping(x + 5) ^ 9
    mb.body(ping, |fb| {
        let two = fb.konst(Ty::U64, 2);
        let a = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), two);
        let r = fb.call(pong, &[a]);
        let k = fb.konst(Ty::U64, 7);
        let out = fb.bin(BinOp::Add, Ty::U64, r, k);
        fb.ret(out);
    });
    mb.body(pong, |fb| {
        let five = fb.konst(Ty::U64, 5);
        let a = fb.bin(BinOp::Add, Ty::U64, fb.p(0), five);
        let r = fb.call(ping, &[a]);
        let k = fb.konst(Ty::U64, 9);
        let out = fb.bin(BinOp::Xor, Ty::U64, r, k);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        let report = fx.report();
        for f in ["rec", "ping", "pong"] {
            assert_kernel_proved(&fx, &report, f);
        }
        // No callee body was inlined to discharge a `bl`: every site is Direct
        // and rests on the callee's OWN certificate (CoEmitted).
        let rc = report.certificate("rec").unwrap();
        assert_eq!(rc.assumptions, vec![Assumption::CoEmitted("rec".into())], "{triple}");
        assert!(rc.call_sites.iter().all(|s| s.kind == CallSiteKind::Direct));
        assert_eq!(
            report.certificate("ping").unwrap().assumptions,
            vec![Assumption::CoEmitted("pong".into())]
        );
        // The recursion SCCs close (greatest fixpoint).
        for f in ["rec", "ping", "pong"] {
            assert!(
                report.closure.closed_kernel.contains(&f.to_string()),
                "{triple}: {:?}",
                report.closure
            );
        }
        report.ships(EmitPolicy::StrictProvenOnly).unwrap_or_else(|e| panic!("{triple}: {e}"));
    }
}

/// `f(x) = g(x)` compiled by trust-cg at O2 — which emits a RELOCATED TAIL
/// CALL for it (measured: `b _g`, ARM64_RELOC_BRANCH26, on Darwin; `stp; mov
/// x29, sp; ldp; b g`, R_AARCH64_JUMP26, on Linux). The gate composes it as
/// call-then-return. `ir_adds_one` swaps the PRODUCER for `g(x) + 1` (the
/// bytes stay the same): the negative control.
fn tail_call_fixture(triple: &str, ir_adds_one: bool) -> Fixture {
    let mut mb = ModBuilder::new("cer_tail");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        fb.ret(r);
    });
    let compiled = mb.finish();
    let object = compile(&compiled, triple, OptLevel::O2);
    // Precondition: the bytes really are a tail call (no `bl`, one `b g`).
    assert!(
        bl_offsets(&object, "f").is_empty(),
        "{triple}: not a tail call\n{}",
        disassemble(&object)
    );
    let b_words: Vec<u64> = function_words(&object, "f")
        .into_iter()
        .filter(|(_, w)| is_b(*w))
        .map(|(o, _)| o)
        .collect();
    assert_eq!(b_words.len(), 1, "{triple}\n{}", disassemble(&object));
    let (_, ty, _) = reloc_at(&object, b_words[0]);
    assert_eq!(ty, if triple == DARWIN { 2 } else { 282 }, "BRANCH26 / JUMP26");
    let mut spec = ModBuilder::new("cer_tail_spec");
    let s2 = spec.sig(&u64s(1), Some(Ty::U64));
    let g2 = spec.declare("g", s2);
    spec.define("f", s2, Linkage::External, |fb| {
        let r = fb.call(g2, &[fb.p(0)]);
        if ir_adds_one {
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        } else {
            fb.ret(r);
        }
    });
    let mut fx = Fixture::with_object(compiled, object, triple);
    let spec = Arc::new(spec.finish());
    fx.producers = vec![ProducerModule::named_by_symbols(spec.clone())];
    fx.bodies.insert("f".into(), ProducerBody { producer: 0, func: spec.functions[1].id });
    fx
}

#[test]
fn relocated_tail_call_composes() {
    for triple in BOTH {
        let fx = tail_call_fixture(triple, false);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        let c = report.certificate("f").unwrap();
        assert_eq!(c.call_sites.len(), 1);
        assert_eq!(c.call_sites[0].kind, CallSiteKind::Tail, "{triple}");
        assert_eq!(
            c.call_sites[0].reloc.as_deref(),
            Some(if triple == DARWIN { "ARM64_RELOC_BRANCH26" } else { "R_AARCH64_JUMP26" })
        );
        // Teeth: the same bytes against `g(x) + 1` are a miscompile.
        assert_refuted(&tail_call_fixture(triple, true), "f", "tail call where the IR adds one");
    }
}

#[test]
fn extern_declaration_call_proved_under_external_premise() {
    let mut mb = ModBuilder::new("cer_extern");
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let ext = mb.declare("ext_sub", s2);
    // f(x, y) = ext_sub(y, x) ^ x : the arguments are swapped at the call, and
    // x must survive it.
    mb.define("f", s2, Linkage::External, |fb| {
        let r = fb.call(ext, &[fb.p(1), fb.p(0)]);
        let out = fb.bin(BinOp::Xor, Ty::U64, r, fb.p(0));
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        let c = report.certificate("f").unwrap();
        assert_eq!(c.assumptions, vec![Assumption::External("ext_sub".into())]);
        // An External callee closes the caller on the EXTERNAL-CALLEE premise.
        assert!(report.closure.closed_kernel.contains(&"f".to_string()));
    }
}

#[test]
fn two_ordered_calls_proved() {
    let mut mb = ModBuilder::new("cer_two_calls");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    let h = mb.declare("h", s);
    // f(x) = g(x) + h(x ^ 1)
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
        let c = fb.call(h, &[x1]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        let c = report.certificate("f").unwrap();
        let order: Vec<&str> = c.call_sites.iter().map(|s| s.symbol.as_str()).collect();
        assert_eq!(order, ["g", "h"], "{triple}");
        assert!(c.call_sites[0].offset < c.call_sites[1].offset);
    }
}

#[test]
fn call_under_condition_is_validated_or_proved() {
    let mut mb = ModBuilder::new("cer_cond");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    // f(x) = if x == 0 { 1 } else { g(x) }
    mb.define("f", s, Linkage::External, |fb| {
        let zero = fb.konst(Ty::U64, 0);
        let is0 = fb.icmp(ICmpOp::Eq, Ty::U64, fb.p(0), zero);
        let (then_b, _) = fb.block(&[]);
        let (else_b, _) = fb.block(&[]);
        fb.cond_br(is0, then_b, &[], else_b, &[]);
        fb.switch_to(then_b);
        let one = fb.konst(Ty::U64, 1);
        fb.ret(one);
        fb.switch_to(else_b);
        let r = fb.call(g, &[fb.p(0)]);
        fb.ret(r);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        let report = fx.report();
        let c = report.certificate("f").unwrap();
        assert!(
            c.verdict.is_proven(),
            "{triple}: conditional call not Proven\n{}\n{}",
            explain(&report),
            disassemble(&fx.object)
        );
        // Disclosed: which grade the conditional site reached.
        eprintln!("call_under_condition [{triple}]: {}", c.grade);
    }
}

#[test]
fn opt4_inlined_leaf_is_interpreted_from_callee_ir() {
    let mut mb = ModBuilder::new("cer_opt4");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    // A pure single-block leaf trust-cg's OPT-4 splices at O1+.
    let leaf = mb.define("leaf", s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x55);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(leaf, &[fb.p(0)]);
        let k = fb.konst(Ty::U64, 3);
        let out = fb.bin(BinOp::Add, Ty::U64, r, k);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        // Precondition: trust-cg really inlined it (no `bl` left in `f`).
        assert!(
            bl_offsets(&fx.object, "f").is_empty(),
            "{triple}: OPT-4 did not inline\n{}",
            disassemble(&fx.object)
        );
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        assert_kernel_proved(&fx, &report, "leaf");
        let c = report.certificate("f").unwrap();
        assert_eq!(c.call_sites.len(), 1);
        assert_eq!(c.call_sites[0].kind, CallSiteKind::InterpretedInline, "{triple}");
        assert!(
            c.assumptions.is_empty(),
            "an interpreted site rests on no premise: {:?}",
            c.assumptions
        );
    }
}

/// `f(x, y) = { assert(y != 0); g(x) ^ y }`, its assert spelled `assert` (None: no assert at
/// all, the twin trust-cg compiles).
fn assert_guarded_call_module(
    assert: Option<(trust_ir::AssertKind, Option<trust_ir::PanicSite>)>,
) -> Module {
    let mut mb = ModBuilder::new("cer_assert");
    let s1 = mb.sig(&u64s(1), Some(Ty::U64));
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let g = mb.declare("g", s1);
    mb.define("f", s2, Linkage::External, |fb| {
        if let Some((kind, site)) = assert {
            let zero = fb.konst(Ty::U64, 0);
            let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(1), zero);
            fb.push_inst_void(trust_ir::inst::Inst::Assert { cond: ok, kind, site });
        }
        let r = fb.call(g, &[fb.p(0)]);
        let out = fb.bin(BinOp::Xor, Ty::U64, r, fb.p(1));
        fb.ret(out);
    });
    mb.finish()
}

/// An IR `Assert` before a call. Until the train that pins trust-cg `7ace0c56` (trust-ir v57)
/// trust-cg lowered its failure path to a bare `brk` tail, which the gate read as divergence on
/// the machine side exactly where the IR's guard fails, and this test proved `f`. trust-cg no
/// longer compiles such a module at all: a kindless (`Unspecified`, pre-v52) assert is refused at
/// its admission floor (`require_assert_panic_kinds`), and a KINDED one is refused because its
/// faithful lowering is a call of the kind's panic entry with the site's location and panic-hook
/// behaviour, never a generic trap. So no `Assert`-bearing object reaches this gate; pinned here
/// so a trust-cg that starts compiling one again is noticed (and this test restored to the
/// divergence check). Compiled as `cer_common::compile` compiles (targeted, under the fixture
/// license): under trust-cg's default license the claim-less body is refused by its license
/// before either assert rule is reached.
#[test]
fn assert_guarded_call_never_reaches_the_gate() {
    let spec = |triple: &str| trust_cg_codegen::target::TargetSpec::parse(triple).expect("triple");
    for triple in BOTH {
        for (assert, needle) in [
            ((trust_ir::AssertKind::Unspecified, None), "require_assert_panic_kinds"),
            ((trust_ir::AssertKind::DivByZero, None), "TCG-ASSERT-PANIC"),
        ] {
            let module = targeted(&assert_guarded_call_module(Some(assert)), triple);
            let config = trust_cg_codegen::CompilerConfig {
                opt_level: OptLevel::O2,
                parallel: false,
                ..Default::default()
            };
            let err = trust_cg_codegen::Compiler::new_for_target_spec(config, spec(triple))
                .with_codegen_license(fixture_license())
                .compile(&module)
                .err()
                .unwrap_or_else(|| panic!("{triple}: trust-cg compiled an unsited assert"));
            assert!(err.to_string().contains(needle), "{triple}: {err}");
        }
    }
}

/// Trust (trust-ir v54): a SITED assert's failure calls its panic entry, which the gate's IR
/// model does not have. trust-cg compiles no assert-bearing module (above), so the object is
/// the assert-free twin's; paired with the module whose assert names a site, the IR side
/// refuses the instruction instead of reading it as a divergence, and `f` is never Proven.
#[test]
fn a_sited_assert_is_never_proven() {
    let twin = assert_guarded_call_module(None);
    let entry = twin.functions.iter().find(|f| f.name == "g").expect("g").id;
    let site = trust_ir::PanicSite {
        entry,
        location: trust_ir::PanicLocation::Value(trust_ir::ValueId::new(0)),
    };
    let sited = assert_guarded_call_module(Some((trust_ir::AssertKind::DivByZero, Some(site))));
    for triple in BOTH {
        let object = Fixture::new(twin.clone(), triple, OptLevel::O2).object;
        let report = Fixture::with_object(sited.clone(), object, triple).report();
        let c = report.certificate("f").expect("f");
        let why = explain(&report);
        assert!(!c.verdict.is_proven(), "{triple}: a sited assert must not be Proven\n{why}");
        assert!(why.contains("`Assert` is outside the modeled fragment"), "{triple}: {why}");
    }
}

/// `f(x, y) = { assert(cond(y)); x OP y }` with the assert UNSITED (the producer's spelling of
/// every runtime check, which is the specification the compiler lane's gate reads), or the
/// assert-free twin trust-cg compiles when `cond` is None. No call follows the check, so no
/// call event can see whether it held.
fn unsited_check_module(cond: Option<(ICmpOp, i128)>, op: BinOp) -> Module {
    let mut mb = ModBuilder::new("cer_unsited_check");
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    mb.define("f", s2, Linkage::External, |fb| {
        if let Some((cmp, k)) = cond {
            let k = fb.konst(Ty::U64, k);
            let ok = fb.icmp(cmp, Ty::U64, fb.p(1), k);
            fb.push_inst_void(trust_ir::inst::Inst::Assert {
                cond: ok,
                kind: trust_ir::AssertKind::DivByZero,
                site: None,
            });
        }
        let out = fb.bin(op, Ty::U64, fb.p(0), fb.p(1));
        fb.ret(out);
    });
    mb.finish()
}

/// SOUNDNESS (2026-11-13): bytes that DROP a check that can fail are never Proven. On the
/// compiler lane the gate reads the producer body, whose every runtime check is an unsited
/// `Assert`, against bytes compiled from the codegen module, where PKG-CP has folded or sited
/// it. A failing unsited check only drops the execution from `spec_reach`, and O4 states
/// `spec_reach ⇒ machine_reach` alone, so before this rule bytes that RETURN where Rust panics
/// (here `x ^ y` with no test of `y`, and `x / y`, which the machine evaluates to 0 at `y = 0`)
/// discharged every item and graded [PROVED]. Paired with the twin object, `f` is Unknown at
/// O4, naming the check.
#[test]
fn a_check_that_can_fail_is_not_proven_against_bytes_without_it() {
    for op in [BinOp::Xor, BinOp::UDiv] {
        let twin = unsited_check_module(None, op);
        let checked = unsited_check_module(Some((ICmpOp::Ne, 0)), op);
        for triple in BOTH {
            let object = Fixture::new(twin.clone(), triple, OptLevel::O2).object;
            let fx = Fixture::with_object(checked.clone(), object, triple);
            // Neither grade: `is_proven` covers [PROVED] and [VALIDATED].
            assert_not_proven(&fx, "f", "a check that can fail, dropped");
            let why = explain(&fx.report());
            assert!(
                why.contains("the unsited check at bb0[2] can fail on a reached path"),
                "{triple} {op:?}: {why}"
            );
        }
    }
}

/// The controls: a check that cannot fail costs nothing. Against the same assert-free bytes,
/// `3 != 0` (two known integers: the shape PKG-CP folds on the codegen module while the producer
/// keeps it) and `y >= 0` unsigned (true on every input, but not folded) leave `f` kernel-[PROVED]:
/// the check joins the kernel conjunction as `fail == 0`, so the grade never rests on ay alone.
#[test]
fn a_check_that_cannot_fail_keeps_the_proof() {
    let twin = unsited_check_module(None, BinOp::Xor);
    let constant = {
        let mut mb = ModBuilder::new("cer_unsited_check");
        let s2 = mb.sig(&u64s(2), Some(Ty::U64));
        mb.define("f", s2, Linkage::External, |fb| {
            let three = fb.konst(Ty::U64, 3);
            let zero = fb.konst(Ty::U64, 0);
            let ok = fb.icmp(ICmpOp::Ne, Ty::U64, three, zero);
            fb.push_inst_void(Inst::Assert {
                cond: ok,
                kind: trust_ir::AssertKind::DivByZero,
                site: None,
            });
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
            fb.ret(out);
        });
        mb.finish()
    };
    let total = unsited_check_module(Some((ICmpOp::Uge, 0)), BinOp::Xor);
    for triple in BOTH {
        let object = Fixture::new(twin.clone(), triple, OptLevel::O2).object;
        for checked in [&constant, &total] {
            let fx = Fixture::with_object(checked.clone(), object.clone(), triple);
            assert_kernel_proved(&fx, &fx.report(), "f");
        }
    }
}

/// The failure predicate carries the path that reaches the check: `if y != 0 { assert(y != 0);
/// x ^ y } else { 0 }` cannot fail, although its check alone could, so against the assert-free
/// twin's bytes `f` is Proven (the branch keeps it at either grade today) and never Unknown at
/// the check.
#[test]
fn a_check_guarded_by_its_path_cannot_fail() {
    let build = |checked: bool| {
        let mut mb = ModBuilder::new("cer_guarded_check");
        let s2 = mb.sig(&u64s(2), Some(Ty::U64));
        mb.define("f", s2, Linkage::External, |fb| {
            let zero = fb.konst(Ty::U64, 0);
            let nz = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(1), zero);
            let (then_b, _) = fb.block(&[]);
            let (else_b, _) = fb.block(&[]);
            fb.cond_br(nz, then_b, &[], else_b, &[]);
            fb.switch_to(then_b);
            if checked {
                let zero = fb.konst(Ty::U64, 0);
                let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(1), zero);
                fb.push_inst_void(Inst::Assert {
                    cond: ok,
                    kind: trust_ir::AssertKind::DivByZero,
                    site: None,
                });
            }
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
            fb.ret(out);
            fb.switch_to(else_b);
            let zero = fb.konst(Ty::U64, 0);
            fb.ret(zero);
        });
        mb.finish()
    };
    let (twin, checked) = (build(false), build(true));
    for triple in BOTH {
        let object = Fixture::new(twin.clone(), triple, OptLevel::O2).object;
        let report = Fixture::with_object(checked.clone(), object, triple).report();
        let c = report.certificate("f").expect("f");
        assert!(c.verdict.is_proven(), "{triple}: {}", explain(&report));
    }
}

/// A miscompile inside the check's domain is still REFUTED, not hidden behind the check: `assert(y
/// != 0); x / y` against bytes that compute `x + y` differs at `y = 1`, a reached execution, so the
/// value item's counterexample stands (the check is decided after the items).
#[test]
fn a_wrong_result_where_the_check_holds_is_refuted() {
    let wrong = unsited_check_module(None, BinOp::Add);
    let checked = unsited_check_module(Some((ICmpOp::Ne, 0)), BinOp::UDiv);
    for triple in BOTH {
        let object = Fixture::new(wrong.clone(), triple, OptLevel::O2).object;
        let fx = Fixture::with_object(checked.clone(), object, triple);
        assert_refuted(&fx, "f", "x + y for a checked x / y");
    }
}

/// `if x < 10 { body } else { unreachable }` in the current block, continuing in the `then` block.
fn below_ten(fb: &mut FnBody, else_arm: impl FnOnce(&mut FnBody)) {
    let ten = fb.konst(Ty::U64, 10);
    let small = fb.icmp(ICmpOp::Ult, Ty::U64, fb.p(0), ten);
    let (then_b, _) = fb.block(&[]);
    let (else_b, _) = fb.block(&[]);
    fb.cond_br(small, then_b, &[], else_b, &[]);
    fb.switch_to(else_b);
    else_arm(fb);
    fb.push_inst_void(Inst::Unreachable);
    fb.switch_to(then_b);
}

/// `assert(p(arg) cmp k)`, unsited.
fn check(fb: &mut FnBody, arg: usize, cmp: ICmpOp, k: i128) {
    let k = fb.konst(Ty::U64, k);
    let ok = fb.icmp(cmp, Ty::U64, fb.p(arg), k);
    fb.push_inst_void(Inst::Assert { cond: ok, kind: trust_ir::AssertKind::DivByZero, site: None });
}

/// `switch x { 0 => x ^ y, 1 => [check y != 0;] y, _ => unreachable }`, returning from each arm.
fn switch_leaf(
    fb: &mut FnBody,
    checked: bool,
    tail: impl Fn(&mut FnBody, trust_ir::value::ValueId),
) {
    use trust_ir::inst::SwitchCase;
    let (zero_b, _) = fb.block(&[]);
    let (one_b, _) = fb.block(&[]);
    let (default, _) = fb.block(&[]);
    fb.push_inst_void(Inst::Switch {
        value: fb.p(0),
        default,
        default_args: vec![],
        cases: vec![
            SwitchCase { value: Constant::Int(0), target: zero_b, args: vec![] },
            SwitchCase { value: Constant::Int(1), target: one_b, args: vec![] },
        ],
        exhaustive_enum_unreachable: false,
    });
    fb.switch_to(default);
    fb.push_inst_void(Inst::Unreachable);
    fb.switch_to(zero_b);
    let v = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
    tail(fb, v);
    fb.switch_to(one_b);
    if checked {
        check(fb, 1, ICmpOp::Ne, 0);
    }
    let v = fb.p(1);
    tail(fb, v);
}

/// Builds `leaf`'s body; `None` when the body already returned from every arm.
type LeafBody = dyn Fn(&mut FnBody, trust_ir::value::FuncId) -> Option<trust_ir::value::ValueId>;

/// A producer whose `f(x, y) = leaf(x, y) + 3` calls the `leaf` that `build` writes (given
/// `inner(x) = if x < 10 { x } else { unreachable }`), or the bytes' module: `f` with `leaf`
/// written out and no check (`switch` picks which shape), `inner` and `leaf` still defined.
fn inlined_module(leaf: Option<&LeafBody>, switch: bool) -> Module {
    let mut mb = ModBuilder::new("cer_inlined_unreachable");
    let s1 = mb.sig(&u64s(1), Some(Ty::U64));
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let inner = mb.define("inner", s1, Linkage::External, |fb| {
        below_ten(fb, |_| {});
        let x = fb.p(0);
        fb.ret(x);
    });
    let leaf_id = mb.define("leaf", s2, Linkage::External, |fb| match leaf {
        Some(build) => {
            if let Some(out) = build(fb, inner) {
                fb.ret(out);
            }
        }
        None => {
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
            fb.ret(out);
        }
    });
    let plus3 = |fb: &mut FnBody, r| {
        let three = fb.konst(Ty::U64, 3);
        let out = fb.bin(BinOp::Add, Ty::U64, r, three);
        fb.ret(out);
    };
    mb.define("f", s2, Linkage::External, |fb| match (leaf, switch) {
        (Some(_), _) => {
            let r = fb.call(leaf_id, &[fb.p(0), fb.p(1)]);
            plus3(fb, r);
        }
        (None, false) => {
            below_ten(fb, |_| {});
            let r = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
            plus3(fb, r);
        }
        (None, true) => switch_leaf(fb, false, plus3),
    });
    mb.finish()
}

/// Grade `f` of `producer` against the check-free written-out bytes; on a positive also checks
/// that the bytes call nothing and the gate interpreted `leaf`.
fn inlined_case(leaf: &LeafBody, switch: bool, proves: bool) {
    let producer = inlined_module(Some(leaf), switch);
    let bytes = inlined_module(None, switch);
    for triple in BOTH {
        let object = Fixture::new(bytes.clone(), triple, OptLevel::O2).object;
        assert!(bl_offsets(&object, "f").is_empty(), "{triple}: the written-out `f` calls");
        let fx = Fixture::with_object(producer.clone(), object, triple);
        let report = fx.report();
        if proves {
            // Proven, not kernel-[PROVED]: no kernel route proves `f`'s conjunction for this
            // `if x < 10` shape, the branch split (DECISION_QUEUE BRANCH-SPLIT-1) included; every
            // case grades [VALIDATED] on both triples (measured 2026-11-14), so the routes decline
            // the shape, not the interpreted call. The grade is pinned so a route that starts to
            // prove the shape shows here; then update this comment and the pin.
            let c = report.certificate("f").expect("f");
            assert!(
                matches!(
                    c.verdict,
                    OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }
                ),
                "{triple}: `f` is not [VALIDATED] (AyValidated): {:?}\n{}",
                c.verdict,
                explain(&report)
            );
            assert_eq!(c.call_sites.len(), 1, "{triple}");
            assert_eq!(c.call_sites[0].kind, CallSiteKind::InterpretedInline, "{triple}");
        } else {
            assert_not_proven(&fx, "f", "an inlined callee's check that can fail, dropped");
            let why = explain(&report);
            assert!(why.contains("a check of the inlined callee at"), "{triple}: {why}");
        }
    }
}

/// An inlined callee's `Unreachable` arm is undefined behaviour, not a failed check: it only
/// drops executions, as the caller's own `Unreachable` does. `leaf = if x < 10 { x ^ y } else {
/// unreachable }` against the written-out bytes proves; from ee87ec5147 (2026-11-13) until this
/// change the gate read the callee's whole `reach` as a check and graded `f` Unknown ("the
/// inlined callee ... (its checks and its `Unreachable` arms)"). The same with the
/// `Unreachable` as a `Switch` default.
#[test]
fn an_inlined_callee_unreachable_arm_is_not_a_failed_check() {
    inlined_case(
        &|fb, _| {
            below_ten(fb, |_| {});
            Some(fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1)))
        },
        false,
        true,
    );
    // A check that holds on its own arm (`x < 10` under `x < 10`): `ok` merges per arm, so the
    // check sits under the arm that tests it (swapping the arms leaves `x < 10` to fail).
    inlined_case(
        &|fb, _| {
            below_ten(fb, |_| {});
            check(fb, 0, ICmpOp::Ult, 10);
            Some(fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1)))
        },
        false,
        true,
    );
    // After a nested call whose `Unreachable` excludes `x >= 10`, `assert(x < 10)` cannot fail:
    // only the nested callee's normal return reaches it.
    inlined_case(
        &|fb, inner| {
            let t = fb.call(inner, &[fb.p(0)]);
            check(fb, 0, ICmpOp::Ult, 10);
            Some(fb.bin(BinOp::Xor, Ty::U64, t, fb.p(1)))
        },
        false,
        true,
    );
    inlined_case(
        &|fb, _| {
            switch_leaf(fb, false, |fb, v| fb.ret(v));
            None
        },
        true,
        true,
    );
}

/// The callee's own checks still count, wherever they fail:
#[test]
fn a_check_of_an_inlined_callee_that_can_fail_is_not_proven() {
    // `assert(y != 0)` on the arm `x < 10`;
    inlined_case(
        &|fb, _| {
            below_ten(fb, |_| {});
            check(fb, 1, ICmpOp::Ne, 0);
            Some(fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1)))
        },
        false,
        false,
    );
    // `assert(y != 0)` just before the `Unreachable` on the same path (the diverging-site
    // encoding `Assert(false); Unreachable`): the failure is reached before the UB is;
    inlined_case(
        &|fb, _| {
            below_ten(fb, |fb| check(fb, 1, ICmpOp::Ne, 0));
            Some(fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1)))
        },
        false,
        false,
    );
    // `assert(x < 10)` BEFORE a nested call whose `Unreachable` excludes `x >= 10`: the nested
    // call's reach shields only what follows it;
    inlined_case(
        &|fb, inner| {
            check(fb, 0, ICmpOp::Ult, 10);
            let t = fb.call(inner, &[fb.p(0)]);
            Some(fb.bin(BinOp::Xor, Ty::U64, t, fb.p(1)))
        },
        false,
        false,
    );
    // and `assert(y != 0)` in one `Switch` arm.
    inlined_case(
        &|fb, _| {
            switch_leaf(fb, true, |fb, v| fb.ret(v));
            None
        },
        true,
        false,
    );
}

/// An Internal callee on AArch64 ELF (the one object path trust-cg binds
/// module-local direct calls on today; Mach-O waits for step 5.3): bound as a
/// LOCAL symbol and composed through its own certificate.
/// FORMER PANIC SITES (TCB panic gate, 2026-10-10; the fifth movement of
/// scripts/frozen-waivers.txt's call_event.rs row). The object reader names a
/// callee for an ELF call spelled `section + addend` only when the addend is a
/// non-preemptible extent's start; it used to test that in a match guard and
/// then re-read the section through an `expect` and the start through an
/// index, and now looks the extent up once. The gate's own pairing loops lost
/// their `expect("checked above")`s the same way: a site that names no callee
/// is refused where it is found. Through the whole gate, on the internal-call
/// fixture with its call rewritten to the section symbol:
///   * `.text + start(g)` still names `g`: the caller stays kernel-[PROVED];
///   * `.text + start(g) + 4` names no extent start: refused, never Proven.
#[test]
fn a_section_relative_call_names_a_callee_only_at_an_extent_start() {
    let fx = Fixture::new(internal_callee_module(), LINUX, OptLevel::O0);
    assert_kernel_proved(&fx, &fx.report(), "f");
    let at = |delta: i64| {
        fx.patched(|o| {
            let (section_sym, start) = elf_section_symbol_of(o, "g");
            let call = bl_offsets(o, "f")[0];
            let (record, _, _) = reloc_at(o, call);
            set_reloc_symbol(o, record, section_sym);
            set_elf_reloc_addend(o, record, start as i64 + delta);
        })
    };
    let twin = at(0);
    let report = twin.report();
    assert_kernel_proved(&twin, &report, "f");
    assert_eq!(
        report.certificate("f").unwrap().assumptions,
        vec![Assumption::CoEmitted("g".into())],
        "`.text + start(g)` must name `g`"
    );
    let why = assert_not_proven(&at(4), "f", "section-relative call off an extent start");
    eprintln!("section + start(g) + 4: {why}");
}

fn internal_callee_module() -> Module {
    let mut mb = ModBuilder::new("cer_internal");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::Internal, |fb| {
        let k = fb.konst(Ty::U64, 0x11);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

#[test]
fn internal_callee_binds_locally_on_elf() {
    let mut mb = ModBuilder::new("cer_internal");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::Internal, |fb| {
        let k = fb.konst(Ty::U64, 0x11);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    let fx = Fixture::new(mb.finish(), LINUX, OptLevel::O0);
    let report = fx.report();
    assert_kernel_proved(&fx, &report, "f");
    assert_kernel_proved(&fx, &report, "g");
    assert_eq!(
        report.certificate("f").unwrap().assumptions,
        vec![Assumption::CoEmitted("g".into())]
    );
    assert_eq!(report.certificate("g").unwrap().linkage, "Internal");
    assert!(report.closure.closed_kernel.contains(&"f".to_string()), "{:?}", report.closure);
}

/// A caller can be [PROVED] on its own while the co-emitted callee it rests on
/// is Unknown: the per-function grade is not the shipping grade. The closure
/// report names the blocking callee and strict refuses the object.
#[test]
fn closure_names_the_unknown_callee_that_blocks_a_proved_caller() {
    let mut mb = ModBuilder::new("cer_closure");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    // spin(x): a loop (outside the loop-free fragment, so Unknown).
    let spin = mb.define("spin", s, Linkage::External, |fb| {
        let (head, hv) = fb.block(&[Ty::U64]);
        let (exit, _) = fb.block(&[]);
        fb.br(head, &[fb.p(0)]);
        fb.switch_to(head);
        let zero = fb.konst(Ty::U64, 0);
        let done = fb.icmp(ICmpOp::Eq, Ty::U64, hv[0], zero);
        let one = fb.konst(Ty::U64, 1);
        let next = fb.bin(BinOp::Sub, Ty::U64, hv[0], one);
        fb.cond_br(done, exit, &[], head, &[next]);
        fb.switch_to(exit);
        let k = fb.konst(Ty::U64, 7);
        fb.ret(k);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(spin, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        // O0: at O2 trust-cg's multi-block inliner splices the loop into `f`
        // (measured), and `f` is then Unknown itself (the interpreted callee
        // loops) — here `f` must keep a real call.
        let fx = Fixture::new(module.clone(), triple, OptLevel::O0);
        assert_eq!(bl_offsets(&fx.object, "f").len(), 1, "{triple}\n{}", disassemble(&fx.object));
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        let spin_c = report.certificate("spin").unwrap();
        assert!(matches!(spin_c.verdict, OutputVerdict::Unknown { .. }), "{}", explain(&report));
        assert!(!report.closure.closed_kernel.contains(&"f".to_string()));
        let f_unclosed =
            report.closure.unclosed.iter().find(|u| u.symbol == "f").expect("f unclosed");
        assert_eq!(f_unclosed.blocked_by, vec!["spin".to_string()]);
        let err = report.ships(EmitPolicy::StrictProvenOnly).unwrap_err();
        assert!(err.contains("blocked by [spin]"), "{err}");
        report.ships(EmitPolicy::AllowUnknown).unwrap();
    }
}

/// x86-64 objects are Unknown function by function, as today — never refused
/// as malformed, never Proven.
#[test]
fn x86_64_object_is_unknown_not_refused() {
    let fx = Fixture::new(wrapper_module(), "x86_64-unknown-linux-gnu", OptLevel::O2);
    let report = fx.report();
    let c = report.certificate("f").unwrap();
    assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{}", explain(&report));
    assert!(c.obligations.o1_binding.detail.contains("x86-64"), "{}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    report.ships(EmitPolicy::AllowUnknown).unwrap();
}

/// A producer parameter that is a two-field aggregate, legalized by FnAbi
/// `PassMode::Pair` into two scalars: the gate binds it through P.
#[test]
fn pair_parameter_is_bound_through_p() {
    // M_cg: the legalized f(a, b) = a - b.
    let mut mb = ModBuilder::new("cer_pair_mcg");
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    mb.define("f", s2, Linkage::External, |fb| {
        let out = fb.bin(BinOp::Sub, Ty::U64, fb.p(0), fb.p(1));
        fb.ret(out);
    });
    let m_cg = mb.finish();
    // The producer: f(p: (u64, u64)) = p.0 - p.1.
    let mut pb = ModBuilder::new("cer_pair_producer");
    let tup = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let sp = pb.sig(&[tup], Some(Ty::U64));
    pb.define("f", sp, Linkage::External, |fb| {
        let a = fb.extract(Ty::U64, fb.p(0), 0);
        let c = fb.extract(Ty::U64, fb.p(0), 1);
        let out = fb.bin(BinOp::Sub, Ty::U64, a, c);
        fb.ret(out);
    });
    let producer = Arc::new(pb.finish());
    for triple in BOTH {
        let mut fx = Fixture::new(m_cg.clone(), triple, OptLevel::O2);
        fx.producers = vec![ProducerModule::named_by_symbols(producer.clone())];
        fx.bodies.insert("f".into(), ProducerBody { producer: 0, func: producer.functions[0].id });
        fx.placements.insert(
            "f".into(),
            FnPlacement {
                params: vec![ParamPlace::Pair(ScalarPlace::gpr(0, 64), ScalarPlace::gpr(1, 64))],
                ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
            },
        );
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
    }
}

// ===========================================================================
// MUTANTS — each Refuted or Unknown (or the object refused), never Proven
// ===========================================================================

/// `f(x, y) = ext(y, x) ^ x`: the arguments are swapped at the call and `x`
/// lives across it (in a callee-saved register or the frame).
fn swap_module() -> Module {
    let mut mb = ModBuilder::new("cer_swap");
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let ext = mb.declare("ext", s2);
    mb.define("f", s2, Linkage::External, |fb| {
        let r = fb.call(ext, &[fb.p(1), fb.p(0)]);
        let out = fb.bin(BinOp::Xor, Ty::U64, r, fb.p(0));
        fb.ret(out);
    });
    mb.finish()
}

/// `f(x) = g(x) + 1` with `g` a co-emitted body (O0: no OPT-4 inlining).
fn local_callee_module() -> Module {
    let mut mb = ModBuilder::new("cer_local");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x33);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

/// `f(x) = g(x) + h(x ^ 1)`, both declarations.
fn two_calls_module() -> Module {
    let mut mb = ModBuilder::new("cer_two");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    let h = mb.declare("h", s);
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
        let c = fb.call(h, &[x1]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    mb.finish()
}

/// The words of `f` after its first `bl`.
fn after_call(o: &[u8], f: &str) -> Vec<(u64, u32)> {
    let bl = bl_offsets(o, f)[0];
    function_words(o, f).into_iter().filter(|(off, _)| *off > bl).collect()
}

/// The words of `f` before its first `bl`.
fn before_call(o: &[u8], f: &str) -> Vec<(u64, u32)> {
    let bl = bl_offsets(o, f)[0];
    function_words(o, f).into_iter().filter(|(off, _)| *off < bl).collect()
}

/// Destination register of a data-processing word (bits 4:0).
fn rd(w: u32) -> u32 {
    w & 0x1f
}

/// A word that is not part of the frame record (`stp/ldp x29, x30` or
/// `mov x29, sp`) — a slot a mutant may overwrite without touching O0.
fn is_frame_pointer_setup(w: u32) -> bool {
    w == 0x9100_03fd // mov x29, sp
}

#[test]
fn mutant_swapped_argument_registers() {
    for triple in BOTH {
        let fx = Fixture::new(swap_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // Every instruction before the call that writes X0 or X1 is dropped:
        // the callee now receives (x, y), not (y, x).
        let m = fx.patched(|o| {
            for (off, w) in before_call(o, "f") {
                let class_dp = w & 0x1f00_0000 == 0x0a00_0000
                    || w & 0x1f00_0000 == 0x1100_0000
                    || w & 0x7fe0_ffe0 == 0x2a00_03e0;
                if class_dp && rd(w) <= 1 {
                    patch_word(o, off, NOP);
                }
            }
        });
        assert_refuted(&m, "f", "swapped argument registers");
    }
}

#[test]
fn mutant_relocation_retargeted_to_another_symbol() {
    for triple in BOTH {
        let fx = Fixture::new(two_calls_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // Both calls now name `h`: `g` is never called, `h` twice.
        let m = fx.patched(|o| {
            let first = bl_offsets(o, "f")[0];
            let (record, _, _) = reloc_at(o, first);
            let h = symbol_index(o, "h");
            set_reloc_symbol(o, record, h);
        });
        let why = assert_not_proven(&m, "f", "relocation retargeted");
        eprintln!("[{triple}] retargeted: {why}");
    }
}

#[test]
fn mutant_dropped_call() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let m = fx.patched(|o| {
            let bl = bl_offsets(o, "f")[0];
            let (record, _, _) = reloc_at(o, bl);
            delete_reloc(o, record);
            patch_word(o, bl, NOP);
        });
        let why = assert_not_proven(&m, "f", "dropped call");
        eprintln!("[{triple}] dropped: {why}");
    }
}

#[test]
fn mutant_duplicated_call() {
    for triple in BOTH {
        let fx = Fixture::new(local_callee_module(), triple, OptLevel::O0);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // A second, unrelocated `bl g` replaces the frame-pointer setup.
        let m = fx.patched(|o| {
            let g = symbol_offset(o, "g") as i64;
            let slot = before_call(o, "f")
                .into_iter()
                .find(|(_, w)| is_frame_pointer_setup(*w))
                .map(|(off, _)| off)
                .expect("mov x29, sp");
            patch_word(o, slot, enc_bl(g - slot as i64));
        });
        let why = assert_not_proven(&m, "f", "duplicated call");
        eprintln!("[{triple}] duplicated: {why}");
    }
}

/// `f(x) = g(x) + h(x)`: both calls take the same argument and the result
/// is commutative, so a reordering is visible ONLY to the call-order check.
fn same_arg_calls_module() -> Module {
    let mut mb = ModBuilder::new("cer_same_arg");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    let h = mb.declare("h", s);
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let c = fb.call(h, &[fb.p(0)]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    mb.finish()
}

#[test]
fn mutant_swapped_call_order() {
    for triple in BOTH {
        let fx = Fixture::new(same_arg_calls_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // The two relocations exchange their symbols: the bytes call h first.
        let m = fx.patched(|o| {
            let bls = bl_offsets(o, "f");
            assert_eq!(bls.len(), 2);
            let (r0, _, s0) = reloc_at(o, bls[0]);
            let (r1, _, s1) = reloc_at(o, bls[1]);
            set_reloc_symbol(o, r0, s1);
            set_reloc_symbol(o, r1, s0);
        });
        assert_refuted(&m, "f", "swapped call order");
        let report = m.report();
        let o2 = &report.certificate("f").unwrap().obligations.o2_pairing;
        assert_eq!(o2.grade, Grade::Refuted, "{}", explain(&report));
        assert!(o2.detail.contains("another order"), "{}", o2.detail);
    }
}

#[test]
fn mutant_result_used_from_the_wrong_register() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // `add x0, x0, #1` after the call reads X1 instead.
        let m = fx.patched(|o| {
            let (off, w) = after_call(o, "f")
                .into_iter()
                .find(|(_, w)| w & 0xff80_0000 == 0x9100_0000 && (w >> 5) & 0x1f == 0)
                .expect("add x?, x0, #imm");
            patch_word(o, off, (w & !(0x1f << 5)) | (1 << 5));
        });
        assert_refuted(&m, "f", "result from the wrong register");
    }
}

#[test]
fn mutant_caller_saved_register_assumed_live_across_a_call() {
    for triple in BOTH {
        let fx = Fixture::new(swap_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // `x` is kept across the call in X9 (caller-saved) instead of the
        // callee-saved register: its save (`mov x19, x0`) and its use after
        // the call both move to X9. Only the call's havoc of X0-X17 can tell.
        let m = fx.patched(|o| {
            let (save, w) = before_call(o, "f")
                .into_iter()
                .find(|(_, w)| {
                    w & 0xffe0_ffe0 == 0xaa00_03e0
                        && (19..=28).contains(&rd(*w))
                        && (w >> 16) & 0x1f == 0
                })
                .expect("mov x19..x28, x0");
            let saved = rd(w);
            patch_word(o, save, (w & !0x1f) | 9);
            // Every read of the saved register (a logical register op naming it
            // as Rm: the argument shuffle before the call, the use after it).
            let reads: Vec<(u64, u32)> = function_words(o, "f")
                .into_iter()
                .filter(|(_, u)| u & 0x1f00_0000 == 0x0a00_0000 && (u >> 16) & 0x1f == saved)
                .collect();
            assert!(
                reads.iter().any(|(off, _)| *off > bl_offsets(o, "f")[0]),
                "a use after the call"
            );
            for (at, u) in reads {
                patch_word(o, at, (u & !(0x1f << 16)) | (9 << 16));
            }
        });
        assert_refuted(&m, "f", "caller-saved register live across a call");
    }
}

#[test]
fn mutant_x19_not_restored() {
    for triple in BOTH {
        let fx = Fixture::new(swap_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // The epilogue load that restores X19 is dropped.
        let m = fx.patched(|o| {
            let (off, _) = after_call(o, "f")
                .into_iter()
                .find(|(_, w)| {
                    (w & 0x3a40_0000 == 0x2840_0000 || w & 0x3b40_0000 == 0x3940_0000)
                        && (w & 0x1f == 19 || (w >> 10) & 0x1f == 19)
                })
                .expect("a load restoring x19");
            patch_word(o, off, NOP);
        });
        assert_refuted(&m, "f", "X19 not restored");
    }
}

/// The frame-record restore `ldp x29, x30, [sp], #imm` of `f`.
fn frame_restore(o: &[u8], f: &str) -> (u64, u32) {
    after_call(o, f)
        .into_iter()
        .find(|(_, w)| w & 0xffc0_7fff == 0xa8c0_7bfd)
        .expect("ldp x29, x30, [sp], #imm")
}

#[test]
fn mutant_sp_off_by_16_at_ret() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let m = fx.patched(|o| {
            let (off, w) = frame_restore(o, "f");
            let imm7 = (w >> 15) & 0x7f;
            patch_word(o, off, (w & !(0x7f << 15)) | ((imm7 + 2) << 15));
        });
        assert_refuted(&m, "f", "SP off by 16 at ret");
    }
}

#[test]
fn mutant_missing_lr_restore() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // The frame record is popped without reloading X29/X30.
        let m = fx.patched(|o| {
            let (off, w) = frame_restore(o, "f");
            let imm = ((w >> 15) & 0x7f) * 8;
            patch_word(o, off, enc_add_imm(31, 31, imm));
        });
        assert_refuted(&m, "f", "missing LR restore");
    }
}

#[test]
fn mutant_store_into_the_caller_frame_across_a_call() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // `str xzr, [sp, #frame]` = SP_entry + 0: the caller's frame.
        let m = fx.patched(|o| {
            let (_, push) = function_words(o, "f")[0];
            assert_eq!(push & 0xffc0_7fff, 0xa980_7bfd, "f opens with stp x29, x30, [sp, #-N]!");
            let frame = ((0x80 - ((push >> 15) & 0x7f)) & 0x7f) * 8;
            let slot = before_call(o, "f")
                .into_iter()
                .find(|(_, w)| is_frame_pointer_setup(*w))
                .map(|(off, _)| off)
                .expect("mov x29, sp");
            patch_word(o, slot, enc_str_sp(31, frame));
        });
        assert_refuted(&m, "f", "store into the caller frame");
        assert_eq!(m.report().certificate("f").unwrap().obligations.o5_frame.grade, Grade::Refuted);
    }
}

#[test]
fn mutant_escaped_frame_address_as_an_argument() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let m = fx.patched(|o| {
            let slot = before_call(o, "f")
                .into_iter()
                .find(|(_, w)| is_frame_pointer_setup(*w))
                .map(|(off, _)| off)
                .expect("mov x29, sp");
            patch_word(o, slot, enc_mov_from_sp(0));
        });
        assert_not_proven(&m, "f", "escaped frame address");
        let report = m.report();
        let o5 = &report.certificate("f").unwrap().obligations.o5_frame;
        assert_eq!(o5.grade, Grade::Unknown, "{}", explain(&report));
        assert!(o5.detail.contains("escapes"), "{}", o5.detail);
    }
}

#[test]
fn mutant_unmodeled_relocation_kind() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let m = fx.patched(|o| {
            let bl = bl_offsets(o, "f")[0];
            let (record, _, _) = reloc_at(o, bl);
            // Mach-O ARM64_RELOC_POINTER_TO_GOT; ELF R_AARCH64_LDST64_ABS_LO12_NC.
            let ty = if is_macho(o) { 7 } else { 286 };
            set_reloc_type(o, record, ty);
        });
        let report = m.report();
        let c = report.certificate("f").unwrap();
        assert!(
            matches!(c.verdict, OutputVerdict::Unknown { .. }),
            "{triple}: {}",
            explain(&report)
        );
        assert!(
            c.obligations.o1_binding.detail.contains("unmodeled relocation kind"),
            "{}",
            explain(&report)
        );
    }
}

#[test]
fn mutant_branch_into_the_middle_of_a_window() {
    for triple in BOTH {
        let fx = Fixture::new(local_callee_module(), triple, OptLevel::O0);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let m = fx.patched(|o| {
            let bl = bl_offsets(o, "f")[0];
            let (record, _, _) = reloc_at(o, bl);
            delete_reloc(o, record);
            let g = symbol_offset(o, "g") as i64;
            patch_word(o, bl, enc_bl(g + 4 - bl as i64));
        });
        let report = m.report();
        let c = report.certificate("f").unwrap();
        assert!(
            matches!(c.verdict, OutputVerdict::Unknown { .. }),
            "{triple}: {}",
            explain(&report)
        );
    }
}

#[test]
fn mutant_same_symbol_under_two_signatures() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // (a) f's PRODUCER calls `g` as (u32) -> u32 while P(g), read from
        //     g's FnAbi, places (u64) -> u64.
        let mut pb = ModBuilder::new("cer_two_sigs_producer");
        let s32 = pb.sig(&[Ty::U32], Some(Ty::U32));
        let s64 = pb.sig(&u64s(1), Some(Ty::U64));
        let g32 = pb.declare("g", s32);
        pb.define("f", s64, Linkage::External, |fb| {
            let one = fb.konst(Ty::U32, 1);
            let r = fb.call(g32, &[one]);
            let w = fb.push_inst(trust_ir::inst::Inst::Cast {
                op: trust_ir::inst::CastOp::ZExt,
                src_ty: Ty::U32,
                dst_ty: Ty::U64,
                operand: r,
            });
            fb.ret(w);
        });
        let producer = Arc::new(pb.finish());
        let mut m = fx.patched(|_| {});
        m.producers = vec![ProducerModule::named_by_symbols(producer.clone())];
        m.bodies.insert("f".into(), ProducerBody { producer: 0, func: producer.functions[1].id });
        let why = assert_not_proven(&m, "f", "same symbol under two signatures (producer vs P)");
        assert!(why.contains("signature") || why.contains("bits"), "{why}");
        // (b) M_cg itself declares `g` twice under two signatures: the object
        //     is refused.
        let mut two = (*fx.m_cg).clone();
        let s32b = two
            .add_func_type(trust_ir::ty::FuncTy {
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut dup = two.functions.iter().find(|f| f.name == "g").unwrap().clone();
        dup.id = trust_ir::value::FuncId::new(two.functions.len() as u32);
        dup.ty = s32b;
        two.functions.push(dup);
        let mut m2 = fx.patched(|_| {});
        m2.m_cg = Arc::new(two);
        assert!(
            m2.verify().is_err(),
            "{triple}: M_cg with `g` under two signatures was not refused"
        );
    }
}

/// KNOWN_HAZARDS "producer C-ABI residuals after S2/S3": the producer declares a callee
/// it cannot sign (a variadic `fcntl`, or a parameter it has no type for) as `(...)` with
/// no fixed parameter. Lowered as `CallVariadic { fixed_args: 0 }`, its arguments go on
/// the stack on Apple arm64 while the callee reads registers. A plain variadic edge is
/// graded Unknown, which `AllowUnknown` ships; this one must be REFUTED under every policy.
#[test]
fn mutant_unsigned_variadic_callee_is_refuted() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        // The unmutated twin: the same object, the producer calling `g` as `(u64) -> u64`.
        assert_kernel_proved(&fx, &fx.report(), "f");
        // f's PRODUCER calls `g` through an unsigned `(...) -> u64` declaration.
        let mut pb = ModBuilder::new("cer_unsigned_producer");
        let s64 = pb.sig(&u64s(1), Some(Ty::U64));
        let unsigned = pb.sig(&[], Some(Ty::U64));
        let g = pb.declare("g", unsigned);
        pb.define("f", s64, Linkage::External, |fb| {
            let r = fb.call(g, &[fb.p(0)]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
        let mut producer = pb.finish();
        producer.func_types[unsigned.as_usize()].is_vararg = true;
        let producer = Arc::new(producer);
        let mut m = fx.patched(|_| {});
        m.producers = vec![ProducerModule::named_by_symbols(producer.clone())];
        m.bodies.insert("f".into(), ProducerBody { producer: 0, func: producer.functions[1].id });
        assert_refuted(&m, "f", "a call through an unsigned `(...)` declaration");
        let report = m.report();
        let c = report.certificate("f").expect("certificate");
        assert!(format!("{c:?}").contains("no fixed parameter"), "{c:?}");
    }
}

// ---------------------------------------------------------------------------
// A variadic signature whose fixed/anonymous split is unknown is BLOCKED
// ---------------------------------------------------------------------------
//
// The ABI passes fixed and anonymous arguments differently (Apple arm64 puts
// every anonymous one on the stack; x86-64 SysV also counts vector registers in
// AL), so a guessed split miscompiles without a trace. trust-cg refuses the two
// shapes whose split trust-ir does not state (OD-55: no fixed parameter, and a
// variadic Rust-ABI signature). The gate must refuse them too, under every
// policy and whatever else it reads first: graded Unknown, `AllowUnknown`
// ships them. A variadic signature that states its fixed prefix keeps the
// grade it had (Unknown: P places no variadic signature before step 5.10).

/// A copy of `fx` whose producer is `producer`: the bodies named in `bodies`
/// (each the function of that name that has blocks) are read from it, and P
/// and the object are untouched.
fn with_producer(fx: &Fixture, producer: Module, bodies: &[&str]) -> Fixture {
    let producer = Arc::new(producer);
    let mut m = fx.patched(|_| {});
    m.producers = vec![ProducerModule::named_by_symbols(producer.clone())];
    for name in bodies {
        let f = producer
            .functions
            .iter()
            .find(|f| f.name == *name && !f.blocks.is_empty())
            .unwrap_or_else(|| panic!("the producer has no body `{name}`"));
        m.bodies.insert((*name).into(), ProducerBody { producer: 0, func: f.id });
    }
    m
}

/// BLOCKED: Refuted (never merely Unknown), naming `reason`, so no policy ships
/// the object.
#[track_caller]
fn assert_blocked(m: &Fixture, symbol: &str, what: &str, reason: &str) {
    assert_refuted(m, symbol, what);
    let report = m.report();
    let c = report.certificate(symbol).expect("certificate");
    let OutputVerdict::Refuted { detail } = &c.verdict else { unreachable!("asserted Refuted") };
    assert!(detail.contains(reason), "{}: `{what}` names no `{reason}`: {detail}", m.triple);
    for policy in [EmitPolicy::AllowUnknown, EmitPolicy::StrictProvenOnly] {
        let err = report.ships(policy).expect_err("a blocked function ships under no policy");
        assert!(err.contains(symbol), "{}: {policy:?}: {err}", m.triple);
    }
}

/// `f(x) = g(x) + 1` as a PRODUCER that calls `g` through a variadic `(u64 x
/// fixed, ...) -> u64` declaration under `conv`.
fn variadic_callee_producer(fixed: usize, conv: CallingConv) -> Module {
    let mut pb = ModBuilder::new("cer_variadic_callee_producer");
    let s64 = pb.sig(&u64s(1), Some(Ty::U64));
    let variadic = pb.sig(&u64s(fixed), Some(Ty::U64));
    let g = pb.declare("g", variadic);
    pb.define("f", s64, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    let mut producer = pb.finish();
    producer.func_types[variadic.as_usize()].is_vararg = true;
    producer.functions[g.as_usize()].calling_conv = conv;
    producer
}

/// The Rust ABI has no variadic form, so a variadic Rust-convention signature's
/// fixed prefix is a producer placeholder (OD-55), even when it states one.
#[test]
fn mutant_variadic_rust_abi_callee_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for conv in [CallingConv::Rust, CallingConv::RustCold] {
            let m = with_producer(&fx, variadic_callee_producer(1, conv), &["f"]);
            assert_blocked(
                &m,
                "f",
                &format!("a call through a variadic {conv:?}-convention `(u64, ...)` declaration"),
                "the Rust ABI has no variadic form",
            );
        }
    }
}

/// A KNOWN split, `(u64, ...)` under a C-family convention that every module
/// the gate reads declares (the compiled module as well as the producer), is
/// graded exactly as before: Unknown on the placement check, never Refuted, so
/// the block does not widen into a callee that states its fixed prefix. The
/// same producer over a compiled module that declares `g` fixed-arity is a
/// symbol under two splits, and is blocked.
#[test]
fn signed_variadic_callee_is_graded_as_before() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for conv in [CallingConv::C, CallingConv::CUnwind] {
            let mismatched = with_producer(&fx, variadic_callee_producer(1, conv), &["f"]);
            assert_blocked(
                &mismatched,
                "f",
                &format!("a {conv:?} `(u64, ...)` callee the compiled module declares `(u64)`"),
                "declared with more than one split",
            );
            // trust-cg compiles the C edge (it refuses a C-unwind call on AArch64); the gate
            // reads that object against a module that declares `g` under `conv`.
            let object =
                compile(&variadic_callee_producer(1, CallingConv::C), triple, OptLevel::O2);
            let m = Fixture::with_object(variadic_callee_producer(1, conv), object, triple);
            let report = m.report();
            let c = report.certificate("f").expect("certificate");
            assert!(
                matches!(c.verdict, OutputVerdict::Unknown { .. }),
                "{triple}: {conv:?}: {}",
                explain(&report)
            );
            assert_eq!(c.obligations.o3_events.grade, Grade::Unknown, "{}", explain(&report));
            assert_eq!(
                c.obligations.o3_events.detail,
                "the callee `g` is called under a signature P(`g`) does not place: variadic (the \
                 same symbol under two signatures)"
            );
            report.ships(EmitPolicy::AllowUnknown).unwrap_or_else(|e| panic!("{triple}: {e}"));
        }
    }
}

/// The unsigned `(...)` edge is blocked before P is read: a callee P has no
/// placement for is not a way back to Unknown.
#[test]
fn mutant_unsigned_variadic_callee_without_a_placement_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut m = with_producer(&fx, variadic_callee_producer(0, CallingConv::C), &["f"]);
        assert!(m.placements.remove("g").is_some());
        assert_blocked(&m, "f", "an unsigned `(...)` callee with no P", "no fixed parameter");
    }
}

/// `f(x) = g(x) + g(x ^ 1)`, `g` a declaration called twice.
fn twice_module() -> Module {
    let mut mb = ModBuilder::new("cer_twice");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
        let c = fb.call(g, &[x1]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    mb.finish()
}

/// An unsigned site of `g` beside a signed one is blocked, not graded Unknown
/// as "the same symbol under two signatures".
#[test]
fn mutant_unsigned_variadic_site_beside_a_signed_one_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(twice_module(), triple, OptLevel::O2);
        assert_eq!(bl_offsets(&fx.object, "f").len(), 2, "{triple}: two calls to `g`");
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut pb = ModBuilder::new("cer_twice_producer");
        let s = pb.sig(&u64s(1), Some(Ty::U64));
        let unsigned = pb.sig(&[], Some(Ty::U64));
        let g = pb.declare("g", s);
        let g_unsigned = pb.declare("g", unsigned);
        pb.define("f", s, Linkage::External, |fb| {
            let a = fb.call(g, &[fb.p(0)]);
            let one = fb.konst(Ty::U64, 1);
            let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
            let c = fb.call(g_unsigned, &[x1]);
            let out = fb.bin(BinOp::Add, Ty::U64, a, c);
            fb.ret(out);
        });
        let mut producer = pb.finish();
        producer.func_types[unsigned.as_usize()].is_vararg = true;
        let m = with_producer(&fx, producer, &["f"]);
        assert_blocked(&m, "f", "a second call to `g` through `(...)`", "no fixed parameter");
    }
}

/// An unsigned call trust-cg's OPT-4 inlined is blocked too: the gate does not
/// interpret its way past a call whose arguments the producer could not sign.
#[test]
fn mutant_unsigned_variadic_call_to_an_inlined_body_is_blocked() {
    let leaf_body = |fb: &mut FnBody| {
        let k = fb.konst(Ty::U64, 0x55);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    };
    let mut mb = ModBuilder::new("cer_opt4_twin");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let leaf = mb.define("leaf", s, Linkage::External, leaf_body);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(leaf, &[fb.p(0)]);
        let k = fb.konst(Ty::U64, 3);
        let out = fb.bin(BinOp::Add, Ty::U64, r, k);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        assert!(bl_offsets(&fx.object, "f").is_empty(), "{triple}: OPT-4 did not inline");
        assert_kernel_proved(&fx, &fx.report(), "f");
        // The producer calls the co-emitted `leaf` through a `(...)` declaration of it.
        let mut pb = ModBuilder::new("cer_opt4_unsigned");
        let s = pb.sig(&u64s(1), Some(Ty::U64));
        let unsigned = pb.sig(&[], Some(Ty::U64));
        pb.define("leaf", s, Linkage::External, leaf_body);
        let leaf_unsigned = pb.declare("leaf", unsigned);
        pb.define("f", s, Linkage::External, |fb| {
            let r = fb.call(leaf_unsigned, &[fb.p(0)]);
            let k = fb.konst(Ty::U64, 3);
            let out = fb.bin(BinOp::Add, Ty::U64, r, k);
            fb.ret(out);
        });
        let mut producer = pb.finish();
        producer.func_types[unsigned.as_usize()].is_vararg = true;
        let m = with_producer(&fx, producer, &["leaf", "f"]);
        assert_blocked(&m, "f", "an inlined call through `(...)`", "no fixed parameter");
    }
}

/// An indirect call states its own signature and convention; through an
/// unsigned `(...)` one it is blocked, not left Unknown until step 5.9.
#[test]
fn mutant_indirect_call_through_an_unsigned_signature_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut pb = ModBuilder::new("cer_indirect_unsigned");
        let s64 = pb.sig(&u64s(1), Some(Ty::U64));
        let unsigned = pb.sig(&[], Some(Ty::U64));
        let g = pb.declare("g", s64);
        pb.define("f", s64, Linkage::External, |fb| {
            let ptr =
                fb.push_inst(Inst::Const { ty: Ty::Func(unsigned), value: Constant::FnDef(g) });
            let r = fb.push_inst(Inst::CallIndirect {
                callee: ptr,
                sig: unsigned,
                args: vec![fb.p(0)],
                calling_conv: CallingConv::C,
            });
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
        let mut producer = pb.finish();
        producer.func_types[unsigned.as_usize()].is_vararg = true;
        let m = with_producer(&fx, producer, &["f"]);
        assert_blocked(&m, "f", "an indirect call through `(...)`", "no fixed parameter");
    }
}

/// The other call forms that name a signature are read the same way: a
/// no-unwind call, an invoke, and their indirect twins through `(...)`.
#[test]
fn mutant_unsigned_variadic_unwind_shapes_are_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for shape in ["CallCannotUnwind", "Invoke", "CallIndirectCannotUnwind", "InvokeIndirect"] {
            // bb0: r = <shape> g(x) -> bb1(r) [unwind bb2]; bb1(v): ret v + 1; bb2: unreachable.
            let mut pb = ModBuilder::new("cer_unwind_shapes");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let unsigned = pb.sig(&[], Some(Ty::U64));
            let g = pb.declare("g", unsigned);
            pb.define("f", s64, Linkage::External, |fb| {
                let x = fb.p(0);
                let (normal, v) = fb.block(&[Ty::U64]);
                let (unwind, _) = fb.block(&[]);
                let ptr =
                    fb.push_inst(Inst::Const { ty: Ty::Func(unsigned), value: Constant::FnDef(g) });
                let args = vec![x];
                let cc = CallingConv::C;
                match shape {
                    "CallCannotUnwind" => {
                        let r = fb.push_inst(Inst::CallCannotUnwind { callee: g, args });
                        fb.br(normal, &[r]);
                    }
                    "CallIndirectCannotUnwind" => {
                        let r = fb.push_inst(Inst::CallIndirectCannotUnwind {
                            callee: ptr,
                            sig: unsigned,
                            args,
                            calling_conv: cc,
                        });
                        fb.br(normal, &[r]);
                    }
                    "Invoke" | "InvokeIndirect" => {
                        // The result is bound on the normal edge: pass it as bb1's argument.
                        let r = trust_ir::value::ValueId::new(1_000);
                        let inst = if shape == "Invoke" {
                            Inst::Invoke {
                                callee: g,
                                args,
                                normal_dest: normal,
                                normal_args: vec![r],
                                unwind_dest: unwind,
                            }
                        } else {
                            Inst::InvokeIndirect {
                                callee: ptr,
                                sig: unsigned,
                                args,
                                calling_conv: cc,
                                normal_dest: normal,
                                normal_args: vec![r],
                                unwind_dest: unwind,
                            }
                        };
                        fb.blocks[0].body.push(trust_ir::node::InstrNode::new(inst).with_result(r));
                    }
                    _ => unreachable!(),
                }
                fb.switch_to(normal);
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, v[0], one);
                fb.ret(out);
                fb.switch_to(unwind);
                fb.push_inst_void(Inst::Unreachable);
            });
            let mut producer = pb.finish();
            producer.func_types[unsigned.as_usize()].is_vararg = true;
            let m = with_producer(&fx, producer, &["f"]);
            assert_blocked(&m, "f", &format!("a {shape} through `(...)`"), "no fixed parameter");
        }
    }
}

/// A DEFINITION whose own producer signature has an unknown split is blocked
/// (trust-cg refuses every variadic definition; the gate does not grade one).
#[test]
fn mutant_definition_of_unknown_arity_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for (fixed, conv, reason) in [
            (0, CallingConv::C, "no fixed parameter"),
            (1, CallingConv::Rust, "the Rust ABI has no variadic form"),
        ] {
            let mut pb = ModBuilder::new("cer_variadic_definition");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let own = pb.sig(&u64s(fixed), Some(Ty::U64));
            let g = pb.declare("g", s64);
            let f = pb.define("f", own, Linkage::External, |fb| {
                let x = if fixed == 0 { fb.konst(Ty::U64, 7) } else { fb.p(0) };
                let r = fb.call(g, &[x]);
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            let mut producer = pb.finish();
            producer.func_types[own.as_usize()].is_vararg = true;
            producer.functions[f.as_usize()].calling_conv = conv;
            let m = with_producer(&fx, producer, &["f"]);
            assert_blocked(&m, "f", &format!("a {conv:?} definition with {fixed} fixed"), reason);
        }
    }
}

/// x86-64 objects are Unknown function by function, which `AllowUnknown`
/// ships; an unsigned edge is blocked there too (SysV also needs AL), while a
/// signed variadic edge that every module declares alike stays Unknown.
#[test]
fn x86_64_unsigned_variadic_callee_is_blocked() {
    let fx = Fixture::new(wrapper_module(), "x86_64-unknown-linux-gnu", OptLevel::O2);
    let report = fx.report();
    assert!(
        matches!(report.certificate("f").unwrap().verdict, OutputVerdict::Unknown { .. }),
        "{}",
        explain(&report)
    );
    report.ships(EmitPolicy::AllowUnknown).unwrap();
    let m = with_producer(&fx, variadic_callee_producer(0, CallingConv::C), &["f"]);
    assert_blocked(&m, "f", "an unsigned `(...)` callee on x86-64", "no fixed parameter");
    let m = Fixture::new(
        variadic_callee_producer(1, CallingConv::C),
        "x86_64-unknown-linux-gnu",
        OptLevel::O2,
    );
    let report = m.report();
    assert!(
        matches!(report.certificate("f").unwrap().verdict, OutputVerdict::Unknown { .. }),
        "{}",
        explain(&report)
    );
    report.ships(EmitPolicy::AllowUnknown).unwrap();
}

#[test]
fn mutant_p_mismatch_against_fnabi() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        // (a) P(f) says the argument arrives in X1; the bytes (and rustc's
        //     FnAbi) put it in X0.
        let mut m = fx.patched(|_| {});
        m.placements.get_mut("f").unwrap().params[0] = ParamPlace::Scalar(ScalarPlace::gpr(1, 64));
        assert_refuted(&m, "f", "P(f) mismatch");
        // (b) P(g) says the callee reads X2.
        let mut m = fx.patched(|_| {});
        m.placements.get_mut("g").unwrap().params[0] = ParamPlace::Scalar(ScalarPlace::gpr(2, 64));
        assert_refuted(&m, "f", "P(g) mismatch");
    }
}

#[test]
fn mutant_pair_split_in_the_wrong_order() {
    // The caller's producer passes the pair (a, b) to `g(p: (u64, u64))`; P(g)
    // is Pair(X0, X1). The legalized M_cg calls g(b, a): split in the wrong
    // order.
    let mut pb = ModBuilder::new("cer_pair_call_producer");
    let tup = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let sg = pb.sig(std::slice::from_ref(&tup), Some(Ty::U64));
    let sf = pb.sig(&u64s(2), Some(Ty::U64));
    let g = pb.declare("g", sg);
    pb.define("f", sf, Linkage::External, |fb| {
        let p = fb.make_pair(tup.clone(), fb.p(0), fb.p(1));
        let r = fb.call(g, &[p]);
        fb.ret(r);
    });
    let producer = Arc::new(pb.finish());
    let legalized = |swap: bool| {
        let mut mb = ModBuilder::new("cer_pair_call_mcg");
        let s2 = mb.sig(&u64s(2), Some(Ty::U64));
        let g = mb.declare("g", s2);
        mb.define("f", s2, Linkage::External, |fb| {
            let (a, c) = if swap { (fb.p(1), fb.p(0)) } else { (fb.p(0), fb.p(1)) };
            let r = fb.call(g, &[a, c]);
            fb.ret(r);
        });
        mb.finish()
    };
    for triple in BOTH {
        for swap in [false, true] {
            let mut fx = Fixture::new(legalized(swap), triple, OptLevel::O2);
            fx.producers = vec![ProducerModule::named_by_symbols(producer.clone())];
            fx.bodies
                .insert("f".into(), ProducerBody { producer: 0, func: producer.functions[1].id });
            fx.placements.insert(
                "g".into(),
                FnPlacement {
                    params: vec![ParamPlace::Pair(
                        ScalarPlace::gpr(0, 64),
                        ScalarPlace::gpr(1, 64),
                    )],
                    ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
                },
            );
            if swap {
                assert_refuted(&fx, "f", "Pair split in the wrong order");
            } else {
                assert_kernel_proved(&fx, &fx.report(), "f");
            }
        }
        // And a Pair PARAMETER bound in the wrong order (P(f) = Pair(X1, X0)).
        let mut mb = ModBuilder::new("cer_pair_mcg2");
        let s2 = mb.sig(&u64s(2), Some(Ty::U64));
        mb.define("f", s2, Linkage::External, |fb| {
            let out = fb.bin(BinOp::Sub, Ty::U64, fb.p(0), fb.p(1));
            fb.ret(out);
        });
        let mut pp = ModBuilder::new("cer_pair_producer2");
        let tup2 = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let sp = pp.sig(&[tup2], Some(Ty::U64));
        pp.define("f", sp, Linkage::External, |fb| {
            let a = fb.extract(Ty::U64, fb.p(0), 0);
            let c = fb.extract(Ty::U64, fb.p(0), 1);
            let out = fb.bin(BinOp::Sub, Ty::U64, a, c);
            fb.ret(out);
        });
        let pmod = Arc::new(pp.finish());
        let mut fx = Fixture::new(mb.finish(), triple, OptLevel::O2);
        fx.producers = vec![ProducerModule::named_by_symbols(pmod.clone())];
        fx.bodies.insert("f".into(), ProducerBody { producer: 0, func: pmod.functions[0].id });
        fx.placements.insert(
            "f".into(),
            FnPlacement {
                params: vec![ParamPlace::Pair(ScalarPlace::gpr(1, 64), ScalarPlace::gpr(0, 64))],
                ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
            },
        );
        assert_refuted(&fx, "f", "Pair parameter split in the wrong order");
    }
}

#[test]
fn mutant_mixed_inline_and_call_sites_of_one_callee() {
    let mut mb = ModBuilder::new("cer_mixed");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x33);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    // f(x) = g(x) + g(x ^ 1): two IR sites of one co-emitted callee.
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
        let c = fb.call(g, &[x1]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O0);
        assert_eq!(
            bl_offsets(&fx.object, "f").len(),
            2,
            "{triple}: O0 keeps both calls\n{}",
            disassemble(&fx.object)
        );
        assert_kernel_proved(&fx, &fx.report(), "f");
        // One of the two calls disappears from the bytes: one IR site called,
        // the other no longer a call — the gate never mixes the two readings.
        let m = fx.patched(|o| {
            let bl = bl_offsets(o, "f")[1];
            let (record, _, _) = reloc_at(o, bl);
            delete_reloc(o, record);
            patch_word(o, bl, NOP);
        });
        let report = m.report();
        let c = report.certificate("f").unwrap();
        assert!(
            matches!(c.verdict, OutputVerdict::Unknown { .. }),
            "{triple}: {}",
            explain(&report)
        );
        assert!(c.obligations.o2_pairing.detail.contains("mixed"), "{}", explain(&report));
    }
}

// ===========================================================================
// DIAGNOSTIC
// ===========================================================================

/// Not an assertion: prints what trust-cg emits for the test modules, so the
/// mutation battery's patch points can be read. Run with `--nocapture`.
#[test]
#[ignore]
fn dump_compiled_shapes() {
    let mut tail = ModBuilder::new("dump_tail");
    let s = tail.sig(&u64s(1), Some(Ty::U64));
    let g = tail.declare("g", s);
    tail.define("t", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        fb.ret(r);
    });
    let tail = tail.finish();
    let mut asserting = ModBuilder::new("dump_assert");
    let s2 = asserting.sig(&u64s(2), Some(Ty::U64));
    asserting.define("q", s2, Linkage::External, |fb| {
        let zero = fb.konst(Ty::U64, 0);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(1), zero);
        fb.push_inst_void(trust_ir::inst::Inst::Assert {
            cond: ok,
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        });
        let out = fb.bin(BinOp::UDiv, Ty::U64, fb.p(0), fb.p(1));
        fb.ret(out);
    });
    let asserting = asserting.finish();
    let modules: Vec<(&str, Module, OptLevel)> = vec![
        ("assert", asserting, OptLevel::O2),
        ("wrapper", wrapper_module(), OptLevel::O2),
        ("tail", tail, OptLevel::O2),
        ("swap", swap_module(), OptLevel::O2),
        ("two_calls", two_calls_module(), OptLevel::O2),
        ("local_callee", local_callee_module(), OptLevel::O0),
    ];
    for triple in BOTH {
        for (name, m, opt) in &modules {
            let obj = compile(m, triple, *opt);
            eprintln!(
                "==== {name} {triple} {opt:?}\n{:?}\n{}",
                section_names(&obj),
                disassemble(&obj)
            );
        }
    }
}

// ===========================================================================
// PKG-C5c: MULTIPLY THEN ADD (the AArch64 MADD shape)
// ===========================================================================
//
// `madd Xd, Xn, Xm, Xa` computes `Xa + Xn * Xm` and the machine semantics
// render the addend first; the source `x * 3 + 7` renders it second. The
// structured kernel route proves the pair through a kernel-checked Add
// commutation (`verify_output_instantiate/add_comm.rs`). The mutants below
// show the commutation cannot be used to prove a different function.

/// `rung(x) = (x * 3) op k`, or `k op (x * 3)` with `k_first`.
fn mul_then_op_module(op: BinOp, k: i128, k_first: bool) -> Module {
    let mut mb = ModBuilder::new("cer_mul_then_op");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define("rung", s, Linkage::External, |fb| {
        let three = fb.konst(Ty::U64, 3);
        let product = fb.bin(BinOp::Mul, Ty::U64, fb.p(0), three);
        let c = fb.konst(Ty::U64, k);
        let out =
            if k_first { fb.bin(op, Ty::U64, c, product) } else { fb.bin(op, Ty::U64, product, c) };
        fb.ret(out);
    });
    mb.finish()
}

/// `madd` with a real addend register (`Ra != 31`; `Ra == 31` is the `mul` alias).
fn is_madd_with_addend(w: u32) -> bool {
    w & 0x7fe0_8000 == 0x1b00_0000 && (w >> 10) & 0x1f != 31
}

/// The in-section offset of `rung`'s one `madd` with an addend.
#[track_caller]
fn the_madd(fx: &Fixture) -> (u64, u32) {
    let hits: Vec<(u64, u32)> = function_words(&fx.object, "rung")
        .into_iter()
        .filter(|(_, w)| is_madd_with_addend(*w))
        .collect();
    assert_eq!(hits.len(), 1, "{}: one madd expected\n{}", fx.triple, disassemble(&fx.object));
    hits[0]
}

/// The in-section offset of `rung`'s one `movz` of the 16-bit immediate `imm`
/// (either register width, no shift).
#[track_caller]
fn the_movz_of(fx: &Fixture, imm: u32) -> (u64, u32) {
    let hits: Vec<(u64, u32)> = function_words(&fx.object, "rung")
        .into_iter()
        .filter(|(_, w)| w & 0x7fe0_0000 == 0x5280_0000 && (w >> 5) & 0xffff == imm)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "{}: one `movz #{imm}` expected\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    hits[0]
}

fn instantiation_theorem(report: &CerReport, symbol: &str) -> Option<String> {
    match &report.certificate(symbol)?.verdict {
        OutputVerdict::Proven {
            evidence:
                trust_cg_bridge::verify_output::ProvenEvidence::KernelInstantiated { theorem, .. },
        } => Some(theorem.clone()),
        _ => None,
    }
}

/// POSITIVE (ladder rung s02_mul_add): `x * 3 + 7` compiled to `madd` is
/// kernel-[PROVED] on both formats, by the commuted structured route.
/// FAILS without the Add-commutation retry: the grade is [VALIDATED].
#[test]
fn mul_then_add_compiled_to_madd_is_kernel_proved() {
    for triple in BOTH {
        let fx = Fixture::new(mul_then_op_module(BinOp::Add, 7, false), triple, OptLevel::O0);
        the_madd(&fx);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "rung");
        let theorem = instantiation_theorem(&report, "rung").unwrap_or_else(|| {
            panic!("{triple}: not a kernel instantiation\n{}", explain(&report))
        });
        assert!(theorem.contains("Trust.BVC.addRecM_comm"), "{triple}: {theorem}");
    }
}

/// MUTANT: the specification says `x * 3 + 8`; the object's addend is patched
/// to 7. The Add commutes; 7 is still not 8.
#[test]
fn mutant_madd_with_another_addend() {
    for triple in BOTH {
        let fx = Fixture::new(mul_then_op_module(BinOp::Add, 8, false), triple, OptLevel::O0);
        the_madd(&fx);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (off, w) = the_movz_of(&fx, 8);
        let m = fx.patched(|o| patch_word(o, off, (w & !(0xffff << 5)) | (7 << 5)));
        assert_refuted(&m, "rung", "x * 3 + 8 specified, x * 3 + 7 computed");
    }
}

/// MUTANT: the specification says `x * 3 + 7`; the object's `madd` is patched
/// into `msub` (bit 15), which computes `7 - x * 3`. Sub sits at the node the
/// retry reorders for Add and is not commuted.
#[test]
fn mutant_madd_turned_into_msub() {
    for triple in BOTH {
        let fx = Fixture::new(mul_then_op_module(BinOp::Add, 7, false), triple, OptLevel::O0);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let (off, w) = the_madd(&fx);
        let m = fx.patched(|o| patch_word(o, off, w | 0x8000));
        assert_refuted(&m, "rung", "madd turned into msub");
    }
}

/// MUTANT: the specification says `x * 3 - 7`; the object is the one compiled
/// from `7 - x * 3`. The two differ exactly by the operand order of a Sub.
#[test]
fn mutant_sub_with_commuted_operands() {
    for triple in BOTH {
        let spec = mul_then_op_module(BinOp::Sub, 7, false);
        let other = mul_then_op_module(BinOp::Sub, 7, true);
        // Each module against its own object is Proven.
        let own = Fixture::new(spec.clone(), triple, OptLevel::O0);
        let own_report = own.report();
        assert!(
            own_report.certificate("rung").expect("rung").verdict.is_proven(),
            "{triple}: x * 3 - 7 against its own object\n{}",
            explain(&own_report)
        );
        let theirs = Fixture::new(other, triple, OptLevel::O0);
        let their_report = theirs.report();
        assert!(
            their_report.certificate("rung").expect("rung").verdict.is_proven(),
            "{triple}: 7 - x * 3 against its own object\n{}",
            explain(&their_report)
        );
        let m = Fixture::with_object(targeted(&spec, triple), theirs.object.clone(), triple);
        assert_refuted(&m, "rung", "x * 3 - 7 specified, 7 - x * 3 computed");
    }
}

// ===========================================================================
// register aggregates (DECISION_QUEUE AGG-SSA-1)
// ===========================================================================

/// The producer's own `-Ztrust-dump=ir:` text for ladder rungs s14, s15, s16 and s23 (trustc
/// ac76a2c1a, `-Ztrust-ir-lower=on -Coverflow-checks=off`), `#loc`/`#scope` comments and the
/// `target` line dropped so [`targeted`] stamps each triple.
const AGG_HEAD: &str = "module \"rung\"\nstruct @P { a: u64 @0, b: u64 @8 } size=16 align=8 id=0\n\
                        enum @E repr(u64) { A = 0, B(u64) = 1 } layout(direct tag@0 size=16 \
                        align=8 offsets=[[], [8]]) id=0\n\
                        functy.0 = (u64) -> (u64)\ntype ty.0 = u64\n";

/// The rung as trust-cg receives it: the lane folds a check whose condition is a constant
/// true out of the codegen module (an unsited `Assert` never reaches trust-cg), while the
/// producer the gate reads keeps it.
fn folded(body: &str) -> String {
    body.lines().filter(|l| !l.trim_start().starts_with("assert ")).collect::<Vec<_>>().join("\n")
}

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

const S16_IR: &str = "    %1 = const u64 2
    %2 = const u64 3
    %3 = const u64 4
    %4 = const [ty.0 x 4] splat[ 0; 4 ]
    %5 = const i64 0
    %6 = insertelement [ty.0 x 4] %4, %5, %0
    %7 = const i64 1
    %8 = insertelement [ty.0 x 4] %6, %7, %1
    %9 = const i64 2
    %10 = insertelement [ty.0 x 4] %8, %9, %2
    %11 = const i64 3
    %12 = insertelement [ty.0 x 4] %10, %11, %3
    %13 = const usize 0
    %14 = const usize 4
    %15 = icmp ult usize %13, %14
    assert %15, bounds_check %13, %14
    %16 = const i64 0
    %17 = extractelement u64 %12, %16
    %18 = const usize 3
    %19 = const usize 4
    %20 = icmp ult usize %18, %19
    assert %20, bounds_check %18, %19
    %21 = const i64 3
    %22 = extractelement u64 %12, %21
    %23 = add u64 %17, %22
    ret %23";

/// `(x+1) ^ (x*2)` and `x + 4` without an aggregate: the scalar twins of s14/s15 and s16.
const S14_TWIN: &str = "    %1 = const u64 1
    %2 = add u64 %0, %1
    %3 = const u64 2
    %4 = mul u64 %0, %3
    %10 = xor u64 %2, %4
    ret %10";
const S16_TWIN: &str = "    %3 = const u64 4\n    %23 = add u64 %0, %3\n    ret %23";

/// `mov xD, xN` (`orr xD, xzr, xN`, 64-bit, any D and N other than 31).
fn is_mov_reg(w: u32) -> bool {
    w & 0xffe0_ffe0 == 0xaa00_03e0 && (w >> 16) & 31 != 31 && w & 31 != 31
}

/// `str`/`ldr xT, [xN]` (unsigned offset 0) whose base register is `n`.
fn is_ldst_base(w: u32, n: u32) -> bool {
    (w & 0xffff_fc00 == 0xf900_0000 || w & 0xffff_fc00 == 0xf940_0000) && (w >> 5) & 31 == n
}

/// Evidence that `rung` at O0 writes its aggregate through a `mov`-copied frame address, the
/// shape `sp_offset`'s OR-zero arm exists for.
fn assert_mov_addressed_frame_access(fx: &Fixture) {
    let words = function_words(&fx.object, "rung");
    let movs: Vec<u32> = words.iter().map(|(_, w)| *w).filter(|w| is_mov_reg(*w)).collect();
    assert!(
        movs.iter().any(|m| words.iter().any(|(_, w)| is_ldst_base(*w, m & 31))),
        "{}: no store or load through a mov-copied address\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
}

/// The aggregate rung at `opt`: O0 is kernel-[PROVED] and reads its aggregate through a
/// `mov`-copied frame address; at O2 it is Proven exactly as far as its scalar twin is.
fn aggregate_rung_proves(rung: &str, twin: &str) {
    for triple in BOTH {
        let fx = rung_fixture(rung, triple, OptLevel::O0);
        assert_mov_addressed_frame_access(&fx);
        assert_kernel_proved(&fx, &fx.report(), "rung");
        let fx = rung_fixture(rung, triple, OptLevel::O2);
        let report = fx.report();
        let c = report.certificate("rung").expect("rung");
        assert!(c.verdict.is_proven(), "{triple} O2\n{}", explain(&report));
        let twin = Fixture::new(rung_ir(twin), triple, OptLevel::O2).report();
        assert_eq!(
            c.is_kernel_proved(),
            twin.certificate("rung").expect("twin").is_kernel_proved(),
            "{triple} O2: the aggregate grades otherwise than its scalar twin\n{}\n{}",
            explain(&report),
            explain(&twin)
        );
    }
}

/// s14 `let t = (x+1, x*2); t.0 ^ t.1`: before AGG-SSA-1 the spec side refused the tuple
/// constant ("type outside the modeled scalar fragment: Tuple([U64, U64])") and the function
/// was Unknown.
#[test]
fn aggregate_tuple_local_is_kernel_proved() {
    aggregate_rung_proves(S14_IR, S14_TWIN);
}

/// s15: the same through a struct.
#[test]
fn aggregate_struct_local_is_kernel_proved() {
    aggregate_rung_proves(S15_IR, S14_TWIN);
}

/// s16 `let a = [x,2,3,4]; a[0] + a[3]`, with its two unsited constant bounds checks.
#[test]
fn aggregate_array_const_index_is_kernel_proved() {
    aggregate_rung_proves(S16_IR, S16_TWIN);
}

/// s17 `let mut y = x; y += 5; y`: the producer's own `-Ztrust-dump=ir:` text for the rung, from
/// the same trustc ac76a2c1a dump as [`AGG_HEAD`]'s rungs, `#loc`/`#scope` comments dropped. One
/// block-local slot, written twice and read twice. Before block-local slots the spec side refused the `alloca`
/// ("instruction `Alloca` is outside the modeled fragment") and the function was Unknown.
const S17_IR: &str = "    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = const u64 5
    %3 = load u64, ptr %1
    %4 = add u64 %3, %2
    store u64 %4, ptr %1
    %5 = load u64, ptr %1
    ret %5";

#[test]
fn block_local_slot_is_kernel_proved() {
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let fx = rung_fixture(S17_IR, triple, opt);
            assert_kernel_proved(&fx, &fx.report(), "rung");
        }
    }
}

/// The slot's spec is s17's value, not one the bytes are free to choose: s17's spec against
/// the bytes of `x + 6`, and of `x` (a load that missed the second store), is Refuted.
#[test]
fn block_local_slot_spec_refutes_other_bytes() {
    for (twin, what) in [
        ("    %1 = const u64 6\n    %2 = add u64 %0, %1\n    ret %2", "x + 6"),
        ("    ret %0", "the second load reads the first store"),
    ] {
        for triple in BOTH {
            for opt in [OptLevel::O0, OptLevel::O2] {
                let object = Fixture::new(rung_ir(twin), triple, opt).object;
                let fx = Fixture::with_object(targeted(&rung_ir(S17_IR), triple), object, triple);
                assert_refuted(&fx, "rung", &format!("{what} at {opt:?}"));
            }
        }
    }
}

/// The slot in a block other than the entry block: the slot step is handed the block being
/// evaluated, so a slot is local to whichever block defines it.
#[test]
fn block_local_slot_outside_the_entry_block_is_kernel_proved() {
    let body = format!("    br bb1\nbb1:\n{S17_IR}");
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let fx = rung_fixture(&body, triple, opt);
            assert_kernel_proved(&fx, &fx.report(), "rung");
        }
    }
}

/// `f(x) = leaf(x) + 3`, with `leaf_body` as `leaf`.
fn slot_callee_module(leaf_body: &str) -> Module {
    let text = format!(
        "module \"rung\"\nfuncty.0 = (u64) -> (u64)\n\
         fn @leaf(functy.0) {{\n    ; #producer: trust\nbb0(%0: u64):\n{leaf_body}\n}}\n\
         fn @f(functy.0) {{\n    ; #producer: trust\nbb0(%0: u64):\n    %1 = call @func.0(%0)\n    \
         %2 = const u64 3\n    %3 = add u64 %1, %2\n    ret %3\n}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{e:?}\n{text}"))
}

/// A slot inside a CALLEE. trust-cg's OPT-4 inlines only pure single-block leaves, so at O2 a
/// leaf holding a slot stays a real call (`bl`): `leaf` is graded on its own slot, `f` on the
/// call event, and both are kernel-[PROVED]; `leaf`'s spec refutes `leaf`'s bytes when they
/// compute `x + 6`. (Were the leaf inlined, the gate would interpret its IR through
/// `interpret_inlined_call`, whose slot step a unit test in `verify_output_trust_ir` pins.)
#[test]
fn block_local_slot_in_a_callee() {
    let x_plus_6 = "    %1 = const u64 6\n    %2 = add u64 %0, %1\n    ret %2";
    for triple in BOTH {
        let fx = Fixture::new(slot_callee_module(S17_IR), triple, OptLevel::O2);
        assert!(
            !bl_offsets(&fx.object, "f").is_empty(),
            "{triple}: OPT-4 now inlines a leaf with a slot; this test must then pin the \
             inlined path\n{}",
            disassemble(&fx.object)
        );
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "leaf");
        assert_kernel_proved(&fx, &report, "f");
        let object = Fixture::new(slot_callee_module(x_plus_6), triple, OptLevel::O2).object;
        let fx =
            Fixture::with_object(targeted(&slot_callee_module(S17_IR), triple), object, triple);
        assert_refuted(&fx, "leaf", "the callee computes x + 6");
    }
}

/// A slot beside a store through a pointer parameter, in one block: the slot is modeled and the
/// pointer store goes to the memory model, so the function is never graded on the slot alone.
#[test]
fn block_local_slot_beside_a_pointer_parameter_store_is_not_proven() {
    let text = "module \"rung\"\nfuncty.0 = (ptr, u64) -> (u64)\nfn @rung(functy.0) {\n    \
                ; #producer: trust\nbb0(%0: ptr, %1: u64):\n    %2 = alloca u64\n    \
                store u64 %1, ptr %2\n    store u64 %1, ptr %0\n    %3 = load u64, ptr %2\n    \
                ret %3\n}\n";
    let module = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{e:?}"));
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let fx = Fixture::new(module.clone(), triple, opt);
            let report = fx.report();
            let c = report.certificate("rung").expect("rung");
            assert!(!c.verdict.is_proven(), "{triple} {opt:?}\n{}", explain(&report));
        }
    }
}

/// The unique offset of `rung`'s word `old` (optionally the one followed by `next`), asserted.
fn the_word(fx: &Fixture, old: u32, next: Option<u32>) -> u64 {
    let words = function_words(&fx.object, "rung");
    let hits: Vec<u64> = words
        .windows(2)
        .filter(|w| w[0].1 == old && next.is_none_or(|n| w[1].1 == n))
        .map(|w| w[0].0)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "{}: {old:#010x} is not unique\n{}",
        fx.triple,
        disassemble(&fx.object)
    );
    hits[0]
}

/// Machine mutants of the O0 aggregate rungs, each Refuted. Words are those of the trust-cg
/// O0 bytes (identical to the fx-ac76 ladder objects), found by value and asserted unique.
#[test]
fn aggregate_rung_mutants_are_refuted() {
    const NOP: u32 = 0xd503_201f;
    for triple in BOTH {
        let s14 = Fixture::new(rung_ir(S14_IR), triple, OptLevel::O0);
        // `str x1, [x2]` (t.0 = x+1) writes x3 (x*2) instead.
        let at = the_word(&s14, 0xf900_0041, None);
        assert_refuted(
            &s14.patched(|o| patch_word(o, at, 0xf900_0043)),
            "rung",
            "field 0 gets field 1's value",
        );
        // `str x3, [x1]` (t.1 = x*2) dropped: t.1 stays the seed 0.
        let at = the_word(&s14, 0xf900_0023, None);
        assert_refuted(&s14.patched(|o| patch_word(o, at, NOP)), "rung", "field 1 never written");
        // The read of t.1 (`add x1, x0, #8` before `ldr x0, [x1]`) reads t.0.
        let at = the_word(&s14, 0x9100_2001, Some(0xf940_0020));
        assert_refuted(
            &s14.patched(|o| patch_word(o, at, 0x9100_0001)),
            "rung",
            "t.1 read from t.0",
        );

        let s16 = rung_fixture(S16_IR, triple, OptLevel::O0);
        // `str x3, [x0]` (a[3] = 4) dropped: a[3] stays 0, so x instead of x + 4.
        let at = the_word(&s16, 0xf900_0003, None);
        assert_refuted(&s16.patched(|o| patch_word(o, at, NOP)), "rung", "a[3] never written");
    }
}

/// A frame address copied with `mov` is still an SP offset: moving s14's aggregate base from
/// `x29 - 16` to `x29 + 16` (the caller's frame) is Refuted at the first store through the
/// copy, `str x4, [x2]` after `mov x2, x0`. Without the OR-zero arm in `sp_offset` that store
/// was Unknown ("addresses memory outside the function's frame") and only the next, `add`-
/// addressed store was Refuted.
#[test]
fn mov_copied_store_above_entry_sp_is_refuted() {
    for triple in BOTH {
        let fx = Fixture::new(rung_ir(S14_IR), triple, OptLevel::O0);
        let base = the_word(&fx, 0xd100_43a0, None); // sub x0, x29, #0x10
        let first = the_word(&fx, 0xf900_0044, Some(0x9100_2002)); // str x4, [x2] after the mov
        assert!(is_mov_reg(word_at(&fx.object, first - 8)), "{triple}: no mov before the store");
        let m = fx.patched(|o| patch_word(o, base, 0x9100_43a0)); // add x0, x29, #0x10
        let report = m.report();
        let c = report.certificate("rung").expect("rung");
        assert!(
            matches!(c.verdict, OutputVerdict::Refuted { .. }),
            "{triple}\n{}",
            explain(&report)
        );
        let o5 = &c.obligations.o5_frame.detail;
        assert!(o5.contains(&format!("the store at {first:#x} writes SP_entry")), "{triple}: {o5}");
    }
}

/// s23 `match if x & 1 == 0 { E::A } else { E::B(x) } { E::A => 5, E::B(y) => y + 1 }` (`five`
/// is the `E::A` arm's literal).
fn s23_ir(five: u64) -> String {
    format!(
        "    %3 = const u64 1
    %4 = and u64 %0, %3
    %5 = const u64 0
    %6 = icmp eq u64 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const enum.0 {{ 0 }}
    br bb3(%7)
bb2:
    %8 = const enum.0 {{ 1, 0 }}
    %9 = insertfield enum.0 %8, 1, %0
    br bb3(%9)
bb3(%1: enum.0):
    %10 = extractfield u64 %1, 0
    switch %10 [ 0: bb4 default: bb5 ]
bb4:
    %11 = const u64 {five}
    br bb6(%11)
bb5:
    %12 = extractfield u64 %1, 1
    %13 = const u64 1
    %14 = add u64 %12, %13
    br bb6(%14)
bb6(%2: u64):
    ret %2"
    )
}

/// Bytes of `report.to_json()`, counted as they are rendered, so a report that renders to
/// gigabytes fails the bound instead of exhausting memory.
fn rendered_bytes(report: &trust_cg_bridge::call_event::CerReport) -> u64 {
    struct Count(u64);
    impl std::io::Write for Count {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0 += bytes.len() as u64;
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut count = Count(0);
    serde_json::to_writer_pretty(&mut count, report).expect("the report renders");
    count.0
}

/// s23: the enum crosses a block edge and its tag selects a literal `Switch` arm. Proven at O0
/// and O2 (before AGG-SSA-1 the spec side refused the enum constant and `rung` was Unknown).
/// Kernel-[PROVED] at O0 through the closed-branch retry: the machine side keeps both arms of
/// the tag branch, whose untaken arm reads unwritten frame memory; the retry folds the two closed
/// `Ite`s, rewrites the machine's and the spec's tag tests to one term, and the kernel proves the
/// two folds' conditions and both rewrites as side conditions (DECISION_QUEUE AGG-SSA-2).
/// Kernel-[PROVED] at O2 too: there the machine tests the tag bit with `tbz`, the folded value is
/// over the bit-blast's refutation limit, and the branch split proves it inside the retry, under
/// the retry's three side conditions (DECISION_QUEUE BRANCH-SPLIT-1). With the branch split
/// stubbed out of the retry (mutant C1, `scripts/frozen-waivers.txt`) O2 is [VALIDATED], measured
/// 2026-11-14 on aarch64-apple-darwin, where the loop stops.
#[test]
fn aggregate_enum_local_is_proven() {
    for triple in BOTH {
        for opt in [OptLevel::O0, OptLevel::O2] {
            let fx = Fixture::new(rung_ir(&s23_ir(5)), triple, opt);
            let report = fx.report();
            let c = report.certificate("rung").expect("rung");
            assert!(c.verdict.is_proven(), "{triple} {opt:?}\n{}", explain(&report));
            // CER-PATH-SIZE-1: at O0 each step after the tag reload carries a 7-14 MB path
            // condition; published whole, the certificates file was 13.9 GB.
            let bytes = rendered_bytes(&report);
            assert!(
                bytes < 1 << 20,
                "{triple} {opt:?}: the certificates file renders to {bytes} bytes"
            );
            if opt == OptLevel::O0 {
                assert_kernel_proved(&fx, &report, "rung");
                let side_conditions = match &c.verdict {
                    OutputVerdict::Proven {
                        evidence:
                            ProvenEvidence::KernelRecheckableWithSideConditions {
                                side_conditions, ..
                            },
                    } => side_conditions.len(),
                    other => panic!("{triple}: not side-conditioned evidence: {other:?}"),
                };
                assert_eq!(
                    side_conditions,
                    4,
                    "{triple}: the two folds' conditions and the two rewrite instances are side \
                     conditions of the certificate\n{}",
                    explain(&report)
                );
            } else {
                assert_kernel_proved(&fx, &report, "rung");
                match &c.verdict {
                    OutputVerdict::Proven {
                        evidence:
                            ProvenEvidence::KernelRecheckableWithSideConditions {
                                value,
                                side_conditions,
                            },
                    } => {
                        assert!(
                            matches!(&**value, ProvenEvidence::KernelInstantiated { theorem, .. }
                                if theorem.ends_with("BRANCH-SPLIT-1)")),
                            "{triple} O2: the value is not the branch split's: {value:?}"
                        );
                        assert_eq!(side_conditions.len(), 3, "{triple} O2\n{}", explain(&report));
                    }
                    other => panic!("{triple} O2: not side-conditioned evidence: {other:?}"),
                }
            }
        }
    }
}

/// s23 mutants: a different `E::A` result in the IR against the original bytes; the machine's
/// `mov x0, #5` made `#6`; the payload store dropped. None is Proven.
#[test]
fn aggregate_enum_mutants_are_not_proven() {
    const NOP: u32 = 0xd503_201f;
    for triple in BOTH {
        let fx = Fixture::new(rung_ir(&s23_ir(5)), triple, OptLevel::O0);
        let spec =
            Fixture::with_object(targeted(&rung_ir(&s23_ir(6)), triple), fx.object.clone(), triple);
        assert_not_proven(&spec, "rung", "E::A => 6 specified, 5 computed");
        let five = the_word(&fx, 0xd280_00a0, None); // mov x0, #5
        assert_not_proven(&fx.patched(|o| patch_word(o, five, 0xd280_00c0)), "rung", "mov x0, #6");
        let words = function_words(&fx.object, "rung");
        // The payload store is the store of x0 (the parameter) through a register base.
        let payload: Vec<u64> =
            words.iter().filter(|(_, w)| w & 0xffff_fc1f == 0xf900_0000).map(|(o, _)| *o).collect();
        assert!(!payload.is_empty(), "{triple}: no payload store\n{}", disassemble(&fx.object));
        for at in payload {
            assert_not_proven(
                &fx.patched(|o| patch_word(o, at, NOP)),
                "rung",
                "a store of x0 dropped",
            );
        }
    }
}

// ===========================================================================
// PKG-C5c S2a: DEAD PANIC TAILS (docs/DECISION_QUEUE.md PKG-C5c-DEAD-TAIL-1)
// ===========================================================================
//
// Ladder rung s21 (`if x != 0 { 1000 / x } else { 0 }`) as the compiler lane hands it to F1:
// `M_cg` sites the division's check at `panic_const_div_by_zero` and an immutable Internal
// Location record, the producer keeps it unsited (`cer_common::sited_div`). At O0 trust-cg
// repeats the check and lowers its failure as `adrp/add` of the record (PAGE21/PAGEOFF12, ELF
// ADR_PREL_PG_HI21/ADD_ABS_LO12_NC), the record moved into x0, `bl <entry>`, `brk #1`: the
// bytes are the ladder's own s21 O0 object word for word (Darwin, 0x34..=0x44). At O2 trust-cg
// drops the dead tail. The unguarded twin (`1000 / x`) keeps its check live, and keeps its tail
// at O0 and O2.
//
// The Rust-only S2a allowance is withdrawn. Every reader Unknown remains in O1;
// neither the exact tail shape nor any mutant gets a semantic exception. Static
// byte-mutation cells below and the F1 Pic legs pin strict refusal/Unknown disclosure.

/// [`sited_div`] compiled for `triple` at `opt`: the bytes from `M_cg`, the gate reading the
/// producer's unsited check.
fn sited_div_fixture(guarded: bool, record: DivRecord, triple: &str, opt: OptLevel) -> Fixture {
    let (m_cg, producer) = sited_div(guarded, record);
    let m_cg = targeted(&m_cg, triple);
    let object = compile(&m_cg, triple, opt);
    let mut fx = Fixture::with_object(m_cg, object, triple);
    let producer = Arc::new(targeted(&producer, triple));
    fx.bodies = producer
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| (f.name.clone(), ProducerBody { producer: 0, func: f.id }))
        .collect();
    fx.producers = vec![ProducerModule::named_by_symbols(producer)];
    fx
}

/// The failure tail of `rung` in `fx`: the offsets of its `adrp`, `add` and `bl` (the `brk` is
/// at `bl + 4`) and the file offsets of their relocation records.
struct DivTail {
    adrp: u64,
    add: u64,
    bl: u64,
    r_adrp: usize,
    r_add: usize,
    r_bl: usize,
}

#[track_caller]
fn div_tail(fx: &Fixture) -> DivTail {
    let o = &fx.object;
    let record = symbol_index(o, DIV_LOCATION);
    let mut halves: Vec<(u64, usize)> = text_relocs(o)
        .into_iter()
        .filter(|(_, _, ty, sym)| *sym == record && !(is_macho(o) && *ty == 10))
        .map(|(r, at, _, _)| (at, r))
        .collect();
    halves.sort_unstable();
    let [(adrp, r_adrp), (add, r_add)] = halves[..] else {
        panic!("{}: {halves:?}\n{}", fx.triple, disassemble(o))
    };
    let bls = bl_offsets(o, "rung");
    let [bl] = bls[..] else { panic!("{}: {bls:?}\n{}", fx.triple, disassemble(o)) };
    let (r_bl, ..) = reloc_at(o, bl);
    assert_eq!(word_at(o, bl + 4), 0xd420_0020, "{}: no `brk #1` after the `bl`", fx.triple);
    assert_eq!(add, adrp + 4, "{}: the halves are not adjacent", fx.triple);
    DivTail { adrp, add, bl, r_adrp, r_add, r_bl }
}

/// Every object-reader Unknown remains in O1 verbatim; DATA cannot license a tail.
#[track_caller]
fn assert_o1_location_unknown(fx: &Fixture, what: &str) -> CerReport {
    use trust_cg_bridge::compiled_object::{CompiledObject, ObjectExpectations, ObjectLayout};
    let object = CompiledObject::parse(&fx.object).expect("parses");
    let expected = ObjectExpectations::from_module(
        &fx.m_cg,
        object.format,
        trust_cg_bridge::compiled_object::RelocationModel::Static,
    )
    .expect("expectations");
    let layout = ObjectLayout::bind(object, &expected).expect("binds");
    let window = &layout.windows["rung"];
    assert!(!window.unknown.is_empty(), "{what}: no reader Unknowns");
    let report = fx.report();
    let c = report.certificate("rung").expect("rung");
    assert_eq!(c.obligations.o1_binding.grade, Grade::Unknown, "{what}: {}", explain(&report));
    assert_eq!(c.obligations.o1_binding.detail, window.unknown.join("; "), "{what}");
    assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{what}: {}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err(), "{what}: strict shipped");
    assert!(report.ships(EmitPolicy::AllowUnknown).is_ok(), "{what}: {}", explain(&report));
    report
}

/// O0 retains the entire unlicensed panic tail; O2's tail-free kernel proof is unchanged.
#[test]
fn s2a_a_dead_sited_division_tail_remains_unknown() {
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        let tail = div_tail(&fx);
        let report = assert_o1_location_unknown(&fx, "s21 O0");
        let detail = &report.certificate("rung").unwrap().obligations.o1_binding.detail;
        assert!(detail.contains(&format!("{:#x}", tail.adrp)));
        assert!(detail.contains(&format!("{:#x}", tail.add)));
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "rung");
    }
}

/// The record's identity and shape. Each mutant keeps the tail and changes one thing the
/// withdrawn admission read; each stays Unknown at O1 on the walk's unchanged account: the `add`
/// relocated against the record's file name (`adrp` S1, `add` S2); both halves against the
/// file name (a verified immutable global that no `Assert` names: not the Location); the
/// `add` reading x2 (`Rd != Rn`); `add #8`; `add #0, lsl #12` (shift 1); `adrp` with `immlo =
/// 1`; an ELF addend of 8 on either half; Mach-O: the `adrp` relocated as GOT_LOAD_PAGE21, not
/// pc-relative, or with length 1; the `add`'s PAGEOFF12 made pc-relative or length 1; the `add`
/// made `str x1, [x0]` (a load/store page half, shift 0, Rn the `adrp`'s Rd). The unmutated
/// twin also remains Unknown. (The `add` relocated GOT_LOAD_PAGEOFF12, or the `adrp` made an `add`, is
/// refused whole by the reader, UnconsumedRelocation: MEASURED, not a gate cell.)
#[test]
fn s2a_a_pair_that_is_not_the_location_s_exact_address_stays_unknown() {
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        assert_o1_location_unknown(&fx, "twin");
        let t = div_tail(&fx);
        let file = symbol_index(&fx.object, DIV_LOCATION_FILE);
        let (wa, wd) = (word_at(&fx.object, t.adrp), word_at(&fx.object, t.add));
        let mut mutants: Vec<(&str, Fixture)> = vec![
            ("add S2", fx.patched(|o| set_reloc_symbol(o, t.r_add, file))),
            (
                "both halves at the file name",
                fx.patched(|o| {
                    set_reloc_symbol(o, t.r_adrp, file);
                    set_reloc_symbol(o, t.r_add, file);
                }),
            ),
            ("add Rn = x2", fx.patched(|o| patch_word(o, t.add, (wd & !(0x1f << 5)) | (2 << 5)))),
            ("add #8", fx.patched(|o| patch_word(o, t.add, wd | (8 << 10)))),
            ("adrp immlo = 1", fx.patched(|o| patch_word(o, t.adrp, wa | (1 << 29)))),
            ("add lsl #12", fx.patched(|o| patch_word(o, t.add, wd | (1 << 22)))),
        ];
        if triple == LINUX {
            mutants.push(("adrp addend 8", fx.patched(|o| set_elf_reloc_addend(o, t.r_adrp, 8))));
            mutants.push(("add addend 8", fx.patched(|o| set_elf_reloc_addend(o, t.r_add, 8))));
        } else {
            // ARM64_RELOC_GOT_LOAD_PAGE21 is raw type 5.
            mutants.push(("adrp GOT_LOAD_PAGE21", fx.patched(|o| set_reloc_type(o, t.r_adrp, 5))));
            mutants.push((
                "adrp not pc-relative",
                fx.patched(|o| macho_reloc_word1(o, t.r_adrp, |w| w & !(1 << 24))),
            ));
            mutants.push((
                "adrp length 1",
                fx.patched(|o| macho_reloc_word1(o, t.r_adrp, |w| (w & !(3 << 25)) | (1 << 25))),
            ));
            mutants.push((
                "add pc-relative",
                fx.patched(|o| macho_reloc_word1(o, t.r_add, |w| w | (1 << 24))),
            ));
            mutants.push((
                "add length 1",
                fx.patched(|o| macho_reloc_word1(o, t.r_add, |w| (w & !(3 << 25)) | (1 << 25))),
            ));
            // `str x1, [x0, #0]`: STR (immediate, unsigned offset), 64-bit.
            mutants.push(("add made str", fx.patched(|o| patch_word(o, t.add, 0xf900_0001))));
        }
        for (what, m) in &mutants {
            assert_o1_location_unknown(m, what);
        }
    }
}

/// Mach-O: rewrite word 1 (`r_symbolnum:24 r_pcrel:1 r_length:2 r_extern:1 r_type:4`) of the
/// relocation record at file offset `record`.
fn macho_reloc_word1(o: &mut [u8], record: usize, f: impl FnOnce(u32) -> u32) {
    let w1 = u32::from_le_bytes(o[record + 4..record + 8].try_into().unwrap());
    o[record + 4..record + 8].copy_from_slice(&f(w1).to_le_bytes());
}

/// A pair against a section, not a symbol: ELF both halves against `.text`'s section symbol
/// (trust-cg's ELF object gives the record's own section none; MEASURED); Mach-O both halves
/// non-extern against the record's section ordinal. Each binds and stays Unknown at O1
/// (MEASURED). The twin also remains Unknown.
#[test]
fn s2a_a_section_relative_pair_stays_unknown() {
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        assert_o1_location_unknown(&fx, "twin");
        let t = div_tail(&fx);
        let m = if triple == LINUX {
            let (section, _) = elf_section_symbol_of(&fx.object, "rung");
            fx.patched(|o| {
                for r in [t.r_adrp, t.r_add] {
                    set_reloc_symbol(o, r, section);
                }
            })
        } else {
            let object = trust_cg_bridge::compiled_object::CompiledObject::parse(&fx.object)
                .expect("parses");
            let ordinal = object
                .symbols
                .iter()
                .find(|y| y.name == DIV_LOCATION)
                .and_then(|y| y.section)
                .expect("the record is defined");
            fx.patched(|o| {
                for r in [t.r_adrp, t.r_add] {
                    macho_reloc_word1(o, r, |w| (w & 0xf700_0000) | ordinal as u32);
                }
            })
        };
        assert_o1_location_unknown(&m, "section-relative pair");
    }
}

/// Each historical tail-shape mutation retains the entire reader Unknown account:
/// a non-trap end, nonadjacent halves, another callee, a call off the trap and
/// a second call. No shape, including the unmodified twin, grants admission.
#[test]
fn s2a_a_tail_not_of_the_one_lowered_shape_stays_unknown() {
    const RET_X30: u32 = 0xd65f_03c0;
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        assert_o1_location_unknown(&fx, "twin");
        let t = div_tail(&fx);
        let mov = word_at(&fx.object, t.bl - 4);
        assert_eq!(mov, enc_mov(0, 1), "{triple}: no `mov x0, x1` before the `bl`");
        assert_eq!(t.add + 8, t.bl, "{triple}: the O0 tail is not adrp/add/mov/bl/brk");
        let add = word_at(&fx.object, t.add);
        let outside = fx.patched(|o| patch_word(o, t.bl + 4, RET_X30));
        assert_o1_location_unknown(&outside, "brk made ret");
        let apart = fx.patched(|o| {
            patch_word(o, t.add, mov);
            patch_word(o, t.add + 4, add);
            set_reloc_offset(o, t.r_add, t.add + 4);
        });
        assert_o1_location_unknown(&apart, "halves apart");
        let rung = symbol_index(&fx.object, "rung");
        assert_o1_location_unknown(&fx.patched(|o| set_reloc_symbol(o, t.r_bl, rung)), "bl rung");
        let unfollowed = fx.patched(|o| {
            patch_word(o, t.bl - 4, word_at(&fx.object, t.bl));
            patch_word(o, t.bl, mov);
            set_reloc_offset(o, t.r_bl, t.bl - 4);
        });
        assert_o1_location_unknown(&unfollowed, "bl not followed by the trap");
        let start = symbol_offset(&fx.object, "rung");
        let second =
            fx.patched(|o| patch_word(o, t.bl - 4, enc_bl(start as i64 - (t.bl as i64 - 4))));
        assert_o1_location_unknown(&second, "a second bl in the run");
    }
}

/// The record `M_cg` names. trust-ir's validation refuses a sited check whose Location is
/// mutable or thread-local before trust-cg emits anything (`PanicLocationGlobalInvalid`,
/// MEASURED both triples), so the gate's own condition is reached only by reading an object
/// compiled from the immutable plain-bytes record against an `M_cg` that declares it mutable,
/// or thread-local: the object binds (the reader checks no mutability for a plain image) and
/// `rung` stays Unknown at O1 (MEASURED). The immutable twin also remains Unknown.
#[test]
fn s2a_a_mutable_or_thread_local_record_is_never_admitted() {
    for triple in BOTH {
        let immutable = DivRecord::Bytes { mutable: false, tls: false };
        let twin = sited_div_fixture(true, immutable, triple, OptLevel::O0);
        assert_o1_location_unknown(&twin, "immutable plain-bytes twin");
        for (what, record) in [
            ("mutable", DivRecord::Bytes { mutable: true, tls: false }),
            ("thread-local", DivRecord::Bytes { mutable: false, tls: true }),
        ] {
            let (m_cg, _) = sited_div(true, record);
            let refusal =
                compile_under(&targeted(&m_cg, triple), triple, OptLevel::O0, fixture_license())
                    .expect_err("trust-ir validation refuses the module");
            assert!(
                refusal.to_string().contains("PanicLocationGlobalInvalid"),
                "{triple} {what}: {refusal}"
            );
            let mut fx = twin.patched(|_| {});
            fx.m_cg = Arc::new(targeted(&m_cg, triple));
            assert_o1_location_unknown(&fx, what);
        }
    }
}

/// Live and guarded tails, including raw ADRP X18 mutations, remain unlicensed.
#[test]
fn s2a_a_live_sited_check_and_x18_tail_remain_unknown() {
    for triple in BOTH {
        for (guarded, opt) in [(false, OptLevel::O0), (false, OptLevel::O2), (true, OptLevel::O0)] {
            let fx = sited_div_fixture(guarded, DivRecord::Pointer, triple, opt);
            assert_o1_location_unknown(&fx, "unmodified tail");
            let t = div_tail(&fx);
            let (wa, wd) = (word_at(&fx.object, t.adrp), word_at(&fx.object, t.add));
            let m = fx.patched(|o| {
                patch_word(o, t.adrp, (wa & !0x1f) | 18);
                patch_word(o, t.add, (wd & !(0x1f << 5)) | (18 << 5));
            });
            assert_o1_location_unknown(&m, "raw ADRP X18 does not supply semantics");
        }
    }
}

/// A reached-tail mutation still cannot bypass the earlier complete O1 refusal.
#[test]
fn s2a_a_tail_reached_where_the_ir_returns_remains_unlicensed() {
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        assert_o1_location_unknown(&fx, "twin");
        let t = div_tail(&fx);
        let words = function_words(&fx.object, "rung");
        let into_tail: Vec<u64> = words
            .iter()
            .filter(|(at, w)| is_b(*w) && *at + u64::from((w & 0x03ff_ffff) * 4) == t.adrp)
            .map(|(at, _)| *at)
            .collect();
        let [b] = into_tail[..] else { panic!("{triple}: {into_tail:?}") };
        let cond = word_at(&fx.object, b - 4);
        assert_eq!(cond & 0xff00_001f, 0x5400_0001);
        let m = fx.patched(|o| patch_word(o, b - 4, cond ^ 1));
        assert_o1_location_unknown(&m, "reached tail");
    }
}

/// An additional live unknown retains its own line and both Location lines,
/// word for word in the reader's order; no line is subtracted.
#[test]
fn s2a_another_unknown_line_keeps_o1_unknown_with_the_whole_account() {
    for triple in BOTH {
        let fx = sited_div_fixture(true, DivRecord::Pointer, triple, OptLevel::O0);
        assert_o1_location_unknown(&fx, "twin");
        let t = div_tail(&fx);
        let start = symbol_offset(&fx.object, "rung");
        assert!(start + 8 < t.adrp, "{triple}: the tail is not after the first two words");
        let m = fx.patched(|o| patch_word(o, start, enc_bl(8)));
        use trust_cg_bridge::compiled_object::RelocKind;
        let (hi, lo) = if triple == LINUX {
            (RelocKind::AdrPrelPgHi21.name(), RelocKind::AddAbsLo12Nc.name())
        } else {
            (RelocKind::Page21.name(), RelocKind::PageOff12.name())
        };
        let line = |kind: &str, at: u64| {
            format!(
                "address materialization ({kind}) at {at:#x}: symbol addresses are bound at steps \
                 5.7/5.9"
            )
        };
        let mut want = std::collections::BTreeSet::new();
        want.insert(line(&hi, t.adrp));
        want.insert(line(&lo, t.add));
        want.insert(format!(
            "unrelocated `bl` at {start:#x} targets {:#x}, which is not the start of a \
             non-preemptible local extent",
            start + 8
        ));
        let want = want.into_iter().collect::<Vec<_>>().join("; ");
        let report = m.report();
        let c = report.certificate("rung").expect("rung");
        let o1 = &c.obligations.o1_binding;
        assert!(
            o1.grade == Grade::Unknown
                && o1.detail == want
                && matches!(c.verdict, OutputVerdict::Unknown { .. }),
            "{triple}: O1 is not Unknown on the whole account\n want: {want}\n{}\n{}",
            explain(&report),
            disassemble(&m.object)
        );
    }
}

// ===========================================================================
// PKG-C5c-L0: loop cut-point segments MEASURED (test-hooks only); every loop
// stays Unknown with the spec side's reason byte for byte
// ===========================================================================

#[cfg(feature = "test-hooks")]
mod l0 {
    use trust_cg_bridge::call_event::{
        CerInput, ItemOutcome, LoopOutcome, LoopRecord, Measurement, record_loop_segments,
        verify_compiled_module,
    };

    use super::*;

    /// The suffix every measured text ends with.
    const SUFFIX: &str = "; cut-point induction not kernel-checked (fail-closed)";

    fn backedge(block: u32) -> String {
        format!("spec side: loop/backedge at bb{block} (fail-closed)")
    }

    /// One gate run on the 8 MiB gate thread, the recorder installed THERE (it is
    /// thread-local, so installing it on the test thread would record nothing).
    fn measured(fx: &Fixture) -> (CerReport, Vec<LoopRecord>) {
        let (report, records) = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(8 << 20)
                .spawn_scoped(scope, || {
                    record_loop_segments(|| {
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
        });
        let report = report.unwrap_or_else(|e| {
            panic!("{}: object refused: {e}\n{}", fx.triple, disassemble(&fx.object))
        });
        (report, records)
    }

    /// The one record, which must be a measurement.
    #[track_caller]
    fn one(fx: &Fixture, records: &[LoopRecord]) -> Measurement {
        let [record] = records else {
            panic!("{}: {} records, not one: {records:#?}", fx.triple, records.len())
        };
        assert_eq!(record.symbol, "rung");
        match &record.outcome {
            LoopOutcome::Measured(m) => (**m).clone(),
            LoopOutcome::Declined(why) => {
                panic!("{}: declined: {why}\n{}", fx.triple, disassemble(&fx.object))
            }
        }
    }

    /// Unknown with the spec side's backedge reason, byte for byte; strict refuses and
    /// allow-unknown ships.
    #[track_caller]
    fn assert_backedge_unknown(fx: &Fixture, report: &CerReport, symbol: &str, block: u32) {
        let c = report.certificate(symbol).expect("certificate");
        assert!(
            matches!(c.verdict, OutputVerdict::Unknown { .. }),
            "{}: {symbol} is not Unknown\n{}",
            fx.triple,
            explain(report)
        );
        assert_eq!(c.obligations.o4_return.detail, backedge(block), "{}", fx.triple);
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        report.ships(EmitPolicy::AllowUnknown).unwrap();
    }

    fn print(fx: &Fixture, m: &Measurement) {
        println!(
            "{}: {} | cut {:?} live-ins {:?} pinned {:?} items {} refl {} queries {} steps {} \
             arrivals ir {} m {} | {} ms",
            fx.triple,
            m.text,
            m.cut,
            m.live_ins,
            m.pinned,
            m.items.len(),
            m.refl,
            m.queries,
            m.machine_steps,
            m.ir_loop_arrivals,
            m.machine_loop_arrivals,
            m.ms
        );
    }

    /// One loop rung compiled at `opt` for `triple`.
    fn rung(r: LoopRung, triple: &str, opt: OptLevel) -> Fixture {
        Fixture::new(loop_rung_module(r, Linkage::External), triple, opt)
    }

    /// The reported pair's (entry, loop) item counts: 27 and 48 fixed items (cover, reach,
    /// return, frame, model and exit items), one `couple`/`step` item per live-in, and on Darwin
    /// (X18 reserved) `entry.x18` and `x18`. MEASURED on every rung at O0 and O2.
    fn item_counts(r: LoopRung, triple: &str) -> (usize, usize) {
        let x18 = usize::from(triple == DARWIN);
        let live = if r == LoopRung::S24 { 2 } else { 3 };
        (27 + live + x18, 48 + live + x18)
    }

    /// Every item discharged, with the text naming the cut and its per-segment counts, and the
    /// x18 and cover items present (or, off Darwin, the x18 items absent).
    #[track_caller]
    fn assert_discharged(fx: &Fixture, m: &Measurement, block: u32, r: LoopRung) {
        print(fx, m);
        assert!(m.all_discharged(), "{}: {}\n{:#?}", fx.triple, m.text, m.items);
        assert_eq!(m.cut.map(|c| c.0), Some(block), "{}: {}", fx.triple, m.text);
        assert!(m.text.starts_with(&format!("loop cut points: IR bb{block}")), "{}", m.text);
        let (e, l) = item_counts(r, &fx.triple);
        assert!(
            m.text.contains(&format!(
                ": entry segment {e}/{e} and loop segment {l}/{l} items discharged ("
            )),
            "{r:?} {}: {}",
            fx.triple,
            m.text
        );
        assert_eq!(m.items.len(), e + l, "{r:?} {}", fx.triple);
        let named = |n: &str| m.items.iter().any(|(k, _)| k == n);
        for n in ["cover.ir(or)", "cover.ir(and)", "cover.m(or)", "cover.m(and)", "exit.cond"] {
            assert!(named(n), "{r:?} {}: no {n}", fx.triple);
        }
        let darwin = fx.triple == DARWIN;
        assert_eq!((named("entry.x18"), named("x18")), (darwin, darwin), "{r:?} {}", fx.triple);
        assert!(m.text.ends_with(SUFFIX), "{}", m.text);
        assert!(m.queries > 0 && m.queries <= 256, "{}: {} queries", fx.triple, m.queries);
        assert!(m.machine_steps <= 65_536);
        assert!(m.pinned.is_empty(), "{}: {:?}", fx.triple, m.pinned);
        let segs = m.segments.as_ref().expect("segments");
        assert_eq!(segs.ir_vars.len(), m.live_ins.len());
    }

    /// PKG-C5c-L0, the O0 loop rungs: r03 (`s + (i ^ (s >> 3))`), s06 (`s += i`) and s24 (the
    /// Collatz diamond with a 64-bit multiply), each `rung(x: u64) -> u64` compiled by trust-cg
    /// at O0. The cut is the loop header bb1 at the bytes' one backward-branch target; every
    /// entry-segment and loop-segment item discharges within the deterministic caps, by refl
    /// or by ay. MEASURED: each copies `x` out of X0 (`mov x3, x0` or `mov x4, x0`) because the
    /// loop reuses X0 as a temporary, so the live-in `%0` sits in that copy (the first
    /// assignment tried, `%0 in X0`, fails first-fail and the copy's is reported). The reported
    /// pair pins nothing. The grade stays Unknown with the spec side's reason byte for byte.
    #[test]
    fn l0_o0_loop_rungs_discharge_every_item_at_the_header() {
        for r in LOOP_RUNGS {
            for triple in BOTH {
                let fx = rung(r, triple, OptLevel::O0);
                let (report, records) = measured(&fx);
                let m = one(&fx, &records);
                assert_discharged(&fx, &m, 1, r);
                assert_eq!(m.header, 1);
                assert_eq!(m.backward_targets.len(), 1, "{}", fx.triple);
                let want_regs: &[(u32, u8)] = match r {
                    LoopRung::R03 => &[(1, 2), (2, 3), (0, 4)],
                    LoopRung::S06 => &[(1, 1), (2, 2), (0, 3)],
                    LoopRung::S24 => &[(1, 3), (2, 4)],
                };
                assert_eq!(m.live_ins, want_regs, "{r:?} {}", fx.triple);
                assert_backedge_unknown(&fx, &report, "rung", 1);
            }
        }
    }

    /// PKG-C5c-L0, the O2 loop rungs. r03 and s24 are ROTATED (the bytes test the exit once
    /// before the loop and again at the latch), so the cut the measurement finds is the BODY
    /// block, not the header: r03 at bb2 and s24 at bb3 (s24's parity test), at the bytes'
    /// one backward-branch target, every item discharged. MEASURED: these ModBuilder modules
    /// do not reproduce the ladder's hoisted shift amount (r03's body is one
    /// `eor x0, x1, x2, lsr #3`), so no REPORTED pair here pins a register, and no fixture
    /// reproduces a hoisted ground-constant pin. The pinned-register path itself runs on every
    /// O0 rung (the first pair tried, `%0 in X0`, pins the copy of `x`); its items are asserted
    /// by `l0_machine_mutants_record_a_counterexample` (stale latch, wrong exit) and
    /// loop_cut/tests.rs `l0_exhaustive_pairs_pin_the_pinned_path_and_the_exit_condition`.
    #[test]
    fn l0_o2_rotated_loops_cut_at_the_body_block() {
        for (r, block) in [(LoopRung::R03, 2), (LoopRung::S24, 3)] {
            for triple in BOTH {
                let fx = rung(r, triple, OptLevel::O2);
                let (report, records) = measured(&fx);
                let m = one(&fx, &records);
                assert_discharged(&fx, &m, block, r);
                assert_eq!(m.header, 1, "{r:?}");
                assert!(
                    m.text.starts_with(&format!(
                        "loop cut points: IR bb{block} (loop header bb1) at "
                    )),
                    "{}",
                    m.text
                );
                // The header was tried first and failed: the entry reaches the body only when
                // the loop runs at least once.
                assert!(m.tried.first().is_some_and(|t| t.starts_with("bb1 [")), "{:?}", m.tried);
                assert_backedge_unknown(&fx, &report, "rung", 1);
            }
        }
    }

    /// PKG-C5c-L0, s06 at O2: trust-cg replaced the loop by a closed form, so the bytes have
    /// no backward branch and no cut-point method applies (PKG-C5c-L5). MEASURED here as on
    /// the ladder.
    #[test]
    fn l0_s06_at_o2_has_no_machine_loop() {
        for triple in BOTH {
            let fx = rung(LoopRung::S06, triple, OptLevel::O2);
            let (report, records) = measured(&fx);
            let m = one(&fx, &records);
            print(&fx, &m);
            assert_eq!(
                m.text,
                format!(
                    "loop cut points: IR loop header bb1: the bytes have 0 backward-branch \
                     target(s) [], not one{SUFFIX}"
                )
            );
            assert!(m.backward_targets.is_empty() && m.items.is_empty() && m.queries == 0);
            assert_backedge_unknown(&fx, &report, "rung", 1);
        }
    }

    /// The offset of the one word of `rung` equal to `word`.
    #[track_caller]
    fn the_word(fx: &Fixture, word: u32) -> u64 {
        let hits: Vec<u64> = function_words(&fx.object, "rung")
            .into_iter()
            .filter(|(_, w)| *w == word)
            .map(|(off, _)| off)
            .collect();
        let [off] = hits.as_slice() else {
            panic!("{}: {word:#010x} is at {hits:x?}\n{}", fx.triple, disassemble(&fx.object))
        };
        *off
    }

    /// Machine mutants of s06 at O0 (`mov x3, x0; mov x2, #0; mov x1, x2; b head; head:
    /// cmp x1, x3; b.lo body; b exit; body: add x2, x2, x1; add x0, x1, #1; mov x1, x0; b head;
    /// exit: mov x0, x2; ret`), each found by its word(s). Each records counterexamples and
    /// discharges no pair: the measurement is not a rubber stamp. For each, the reported pair
    /// (its live-ins and pins) and its EXACT set of undischarged items are pinned, every one a
    /// counterexample, so a dropped or self-compared item is caught:
    ///
    /// - forged step, clobbered live-in, callee-saved x19 (entry), wrong return (two) and x19
    ///   written in the body fail only their own items on the correct assignment;
    /// - stale latch and wrong exit are reported on the FIRST pair tried, `%0 in X0` with X3 (the
    ///   copy of `x`) pinned to its entry-arrival value: its `step.pinned(X3)` item discharges and
    ///   its counterexamples include the wrong assignment's own. That the wrong exit's
    ///   `exit.cond` is a counterexample on the CORRECT assignment too is pinned in
    ///   loop_cut/tests.rs (`l0_exhaustive_pairs_pin_the_pinned_path_and_the_exit_condition`).
    ///
    /// The grade is the same Unknown as the clean object's, byte for byte.
    #[test]
    fn l0_machine_mutants_record_a_counterexample() {
        let correct: &[(u32, u8)] = &[(1, 1), (2, 2), (0, 3)];
        let first: &[(u32, u8)] = &[(1, 1), (2, 2), (0, 0)];
        let wrong_pair: &[&str] =
            &["step(%1 in X1)", "step(%2 in X2)", "step(%0 in X0)", "exit.cond", "exit.return"];
        // (name, [(clean word, mutant word)], reported live-ins, pinned, undischarged items)
        let mutants: [(&str, &[(u32, u32)], &[(u32, u8)], &[u8], &[&str]); 8] = [
            // the latch does not advance: `add x0, x1, #1` -> `add x0, x1, #0`
            ("stale latch", &[(0x9100_0420, 0x9100_0020)], first, &[3], wrong_pair),
            // the sum lands in x's register: `add x2, x2, x1` -> `add x3, x2, x1`
            (
                "clobbered live-in",
                &[(0x8b01_0042, 0x8b01_0043)],
                correct,
                &[],
                &["step(%2 in X2)", "step(%0 in X3)"],
            ),
            // one iteration too many: `b.lo` -> `b.ls`
            ("wrong exit", &[(0x5400_0043, 0x5400_0049)], first, &[3], wrong_pair),
            // the body subtracts: `add x2, x2, x1` -> `sub x2, x2, x1`
            ("forged step", &[(0x8b01_0042, 0xcb01_0042)], correct, &[], &["step(%2 in X2)"]),
            // the entry's `b head` -> `mov x19, x0`
            ("callee-saved x19", &[(0x1400_0001, 0xaa00_03f3)], correct, &[], &["exit.frame(X19)"]),
            // the exit returns i: `mov x0, x2` -> `mov x0, x1`
            ("wrong return i", &[(0xaa02_03e0, 0xaa01_03e0)], correct, &[], &["exit.return"]),
            // the exit returns x: `mov x0, x2` -> `mov x0, x3`
            ("wrong return x", &[(0xaa02_03e0, 0xaa03_03e0)], correct, &[], &["exit.return"]),
            // the body writes x19: `add x0, x1, #1; mov x1, x0` -> `add x1, x1, #1; mov x19, x0`
            (
                "x19 in the body",
                &[(0x9100_0420, 0x9100_0421), (0xaa00_03e1, 0xaa00_03f3)],
                correct,
                &[],
                &["step.frame(X19)"],
            ),
        ];
        for triple in BOTH {
            let clean = rung(LoopRung::S06, triple, OptLevel::O0);
            let (clean_report, clean_records) = measured(&clean);
            assert!(one(&clean, &clean_records).all_discharged());
            let clean_o4 = clean_report.certificate("rung").unwrap().obligations.o4_return.clone();
            for (name, patches, live_ins, pinned, failing) in mutants {
                let at: Vec<(u64, u32)> =
                    patches.iter().map(|(from, to)| (the_word(&clean, *from), *to)).collect();
                let fx = clean.patched(|o| {
                    for (off, to) in &at {
                        patch_word(o, *off, *to);
                    }
                });
                let (report, records) = measured(&fx);
                let m = one(&fx, &records);
                print(&fx, &m);
                assert!(!m.all_discharged(), "{triple} {name}: {}", m.text);
                assert!(
                    m.text.contains("has a counterexample (not evidence against the bytes"),
                    "{triple} {name}: {}",
                    m.text
                );
                assert!(!m.text.contains(" items discharged ("), "{triple} {name}: {}", m.text);
                let undischarged: Vec<&str> = m
                    .items
                    .iter()
                    .filter(|(_, o)| !o.discharged())
                    .map(|(n, _)| n.as_str())
                    .collect();
                println!(
                    "{triple} {name}: live-ins {:?} pinned {:?}: {undischarged:?}",
                    m.live_ins, m.pinned
                );
                assert_eq!(undischarged, failing, "{triple} {name}: {:#?}", m.items);
                assert!(
                    m.items
                        .iter()
                        .filter(|(_, o)| !o.discharged())
                        .all(|(_, o)| *o == ItemOutcome::CounterExample),
                    "{triple} {name}: {:#?}",
                    m.items
                );
                assert_eq!(
                    (m.live_ins.as_slice(), m.pinned.as_slice()),
                    (live_ins, pinned),
                    "{triple} {name}"
                );
                for r in pinned {
                    let item = format!("step.pinned(X{r})");
                    let o = m.items.iter().find(|(n, _)| *n == item).map(|i| &i.1);
                    assert!(o.is_some_and(ItemOutcome::discharged), "{triple} {name}: {item}");
                }
                let c = report.certificate("rung").unwrap();
                assert_eq!(c.obligations.o4_return, clean_o4, "{triple} {name}");
                assert_backedge_unknown(&fx, &report, "rung", 1);
            }
        }
    }

    /// The recorder changes nothing the gate reports: for every loop rung at O0 and O2 the
    /// report's JSON is byte-identical with and without it, and every O4 is the spec side's
    /// backedge text.
    #[test]
    fn l0_the_recorder_leaves_the_report_byte_identical() {
        for r in LOOP_RUNGS {
            for opt in [OptLevel::O0, OptLevel::O2] {
                for triple in BOTH {
                    let fx = rung(r, triple, opt);
                    let plain = fx.report();
                    let (recorded, records) = measured(&fx);
                    assert_eq!(records.len(), 1, "{r:?} {opt:?} {triple}");
                    assert_eq!(
                        serde_json::to_string(&plain).unwrap(),
                        serde_json::to_string(&recorded).unwrap(),
                        "{r:?} {opt:?} {triple}"
                    );
                    assert_backedge_unknown(&fx, &plain, "rung", 1);
                }
            }
        }
    }

    /// The declined record of `fx`'s one function (or `symbol`).
    #[track_caller]
    fn declined(fx: &Fixture, symbol: &str) -> String {
        let (_, records) = measured(fx);
        let hits: Vec<&LoopRecord> = records.iter().filter(|r| r.symbol == symbol).collect();
        let [record] = hits.as_slice() else { panic!("{}: {records:#?}", fx.triple) };
        match &record.outcome {
            LoopOutcome::Declined(why) => why.clone(),
            LoopOutcome::Measured(m) => panic!("{}: measured: {}", fx.triple, m.text),
        }
    }

    /// s06 with the body's add routed through a call to an external `g`.
    fn s06_with_call() -> Module {
        let mut mb = ModBuilder::new("loop_rung");
        let s = mb.sig(&[Ty::U64], Some(Ty::U64));
        let g = mb.declare("g", s);
        mb.define("rung", s, Linkage::External, |fb| {
            let x = fb.p(0);
            let (head, hv) = fb.block(&[Ty::U64, Ty::U64]);
            let (body, _) = fb.block(&[]);
            let (exit, _) = fb.block(&[]);
            let zero = fb.konst(Ty::U64, 0);
            fb.br(head, &[zero, zero]);
            fb.switch_to(head);
            let (i, s) = (hv[0], hv[1]);
            let go = fb.icmp(ICmpOp::Ult, Ty::U64, i, x);
            fb.cond_br(go, body, &[], exit, &[]);
            fb.switch_to(body);
            let gi = fb.call(g, &[i]);
            let s2 = fb.bin(BinOp::Add, Ty::U64, s, gi);
            let one = fb.konst(Ty::U64, 1);
            let i2 = fb.bin(BinOp::Add, Ty::U64, i, one);
            fb.br(head, &[i2, s2]);
            fb.switch_to(exit);
            fb.ret(s);
        });
        mb.finish()
    }

    /// Two nested counting loops: `for i in 0..x { for j in 0..i { s += j } }`.
    fn nested() -> Module {
        let mut mb = ModBuilder::new("loop_rung");
        let s = mb.sig(&[Ty::U64], Some(Ty::U64));
        mb.define("rung", s, Linkage::External, |fb| {
            let x = fb.p(0);
            let (outer, ov) = fb.block(&[Ty::U64, Ty::U64]);
            let (inner, iv) = fb.block(&[Ty::U64, Ty::U64, Ty::U64]);
            let (body, _) = fb.block(&[]);
            let (next, _) = fb.block(&[]);
            let (exit, _) = fb.block(&[]);
            let zero = fb.konst(Ty::U64, 0);
            fb.br(outer, &[zero, zero]);
            fb.switch_to(outer);
            let go = fb.icmp(ICmpOp::Ult, Ty::U64, ov[0], x);
            let zero = fb.konst(Ty::U64, 0);
            fb.cond_br(go, inner, &[ov[0], zero, ov[1]], exit, &[]);
            fb.switch_to(inner);
            let more = fb.icmp(ICmpOp::Ult, Ty::U64, iv[1], iv[0]);
            fb.cond_br(more, body, &[], next, &[]);
            fb.switch_to(body);
            let s2 = fb.bin(BinOp::Add, Ty::U64, iv[2], iv[1]);
            let one = fb.konst(Ty::U64, 1);
            let j2 = fb.bin(BinOp::Add, Ty::U64, iv[1], one);
            fb.br(inner, &[iv[0], j2, s2]);
            fb.switch_to(next);
            let one = fb.konst(Ty::U64, 1);
            let i2 = fb.bin(BinOp::Add, Ty::U64, iv[0], one);
            fb.br(outer, &[i2, iv[2]]);
            fb.switch_to(exit);
            fb.ret(ov[1]);
        });
        mb.finish()
    }

    /// s06 over `u32`.
    fn s06_u32() -> Module {
        let mut mb = ModBuilder::new("loop_rung");
        let s = mb.sig(&[Ty::U32], Some(Ty::U32));
        mb.define("rung", s, Linkage::External, |fb| {
            let x = fb.p(0);
            let (head, hv) = fb.block(&[Ty::U32, Ty::U32]);
            let (body, _) = fb.block(&[]);
            let (exit, _) = fb.block(&[]);
            let zero = fb.konst(Ty::U32, 0);
            fb.br(head, &[zero, zero]);
            fb.switch_to(head);
            let go = fb.icmp(ICmpOp::Ult, Ty::U32, hv[0], x);
            fb.cond_br(go, body, &[], exit, &[]);
            fb.switch_to(body);
            let s2 = fb.bin(BinOp::Add, Ty::U32, hv[1], hv[0]);
            let one = fb.konst(Ty::U32, 1);
            let i2 = fb.bin(BinOp::Add, Ty::U32, hv[0], one);
            fb.br(head, &[i2, s2]);
            fb.switch_to(exit);
            fb.ret(hv[1]);
        });
        mb.finish()
    }

    /// s06 whose body carries an unsited check `i != 7` (the producer's shape; the codegen
    /// twin has none).
    fn s06_checked(check: bool) -> Module {
        let mut mb = ModBuilder::new("loop_rung");
        let s = mb.sig(&[Ty::U64], Some(Ty::U64));
        mb.define("rung", s, Linkage::External, |fb| {
            let x = fb.p(0);
            let (head, hv) = fb.block(&[Ty::U64, Ty::U64]);
            let (body, _) = fb.block(&[]);
            let (exit, _) = fb.block(&[]);
            let zero = fb.konst(Ty::U64, 0);
            fb.br(head, &[zero, zero]);
            fb.switch_to(head);
            let (i, s) = (hv[0], hv[1]);
            let go = fb.icmp(ICmpOp::Ult, Ty::U64, i, x);
            fb.cond_br(go, body, &[], exit, &[]);
            fb.switch_to(body);
            if check {
                let seven = fb.konst(Ty::U64, 7);
                let ok = fb.icmp(ICmpOp::Ne, Ty::U64, i, seven);
                fb.push_inst_void(Inst::Assert {
                    cond: ok,
                    kind: trust_ir::AssertKind::DivByZero,
                    site: None,
                });
            }
            let s2 = fb.bin(BinOp::Add, Ty::U64, s, i);
            let one = fb.konst(Ty::U64, 1);
            let i2 = fb.bin(BinOp::Add, Ty::U64, i, one);
            fb.br(head, &[i2, s2]);
            fb.switch_to(exit);
            fb.ret(s);
        });
        mb.finish()
    }

    /// Outside L0's fragment the record is a decline naming why, and the grade is unchanged:
    /// a call in the loop, two nested loops, 32-bit values, and an unsited check in the loop
    /// (the producer body against its check-free twin's bytes).
    #[test]
    fn l0_out_of_fragment_loops_are_declined() {
        for triple in BOTH {
            let fx = Fixture::new(s06_with_call(), triple, OptLevel::O0);
            let why = declined(&fx, "rung");
            assert!(why.starts_with("call-free: "), "{triple}: {why}");
            assert_backedge_unknown(&fx, &fx.report(), "rung", 1);

            let fx = Fixture::new(nested(), triple, OptLevel::O0);
            let why = declined(&fx, "rung");
            assert_eq!(why, "headers: 2 loop header(s), not one", "{triple}");
            // The spec side meets the inner loop's backedge first.
            assert_backedge_unknown(&fx, &fx.report(), "rung", 2);

            let fx = Fixture::new(s06_u32(), triple, OptLevel::O0);
            let why = declined(&fx, "rung");
            assert_eq!(why, "width: the result is not a 64-bit X0 scalar", "{triple}");
            assert_backedge_unknown(&fx, &fx.report(), "rung", 1);

            let object = Fixture::new(s06_checked(false), triple, OptLevel::O0).object;
            let fx = Fixture::with_object(s06_checked(true), object, triple);
            let why = declined(&fx, "rung");
            // bb1 and bb2: the check is in the loop segment (`shape_guard`'s `checks:`); bb3, the
            // exit, cuts no cycle, so its entry segment meets the backedge.
            let checks = "checks: the loop segment has side conditions, checks, events, results \
                          or memory accesses (0, 1, 0, 0, 0)";
            assert_eq!(
                why,
                format!(
                    "segments: no candidate cut block yields both segments: bb1: {checks}; bb2: \
                     {checks}; bb3: loop/backedge at bb1 (fail-closed)"
                ),
                "{triple}"
            );
            assert_backedge_unknown(&fx, &fx.report(), "rung", 1);
        }
    }

    /// Straight-line functions around two loop functions (s24's and r03's bodies) in ONE
    /// module, graded on one gate thread: the report's JSON is byte-identical with the recorder
    /// installed and without it, and a plain run on the SAME thread after the recorded one is
    /// byte-identical too, so nothing the recorder's ay queries or machine runs leave behind
    /// reaches a later function's grade. Both loops are measured; both stay Unknown with the
    /// spec side's backedge reason.
    #[test]
    fn l0_the_recorder_leaves_a_mixed_module_byte_identical() {
        fn mixed() -> Module {
            let mut mb = ModBuilder::new("mixed");
            let s = mb.sig(&[Ty::U64], Some(Ty::U64));
            mb.define("a_inc", s, Linkage::External, |fb| {
                let x = fb.p(0);
                let one = fb.konst(Ty::U64, 1);
                let r = fb.bin(BinOp::Add, Ty::U64, x, one);
                fb.ret(r);
            });
            mb.define("m_rung", s, Linkage::External, |fb| loop_rung_body(LoopRung::S24, fb));
            mb.define("n_mid", s, Linkage::External, |fb| {
                let x = fb.p(0);
                let three = fb.konst(Ty::U64, 3);
                let m = fb.bin(BinOp::Mul, Ty::U64, x, three);
                let one = fb.konst(Ty::U64, 1);
                let r = fb.bin(BinOp::Add, Ty::U64, m, one);
                fb.ret(r);
            });
            mb.define("r_rung", s, Linkage::External, |fb| loop_rung_body(LoopRung::R03, fb));
            mb.define("z_xor", s, Linkage::External, |fb| {
                let x = fb.p(0);
                let three = fb.konst(Ty::U64, 3);
                let sh = fb.bin(BinOp::LShr, Ty::U64, x, three);
                let r = fb.bin(BinOp::Xor, Ty::U64, x, sh);
                fb.ret(r);
            });
            mb.finish()
        }
        let json = |r: &CerReport| serde_json::to_string(r).unwrap();
        for opt in [OptLevel::O0, OptLevel::O2] {
            for triple in BOTH {
                let fx = Fixture::new(mixed(), triple, opt);
                let plain = fx.report();
                let input = CerInput {
                    m_cg: &fx.m_cg,
                    producers: &fx.producers,
                    bodies: &fx.bodies,
                    placements: &fx.placements,
                    object: &fx.object,
                    relocation_model: fx.model,
                };
                let (recorded, records, after) = std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(8 << 20)
                        .spawn_scoped(scope, || {
                            let (recorded, records) =
                                record_loop_segments(|| verify_compiled_module(&input));
                            (recorded, records, verify_compiled_module(&input))
                        })
                        .expect("spawn the gate thread")
                        .join()
                        .expect("the gate thread panicked")
                });
                let (recorded, after) = (recorded.unwrap(), after.unwrap());
                let symbols: Vec<&str> = records.iter().map(|r| r.symbol.as_str()).collect();
                assert_eq!(symbols, ["m_rung", "r_rung"], "{triple} {opt:?}");
                assert!(
                    records.iter().all(|r| matches!(r.outcome, LoopOutcome::Measured(_))),
                    "{triple} {opt:?}: {records:#?}"
                );
                assert_eq!(json(&plain), json(&recorded), "{triple} {opt:?}");
                assert_eq!(json(&plain), json(&after), "{triple} {opt:?} (plain after recorded)");
                assert_backedge_unknown(&fx, &plain, "m_rung", 1);
                assert_backedge_unknown(&fx, &plain, "r_rung", 1);
                for sym in ["a_inc", "n_mid", "z_xor"] {
                    let c = plain.certificate(sym).expect("certificate");
                    println!("{triple} {opt:?} {sym}: {:?}", c.verdict);
                }
            }
        }
    }
}
