// tests/pointer_slots.rs — the call-event refinement (CER) gate's EVIDENCE FOR
// POINTER SLOTS (increment 5, pointer-arguments plan PTR.0;
// docs/design/2026-10-13-step2-inc5-pointer-args-plan.md §2).
//
// What PTR.1 (sub-step 5.4.3b) will rely on when the compiler lane admits thin
// `&mut T`, `*const T` and `*mut T` slots, measured on the gate as it stands
// (no source change; `call_event.rs` is frozen SAMPLE-MORE-OR-REFUSE-MORE):
//   * a thin pointer is a CARRIED 64-bit value: passed along, swapped between
//     argument registers and returned, it is kernel-[PROVED];
//   * a pointer argument moved to the wrong register, or offset before the
//     call, is Refuted;
//   * every memory touch through a pointer (an IR `Store`/`Load`, or a store
//     the bytes make and the IR does not) and a `Ty::Func` parameter are
//     Unknown, never Proven;
//   * a frame address handed to a callee is O5 Unknown ("the frame escapes")
//     and never Proven; its verdict measures Refuted, because O3 also sees the
//     argument differ from the IR's (test 7);
//   * a co-emitted callee that writes through the pointer blocks its caller's
//     closure, so strict refuses the object;
//   * the gate reads no parameter attribute (`noalias`, `readonly`, ...).
//
// Modules are hand-built with `cer_common::ModBuilder` and compiled by trust-cg
// for Darwin `Static`, Linux `Static` and Linux `Pic` (rustc's AArch64 Linux
// default, INC5.4-PIC), at O0 and O2. P comes from
// `FnPlacement::from_scalar_signature` (which places `Ty::Ptr` at 64 bits),
// except test 8's, whose `Ty::Func` parameter that helper refuses to place.
//
// Each test names the rule it fails without; the teeth were measured with that
// rule disabled in an uncommitted working tree (restored afterwards) and are
// recorded in docs/DECISION_QUEUE.md INC5.4-PTR-EVIDENCE, and for 5(a) and 6
// since af4b2d3abd in CG-BRIDGE-LANES-1.
//
// Run (the harness row `slow.trust-cg-cer-gate` runs it):
// `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks --test pointer_slots`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "kernel-recheck")]

mod cer_common;

use cer_common::*;
use trust_cg_bridge::call_event::{
    Assumption, CallSiteKind, CerReport, FnPlacement, Grade, ParamPlace, ReturnPlace, ScalarPlace,
};
use trust_cg_bridge::compiled_object::RelocationModel;
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::RelocationModel as CgRelocationModel;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::{Endianness, Linkage, Module, StructPassingPolicy, TargetInfo, Ty};

// ===========================================================================
// helpers
// ===========================================================================

/// One (target, relocation model) leg.
#[derive(Debug, Clone, Copy)]
struct Leg {
    triple: &'static str,
    model: RelocationModel,
}

/// Darwin `Static`, Linux `Static` and Linux `Pic`.
const LEGS: [Leg; 3] = [
    Leg { triple: DARWIN, model: RelocationModel::Static },
    Leg { triple: LINUX, model: RelocationModel::Static },
    Leg { triple: LINUX, model: RelocationModel::Pic },
];

const OPTS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// Compile `module` with trust-cg for `leg` at `opt` (as `cer_common::compile`:
/// [`targeted`] at the leg's triple, under [`fixture_license`]), the symbols in
/// `never_inline` kept calls, and take it as its own producer with the natural
/// all-scalar P.
fn compile_leg(module: &Module, leg: Leg, opt: OptLevel, never_inline: &[&str]) -> Fixture {
    let module = &targeted(module, leg.triple);
    let spec = TargetSpec::parse(leg.triple).expect("triple parses");
    let config = CompilerConfig {
        opt_level: opt,
        parallel: false,
        relocation_model: match leg.model {
            RelocationModel::Static => CgRelocationModel::Static,
            RelocationModel::Pie => CgRelocationModel::Pie,
            RelocationModel::Pic => CgRelocationModel::Pic,
        },
        never_inline: never_inline.iter().map(|s| (*s).to_string()).collect(),
        ..CompilerConfig::default()
    };
    let object = Compiler::new_for_target_spec(config, spec)
        .with_codegen_license(fixture_license())
        .compile(module)
        .unwrap_or_else(|e| panic!("{leg:?} {opt:?}: Compiler::compile failed: {e}"))
        .object_code;
    let mut fx = Fixture::with_object(module.clone(), object, leg.triple);
    fx.model = leg.model;
    fx
}

fn kernel_proved(report: &CerReport, symbol: &str) -> bool {
    report.certificate(symbol).is_some_and(|c| c.is_kernel_proved())
}

#[track_caller]
fn assert_kernel_proved(fx: &Fixture, report: &CerReport, symbol: &str, what: &str) {
    assert!(
        kernel_proved(report, symbol),
        "{what}: `{symbol}` is not kernel-[PROVED]\n{}\n{}",
        explain(report),
        disassemble(&fx.object)
    );
}

/// The certificate of `symbol`, which must be Unknown: neither Proven nor a
/// fabricated Refuted.
#[track_caller]
fn assert_unknown<'r>(
    fx: &Fixture,
    report: &'r CerReport,
    symbol: &str,
    what: &str,
) -> &'r trust_cg_bridge::call_event::FunctionCertificate {
    let c = report.certificate(symbol).unwrap_or_else(|| panic!("{what}: no `{symbol}`"));
    assert!(
        matches!(c.verdict, OutputVerdict::Unknown { .. }),
        "{what}: `{symbol}` is not Unknown ({})\n{}\n{}",
        c.grade,
        explain(report),
        disassemble(&fx.object)
    );
    c
}

/// The words of `f` before its first `bl`.
fn before_call(o: &[u8], f: &str) -> Vec<(u64, u32)> {
    let bl = *bl_offsets(o, f).first().expect("a `bl` in the caller");
    function_words(o, f).into_iter().filter(|(off, _)| *off < bl).collect()
}

/// The frame-pointer setup `mov x29, sp` / `add x29, sp, #imm` of `f`, before
/// its first call: a slot a machine-side mutant may overwrite (the frame record
/// is restored from the stack, so O0 does not depend on it).
fn frame_pointer_setup(o: &[u8], f: &str) -> u64 {
    before_call(o, f)
        .into_iter()
        .find(|(_, w)| w & 0xffc0_03ff == 0x9100_03fd)
        .map(|(off, _)| off)
        .unwrap_or_else(|| {
            panic!("`{f}` sets no frame pointer before its call\n{}", disassemble(o))
        })
}

/// Whether `w` writes `X0` or `X1`: the register-writing classes trust-cg
/// emits before a call (logical and add/sub, register and immediate forms;
/// wide moves; 64-bit loads; load pairs).
fn writes_x0_or_x1(w: u32) -> bool {
    let rd = w & 0x1f;
    let dp = w & 0x1f00_0000 == 0x0a00_0000
        || w & 0x1f00_0000 == 0x0b00_0000
        || w & 0x1f00_0000 == 0x1100_0000
        || w & 0x1f80_0000 == 0x1200_0000
        || w & 0x1f80_0000 == 0x1280_0000;
    let load = w & 0xffc0_0000 == 0xf940_0000 || w & 0xffe0_0c00 == 0xf840_0000;
    let load_pair = w & 0x7e40_0000 == 0x2840_0000;
    ((dp || load) && rd <= 1) || (load_pair && (rd <= 1 || (w >> 10) & 0x1f <= 1))
}

/// `str xzr, [x0]`.
const STR_XZR_AT_X0: u32 = 0xf900_001f;

// ===========================================================================
// modules
// ===========================================================================

/// `g(q: ptr, y: u64) -> ptr = q` (Internal, kept a call) and
/// `f(x: u64, p: ptr) -> ptr = g(p, x)`: the pointer moves from X1 to X0 at the
/// call, and back out as `f`'s result.
fn pass_through_module() -> Module {
    let mut mb = ModBuilder::new("ptr_pass_through");
    let sg = mb.sig(&[Ty::Ptr, Ty::U64], Some(Ty::Ptr));
    let sf = mb.sig(&[Ty::U64, Ty::Ptr], Some(Ty::Ptr));
    let g = mb.define("g", sg, Linkage::Internal, |fb| fb.ret(fb.p(0)));
    mb.define("f", sf, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(1), fb.p(0)]);
        fb.ret(r);
    });
    mb.finish()
}

/// `id(p: ptr) -> ptr = p`, `pick(a: ptr, b: ptr, k: u64) -> ptr =
/// if k != 0 { a } else { b }` (a `Select` of two pointers), and `pick_u64`,
/// the same function over `u64`: the control `pick` is graded against.
fn identity_and_pick_module() -> Module {
    let mut mb = ModBuilder::new("ptr_identity");
    let s1 = mb.sig(&[Ty::Ptr], Some(Ty::Ptr));
    mb.define("id", s1, Linkage::External, |fb| fb.ret(fb.p(0)));
    for (name, ty) in [("pick", Ty::Ptr), ("pick_u64", Ty::U64)] {
        let s3 = mb.sig(&[ty.clone(), ty.clone(), Ty::U64], Some(ty.clone()));
        mb.define(name, s3, Linkage::External, |fb| {
            let zero = fb.konst(Ty::U64, 0);
            let k = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(2), zero);
            let out = fb.push_inst(Inst::Select {
                ty: ty.clone(),
                cond: k,
                then_val: fb.p(0),
                else_val: fb.p(1),
            });
            fb.ret(out);
        });
    }
    mb.finish()
}

/// `f(p: ptr, q: ptr) -> ptr { ext(q, p); p }`, `ext(ptr, ptr) -> u64` an
/// External declaration: the arguments are swapped at the call and `p` lives
/// across it.
fn swap_module() -> Module {
    let mut mb = ModBuilder::new("ptr_swap");
    let se = mb.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::U64));
    let sf = mb.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::Ptr));
    let ext = mb.declare("ext", se);
    mb.define("f", sf, Linkage::External, |fb| {
        let _ignored = fb.call(ext, &[fb.p(1), fb.p(0)]);
        fb.ret(fb.p(0));
    });
    mb.finish()
}

/// `f(p: ptr) -> u64 = g(p) + 1`, `g(ptr) -> u64` an External declaration.
fn ptr_wrapper_module() -> Module {
    let mut mb = ModBuilder::new("ptr_wrapper");
    let sg = mb.sig(&[Ty::Ptr], Some(Ty::U64));
    let g = mb.declare("g", sg);
    mb.define("f", sg, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

/// `f(p: ptr, v: u64) -> u64 { *p = v; v }`.
fn store_module() -> Module {
    let mut mb = ModBuilder::new("ptr_store");
    let s = mb.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    mb.define("f", s, Linkage::External, |fb| {
        fb.push_inst_void(Inst::Store {
            ty: Ty::U64,
            ptr: fb.p(0),
            value: fb.p(1),
            volatile: false,
            align: None,
        });
        fb.ret(fb.p(1));
    });
    mb.finish()
}

/// `module` carrying the `target_info` the producer states for `triple`
/// (`compiler/rustc_codegen_trust_cg/src/trust_ir_frontend/codegen_module.rs`,
/// rule 7: 8-byte pointers, little-endian, `struct_passing = unclassified`), so
/// the spec side reaches the source byte-memory model instead of its no-target
/// refusal. f1_compile's `m_cg_target_info` states the same.
fn stated_target(module: &Module, triple: &str) -> Module {
    let mut module = module.clone();
    module.target_info = Some(TargetInfo {
        triple: triple.to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}

/// `f(p: ptr) -> u64 = *p`.
fn load_module() -> Module {
    let mut mb = ModBuilder::new("ptr_load");
    let s = mb.sig(&[Ty::Ptr], Some(Ty::U64));
    mb.define("f", s, Linkage::External, |fb| {
        let v =
            fb.push_inst(Inst::Load { ty: Ty::U64, ptr: fb.p(0), volatile: false, align: None });
        fb.ret(v);
    });
    mb.finish()
}

/// `f(x: u64, h: fn(u64) -> u64) -> fn(u64) -> u64 = h`: a `Ty::Func`
/// parameter moved from X1 to X0.
fn fn_pointer_module() -> Module {
    let mut mb = ModBuilder::new("ptr_fn");
    let callee = mb.sig(&[Ty::U64], Some(Ty::U64));
    let fty = Ty::Func(callee);
    let s = mb.sig(&[Ty::U64, fty.clone()], Some(fty));
    mb.define("f", s, Linkage::External, |fb| fb.ret(fb.p(1)));
    mb.finish()
}

/// `g(p: ptr, v: u64) { *p = v }` (Internal, kept a call: a co-emitted callee
/// that writes through its pointer) and `f(p: ptr, v: u64) -> u64 { g(p, v); v }`.
fn writer_callee_module() -> Module {
    let mut mb = ModBuilder::new("ptr_writer_callee");
    let sg = mb.sig(&[Ty::Ptr, Ty::U64], None);
    let sf = mb.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    let g = mb.define("g", sg, Linkage::Internal, |fb| {
        fb.push_inst_void(Inst::Store {
            ty: Ty::U64,
            ptr: fb.p(0),
            value: fb.p(1),
            volatile: false,
            align: None,
        });
        fb.ret_void();
    });
    mb.define("f", sf, Linkage::External, |fb| {
        fb.call_void(g, &[fb.p(0), fb.p(1)]);
        fb.ret(fb.p(1));
    });
    mb.finish()
}

// ===========================================================================
// 1-2. A THIN POINTER IS A CARRIED VALUE
// ===========================================================================

/// Test 1. `f(x, p) = g(p, x)` with `g` a co-emitted body: the pointer moves X1 ->
/// X0 at the call and comes back as the result. Both functions are
/// kernel-[PROVED] and `f` closes on `g`'s certificate, on every leg and level.
/// FAILS without `scalar_reg_width`'s `Ty::Ptr => 64` arm
/// (verify_output_trust_ir.rs): P cannot place either signature.
#[test]
fn pointer_pass_through_to_a_coemitted_callee_is_kernel_proved() {
    let module = pass_through_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &["g"]);
            let report = fx.report();
            assert_kernel_proved(&fx, &report, "f", &what);
            assert_kernel_proved(&fx, &report, "g", &what);
            let c = report.certificate("f").unwrap();
            assert_eq!(c.call_sites.len(), 1, "{what}\n{}", explain(&report));
            assert_eq!(c.call_sites[0].symbol, "g", "{what}");
            assert!(
                matches!(c.call_sites[0].kind, CallSiteKind::Direct | CallSiteKind::Tail),
                "{what}: {:?}",
                c.call_sites[0]
            );
            assert_eq!(c.assumptions, vec![Assumption::CoEmitted("g".into())], "{what}");
            assert!(report.closure.closed_kernel.contains(&"f".to_string()), "{what}");
            report.ships(EmitPolicy::StrictProvenOnly).unwrap_or_else(|e| panic!("{what}: {e}"));
        }
    }
}

/// Test 2. `id(p) = p` is kernel-[PROVED] on every leg and level. `pick(a, b, k)`
/// (a `Select` of two pointers) is Proven, at exactly the grade of the same
/// function over `u64`: the pointer slot changes nothing. MEASURED at this
/// commit: both are [VALIDATED] (ay discharges them; the clean kernel does not
/// re-check the `csel` conjunction) on every leg and level, which
/// INC5.4-PTR-EVIDENCE records as a finding for PTR.1's strict expectations.
/// FAILS without `scalar_reg_width`'s `Ty::Ptr => 64` arm.
#[test]
fn pointer_identity_return_is_kernel_proved() {
    let module = identity_and_pick_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &[]);
            let report = fx.report();
            assert_kernel_proved(&fx, &report, "id", &what);
            let pick = report.certificate("pick").expect("pick");
            let control = report.certificate("pick_u64").expect("pick_u64");
            assert!(
                pick.verdict.is_proven() && control.verdict.is_proven(),
                "{what}: `pick` is {}, `pick_u64` is {}\n{}\n{}",
                pick.grade,
                control.grade,
                explain(&report),
                disassemble(&fx.object)
            );
            assert_eq!(
                pick.grade, control.grade,
                "{what}: a pointer `Select` grades apart from u64"
            );
            eprintln!("pick [{what}]: {} (u64 control: {})", pick.grade, control.grade);
        }
    }
}

// ===========================================================================
// 3-4. A MOVED OR OFFSET POINTER ARGUMENT IS REFUTED
// ===========================================================================

/// Test 3. As `call_event_gate.rs`'s `mutant_swapped_argument_registers`, with two
/// pointers: every instruction before the call that writes X0 or X1 is
/// dropped, so `ext` receives `(p, q)`, not `(q, p)`. The twin is
/// kernel-[PROVED]; the mutant is Refuted.
/// FAILS without O3's per-argument equation (`discharge_under`'s `arg{j}`
/// items, call_event.rs): the mutant is then Proven.
#[test]
fn mutant_swapped_pointer_arguments_is_refuted() {
    let module = swap_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &[]);
            assert_kernel_proved(&fx, &fx.report(), "f", &what);
            let mut patched = 0;
            let m = fx.patched(|o| {
                for (off, w) in before_call(o, "f") {
                    if writes_x0_or_x1(w) {
                        patch_word(o, off, NOP);
                        patched += 1;
                    }
                }
            });
            assert!(patched > 0, "{what}: nothing wrote X0/X1\n{}", disassemble(&fx.object));
            let report = m.report();
            let c = report.certificate("f").unwrap();
            assert!(
                matches!(c.verdict, OutputVerdict::Refuted { .. }),
                "{what}: swapped pointer arguments not Refuted\n{}\n{}",
                explain(&report),
                disassemble(&m.object)
            );
            assert_eq!(c.obligations.o3_events.grade, Grade::Refuted, "{}", explain(&report));
        }
    }
}

/// Test 4. `f(p) = g(p) + 1` with `add x0, x0, #8` written into the frame-pointer
/// setup before `bl g`: `g` receives `p + 8`. The twin is kernel-[PROVED]; the
/// mutant is Refuted at O3.
/// FAILS without O3's per-argument equation.
#[test]
fn mutant_offset_pointer_argument_is_refuted() {
    let module = ptr_wrapper_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &[]);
            assert_kernel_proved(&fx, &fx.report(), "f", &what);
            let m = fx.patched(|o| {
                let slot = frame_pointer_setup(o, "f");
                patch_word(o, slot, enc_add_imm(0, 0, 8));
            });
            let report = m.report();
            let c = report.certificate("f").unwrap();
            assert!(
                matches!(c.verdict, OutputVerdict::Refuted { .. }),
                "{what}: offset pointer argument not Refuted\n{}\n{}",
                explain(&report),
                disassemble(&m.object)
            );
            assert_eq!(c.obligations.o3_events.grade, Grade::Refuted, "{}", explain(&report));
        }
    }
}

// ===========================================================================
// 5-8. EVERY MEMORY TOUCH, EVERY ESCAPE AND A `Ty::Func` PARAMETER ARE UNKNOWN
// ===========================================================================

/// Test 5. (a) The IR stores through `p`: Unknown, and never a fabricated
/// Refuted. The module states its leg's target, so since af4b2d3abd the IR
/// `Store` reaches the source byte-memory model, whose PTR.3b frontier sends
/// `f` to the bounded-leaf route: on Linux that route has no evidence, and on
/// Darwin its joint kernel goal is declined (`pointer_memory_refusal`). (a)
/// pins each leg's refusal by name. FAILS without
/// `ResultMemory::missing_integration` (measured 2026-11-06 by the hostile
/// review: O4 is then Proven and `f` stays Unknown only through O5, so only
/// the refusal assertion catches it; with O5's frame clause disabled as well,
/// `f` is [PROVED]). On Darwin the Unknown rests on that kernel decline: a
/// leaf grade there would be a kernel proof of the store, so this assertion
/// moves with a recorded decision if the leaf kernel learns to close it.
/// (b) The bytes store through `p` (`str xzr, [x0]` written into the
/// frame-pointer setup of `f(p) = g(p) + 1`) and the IR does not: O5 is
/// Unknown (a store outside the function's frame), and so is the function.
/// Before af4b2d3abd (a)'s refusal was `eval_ir_inst`'s catch-all, measured
/// then: skipping the `Store` left `f` Unknown only through O5, and with O5's
/// clause disabled as well, `f` was [PROVED]. (b) FAILS without O5's "outside
/// the function's frame" clause (`check_memory`, call_event.rs): measured, the
/// mutant is then [PROVED].
#[test]
fn a_store_through_a_pointer_parameter_is_unknown_never_proven() {
    let stores = store_module();
    let wrapper = ptr_wrapper_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            // (a)
            let fx = compile_leg(&stated_target(&stores, leg.triple), leg, opt, &[]);
            let report = fx.report();
            let c = assert_unknown(&fx, &report, "f", &format!("{what} (a)"));
            if let Err(e) = pointer_memory_refusal(c, leg.triple == DARWIN) {
                panic!("{what} (a): {e}\n{}", explain(&report));
            }
            // (b)
            let fx = compile_leg(&wrapper, leg, opt, &[]);
            assert_kernel_proved(&fx, &fx.report(), "f", &what);
            let m = fx.patched(|o| {
                let slot = frame_pointer_setup(o, "f");
                patch_word(o, slot, STR_XZR_AT_X0);
            });
            let report = m.report();
            let c = assert_unknown(&m, &report, "f", &format!("{what} (b)"));
            assert_eq!(c.obligations.o5_frame.grade, Grade::Unknown, "{}", explain(&report));
            assert!(
                c.obligations.o5_frame.detail.contains("outside the function's frame"),
                "{what} (b): {}",
                explain(&report)
            );
        }
    }
}

/// Test 6. `f(p) = *p`: Unknown, never Proven and never a fabricated Refuted.
/// The module states its leg's target, so since af4b2d3abd the IR `Load`
/// reaches the source byte-memory model, whose PTR.3b frontier sends `f` to
/// the bounded-leaf route, refused as in test 5(a) (`pointer_memory_refusal`);
/// the assertion pins each leg's refusal by name. FAILS without
/// `ResultMemory::missing_integration` (measured 2026-11-06 by the hostile
/// review: O4 is then Proven and `f` stays Unknown only through O5; with O5's
/// frame clause disabled as well, `f` is [VALIDATED]). Before it, the refusal was
/// `eval_ir_inst`'s catch-all, measured then: modeling the load as a fresh value
/// left `f` Unknown through two other readings (O4: "a counterexample only
/// through memory"; O5: a load outside the frame).
#[test]
fn a_load_through_a_pointer_parameter_is_unknown() {
    let module = load_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&stated_target(&module, leg.triple), leg, opt, &[]);
            let report = fx.report();
            let c = assert_unknown(&fx, &report, "f", &what);
            if let Err(e) = pointer_memory_refusal(c, leg.triple == DARWIN) {
                panic!("{what}: {e}\n{}", explain(&report));
            }
        }
    }
}

/// Test 7. `f(p) = g(p) + 1` with `mov x0, sp` written into the frame-pointer
/// setup: the call hands `g` an address in `f`'s frame. O5 is Unknown (the
/// frame escapes) and the function is never Proven. The verdict is Refuted
/// (measured): O3 also sees the argument differ from the IR's `p`, since an
/// IR in the gate's fragment cannot name a frame address (`Alloca` is outside
/// it), so this real frame address and an argument mismatch arrive together.
/// FAILS without the escape clause of `CerExec::event` (call_event.rs: an
/// argument that mentions SP is O5 Unknown) — through the O5 assertions only:
/// with the clause off the verdict stays Refuted by O3, so this test cannot
/// show that O5 alone stops a false [PROVED]. The clause is syntactic
/// (`mentions_sp`); an argument term that mentions SP yet equals the IR's
/// value would pass O3 and leave O5 its only guard (not measured).
#[test]
fn a_frame_address_passed_at_a_call_is_unknown() {
    let module = ptr_wrapper_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &[]);
            assert_kernel_proved(&fx, &fx.report(), "f", &what);
            let m = fx.patched(|o| {
                let slot = frame_pointer_setup(o, "f");
                patch_word(o, slot, enc_mov_from_sp(0));
            });
            let report = m.report();
            let c = report.certificate("f").unwrap();
            assert!(!c.verdict.is_proven(), "{what}: an escaped frame address was PROVEN");
            assert_eq!(
                c.obligations.o5_frame.grade,
                Grade::Unknown,
                "{what}: {}",
                explain(&report)
            );
            assert!(
                c.obligations.o5_frame.detail.contains("the frame escapes"),
                "{what}: {}",
                explain(&report)
            );
            eprintln!("escaped frame address [{what}]: {}", c.grade);
        }
    }
}

/// Test 8. `f(x, h: fn(u64) -> u64) = h`, under a hand-built P that places `h` as a
/// 64-bit X1 slot (`from_scalar_signature` refuses `Ty::Func`): Unknown until
/// step 5.9, because the gate does not place a `Ty::Func` slot even when P
/// does.
/// FAILS without `scalar_reg_width`'s refusal of `Ty::Func` (its catch-all):
/// with a `Func => 64` arm the move is Proven.
#[test]
fn a_fn_pointer_parameter_is_unknown_until_5_9() {
    let module = fn_pointer_module();
    let p = FnPlacement {
        params: vec![
            ParamPlace::Scalar(ScalarPlace::gpr(0, 64)),
            ParamPlace::Scalar(ScalarPlace::gpr(1, 64)),
        ],
        ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
    };
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let mut fx = compile_leg(&module, leg, opt, &[]);
            fx.placements.insert("f".into(), p.clone());
            let report = fx.report();
            let c = assert_unknown(&fx, &report, "f", &what);
            let o4 = &c.obligations.o4_return.detail;
            assert!(
                o4.contains("disagrees with its producer signature") && o4.contains("Func"),
                "{what}: {}",
                explain(&report)
            );
        }
    }
    // The hand-built P is needed: the helper refuses to place a `Ty::Func` slot.
    let f = module.functions.iter().find(|f| f.name == "f").unwrap();
    assert!(
        FnPlacement::from_scalar_signature(&module, f).is_err(),
        "the helper places a `Ty::Func` slot: this test no longer needs its hand-built P"
    );
}

// ===========================================================================
// 9. A CALLEE THAT WRITES THROUGH THE POINTER BLOCKS ITS CALLER
// ===========================================================================

/// Test 9. `f(p, v) { g(p, v); v }` with `g(p, v) { *p = v }` co-emitted: `f` is
/// kernel-[PROVED] by itself, `g` is Unknown, and the closure names `g` as what
/// blocks `f`, so strict refuses the object and allow-unknown ships it.
/// FAILS without the closure's `CoEmitted` rule (`closure_report`,
/// call_event.rs: a co-emitted callee must itself be closed).
#[test]
fn a_callee_writing_through_the_pointer_blocks_its_caller_under_strict() {
    let module = writer_callee_module();
    for leg in LEGS {
        for opt in OPTS {
            let what = format!("{leg:?} {opt:?}");
            let fx = compile_leg(&module, leg, opt, &["g"]);
            let report = fx.report();
            assert_kernel_proved(&fx, &report, "f", &what);
            assert_unknown(&fx, &report, "g", &what);
            assert_eq!(
                report.certificate("f").unwrap().assumptions,
                vec![Assumption::CoEmitted("g".into())],
                "{what}"
            );
            assert!(!report.closure.closed_kernel.contains(&"f".to_string()), "{what}");
            let f_unclosed = report
                .closure
                .unclosed
                .iter()
                .find(|u| u.symbol == "f")
                .unwrap_or_else(|| panic!("{what}: `f` closed: {:?}", report.closure));
            assert_eq!(f_unclosed.blocked_by, vec!["g".to_string()], "{what}");
            let err = report.ships(EmitPolicy::StrictProvenOnly).unwrap_err();
            assert!(err.contains("f ([PROVED]; blocked by [g])"), "{what}: {err}");
            report.ships(EmitPolicy::AllowUnknown).unwrap_or_else(|e| panic!("{what}: {e}"));
        }
    }
}

// ===========================================================================
// 10. THE GATE READS NO PARAMETER ATTRIBUTE
// ===========================================================================

/// Test 10. The gate's sources contain no read of a parameter attribute or of a
/// signature's ABI attributes: CE, the trust-ir executor, the shared executor
/// pieces it reads (`verify_output.rs`, frozen-files.txt's SCOPE note), the
/// object reader and the shipping consumer. `.abi.` is not a needle:
/// `verify_output.rs` reads `outcome.abi.slots()`, which is not a signature.
/// FAILS the day one of these files names an attribute.
#[test]
fn the_gate_reads_no_param_attrs() {
    const SOURCES: [(&str, &str); 5] = [
        ("src/call_event.rs", include_str!("../src/call_event.rs")),
        ("src/verify_output_trust_ir.rs", include_str!("../src/verify_output_trust_ir.rs")),
        ("src/verify_output.rs", include_str!("../src/verify_output.rs")),
        ("src/compiled_object.rs", include_str!("../src/compiled_object.rs")),
        ("src/f1_compile.rs", include_str!("../src/f1_compile.rs")),
    ];
    const NEEDLES: [&str; 9] = [
        ".noalias",
        ".readonly",
        ".readnone",
        ".dereferenceable",
        ".nonnull",
        "attrs.params",
        "ParamAttrs",
        "SignatureAbi",
        "AbiAttributes",
    ];
    // The scan reads the files it names.
    assert!(SOURCES[0].1.contains("pub fn verify_compiled_module"));
    assert!(SOURCES[4].1.contains("pub fn compile_and_verify_trust_ir_module"));
    let hits: Vec<String> = SOURCES
        .iter()
        .flat_map(|(path, text)| {
            text.lines().enumerate().flat_map(move |(i, line)| {
                NEEDLES
                    .iter()
                    .filter(move |n| line.contains(**n))
                    .map(move |n| format!("{path}:{}: `{n}`: {}", i + 1, line.trim()))
            })
        })
        .collect();
    assert!(
        hits.is_empty(),
        "the CER gate reads a parameter attribute; PTR.1 assumes it reads none \
         (docs/design/2026-10-13-step2-inc5-pointer-args-plan.md §0.5, §8):\n{}",
        hits.join("\n")
    );
}

// ===========================================================================
// measurement
// ===========================================================================

/// Not an assertion: prints what trust-cg emits for each module on each leg,
/// so the patchers above can be read off the bytes. `--ignored --nocapture`.
#[test]
#[ignore]
fn dump_pointer_shapes() {
    for (name, module, keep) in [
        ("pass_through", pass_through_module(), &["g"][..]),
        ("identity_and_pick", identity_and_pick_module(), &[][..]),
        ("swap", swap_module(), &[][..]),
        ("ptr_wrapper", ptr_wrapper_module(), &[][..]),
        ("store", store_module(), &[][..]),
        ("load", load_module(), &[][..]),
        ("fn_pointer", fn_pointer_module(), &[][..]),
        ("writer_callee", writer_callee_module(), &["g"][..]),
    ] {
        for leg in LEGS {
            for opt in OPTS {
                let fx = compile_leg(&module, leg, opt, keep);
                eprintln!("==== {name} {leg:?} {opt:?}\n{}", disassemble(&fx.object));
                match fx.verify() {
                    Ok(report) => eprintln!("{}", explain(&report)),
                    Err(e) => eprintln!("object refused: {e}"),
                }
            }
        }
    }
}
