// tests/variadic_split_attacks.rs — the adversarial battery against the
// call-event gate's unknown-variadic-split block (`block_unknown_variadic_split`
// in src/call_event.rs), kept as regression tests.
//
// Each test builds a producer (or a compiled module) whose call has an UNKNOWN
// or WRONG fixed/anonymous split by a route other than the two shapes the first
// version of the block named (`(...)` and a variadic Rust-ABI signature, read
// only on the six call instructions' own signatures), and asserts what the
// block promises: Refuted, so the object ships under NO policy. A failing test
// is a hole: the gate graded the shape Unknown (or Proven) and
// `EmitPolicy::AllowUnknown` ships it. The failure message carries every
// certificate's grade. MEASURED before the closing change: A1-A9 failed (55
// instances), the two controls passed.
//
// Every attack has an unmutated twin in the same test that is kernel-[PROVED],
// so an attack cannot pass by the harness being broken.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Run: `targo --unverified test -p trust-cg-bridge --features
// kernel-recheck,test-hooks --test variadic_split_attacks`.

#![cfg(feature = "kernel-recheck")]

mod cer_common;

use std::sync::Arc;

use cer_common::*;
use trust_cg_bridge::call_event::{CerReport, ProducerBody, ProducerModule};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::{AssertKind, BinOp, CastOp, ICmpOp, Inst, PanicLocation, PanicSite};
use trust_ir::value::FuncTyId;
use trust_ir::{CallingConv, Constant, Global, Linkage, Module, Ty, Visibility};

const X86_64: &str = "x86_64-unknown-linux-gnu";

fn u64s(n: usize) -> Vec<Ty> {
    vec![Ty::U64; n]
}

/// `f(x) = g(x) + 1`, `g` an External declaration.
fn wrapper_module() -> Module {
    let mut mb = ModBuilder::new("attack_wrapper");
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

#[track_caller]
fn assert_kernel_proved(fx: &Fixture, report: &CerReport, symbol: &str) {
    assert!(
        report.certificate(symbol).is_some_and(|c| c.is_kernel_proved()),
        "{}: harness twin `{symbol}` is not kernel-[PROVED]\n{}",
        fx.triple,
        explain(report)
    );
}

/// A copy of `fx` whose only producer is `producer`; the named bodies are read
/// from it. P and the object are untouched.
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

/// [`with_producer`], with `M_cg` the producer itself: every module the gate
/// reads then declares the callee alike, so the cross-declaration rule cannot
/// block the attack and only the rule the test names can.
fn with_producer_as_m_cg(fx: &Fixture, producer: Module, bodies: &[&str]) -> Fixture {
    let mut m = with_producer(fx, producer, bodies);
    m.m_cg = m.producers[0].module.clone();
    m
}

/// The attack read both ways: `M_cg` as compiled (declaring `g` fixed-arity),
/// and `M_cg` alike the producer.
#[track_caller]
fn assert_both_ways_ship_under_no_policy(fx: &Fixture, producer: Module, attack: &str) {
    assert_ships_under_no_policy(&with_producer(fx, producer.clone(), &["f"]), attack);
    assert_ships_under_no_policy(
        &with_producer_as_m_cg(fx, producer, &["f"]),
        &format!("{attack} (M_cg alike)"),
    );
}

thread_local! {
    static HOLES: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The block's promise: the object ships under NO policy. Records a HOLE, with
/// every certificate's grade, when the gate lets it through; [`no_holes`]
/// fails the test with the whole matrix.
#[track_caller]
fn assert_ships_under_no_policy(m: &Fixture, attack: &str) {
    let report = match m.verify() {
        Err(refusal) => {
            eprintln!("[{}] {attack}: object refused ({refusal})", m.triple);
            return;
        }
        Ok(r) => r,
    };
    let grades: Vec<String> =
        report.certificates.iter().map(|c| format!("{}={}", c.symbol, c.grade)).collect();
    let shipping: Vec<String> = [EmitPolicy::AllowUnknown, EmitPolicy::StrictProvenOnly]
        .into_iter()
        .filter(|p| report.ships(*p).is_ok())
        .map(|p| format!("{p:?}"))
        .collect();
    if shipping.is_empty() {
        let why: Vec<String> = report
            .certificates
            .iter()
            .filter_map(|c| match &c.verdict {
                OutputVerdict::Refuted { detail } => Some(detail.clone()),
                _ => None,
            })
            .collect();
        eprintln!("[{}] {attack}: blocked ({}): {}", m.triple, grades.join(", "), why.join(" | "));
    } else {
        let line = format!(
            "HOLE [{}] {attack}: ships under {} ({})",
            m.triple,
            shipping.join("+"),
            grades.join(", ")
        );
        eprintln!("{line}\n{}", explain(&report));
        HOLES.with(|h| h.borrow_mut().push(line));
    }
}

#[track_caller]
fn no_holes() {
    let holes = HOLES.with(|h| std::mem::take(&mut *h.borrow_mut()));
    assert!(holes.is_empty(), "{} hole(s):\n{}", holes.len(), holes.join("\n"));
}

fn unsigned_sig(pb: &mut ModBuilder) -> FuncTyId {
    let id = pb.sig(&[], Some(Ty::U64));
    pb.m.func_types[id.as_usize()].is_vararg = true;
    id
}

fn variadic_sig(pb: &mut ModBuilder, fixed: usize) -> FuncTyId {
    let id = pb.sig(&u64s(fixed), Some(Ty::U64));
    pb.m.func_types[id.as_usize()].is_vararg = true;
    id
}

/// `ptr = <route>(g)`: a function pointer to the declaration `g` (of signature
/// `g_sig`), re-typed to `to` by a cast when the route names one.
fn pointer_to(
    fb: &mut FnBody,
    route: &str,
    g: trust_ir::value::FuncId,
    g_sig: FuncTyId,
    to: FuncTyId,
) -> trust_ir::value::ValueId {
    let raw = if route == "SymbolAddr" {
        fb.push_inst(Inst::Const {
            ty: Ty::Func(g_sig),
            value: Constant::SymbolAddr { symbol: "g".into(), addend: 0 },
        })
    } else {
        fb.push_inst(Inst::Const { ty: Ty::Func(g_sig), value: Constant::FnDef(g) })
    };
    let op = match route {
        "PtrToPtr" => CastOp::PtrToPtr,
        "Transmute" => CastOp::Transmute,
        "Bitcast" => CastOp::Bitcast,
        _ => return raw,
    };
    fb.push_inst(Inst::Cast { op, src_ty: Ty::Func(g_sig), dst_ty: Ty::Func(to), operand: raw })
}

const ROUTES: [&str; 5] = ["FnDef", "SymbolAddr", "PtrToPtr", "Transmute", "Bitcast"];

// ---------------------------------------------------------------------------
// A1. A fixed-arity indirect call through a pointer to an UNSIGNED `(...)`
//     declaration (function pointer, cast, symbol address). trust-cg refuses it
//     (`refuse_indirect_call_to_variadic_declaration`, OD-56: "put FD_CLOEXEC in
//     w2 where DarwinPCS reads [sp]"); trust-ir's interpreter calls it a
//     signature mismatch. The pre-pass reads only the edge's own `sig`.
// ---------------------------------------------------------------------------
#[test]
fn attack_fixed_arity_call_through_pointer_to_unsigned_declaration() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for route in ROUTES {
            let mut pb = ModBuilder::new("attack_a1");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let s3 = pb.sig(&u64s(3), Some(Ty::U64));
            let unsigned = unsigned_sig(&mut pb);
            let g = pb.declare("g", unsigned);
            pb.define("f", s64, Linkage::External, |fb| {
                // fcntl(fd, F_SETFD, FD_CLOEXEC) through `unsafe extern "C" fn(i32, i32, i32)`.
                let ptr = pointer_to(fb, route, g, unsigned, s3);
                let two = fb.konst(Ty::U64, 2);
                let one = fb.konst(Ty::U64, 1);
                let r = fb.push_inst(Inst::CallIndirect {
                    callee: ptr,
                    sig: s3,
                    args: vec![fb.p(0), two, one],
                    calling_conv: CallingConv::C,
                });
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            assert_both_ways_ship_under_no_policy(
                &fx,
                pb.finish(),
                &format!("A1 fixed-arity CallIndirect via {route} to a `(...)` declaration"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A2. The same through a pointer to a SIGNED variadic declaration `g(u64, ...)`:
//     the edge places its second argument as a named one where the callee reads
//     an anonymous one (wrong split). trust-cg: [TCG-VARARG-ABI].
// ---------------------------------------------------------------------------
#[test]
fn attack_fixed_arity_call_through_pointer_to_signed_variadic_declaration() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for route in ROUTES {
            let mut pb = ModBuilder::new("attack_a2");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let s2 = pb.sig(&u64s(2), Some(Ty::U64));
            let variadic = variadic_sig(&mut pb, 1);
            let g = pb.declare("g", variadic);
            pb.define("f", s64, Linkage::External, |fb| {
                let ptr = pointer_to(fb, route, g, variadic, s2);
                let seven = fb.konst(Ty::U64, 7);
                let r = fb.push_inst(Inst::CallIndirect {
                    callee: ptr,
                    sig: s2,
                    args: vec![fb.p(0), seven],
                    calling_conv: CallingConv::C,
                });
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            assert_both_ways_ship_under_no_policy(
                &fx,
                pb.finish(),
                &format!("A2 fixed-arity CallIndirect via {route} to `g(u64, ...)`"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A3. The reverse: a VARIADIC indirect edge `(u64, ...)` through a pointer to a
//     fixed-arity `g(u64, u64)`. The caller stacks its second argument
//     (DarwinPCS); the callee reads x1.
// ---------------------------------------------------------------------------
#[test]
fn attack_variadic_call_through_pointer_to_fixed_arity_declaration() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for route in ROUTES {
            let mut pb = ModBuilder::new("attack_a3");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let s2 = pb.sig(&u64s(2), Some(Ty::U64));
            let variadic = variadic_sig(&mut pb, 1);
            let g = pb.declare("g", s2);
            pb.define("f", s64, Linkage::External, |fb| {
                let ptr = pointer_to(fb, route, g, s2, variadic);
                let seven = fb.konst(Ty::U64, 7);
                let r = fb.push_inst(Inst::CallIndirect {
                    callee: ptr,
                    sig: variadic,
                    args: vec![fb.p(0), seven],
                    calling_conv: CallingConv::C,
                });
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            assert_both_ways_ship_under_no_policy(
                &fx,
                pb.finish(),
                &format!("A3 `(u64, ...)` CallIndirect via {route} to fixed-arity `g(u64, u64)`"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A4. `SeqMap { fwd }` names a FuncId it CALLS once per element, and the
//     pre-pass reads only the six call instructions. trust-cg lowers `fwd` as a
//     call (`translate_seq_map`) and refuses a variadic one by name.
// ---------------------------------------------------------------------------
#[test]
fn attack_seqmap_element_function_declared_unsigned() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut pb = ModBuilder::new("attack_a4");
        let s64 = pb.sig(&u64s(1), Some(Ty::U64));
        let elem = pb.m.add_type(Ty::U64).expect("Module::add_type: test fixture");
        let fwd_sig = pb.sig(&[], None);
        pb.m.func_types[fwd_sig.as_usize()].is_vararg = true;
        let g = pb.declare("g", s64);
        let fwd = pb.declare("fwd", fwd_sig);
        pb.define("f", s64, Linkage::External, |fb| {
            let _mapped = fb.push_inst(Inst::SeqMap { ty: Ty::Sequence(elem), seq: fb.p(0), fwd });
            let r = fb.call(g, &[fb.p(0)]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
        let m = with_producer(&fx, pb.finish(), &["f"]);
        assert_ships_under_no_policy(&m, "A4 SeqMap whose element function is `(...)`");
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A5. A variadic signature under a convention with NO variadic form. The block
//     names Rust and RustCold because "the Rust ABI has no variadic form, so its
//     fixed prefix is a producer placeholder". The same holds of fastcc and
//     coldcc (LLVM LangRef: "This calling convention does not support varargs")
//     and of swiftcall and vectorcall (clang `supportsVariadicCall` is false).
//     trust-cg lowers Fast/Cold through the C register ABI
//     (`calling_conv_uses_c_register_abi`), i.e. it GUESSES the C variadic split.
// ---------------------------------------------------------------------------
#[test]
fn attack_variadic_callee_under_a_convention_with_no_variadic_form() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for conv in
            [CallingConv::Fast, CallingConv::Cold, CallingConv::Swift, CallingConv::VectorCall]
        {
            let mut pb = ModBuilder::new("attack_a5");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let variadic = variadic_sig(&mut pb, 1);
            let g = pb.declare("g", variadic);
            pb.define("f", s64, Linkage::External, |fb| {
                let seven = fb.konst(Ty::U64, 7);
                let r = fb.call(g, &[fb.p(0), seven]);
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            let mut producer = pb.finish();
            producer.functions[g.as_usize()].calling_conv = conv;
            assert_both_ways_ship_under_no_policy(
                &fx,
                producer,
                &format!("A5 call to a variadic {conv:?}-convention `g(u64, ...)`"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A6. Re-declaration with a different split. (a) The caller declares the
//     co-emitted `g` as `(u64, ...)` and passes its second argument anonymously;
//     g's own producer body is `g(u64, u64)` and reads it from x1. (b) Two
//     producers declare one External `g` with different splits; the caller of
//     the fixed-arity view is kernel-[PROVED].
// ---------------------------------------------------------------------------
#[test]
fn attack_caller_redeclares_co_emitted_callee_with_another_split() {
    let mut mb = ModBuilder::new("attack_a6a");
    let s1 = mb.sig(&u64s(1), Some(Ty::U64));
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let g = mb.define("g", s2, Linkage::External, |fb| {
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), fb.p(1));
        fb.ret(out);
    });
    mb.define("f", s1, Linkage::External, |fb| {
        let seven = fb.konst(Ty::U64, 7);
        let r = fb.call(g, &[fb.p(0), seven]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O0);
        assert_eq!(bl_offsets(&fx.object, "f").len(), 1, "{triple}: f keeps its call");
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        assert_kernel_proved(&fx, &report, "g");
        // Producer 0: f's own module, which declares `g` as `(u64, ...)`.
        let mut pb = ModBuilder::new("attack_a6a_caller");
        let s1 = pb.sig(&u64s(1), Some(Ty::U64));
        let variadic = variadic_sig(&mut pb, 1);
        let g_decl = pb.declare("g", variadic);
        let f = pb.define("f", s1, Linkage::External, |fb| {
            let seven = fb.konst(Ty::U64, 7);
            let r = fb.call(g_decl, &[fb.p(0), seven]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
        let mut m = fx.patched(|_| {});
        let g_body = fx.m_cg.functions.iter().find(|x| x.name == "g").unwrap().id;
        m.producers = vec![
            ProducerModule::named_by_symbols(Arc::new(pb.finish())),
            ProducerModule::named_by_symbols(fx.m_cg.clone()),
        ];
        m.bodies.insert("f".into(), ProducerBody { producer: 0, func: f });
        m.bodies.insert("g".into(), ProducerBody { producer: 1, func: g_body });
        assert_ships_under_no_policy(
            &m,
            "A6a caller declares co-emitted `g(u64, u64)` as `(u64, ...)`",
        );
    }
    no_holes();
}

#[test]
fn attack_two_producers_declare_one_external_callee_with_different_splits() {
    let mut mb = ModBuilder::new("attack_a6b");
    let s1 = mb.sig(&u64s(1), Some(Ty::U64));
    let s2 = mb.sig(&u64s(2), Some(Ty::U64));
    let g = mb.declare("g", s2);
    for (name, k) in [("f", 5), ("h", 9)] {
        mb.define(name, s1, Linkage::External, |fb| {
            let kk = fb.konst(Ty::U64, k);
            let r = fb.call(g, &[fb.p(0), kk]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
    }
    let module = mb.finish();
    for triple in BOTH {
        let fx = Fixture::new(module.clone(), triple, OptLevel::O2);
        let report = fx.report();
        assert_kernel_proved(&fx, &report, "f");
        assert_kernel_proved(&fx, &report, "h");
        // Producer 1: h's module declares the same External `g` as `(u64, ...)`.
        let mut pb = ModBuilder::new("attack_a6b_h");
        let s1 = pb.sig(&u64s(1), Some(Ty::U64));
        let variadic = variadic_sig(&mut pb, 1);
        let g_decl = pb.declare("g", variadic);
        let h = pb.define("h", s1, Linkage::External, |fb| {
            let kk = fb.konst(Ty::U64, 9);
            let r = fb.call(g_decl, &[fb.p(0), kk]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
        });
        let mut m = fx.patched(|_| {});
        m.producers.push(ProducerModule::named_by_symbols(Arc::new(pb.finish())));
        m.bodies.insert("h".into(), ProducerBody { producer: 1, func: h });
        let r = m.report();
        eprintln!(
            "[{triple}] A6b: f is {} with g(u64, u64) while h's producer declares g(u64, ...)",
            r.certificate("f").unwrap().grade
        );
        assert_ships_under_no_policy(
            &m,
            "A6b `g` is `(u64, u64)` in f's producer and `(u64, ...)` in h's",
        );
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A7. The known-count path with a mismatched call: `g(u64, u64, ...)` called
//     with ONE argument, so the stated fixed prefix is not supplied. trust-cg
//     refuses ("expected at least 2 fixed arguments"); trust-ir's interpreter
//     refuses (`check_vararg_declaration_args`).
// ---------------------------------------------------------------------------
#[test]
fn attack_variadic_call_short_of_its_stated_fixed_prefix() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for conv in [CallingConv::C, CallingConv::CUnwind] {
            let mut pb = ModBuilder::new("attack_a7");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let variadic = variadic_sig(&mut pb, 2);
            let g = pb.declare("g", variadic);
            pb.define("f", s64, Linkage::External, |fb| {
                let r = fb.call(g, &[fb.p(0)]);
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            let mut producer = pb.finish();
            producer.functions[g.as_usize()].calling_conv = conv;
            assert_both_ways_ship_under_no_policy(
                &fx,
                producer,
                &format!("A7 one argument to {conv:?} `g(u64, u64, ...)`"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A8. A callee whose signature the gate cannot read (a FuncTyId the module
//     lacks, direct and indirect): whether it is variadic, and its split, are
//     unknown. The pre-pass skips an unreadable signature.
// ---------------------------------------------------------------------------
#[test]
fn attack_callee_signature_the_gate_cannot_read() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for shape in ["Call", "CallIndirect"] {
            let mut pb = ModBuilder::new("attack_a8");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let bogus = FuncTyId::new(999);
            let g = pb.declare("g", s64);
            pb.define("f", s64, Linkage::External, |fb| {
                let r = if shape == "Call" {
                    fb.call(g, &[fb.p(0)])
                } else {
                    let ptr = fb
                        .push_inst(Inst::Const { ty: Ty::Func(bogus), value: Constant::FnDef(g) });
                    fb.push_inst(Inst::CallIndirect {
                        callee: ptr,
                        sig: bogus,
                        args: vec![fb.p(0)],
                        calling_conv: CallingConv::C,
                    })
                };
                let one = fb.konst(Ty::U64, 1);
                let out = fb.bin(BinOp::Add, Ty::U64, r, one);
                fb.ret(out);
            });
            let mut producer = pb.finish();
            if shape == "Call" {
                producer.functions[g.as_usize()].ty = bogus;
            }
            assert_both_ways_ship_under_no_policy(
                &fx,
                producer,
                &format!("A8 {shape} with an unreadable signature"),
            );
        }
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A9. The gate reads only the PRODUCER; it never reads the module trust-cg
//     compiled. (a) x86-64: M_cg calls `g` through `(...)`, the producer signs
//     it; nothing checks the x86-64 bytes, so only the pre-pass stands between
//     that edge and `AllowUnknown`. (b) AArch64: M_cg calls `(...)` and no
//     producer body is supplied for `f` ("left to the caller").
// ---------------------------------------------------------------------------
fn wrapper_module_unsigned_in_m_cg() -> Module {
    let mut mb = ModBuilder::new("attack_wrapper");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let unsigned = unsigned_sig(&mut mb);
    let g = mb.declare("g", unsigned);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    mb.finish()
}

#[test]
fn attack_m_cg_unsigned_edge_behind_a_signed_producer_on_x86_64() {
    let fx = Fixture::new(wrapper_module(), X86_64, OptLevel::O2);
    let mut m = fx.patched(|_| {});
    m.m_cg = Arc::new(wrapper_module_unsigned_in_m_cg());
    assert_ships_under_no_policy(&m, "A9a x86-64 M_cg edge through `(...)`, producer signed");
    no_holes();
}

#[test]
fn attack_m_cg_unsigned_edge_with_no_producer_body() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut m = fx.patched(|_| {});
        m.m_cg = Arc::new(wrapper_module_unsigned_in_m_cg());
        m.producers = vec![ProducerModule::named_by_symbols(m.m_cg.clone())];
        m.bodies.remove("f");
        let r = m.report();
        assert!(
            !matches!(r.certificate("f").unwrap().verdict, OutputVerdict::Proven { .. }),
            "{}",
            explain(&r)
        );
        assert_ships_under_no_policy(&m, "A9b M_cg edge through `(...)`, no producer body");
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// A10. The remaining routes by which a variadic callee is reached without a
//      call instruction naming its signature, closed with A1-A9: (a) a DATA
//      initializer holding the address of a variadic function (a static table
//      of function pointers), (b) drop glue declared variadic (`Inst::Drop`
//      calls it with one pointer), (c) a sited assert whose panic entry is
//      declared variadic (its failure calls the entry with its own operands).
// ---------------------------------------------------------------------------

/// `f(x) = g(x) + 1` as a producer that also declares a variadic
/// `v(u64, ...)`, with `extra` adding to f's body before its call.
fn producer_with_variadic_v(extra: impl FnOnce(&mut FnBody, trust_ir::value::FuncId)) -> Module {
    let mut pb = ModBuilder::new("attack_a10");
    let s64 = pb.sig(&u64s(1), Some(Ty::U64));
    let variadic = variadic_sig(&mut pb, 1);
    let g = pb.declare("g", s64);
    let v = pb.declare("v", variadic);
    pb.define("f", s64, Linkage::External, |fb| {
        extra(fb, v);
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    pb.finish()
}

#[test]
fn attack_data_initializer_holds_a_variadic_address() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        for (route, init) in [
            ("SymbolAddr", Constant::SymbolAddr { symbol: "v".into(), addend: 0 }),
            ("FnDef", Constant::FnDef(trust_ir::value::FuncId::new(1))),
        ] {
            let mut producer = producer_with_variadic_v(|_, _| {});
            assert_eq!(producer.functions[1].name, "v");
            producer.globals.push(Global {
                name: "TABLE".into(),
                ty: Ty::U64,
                mutable: false,
                initializer: Some(Constant::Aggregate(vec![init])),
                linkage: Linkage::External,
                tls: None,
                align: None,
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            let m = with_producer(&fx, producer, &["f"]);
            assert_ships_under_no_policy(
                &m,
                &format!("A10a a data initializer holds the {route} address of `v(u64, ...)`"),
            );
        }
    }
    no_holes();
}

#[test]
fn attack_drop_glue_declared_variadic() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let mut producer = producer_with_variadic_v(|fb, _| {
            fb.push_inst_void(Inst::Drop { ty: Ty::U32, ptr: fb.p(0) });
        });
        producer.set_drop_glue(Ty::U32, trust_ir::value::FuncId::new(1)).expect("one glue row");
        let m = with_producer(&fx, producer, &["f"]);
        assert_ships_under_no_policy(&m, "A10b a drop whose glue is `v(u64, ...)`");
    }
    no_holes();
}

#[test]
fn attack_panic_entry_declared_variadic() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        assert_kernel_proved(&fx, &fx.report(), "f");
        let producer = producer_with_variadic_v(|fb, v| {
            let zero = fb.konst(Ty::U64, 0);
            let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(0), zero);
            fb.push_inst_void(Inst::Assert {
                cond: ok,
                kind: AssertKind::default(),
                site: Some(PanicSite { entry: v, location: PanicLocation::Value(fb.p(0)) }),
            });
        });
        let m = with_producer(&fx, producer, &["f"]);
        assert_ships_under_no_policy(&m, "A10c a sited assert whose panic entry is `v(u64, ...)`");
    }
    no_holes();
}

// ---------------------------------------------------------------------------
// CONTROLS (expected blocked): the shapes the first version of the block
// claimed, reached by routes its own tests did not use.
// ---------------------------------------------------------------------------

/// A `(...)` FnDef reified into an indirect edge whose OWN sig is `(...)`, via
/// every cast route; and the same edge on x86-64.
#[test]
fn control_unsigned_indirect_sig_via_casts_is_blocked() {
    for triple in [DARWIN, LINUX, X86_64] {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        for route in ROUTES {
            let mut pb = ModBuilder::new("control_c1");
            let s64 = pb.sig(&u64s(1), Some(Ty::U64));
            let unsigned = unsigned_sig(&mut pb);
            let g = pb.declare("g", s64);
            pb.define("f", s64, Linkage::External, |fb| {
                let ptr = pointer_to(fb, route, g, s64, unsigned);
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
            let m = with_producer(&fx, pb.finish(), &["f"]);
            assert_ships_under_no_policy(&m, &format!("C1 `(...)` indirect sig via {route}"));
        }
    }
    no_holes();
}

/// An unsigned call in a block the function never reaches.
#[test]
fn control_unsigned_call_in_an_unreachable_block_is_blocked() {
    for triple in BOTH {
        let fx = Fixture::new(wrapper_module(), triple, OptLevel::O2);
        let mut pb = ModBuilder::new("control_c2");
        let s64 = pb.sig(&u64s(1), Some(Ty::U64));
        let unsigned = unsigned_sig(&mut pb);
        let g = pb.declare("g", s64);
        let u = pb.declare("u", unsigned);
        pb.define("f", s64, Linkage::External, |fb| {
            let (dead, _) = fb.block(&[]);
            let r = fb.call(g, &[fb.p(0)]);
            let one = fb.konst(Ty::U64, 1);
            let out = fb.bin(BinOp::Add, Ty::U64, r, one);
            fb.ret(out);
            fb.switch_to(dead);
            let z = fb.call(u, &[fb.p(0)]);
            fb.ret(z);
        });
        let m = with_producer(&fx, pb.finish(), &["f"]);
        assert_ships_under_no_policy(&m, "C2 `(...)` call in an unreachable block");
    }
    no_holes();
}
