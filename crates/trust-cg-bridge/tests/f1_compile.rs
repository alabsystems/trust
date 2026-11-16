// tests/f1_compile.rs — the bridge's SHIPPING CONSUMER for the compiler lane
// (increment 5, step 5.4.1; plan
// docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md §1 "Tests").
//
// Every test drives the public API (`compile_and_verify_trust_ir_module`,
// `census_trust_ir_module`, `F1Target`), never `verify_compiled_module`
// directly, and each names what it fails without. Modules are hand-built with
// `cer_common::ModBuilder`; every body is stamped
// `Gated { trust-direct-lane-structural }` unless the test is about the
// license, because the D31 license refuses a claim-less body, and a module
// with a bodyless declaration (an FFI boundary) carries the `target_info` the
// plugin's M_cg carries for the leg it compiles for, because trust-ir and
// trust-cg's ingestion admission refuse an untargeted one (`TargetInfoRequired`,
// trust-cg WS7.3). Since 2026-10-14
// it also holds sub-step 5.6.1(a)'s External-declaration tests
// (docs/design/2026-10-13-step2-inc5-step6-instance-links-plan.md §2(a)) and
// PTR.0's consumer tests 11-12
// (docs/design/2026-10-13-step2-inc5-pointer-args-plan.md §2), and since
// 2026-11-11 PKG-CP's two tests of a sited check (which checks are a boundary
// row, and what the consumer returns for a sited overflow check) and its
// tests of a location record: what the consumer returns for a check sited at
// one, that a record no function reads ships under strict, what the reader
// refuses when the record's relocation moves, the shipped object linked and
// run on this host, and what the reader refuses so that the linked pointer
// leads to the bytes it compared (a string-literal or merge section, any
// section or file header word that is not ordinary data), with the system
// linker's behaviour behind those refusals linked and run. The admission's
// second adjudication committed one test of that group failing,
// `a_second_symbol_table_refuses_the_located_object` (the reader bound a
// Mach-O object that carries two `LC_SYMTAB` commands); it passes since the
// parser refuses a second symbol table, and the two tests after it pin that
// refusal and the one for an `ARM64_RELOC_ADDEND` entry on the record's
// pointer. TWO tests of that group FAIL today, committed failing by the
// admission's third adjudication:
// `a_relocation_section_the_linker_drops_refuses_the_located_object` and
// `a_text_relocation_section_the_linker_drops_refuses_the_wrapper_object`
// (the reader binds an ELF object whose relocation section is marked
// `SHF_EXCLUDE`, which LLD drops from the link: the record's pointer links
// null, and a certified call links as a branch to itself).
//
// Run (the harness row `slow.trust-cg-cer-gate` runs it):
// `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks --test f1_compile`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "kernel-recheck")]

mod cer_common;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use cer_common::*;
use sha2::{Digest, Sha256};
use trust_cg_bridge::call_event::{
    Assumption, CallSiteKind, CerReport, FnPlacement, Grade, ParamPlace, ProducerBody,
    ProducerModule, ReturnPlace, ScalarPlace,
};
use trust_cg_bridge::compiled_object::{ObjectRefusalKind, RelocationModel};
use trust_cg_bridge::f1_compile::{
    CensusRow, F1CompileConfig, F1CompileInput, F1OptLevel, F1Refusal, F1Shipped, F1Target,
    TRUST_DIRECT_LANE_AUTHORITY, TRUST_INSTANCE_LANE_AUTHORITY, TRUST_UPSTREAM_MIR_LANE_AUTHORITY,
    census_trust_ir_module, compile_and_verify_trust_ir_module,
};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict, ProvenEvidence};
use trust_ir::inst::{
    AssertOverflowOp, BinOp, ICmpOp, Inst, OverflowOp, PanicLocation, PanicSite, SwitchCase,
};
use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, ValueId};
use trust_ir::{
    AssertKind, Block, BodyGate, Constant, Endianness, Function, Global, InstrNode, Linkage,
    Module, Producer, StructPassingPolicy, TargetInfo, Ty, Visibility,
};

// ===========================================================================
// helpers
// ===========================================================================

const DARWIN_T: F1Target = F1Target::Aarch64AppleDarwin;
const LINUX_T: F1Target = F1Target::Aarch64UnknownLinuxGnu;

/// Every (target, relocation model) leg a test that must hold on both formats
/// runs: Darwin (compiled `Static`), Linux `Static`, and Linux `Pic` (rustc's
/// AArch64 Linux default, INC5.4-PIC).
const LEGS: [(F1Target, RelocationModel); 3] = [
    (DARWIN_T, RelocationModel::Static),
    (LINUX_T, RelocationModel::Static),
    (LINUX_T, RelocationModel::Pic),
];

/// The fourth leg (docs/design/2026-10-13-step2-inc5-step6-instance-links-plan.md
/// §2(a)): Darwin under rustc's default `Pic`, which the consumer compiles
/// `Static` on Mach-O. Only the External-declaration tests use it; `LEGS` is
/// unchanged.
const DARWIN_PIC: (F1Target, RelocationModel) = (DARWIN_T, RelocationModel::Pic);

/// Darwin `Static` and `Pic`, Linux `Static` and `Pic`.
const DECLARATION_LEGS: [(F1Target, RelocationModel); 4] = [LEGS[0], DARWIN_PIC, LEGS[1], LEGS[2]];

fn u64s(n: usize) -> Vec<Ty> {
    vec![Ty::U64; n]
}

fn gated(authority: &str) -> Option<BodyGate> {
    Some(BodyGate::Gated { authority: authority.to_string(), evidence: None })
}

/// Stamp every body `Gated { trust-direct-lane-structural }`.
fn licensed(mut m: Module) -> Module {
    for f in m.functions.iter_mut().filter(|f| !f.blocks.is_empty()) {
        f.body_gate = gated(TRUST_DIRECT_LANE_AUTHORITY);
    }
    m
}

fn set_gate(m: &mut Module, name: &str, gate: Option<BodyGate>) {
    m.functions.iter_mut().find(|f| f.name == name).expect("function").body_gate = gate;
}

fn config(target: F1Target, opt: F1OptLevel, relocation: RelocationModel) -> F1CompileConfig {
    F1CompileConfig {
        force_frame_pointers: false,
        target,
        opt_level: opt,
        relocation,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    }
}

fn never_inline(mut c: F1CompileConfig, names: &[&str]) -> F1CompileConfig {
    c.never_inline = names.iter().map(|s| (*s).to_string()).collect();
    c
}

/// One compile's inputs: M_cg, its producers (M_cg itself by default, named by
/// symbol), the bodies and the natural all-scalar P.
struct Case {
    m_cg: Module,
    producers: Vec<ProducerModule>,
    bodies: BTreeMap<String, ProducerBody>,
    placements: BTreeMap<String, FnPlacement>,
}

impl Case {
    fn new(m_cg: Module) -> Self {
        let producer = Arc::new(m_cg.clone());
        let mut bodies = BTreeMap::new();
        let mut placements = BTreeMap::new();
        for f in &producer.functions {
            if !f.blocks.is_empty() {
                bodies.insert(f.name.clone(), ProducerBody { producer: 0, func: f.id });
            }
            if let Ok(p) = FnPlacement::from_scalar_signature(&producer, f) {
                placements.insert(f.name.clone(), p);
            }
        }
        Case {
            m_cg,
            producers: vec![ProducerModule::named_by_symbols(producer)],
            bodies,
            placements,
        }
    }

    /// M_cg compiled, `producer` read as the specification of every body.
    fn with_producer(m_cg: Module, producer: Module) -> Self {
        let mut case = Case::new(producer);
        case.m_cg = m_cg;
        case
    }

    fn run(&self, config: &F1CompileConfig, policy: EmitPolicy) -> Result<F1Shipped, F1Refusal> {
        compile_and_verify_trust_ir_module(&F1CompileInput {
            m_cg: &self.m_cg,
            producers: &self.producers,
            bodies: &self.bodies,
            placements: &self.placements,
            policy,
            config,
        })
    }
}

#[track_caller]
fn shipped(r: Result<F1Shipped, F1Refusal>, what: &str) -> F1Shipped {
    r.unwrap_or_else(|e| panic!("{what}: refused:\n{e}"))
}

#[track_caller]
fn refused(r: Result<F1Shipped, F1Refusal>, what: &str) -> F1Refusal {
    match r {
        Ok(s) => panic!("{what}: SHIPPED\n{}\n{}", explain(&s.report), disassemble(&s.object)),
        Err(e) => e,
    }
}

fn kernel_proved(report: &CerReport, symbol: &str) -> bool {
    report.certificate(symbol).is_some_and(|c| c.is_kernel_proved())
}

fn census_variants(e: &F1Refusal) -> Vec<(String, String)> {
    match e {
        F1Refusal::Census(rows) | F1Refusal::Boundary(rows) => {
            rows.iter().map(|r: &CensusRow| (r.symbol.clone(), r.variant.clone())).collect()
        }
        other => panic!("not a census or boundary refusal: {other}"),
    }
}

/// `f(x) = g(x) + 1` with `g(x) = x ^ 0x33` co-emitted under `g_linkage`.
fn wrapper_module(g_linkage: Linkage) -> Module {
    let mut mb = ModBuilder::new("f1_wrapper");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, g_linkage, |fb| {
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
    licensed(mb.finish())
}

/// `h(x) = x ^ 0x55`: one leaf, nothing else.
fn leaf_module(name: &str) -> Module {
    let mut mb = ModBuilder::new("f1_leaf");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define(name, s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x55);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    licensed(mb.finish())
}

// ===========================================================================
// 1-2. THE LICENSE AND THE CENSUS
// ===========================================================================

/// D31(a)/(b): exactly the direct and instance lane authorities, plus the
/// upstream-MIR authority only under its flag; a claim-less body refused.
/// FAILS under `CodegenLicensePolicy::default()` (the direct authority is not
/// recognized, the clean-kernel-tv one is, and a claim-less body is permitted)
/// or under `recognizing_nothing()` without `Refuse` (the claim-less body
/// compiles).
#[test]
fn license_is_exactly_d31() {
    let cfg = config(DARWIN_T, F1OptLevel::O2, RelocationModel::Static);
    let refused_gates: [(&str, Option<BodyGate>); 5] = [
        ("drop-glue lane", gated("trust-drop-glue-lane-structural")),
        ("no claim", None),
        ("Ungated", Some(BodyGate::Ungated)),
        ("clean-kernel-tv", gated("clean-kernel-tv")),
        ("upstream-MIR authority, flag off", gated(TRUST_UPSTREAM_MIR_LANE_AUTHORITY)),
    ];
    for (what, gate) in refused_gates {
        let mut m = leaf_module("h");
        set_gate(&mut m, "h", gate);
        let e = refused(Case::new(m).run(&cfg, EmitPolicy::AllowUnknown), what);
        let rows = census_variants(&e);
        assert!(matches!(e, F1Refusal::Census(_)), "{what}: {e}");
        assert_eq!(rows.len(), 1, "{what}: {e}");
        assert_eq!(rows[0].0, "h", "{what}: {e}");
        assert!(rows[0].1.starts_with("Adapter::"), "{what}: {e}");
        assert!(e.to_string().starts_with("[trust-cg-refused:Adapter::"), "{what}: {e}");
    }
    // The three recognized authorities compile (the upstream one under its flag).
    for (authority, flag) in [
        (TRUST_DIRECT_LANE_AUTHORITY, false),
        (TRUST_INSTANCE_LANE_AUTHORITY, false),
        (TRUST_UPSTREAM_MIR_LANE_AUTHORITY, true),
    ] {
        let mut m = leaf_module("h");
        set_gate(&mut m, "h", gated(authority));
        let mut c = cfg.clone();
        c.upstream_mir_lane = flag;
        shipped(Case::new(m).run(&c, EmitPolicy::AllowUnknown), authority);
    }
}

/// Every refused function is reported and nothing is compiled.
/// FAILS if only `Compiler::compile`'s first error were returned (one row, a
/// `Compile` refusal).
#[test]
fn census_reports_every_refused_function_and_skips_compile() {
    let mut mb = ModBuilder::new("f1_census");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    for name in ["a", "b", "memcpy"] {
        mb.define(name, s, Linkage::Internal, |fb| {
            let k = fb.konst(Ty::U64, 3);
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
            fb.ret(out);
        });
    }
    let mut m = licensed(mb.finish());
    set_gate(&mut m, "a", None);
    set_gate(&mut m, "b", Some(BodyGate::Ungated));
    for (target, relocation) in LEGS {
        let cfg = config(target, F1OptLevel::O0, relocation);
        let e = refused(Case::new(m.clone()).run(&cfg, EmitPolicy::AllowUnknown), "census");
        let rows = census_variants(&e);
        assert!(matches!(e, F1Refusal::Census(_)), "{target:?}: {e}");
        let variants: BTreeSet<&str> = rows.iter().map(|(_, v)| v.as_str()).collect();
        assert_eq!(rows.len(), 3, "{target:?}: {e}");
        assert_eq!(variants.len(), 3, "{target:?}: three distinct variants: {e}");
        for (sym, _) in &rows {
            assert!(["a", "b", "memcpy"].contains(&sym.as_str()), "{e}");
        }
        assert_eq!(e.to_string().lines().count(), 3, "{e}");
        // The census entry point reports the same rows, on its own thread.
        let census = census_trust_ir_module(&m, &cfg).expect("census runs");
        assert_eq!(census.len(), 3);
    }
}

// ===========================================================================
// 3. THE GATE THREAD (INC5.4-STACK)
// ===========================================================================

/// The unmutated O0 module of `call_event_gate.rs`'s
/// `mutant_mixed_inline_and_call_sites_of_one_callee`, run through the API
/// from a 2 MiB thread under allow-unknown. FAILS (the process aborts with a
/// stack overflow) when `on_gate_thread` is replaced by a direct call:
/// measured, see `docs/DECISION_QUEUE.md` INC5.4-STACK.
#[test]
fn gate_runs_on_its_own_stack_when_called_from_a_2mib_thread() {
    let mut mb = ModBuilder::new("f1_mixed");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x33);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let x1 = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), one);
        let c = fb.call(g, &[x1]);
        let out = fb.bin(BinOp::Add, Ty::U64, a, c);
        fb.ret(out);
    });
    let case = Case::new(licensed(mb.finish()));
    for target in [DARWIN_T, LINUX_T] {
        let cfg = config(target, F1OptLevel::O0, RelocationModel::Static);
        let out = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(2 << 20)
                .spawn_scoped(scope, || case.run(&cfg, EmitPolicy::AllowUnknown))
                .expect("spawn the 2 MiB caller")
                .join()
                .expect("the 2 MiB caller panicked")
        });
        let s = shipped(out, "2 MiB caller");
        assert!(kernel_proved(&s.report, "f"), "{target:?}\n{}", explain(&s.report));
    }
}

// ===========================================================================
// 4-6, 9. SHIPPING IS `CerReport::ships`, OVER THE BYTES VERIFIED
// ===========================================================================

/// A proved `f` calls an Internal `spin` (a loop: Unknown). Strict refuses,
/// naming `spin`; allow-unknown ships and discloses `f` blocked by `spin`.
/// FAILS if shipping read `f`'s own grade (`f` is kernel-[PROVED] by itself:
/// compare `call_event_gate.rs`'s
/// `closure_names_the_unknown_callee_that_blocks_a_proved_caller`).
#[test]
fn strict_ships_only_a_closed_object() {
    let mut mb = ModBuilder::new("f1_closure");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let spin = mb.define("spin", s, Linkage::Internal, |fb| {
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
    let case = Case::new(licensed(mb.finish()));
    for (target, relocation) in LEGS {
        let cfg = never_inline(config(target, F1OptLevel::O0, relocation), &["spin"]);
        let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), "strict, spin unknown");
        let F1Refusal::Policy(why) = &e else { panic!("{target:?}: not a policy refusal: {e}") };
        assert!(why.contains("spin"), "{target:?}: {why}");
        assert!(e.to_string().starts_with("[f1-output-gate:policy]"), "{e}");
        let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "allow-unknown");
        assert!(
            kernel_proved(&s.report, "f"),
            "{target:?}: f is [PROVED] by itself\n{}",
            explain(&s.report)
        );
        assert!(
            s.unclosed.iter().any(|l| l.starts_with("f: [PROVED]; blocked by [spin]")),
            "{target:?}: {:?}",
            s.unclosed
        );
        assert!(s.unclosed.iter().any(|l| l.starts_with("spin: Unknown")), "{:?}", s.unclosed);
    }
}

/// An Internal `g` (never inlined) and an External `f(x) = g(x) + 1` ship
/// under strict on Darwin, Linux `Static` and Linux `Pic`; `f`'s certificate
/// pairs its one call site with a real `bl` (or a tail `b`).
#[test]
fn wrapper_call_ships_strict_on_both_formats() {
    let case = Case::new(wrapper_module(Linkage::Internal));
    for (target, relocation) in LEGS {
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let cfg = never_inline(config(target, opt, relocation), &["g"]);
            let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), "strict wrapper");
            let c = s.report.certificate("f").expect("f certified");
            assert_eq!(c.call_sites.len(), 1, "{target:?} {opt:?}\n{}", explain(&s.report));
            assert!(
                matches!(c.call_sites[0].kind, CallSiteKind::Direct | CallSiteKind::Tail),
                "{target:?} {opt:?}: {:?}",
                c.call_sites[0]
            );
            assert_eq!(c.call_sites[0].symbol, "g");
            assert_eq!(c.assumptions, vec![Assumption::CoEmitted("g".into())], "{target:?}");
            assert!(s.unclosed.is_empty(), "{:?}", s.unclosed);
        }
    }
}

/// The producer says `x + 1`, M_cg (what trust-cg compiles) says `x + 2`:
/// Refuted, and refused under BOTH policies.
#[test]
fn spec_mismatch_is_refused_under_both_policies() {
    let body = |k: i128| {
        let mut mb = ModBuilder::new("f1_mismatch");
        let s = mb.sig(&u64s(1), Some(Ty::U64));
        mb.define("f", s, Linkage::External, |fb| {
            let c = fb.konst(Ty::U64, k);
            let out = fb.bin(BinOp::Add, Ty::U64, fb.p(0), c);
            fb.ret(out);
        });
        licensed(mb.finish())
    };
    let case = Case::with_producer(body(2), body(1));
    for (target, relocation) in LEGS {
        let cfg = config(target, F1OptLevel::O2, relocation);
        for policy in [EmitPolicy::StrictProvenOnly, EmitPolicy::AllowUnknown] {
            let e = refused(case.run(&cfg, policy), "spec mismatch");
            let F1Refusal::Policy(why) = &e else {
                panic!("{target:?}: not a policy refusal: {e}")
            };
            assert!(why.contains("Refuted") && why.contains('f'), "{target:?} {policy:?}: {why}");
        }
    }
}

/// The object handed out is exactly the object the report is bound to.
#[test]
fn shipped_bytes_are_the_verified_bytes() {
    let case = Case::new(wrapper_module(Linkage::Internal));
    for (target, relocation) in LEGS {
        let cfg = never_inline(config(target, F1OptLevel::O2, relocation), &["g"]);
        let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "ship");
        let digest: String = Sha256::digest(&s.object).iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(digest, s.report.object_sha256, "{target:?}");
        assert!(!s.object.is_empty());
    }
}

// ===========================================================================
// 7-8. THE BOUNDARY AND THE TARGETS
// ===========================================================================

/// An `Assert` without a panic site, `AssertInvoke`, a Clean-origin body and a
/// tC body are each a `Boundary` row; trust-cg never sees them. (Which checks
/// are a row: `only_a_check_with_no_faithful_panic_is_a_boundary_row`.)
#[test]
fn assert_clean_and_deprecated_producer_bodies_are_refused_before_trust_cg() {
    let cfg = config(DARWIN_T, F1OptLevel::O2, RelocationModel::Static);
    let mut mb = ModBuilder::new("f1_boundary");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define("asserting", s, Linkage::External, |fb| {
        let zero = fb.konst(Ty::U64, 0);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(0), zero);
        fb.push_inst_void(Inst::Assert { cond: ok, kind: AssertKind::Unspecified, site: None });
        fb.ret(fb.p(0));
    });
    mb.define("assert_invoking", s, Linkage::External, |fb| {
        let zero = fb.konst(Ty::U64, 0);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(0), zero);
        let (normal, _) = fb.block(&[]);
        let (unwind, _) = fb.block(&[]);
        fb.push_inst_void(Inst::AssertInvoke {
            cond: ok,
            kind: AssertKind::Unspecified,
            site: PanicSite {
                entry: FuncId::new(0),
                location: PanicLocation::Global(GlobalId::new(0)),
            },
            normal_dest: normal,
            normal_args: vec![],
            unwind_dest: unwind,
        });
        fb.switch_to(normal);
        fb.ret(fb.p(0));
        fb.switch_to(unwind);
        fb.ret(fb.p(0));
    });
    for name in ["clean_origin", "tc_origin"] {
        mb.define(name, s, Linkage::External, |fb| fb.ret(fb.p(0)));
    }
    let mut m = licensed(mb.finish());
    for (name, p) in [("clean_origin", Producer::Clean), ("tc_origin", Producer::TC)] {
        m.functions.iter_mut().find(|f| f.name == name).unwrap().producer = Some(p);
    }
    let e = refused(Case::new(m).run(&cfg, EmitPolicy::AllowUnknown), "boundary");
    assert!(matches!(e, F1Refusal::Boundary(_)), "{e}");
    let rows: BTreeSet<(String, String)> = census_variants(&e).into_iter().collect();
    let want: BTreeSet<(String, String)> = [
        ("asserting", "ImplicitPanicUnfaithful"),
        ("assert_invoking", "ImplicitPanicUnfaithful"),
        ("clean_origin", "CleanOriginBelowCodegenGate"),
        ("tc_origin", "DeprecatedProducer"),
    ]
    .into_iter()
    .map(|(a, b)| (a.to_string(), b.to_string()))
    .collect();
    assert_eq!(rows, want, "{e}");
    assert!(e.to_string().lines().all(|l| l.starts_with("[f1-boundary:")), "{e}");
}

// ---------------------------------------------------------------------------
// PKG-CP (faithful panics): a sited check at the boundary and through the gate
// ---------------------------------------------------------------------------

/// The symbol of the panic entry the sited fixtures call: the `core` lang item
/// `AssertKind::Overflow(Add)` names. Production binds the session's mangled
/// symbol for that lang item; a hand-built module has no session, so it spells
/// the lang item's own name.
const ADD_OVERFLOW_ENTRY: &str = "panic_const_add_overflow";

/// A module holding the bodyless panic entry `(ptr) -> ()` and the
/// `(u64, ptr) -> u64` signature of [`checked_add_function`], stating the
/// target M_cg states for `target` (a bodyless declaration needs one, see
/// [`external_declaration_module`]).
fn panic_entry_module(name: &str, target: F1Target) -> (ModBuilder, FuncId, FuncTyId) {
    let mut mb = ModBuilder::new(name);
    let entry_sig = mb.sig(&[Ty::Ptr], None);
    let entry = mb.declare(ADD_OVERFLOW_ENTRY, entry_sig);
    let checked_sig = mb.sig(&[Ty::U64, Ty::Ptr], Some(Ty::U64));
    mb.m.target_info = Some(m_cg_target_info(target));
    (mb, entry, checked_sig)
}

/// `name(x: u64, loc: ptr) -> u64 { x + 1 }` with the check the THIR producer
/// emits for a checked add (`Inst::Overflow`, its flag negated through a
/// `Select`, then the `Assert`: crates/trust-thir-lower `emit_arith_binop` and
/// `emit_bool_not`), the `Assert` carrying `kind` and `site` as given. `loc`
/// (value 1) is the run-time location a `PanicLocation::Value` site passes to
/// the entry. `FnBody` binds one result per instruction and `Inst::Overflow`
/// binds two, so the body is spelled out.
fn checked_add_function(
    m: &mut Module,
    name: &str,
    sig: FuncTyId,
    kind: AssertKind,
    site: Option<PanicSite>,
) {
    let params = vec![(ValueId::new(0), Ty::U64), (ValueId::new(1), Ty::Ptr)];
    checked_add_function_over(m, name, sig, params, kind, site);
}

/// [`checked_add_function`]'s body over the block parameters given: `x` is
/// value 0, and the body's own values start at 2 whether or not there is a
/// value 1 (a function whose site names a `PanicLocation::Global` has no
/// location parameter).
fn checked_add_function_over(
    m: &mut Module,
    name: &str,
    sig: FuncTyId,
    params: Vec<(ValueId, Ty)>,
    kind: AssertKind,
    site: Option<PanicSite>,
) {
    let v = ValueId::new;
    let id = FuncId::new(m.functions.len() as u32);
    let mut f = Function::new(id, name, sig, BlockId::new(0));
    f.linkage = Linkage::External;
    f.producer = Some(Producer::TRust);
    let mut block = Block::new(BlockId::new(0));
    block.params = params;
    block.body = vec![
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }).with_result(v(2)),
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U64,
            lhs: v(0),
            rhs: v(2),
        })
        .with_results([v(3), v(4)]),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(v(5)),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) }).with_result(v(6)),
        InstrNode::new(Inst::Select { ty: Ty::Bool, cond: v(4), then_val: v(5), else_val: v(6) })
            .with_result(v(7)),
        InstrNode::new(Inst::Assert { cond: v(7), kind, site }),
        InstrNode::new(Inst::Return { values: vec![v(3)] }),
    ];
    f.blocks = vec![block];
    m.functions.push(f);
}

/// The site every sited fixture carries: the entry, and the function's own
/// `loc` parameter as the location.
fn value_site(entry: FuncId) -> PanicSite {
    PanicSite { entry, location: PanicLocation::Value(ValueId::new(1)) }
}

/// PKG-CP. The boundary's check row is for a check with no faithful panic to
/// deliver, not for every check: beside a sited `Assert` of a named kind
/// (`sited`), which gets NO row, an `Assert` without a site, a sited `Assert`
/// of `Unspecified` kind and an `AssertInvoke` each still get
/// `ImplicitPanicUnfaithful`, each naming its own reason.
/// FAILS if every `Assert` is a row again (a fourth row, for `sited`), if the
/// row is dropped for a kinded `Assert` that has no site (`unsited` passes; the
/// THIR producer emits exactly that shape today), if a sited check that names
/// no Rust panic passes (`sited_unspecified`), or if `AssertInvoke` passes.
#[test]
fn only_a_check_with_no_faithful_panic_is_a_boundary_row() {
    let add = AssertKind::Overflow(AssertOverflowOp::Add);
    let (mut mb, entry, sig) = panic_entry_module("f1_check_boundary", DARWIN_T);
    checked_add_function(&mut mb.m, "sited", sig, add, Some(value_site(entry)));
    checked_add_function(&mut mb.m, "unsited", sig, add, None);
    checked_add_function(
        &mut mb.m,
        "sited_unspecified",
        sig,
        AssertKind::Unspecified,
        Some(value_site(entry)),
    );
    mb.define("assert_invoking", sig, Linkage::External, |fb| {
        let zero = fb.konst(Ty::U64, 0);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U64, fb.p(0), zero);
        let (normal, _) = fb.block(&[]);
        let (unwind, _) = fb.block(&[]);
        fb.push_inst_void(Inst::AssertInvoke {
            cond: ok,
            kind: add,
            site: value_site(entry),
            normal_dest: normal,
            normal_args: vec![],
            unwind_dest: unwind,
        });
        fb.switch_to(normal);
        fb.ret(fb.p(0));
        fb.switch_to(unwind);
        fb.ret(fb.p(0));
    });
    let cfg = config(DARWIN_T, F1OptLevel::O2, RelocationModel::Static);
    let e = refused(Case::new(licensed(mb.finish())).run(&cfg, EmitPolicy::AllowUnknown), "checks");
    let F1Refusal::Boundary(rows) = &e else { panic!("not a boundary refusal: {e}") };
    let got: BTreeMap<&str, (&str, &str)> =
        rows.iter().map(|r| (r.symbol.as_str(), (r.variant.as_str(), r.detail.as_str()))).collect();
    assert_eq!(rows.len(), got.len(), "one row per function: {e}");
    assert_eq!(
        got.keys().copied().collect::<Vec<_>>(),
        ["assert_invoking", "sited_unspecified", "unsited"],
        "{e}"
    );
    for (symbol, reason) in [
        ("unsited", "an `Assert` without a panic site"),
        ("sited_unspecified", "a sited `Assert` of `Unspecified` kind"),
        ("assert_invoking", "an `AssertInvoke`"),
    ] {
        let (variant, detail) = got[symbol];
        assert_eq!(variant, "ImplicitPanicUnfaithful", "{symbol}: {e}");
        assert!(detail.contains(reason), "{symbol}: {detail}");
    }
}

/// PKG-CP, MEASURED 2026-11-11: what the whole consumer returns for the one
/// shape a sited check has before any producer emits it. `rung(x: u64, loc:
/// ptr) -> u64 { x + 1 }` with `Assert { kind: Overflow(Add), site: Some(entry,
/// Value(loc)) }` and the bodyless entry `panic_const_add_overflow(ptr)`,
/// through `compile_and_verify_trust_ir_module` on all four legs at O0 and O2:
///
/// * it passes the boundary, the census and trust-cg's compile, and the gate
///   accepts the object (no `Boundary`, `Census`, `Compile` or `Object`
///   refusal);
/// * the gate grades `rung` Unknown at O2: the entry call sits in the check's
///   failure tail, a divergent call event the gate does not model (design step
///   5.7). So STRICT REFUSES with `F1Refusal::Policy` naming `rung`, and
///   ALLOW-UNKNOWN SHIPS with `rung` disclosed as unclosed. The strict lane
///   does not carry a checked function yet: that is the gate work the plan
///   still owes, not a property of the boundary;
/// * the shipped failure path is the delivery trust-ir §19.1 asks for: the
///   location moved into the entry's argument register (`mov x0, x1`), one
///   `bl` relocated against the entry, which the object leaves undefined, and
///   a `brk` after it in case the entry returns.
///
/// FAILS if the boundary refuses a sited check again (`Boundary`), if the gate
/// starts refusing the object or grading the function Refuted, if strict ships
/// a function whose failure call nothing has checked, or if the failure path
/// stops delivering the location to the entry. When the gate learns the
/// divergent call event, the strict half of this test is what moves.
#[test]
fn a_sited_overflow_check_is_unknown_strict_refuses_and_allow_unknown_ships() {
    let add = AssertKind::Overflow(AssertOverflowOp::Add);
    assert_eq!(add.rust_panic_lang_item(), Some(ADD_OVERFLOW_ENTRY));
    const BRK_1: u32 = 0xd420_0020;
    for (target, relocation) in DECLARATION_LEGS {
        let (mut mb, entry, sig) = panic_entry_module("f1_sited_rung", target);
        checked_add_function(&mut mb.m, "rung", sig, add, Some(value_site(entry)));
        let case = Case::new(licensed(mb.finish()));
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);

            let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            let F1Refusal::Policy(why) = &e else { panic!("{what}: not a policy refusal: {e}") };
            assert!(
                why.starts_with("strict: not closed-[PROVED]: rung (Unknown; blocked by [])"),
                "{what}: {why}"
            );
            assert!(e.to_string().starts_with("[f1-output-gate:policy]"), "{what}: {e}");

            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
            assert_eq!(s.unclosed, vec!["rung: Unknown; blocked by []".to_string()], "{what}");
            let c = s.report.certificate("rung").expect("rung");
            assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{what}");
            let o2 = &c.obligations.o2_pairing.detail;
            assert!(
                o2.contains("lies in an assert's failure tail: a divergent call event")
                    && o2.contains(ADD_OVERFLOW_ENTRY),
                "{what}: {}",
                explain(&s.report)
            );
            assert!(s.report.certificate(ADD_OVERFLOW_ENTRY).is_none(), "{what}");

            let object = trust_cg_bridge::compiled_object::CompiledObject::parse(&s.object)
                .expect("the shipped object parses");
            let entry_syms: Vec<_> =
                object.symbols.iter().filter(|y| y.name == ADD_OVERFLOW_ENTRY).collect();
            assert!(!entry_syms.is_empty(), "{what}: the entry is not in the symbol table");
            assert!(
                entry_syms.iter().all(|y| y.section.is_none()),
                "{what}: the entry is defined in the object: {entry_syms:?}"
            );
            let words: BTreeMap<u64, u32> = function_words(&s.object, "rung").into_iter().collect();
            let calls = bl_offsets(&s.object, "rung");
            let [call] = calls.as_slice() else {
                panic!("{what}: `rung` has {} `bl`\n{}", calls.len(), disassemble(&s.object))
            };
            let (_, _, target_symbol) = reloc_at(&s.object, *call);
            assert_eq!(
                target_symbol,
                symbol_index(&s.object, ADD_OVERFLOW_ENTRY),
                "{what}: the failure call is not relocated against the entry"
            );
            assert_eq!(
                words.get(&(call - 4)).copied(),
                Some(enc_mov(0, 1)),
                "{what}: the location (x1) is not the entry's argument (x0)\n{}",
                disassemble(&s.object)
            );
            assert_eq!(
                words.get(&(call + 4)).copied(),
                Some(BRK_1),
                "{what}: no trap after the entry call\n{}",
                disassemble(&s.object)
            );
        }
    }
}

/// The source position the located fixture's check reports, and the symbols of
/// its two data globals.
const RUNG_FILE: &str = "src/rung.rs";
const RUNG_LINE: u32 = 7;
const RUNG_COL: u32 = 5;
const RUNG_LOCATION: &str = "rung_location";
const RUNG_LOCATION_FILE: &str = "rung_location_file";

/// An Internal, immutable, non-TLS global holding the flat image `elements`,
/// typed the way a producer that starts from an allocation types it
/// (trust-cg-lower `type_flat_image`: `[u8; n]` with no relocation, else the
/// packed `<name>.allocation` struct with one `ptr` field per relocation).
fn image_global(m: &mut Module, name: &str, elements: Vec<Constant>, align: u32) -> GlobalId {
    let image = trust_cg_lower::global_image::type_flat_image(m, name, elements, 8)
        .expect("a flat byte/relocation image");
    let id = GlobalId::new(m.globals.len() as u32);
    m.globals.push(Global {
        section: None,
        visibility: Visibility::Default,
        retained: false,
        name: name.to_string(),
        ty: image.ty,
        mutable: false,
        initializer: Some(image.initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(align),
    });
    id
}

fn image_bytes(bytes: &[u8]) -> impl Iterator<Item = Constant> + '_ {
    bytes.iter().map(|b| Constant::Int(i128::from(*b)))
}

/// The two data globals of a located check: the NUL-terminated file name in
/// `rung_location_file`, and the 24-byte record `rung_location` =
/// `{ file: ptr @0, len: u64 @8, line: u32 @16, col: u32 @20 }` whose first
/// word is `SymbolAddr { rung_location_file, 0 }`. That record is this
/// fixture's own layout (the one its C reader declares); it is not a claim
/// about `core::panic::Location`'s layout, which is the producer's to take
/// from the session. Returns the record.
fn location_record(m: &mut Module) -> GlobalId {
    let mut name = RUNG_FILE.as_bytes().to_vec();
    name.push(0);
    image_global(m, RUNG_LOCATION_FILE, image_bytes(&name).collect(), 1);
    let mut record = vec![Constant::SymbolAddr { symbol: RUNG_LOCATION_FILE.into(), addend: 0 }];
    record.extend(image_bytes(&(RUNG_FILE.len() as u64).to_le_bytes()));
    record.extend(image_bytes(&RUNG_LINE.to_le_bytes()));
    record.extend(image_bytes(&RUNG_COL.to_le_bytes()));
    image_global(m, RUNG_LOCATION, record, 8)
}

/// `rung(x: u64) -> u64 { x + 1 }` whose check is sited at a
/// `PanicLocation::Global`: the bodyless entry `panic_const_add_overflow(ptr)`
/// and [`location_record`]'s two globals.
fn located_rung_module(target: F1Target) -> Module {
    let mut mb = ModBuilder::new("f1_located_rung");
    let entry_sig = mb.sig(&[Ty::Ptr], None);
    let entry = mb.declare(ADD_OVERFLOW_ENTRY, entry_sig);
    let rung_sig = mb.sig(&[Ty::U64], Some(Ty::U64));
    mb.m.target_info = Some(m_cg_target_info(target));
    let location = location_record(&mut mb.m);
    checked_add_function_over(
        &mut mb.m,
        "rung",
        rung_sig,
        vec![(ValueId::new(0), Ty::U64)],
        AssertKind::Overflow(AssertOverflowOp::Add),
        Some(PanicSite { entry, location: PanicLocation::Global(location) }),
    );
    licensed(mb.finish())
}

/// The reader's whole-object refusal of a relocated data section, which every
/// data relocation but a location record's pointer keeps.
fn data_relocation_refusal(target: F1Target) -> String {
    let section = if target.is_elf() { ".data.rel.ro" } else { "__DATA,__const" };
    format!("data section `{section}` carries relocations: pointer-bearing statics are refused")
}

/// PKG-CP, MEASURED 2026-11-11: what the whole consumer returns for a check
/// sited at a `PanicLocation::Global`, the shape a producer emits (the record
/// is a `core::panic::Location`: a pointer to the file name, then its length,
/// the line and the column). [`located_rung_module`] through
/// `compile_and_verify_trust_ir_module` on all four legs at O0 and O2:
///
/// * BEFORE the object reader admitted the record's pointer relocation, every
///   leg under both policies was `F1Refusal::Object`: first
///   [`data_relocation_refusal`], and behind it (measured with that refusal
///   switched off) `` global `rung_location` has an initializer the gate cannot
///   image (fail-closed) ``. Nothing earlier refuses: the boundary, the census
///   and trust-cg's compile accept the module;
/// * NOW the object binds. STRICT REFUSES with `F1Refusal::Policy` naming
///   `rung`, never `F1Refusal::Object`, and ALLOW-UNKNOWN SHIPS with `rung`
///   disclosed as unclosed. Until PKG-C5c S2a the grade was Unknown at O1: the
///   failure path materializes the record's address (`adrp`/`add` relocated
///   against `rung_location`), and the gate bound no symbol address. Since S2a
///   (MEASURED 2026-11-15, all four legs at O0 and O2) that pair and the entry
///   call are the tail S2a admits unexecuted, so O1 is Proven and lists the
///   walk's two lines, word for word, as set aside, and the first blocker is O4:
///   this fixture's producer is `M_cg` itself, and the spec side refuses its
///   sited `Assert` (`instruction \`Assert\` is outside the modeled fragment`).
///   Were the producer's check unsited, it would be the live check (4b) keeps
///   Unknown (`x + 1` overflows at `u64::MAX`). The strict lane still does not
///   carry a checked function: that is the gate work the plan owes, not policy;
/// * the shipped object leaves exactly one symbol undefined, the entry, and
///   carries exactly one data relocation: the record's first word, against the
///   object's own local `rung_location_file`, in the kind and addend spelling
///   of its format;
/// * the failure path is the delivery trust-ir §19.1 asks for: the record's
///   address in the entry's argument register, one `bl` relocated against the
///   entry, and a `brk` after it in case the entry returns.
///
/// FAILS if the reader refuses the record again (`Object`), if strict ships a
/// function whose failure call nothing has checked, if the object gains a
/// second undefined symbol or data relocation, or if the failure path stops
/// passing the record to the entry.
#[test]
fn a_located_overflow_check_ships_its_location_record_and_strict_refuses() {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, RelocKind, RelocTarget, SectionClass, SymbolBinding, SymbolKind,
    };
    const BRK_1: u32 = 0xd420_0020;
    for (target, relocation) in DECLARATION_LEGS {
        let case = Case::new(located_rung_module(target));
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);

            let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            let F1Refusal::Policy(why) = &e else { panic!("{what}: not a policy refusal: {e}") };
            assert!(
                why.starts_with("strict: not closed-[PROVED]: rung (Unknown; blocked by [])"),
                "{what}: {why}"
            );
            // The refusal names the real blocker, `rung`'s first undecided obligation (O4 since
            // PKG-C5c S2a: the spec side refuses the producer's sited `Assert`), not only its
            // grade.
            assert!(
                why.contains(
                    "rung o4: Unknown: spec side: instruction `Assert` is outside the modeled \
                     fragment (fail-closed)"
                ),
                "{what}: {why}"
            );
            assert!(e.to_string().starts_with("[f1-output-gate:policy]"), "{what}: {e}");

            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
            assert_eq!(s.unclosed, vec!["rung: Unknown; blocked by []".to_string()], "{what}");
            let c = s.report.certificate("rung").expect("rung");
            assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{what}");
            // O1 admits the record's address pair as a dead tail's (PKG-C5c S2a) and lists the
            // walk's own two lines, unchanged, as set aside.
            let o1 = &c.obligations.o1_binding;
            assert!(
                o1.grade == Grade::Proven
                    && o1.detail.contains(
                        "1 dead panic-tail Location pair(s) admitted unexecuted (PKG-C5c S2a)"
                    )
                    && o1.detail.contains("address materialization")
                    && o1.detail.contains("symbol addresses are bound at steps 5.7/5.9"),
                "{what}: {}",
                explain(&s.report)
            );

            // The object: one undefined symbol, one data relocation.
            let object = CompiledObject::parse(&s.object).expect("the shipped object parses");
            let undefined: Vec<&str> = object
                .symbols
                .iter()
                .filter(|y| y.kind == SymbolKind::Undefined && !y.name.is_empty())
                .map(|y| y.name.as_str())
                .collect();
            assert_eq!(undefined, [ADD_OVERFLOW_ENTRY], "{what}");
            let data: Vec<_> = object
                .sections
                .iter()
                .filter(|x| matches!(x.class, SectionClass::Data | SectionClass::ZeroFill))
                .flat_map(|x| x.relocations.iter().map(move |r| (x, r)))
                .collect();
            let [(section, reloc)] = data.as_slice() else {
                panic!("{what}: {} data relocations", data.len())
            };
            let defined = |name: &str| {
                let y = object.symbols.iter().find(|y| y.name == name).expect("data symbol");
                assert_eq!(y.binding, SymbolBinding::Local, "{what}: {name}");
                (y.index, y.section.expect("defined"), y.value)
            };
            let (_, record_section, record_at) = defined(RUNG_LOCATION);
            let (file, _, _) = defined(RUNG_LOCATION_FILE);
            assert_eq!((section.index, reloc.offset), (record_section, record_at), "{what}");
            assert_eq!(reloc.target, RelocTarget::Symbol(file), "{what}");
            assert!(!reloc.pc_relative && reloc.addend == 0, "{what}: {reloc:?}");
            // R_AARCH64_ABS64 and ARM64_RELOC_UNSIGNED of length 3 both write 8 bytes.
            let (raw, length) = if target.is_elf() { (257, 3) } else { (0, 3) };
            assert_eq!((reloc.kind, reloc.length), (RelocKind::Other { raw }, length), "{what}");
            let record = &section.bytes[record_at as usize..record_at as usize + 24];
            assert_eq!(record[..8], [0; 8], "{what}: the pointer's bytes in place");
            assert_eq!(record[8..16], (RUNG_FILE.len() as u64).to_le_bytes(), "{what}");
            assert_eq!(record[16..20], RUNG_LINE.to_le_bytes(), "{what}");
            assert_eq!(record[20..24], RUNG_COL.to_le_bytes(), "{what}");

            // The failure path: the record's address (`adrp`/`add` relocated
            // against `rung_location`) in x0, `bl <entry>`, `brk #1`.
            let words: BTreeMap<u64, u32> = function_words(&s.object, "rung").into_iter().collect();
            let calls = bl_offsets(&s.object, "rung");
            let [call] = calls.as_slice() else {
                panic!("{what}: `rung` has {} `bl`\n{}", calls.len(), disassemble(&s.object))
            };
            let (_, _, callee) = reloc_at(&s.object, *call);
            assert_eq!(callee, symbol_index(&s.object, ADD_OVERFLOW_ENTRY), "{what}");
            let record_symbol = symbol_index(&s.object, RUNG_LOCATION);
            let materializing: Vec<u64> = text_relocs(&s.object)
                .into_iter()
                .filter_map(|(_, at, _, symbol)| (symbol == record_symbol).then_some(at))
                .collect();
            let [adrp, add] = materializing.as_slice() else {
                panic!("{what}: {materializing:?}\n{}", disassemble(&s.object))
            };
            // `adrp xP, page; add xR, xP, #offset`.
            let register = words[add] & 0x1f;
            assert_eq!((*add, words[adrp] & 0x1f), (adrp + 4, (words[add] >> 5) & 0x1f), "{what}");
            // Straight into x0, or (O0) through a register moved into x0.
            let delivered = (add + 4 == *call && register == 0)
                || (add + 8 == *call && words[&(add + 4)] == enc_mov(0, register));
            assert!(
                delivered,
                "{what}: the entry's argument is not the record's address\n{}",
                disassemble(&s.object)
            );
            assert_eq!(
                words.get(&(call + 4)).copied(),
                Some(BRK_1),
                "{what}: no trap after the entry call\n{}",
                disassemble(&s.object)
            );
        }
    }
}

/// PKG-C5c S2a (docs/DECISION_QUEUE.md PKG-C5c-DEAD-TAIL-1), MEASURED 2026-11-15: ladder rung
/// s21 (`if x != 0 { 1000 / x } else { 0 }`) through the whole consumer, `M_cg` siting the
/// division's check at `panic_const_div_by_zero` and an immutable Internal Location record, the
/// producer keeping it unsited (`cer_common::sited_div`), on all four legs:
///
/// * at O0 the bytes keep the dead check's failure tail (`adrp/add` of the record, `bl` the
///   entry, `brk`). Before S2a `rung` was Unknown at O1 (the ladder's certificate). Now the
///   tail is admitted unexecuted and `rung` grades [VALIDATED]: ALLOW-UNKNOWN SHIPS it
///   disclosed as `[VALIDATED]`, STRICT REFUSES it as "Proven without kernel evidence" (the
///   step-(5) division split declines the repeated guard: tests/call_event_gate.rs
///   `s2a_a_dead_sited_division_tail_is_admitted_unexecuted`);
/// * at O2 trust-cg drops the dead tail and STRICT SHIPS `rung` kernel-[PROVED], as before.
///
/// FAILS if the O0 tail stops being admitted (Unknown again), if strict ships a function with a
/// tail on ay's word alone, or if the O2 cell stops shipping under strict.
#[test]
fn a_dead_sited_division_check_ships_validated_at_o0_and_proved_at_o2() {
    for (target, relocation) in DECLARATION_LEGS {
        let triple = if target.is_elf() { LINUX } else { DARWIN };
        let (mut m_cg, producer) = sited_div(true, DivRecord::Pointer);
        m_cg.target_info = Some(m_cg_target_info(target));
        let case = Case::with_producer(licensed(m_cg), licensed(targeted(&producer, triple)));
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);
            let strict = case.run(&cfg, EmitPolicy::StrictProvenOnly);
            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
            let c = s.report.certificate("rung").expect("rung");
            if opt == F1OptLevel::O0 {
                let e = refused(strict, &what);
                let F1Refusal::Policy(why) = &e else {
                    panic!("{what}: not a policy refusal: {e}")
                };
                assert!(
                    why.starts_with(
                        "strict: not closed-[PROVED]: rung ([VALIDATED]; blocked by [])"
                    ) && why.contains("rung: Proven without kernel evidence"),
                    "{what}: {why}"
                );
                assert_eq!(s.unclosed, vec!["rung: [VALIDATED]; blocked by []".to_string()]);
                assert!(
                    c.obligations.o1_binding.detail.contains(
                        "1 dead panic-tail Location pair(s) admitted unexecuted (PKG-C5c S2a)"
                    ) && c.obligations.o2_pairing.detail.contains("entry and Location unverified"),
                    "{what}: {}",
                    explain(&s.report)
                );
                assert_eq!(bl_offsets(&s.object, "rung").len(), 1, "{what}: the tail's `bl`");
            } else {
                let strict = shipped(strict, &what);
                assert!(kernel_proved(&strict.report, "rung"), "{what}");
                assert!(s.unclosed.is_empty(), "{what}: {:?}", s.unclosed);
                assert!(bl_offsets(&s.object, "rung").is_empty(), "{what}: a tail at O2");
            }
        }
    }
}

/// `mk(a: u64) -> (u64, u64, u64)`: a by-value 24-byte result, handed to F1 as the compiler lane
/// hands rustc's sret return (codegen_module.rs rule 10). The producer returns the tuple; M_cg's
/// copy takes a leading result pointer and stores the three fields through it; and P places the
/// result `ReturnPlace::Indirect`, which the gate grades O4 Unknown until step 5.10, before it
/// reads M_cg's bytes as a refinement.
fn sret_result_case() -> Case {
    let s24 = Ty::Tuple(vec![Ty::U64; 3]);
    let mut producer = ModBuilder::new("f1_sret");
    let sig = producer.sig(&[Ty::U64], Some(s24.clone()));
    producer.define("mk", sig, Linkage::External, |fb| {
        let out = fb.push_inst(Inst::MakeAggregate {
            ty: s24.clone(),
            variant: None,
            fields: vec![fb.p(0); 3],
        });
        fb.ret(out);
    });
    let mut m_cg = ModBuilder::new("f1_sret");
    let sig = m_cg.sig(&[Ty::Ptr, Ty::U64], None);
    m_cg.define("mk", sig, Linkage::External, |fb| {
        for field in 0..3 {
            let at = if field == 0 {
                fb.p(0)
            } else {
                let index = fb.konst(Ty::U64, field);
                fb.push_inst(Inst::GEP {
                    pointee_ty: Ty::U64,
                    base: fb.p(0),
                    indices: vec![index],
                    inbounds: true,
                })
            };
            fb.push_inst_void(Inst::Store {
                ty: Ty::U64,
                ptr: at,
                value: fb.p(1),
                volatile: false,
                align: None,
            });
        }
        fb.ret_void();
    });
    let mut case = Case::with_producer(licensed(m_cg.finish()), licensed(producer.finish()));
    case.placements.insert(
        "mk".into(),
        FnPlacement {
            params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))],
            ret: ReturnPlace::Indirect,
        },
    );
    case
}

/// PKG-CP S0. The strict refusal names the function's first unproven obligation, here O4's sret
/// placement, after `ships`' own list and under its own label. FAILS when the refusal names only
/// the grade (`mk (Unknown; blocked by [])`) or lists the SemR frame request as the cause.
/// Allow-unknown ships the same object with `mk` unclosed and the same O4 on its certificate.
#[test]
fn strict_refusal_names_first_unproven_obligation() {
    let case = sret_result_case();
    for (target, relocation) in LEGS {
        let what = format!("{target:?} {relocation:?}");
        let cfg = config(target, F1OptLevel::O0, relocation);
        let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
        let F1Refusal::Policy(why) = &e else { panic!("{what}: not a policy refusal: {e}") };
        assert!(
            why.starts_with("strict: not closed-[PROVED]: mk (Unknown; blocked by [])"),
            "{what}: {why}"
        );
        assert!(
            why.contains("; blockers: mk o4: Unknown: ")
                && why.contains("an sret result is Unknown until step 5.10"),
            "{what}: {why}"
        );

        let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
        assert_eq!(s.unclosed, vec!["mk: Unknown; blocked by []".to_string()], "{what}");
        let c = s.report.certificate("mk").expect("mk");
        assert!(
            c.obligations.o4_return.detail.contains("an sret result is Unknown until step 5.10"),
            "{what}\n{}",
            explain(&s.report)
        );
    }
}

/// The file offset of the one occurrence of `needle` in `object`.
#[track_caller]
fn only_occurrence(object: &[u8], needle: &[u8], what: &str) -> usize {
    let at: Vec<usize> = object
        .windows(needle.len())
        .enumerate()
        .filter_map(|(i, w)| (w == needle).then_some(i))
        .collect();
    let [at] = at.as_slice() else { panic!("{what}: {} occurrences", at.len()) };
    *at
}

/// PKG-CP: the reader's admission of the record's relocation, through the real
/// parser on the real object (the unit tests in
/// `src/compiled_object/pointer_record_tests.rs` take the arm apart condition
/// by condition on parsed objects). The object trust-cg compiles for
/// [`located_rung_module`] binds; with ONE field of its data relocation record,
/// or one byte under it, changed in the file, the gate refuses the whole
/// object with the refusal every relocated data section had before.
/// FAILS if the reader admits a data relocation of another kind, width or
/// pc-relativity, against a function, an undefined symbol, a section or
/// another global, with a stray addend, or over bytes that are not the addend.
#[test]
fn a_moved_field_of_the_location_relocation_refuses_the_object() {
    for target in [DARWIN_T, LINUX_T] {
        let elf = target.is_elf();
        let mut module = located_rung_module(target);
        set_gate(&mut module, "rung", None);
        let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let fx = Fixture::with_object(module, object, target.triple());
        fx.verify().unwrap_or_else(|e| panic!("{target:?}: the unpatched object is refused: {e}"));

        let symbol = |name: &str| symbol_index(&fx.object, name);
        let file = symbol(RUNG_LOCATION_FILE);
        // The record as its format writes it: at offset 0 of its section,
        // against `rung_location_file`, addend 0.
        let record = if elf {
            let info = ((file as u64) << 32) | 257;
            [0_u64.to_le_bytes(), info.to_le_bytes(), 0_u64.to_le_bytes()].concat()
        } else {
            // r_address 0; symbolnum | length 3 << 25 | extern << 27 | type 0 << 28.
            let w1 = file as u32 | 3 << 25 | 1 << 27;
            [0_u32.to_le_bytes(), w1.to_le_bytes()].concat()
        };
        let at = only_occurrence(&fx.object, &record, "the data relocation record");
        let mut image = vec![0; 8];
        image.extend_from_slice(&(RUNG_FILE.len() as u64).to_le_bytes());
        image.extend_from_slice(&RUNG_LINE.to_le_bytes());
        image.extend_from_slice(&RUNG_COL.to_le_bytes());
        let bytes_at = only_occurrence(&fx.object, &image, "the record's bytes");

        let flip_w1 =
            |bit: u32| move |o: &mut Vec<u8>| o[at + 4 + bit as usize / 8] ^= 1 << (bit % 8);
        let mut patches: Vec<(&str, Box<dyn Fn(&mut Vec<u8>)>)> = vec![
            ("against the function", Box::new(|o| set_reloc_symbol(o, at, symbol("rung")))),
            (
                "against the undefined entry",
                Box::new(|o| set_reloc_symbol(o, at, symbol(ADD_OVERFLOW_ENTRY))),
            ),
            (
                "against the record itself",
                Box::new(|o| set_reloc_symbol(o, at, symbol(RUNG_LOCATION))),
            ),
            ("at an offset inside the record's bytes", Box::new(|o| set_reloc_offset(o, at, 8))),
        ];
        if elf {
            // R_AARCH64_ABS32, R_AARCH64_PREL64, R_AARCH64_NONE.
            for ty in [258, 260, 0] {
                patches.push(("another kind", Box::new(move |o| set_reloc_type(o, at, ty))));
            }
            patches.push(("a stray r_addend", Box::new(|o| set_elf_reloc_addend(o, at, 4))));
        } else {
            // ARM64_RELOC_SUBTRACTOR, ARM64_RELOC_POINTER_TO_GOT, ARM64_RELOC_PAGEOFF12.
            for ty in [1, 7, 4] {
                patches.push(("another kind", Box::new(move |o| set_reloc_type(o, at, ty))));
            }
            patches.push(("pc-relative", Box::new(flip_w1(24))));
            patches.push(("4 bytes wide", Box::new(flip_w1(25))));
            patches.push(("section-relative", Box::new(flip_w1(27))));
        }
        for (what, patch) in &patches {
            let e = fx.patched(patch).verify().expect_err(what);
            assert_eq!(
                (e.kind, e.reason.as_str()),
                (ObjectRefusalKind::DataImage, data_relocation_refusal(target).as_str()),
                "{target:?}: {what}"
            );
        }
        // Bytes under the relocation that are not the addend (zero here).
        let e = fx.patched(|o| o[bytes_at] = 8).verify().expect_err("in-place bytes");
        assert_eq!(
            (e.kind, e.reason.as_str()),
            (
                ObjectRefusalKind::DataImage,
                "global `rung_location`'s bytes differ from its initializer image"
            ),
            "{target:?}"
        );
    }
}

/// PKG-CP: the shipped object, LINKED AND RUN on this host. The Darwin object
/// [`located_rung_module`] ships under allow-unknown is linked by the system
/// `cc` with a C file that defines the entry and prints what it reads through
/// its location argument (the record's layout is the fixture's, see
/// [`location_record`]). `rung(41)` returns 42 and never calls the entry;
/// `rung(u64::MAX)` calls the entry with a location that reads
/// `src/rung.rs:7:5`, the file name NUL-terminated at its length; and when the
/// entry returns, the process dies in the trap that follows the call instead
/// of running on. This is what the linker and dyld make of the one data
/// relocation the reader admits: the record's pointer is the file name's
/// address.
/// FAILS if the object does not link against an entry defined elsewhere, if
/// the failed check delivers another location (or none), if a passing check
/// reaches the entry, or if control survives a returning entry.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn a_located_overflow_check_links_and_reports_its_location_natively() {
    use std::os::unix::process::ExitStatusExt;
    use std::process::Command;
    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
struct location { const char *file; uint64_t len; uint32_t line; uint32_t col; };
extern uint64_t rung(uint64_t);
static int entry_returns;
void panic_const_add_overflow(const struct location *loc) {
    printf("%.*s:%u:%u nul=%d\n", (int)loc->len, loc->file, loc->line, loc->col,
           loc->file[loc->len] == 0);
    fflush(stdout);
    if (entry_returns) return;
    _exit(101);
}
int main(int argc, char **argv) {
    entry_returns = argc > 2;
    uint64_t r = rung(strtoull(argv[1], 0, 10));
    printf("returned %llu\n", (unsigned long long)r);
    return 0;
}
"#;
    const SIGTRAP: i32 = 5;
    let case = Case::new(located_rung_module(DARWIN_T));
    let dir = tempfile::tempdir().expect("the test's temp dir");
    std::fs::write(dir.path().join("driver.c"), DRIVER).expect("write the driver");
    let located = format!("{RUNG_FILE}:{RUNG_LINE}:{RUNG_COL} nul=1\n");
    for opt in [F1OptLevel::O0, F1OptLevel::O2] {
        let cfg = config(DARWIN_T, opt, RelocationModel::Static);
        let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "the located rung");
        let object = dir.path().join(format!("rung-{opt:?}.o"));
        let binary = dir.path().join(format!("driver-{opt:?}"));
        std::fs::write(&object, &s.object).expect("write the object");
        let link = Command::new("cc")
            .arg(dir.path().join("driver.c"))
            .arg(&object)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run the system cc");
        assert!(link.status.success(), "{opt:?}: cc failed: {link:?}");
        let run = |args: &[&str]| {
            let out = Command::new(&binary).args(args).output().expect("run the linked binary");
            (String::from_utf8_lossy(&out.stdout).into_owned(), out.status)
        };

        let (stdout, status) = run(&["41"]);
        assert_eq!((stdout.as_str(), status.code()), ("returned 42\n", Some(0)), "{opt:?}");

        let max = u64::MAX.to_string();
        let (stdout, status) = run(&[&max]);
        assert_eq!((stdout.as_str(), status.code()), (located.as_str(), Some(101)), "{opt:?}");

        let (stdout, status) = run(&[&max, "entry-returns"]);
        assert_eq!(stdout, located, "{opt:?}: a returning entry must not reach the result");
        assert_eq!(
            (status.code(), status.signal()),
            (None, Some(SIGTRAP)),
            "{opt:?}: no trap after a returning entry: {status:?}"
        );
    }
}

/// PKG-CP, MEASURED 2026-11-11: what the reader's admission reaches in the
/// STRICT lane. A module whose only function is the closed leaf `h` and which
/// also carries [`location_record`]'s two globals, read by no function, SHIPS
/// UNDER STRICT on all four legs at O0 and O2, with nothing unclosed and the
/// record's one pointer relocation in the object. Against the reader before
/// the admission the same module is `F1Refusal::Object`
/// ([`data_relocation_refusal`]): run on Darwin Static at O0 under strict, and
/// the reader runs before policy is consulted.
///
/// So a strict object can now carry a relocated record. What stands behind
/// that is the reader's check of the relocation and of the record's bytes
/// against `M_cg` (compiled_object.rs, DATA RELOCATIONS) and the static
/// linker's meaning of an absolute pointer relocation; no function verdict
/// speaks about the record. A function that takes the record's address is not
/// closed by this
/// ([`a_located_overflow_check_ships_its_location_record_and_strict_refuses`]).
///
/// FAILS if the reader refuses the record again, or if the object stops
/// carrying exactly the one data relocation this test counts.
#[test]
fn a_location_record_no_function_reads_ships_strict_beside_a_closed_function() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SectionClass};
    for (target, relocation) in DECLARATION_LEGS {
        let mut m = leaf_module("h");
        m.target_info = Some(m_cg_target_info(target));
        location_record(&mut m);
        let case = Case::new(m);
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);
            let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            assert!(s.unclosed.is_empty(), "{what}: {:?}", s.unclosed);
            assert!(kernel_proved(&s.report, "h"), "{what}\n{}", explain(&s.report));
            let object = CompiledObject::parse(&s.object).expect("the shipped object parses");
            let relocated: Vec<&str> = object
                .sections
                .iter()
                .filter(|section| section.class == SectionClass::Data)
                .flat_map(|section| &section.relocations)
                .map(|r| object.reloc_symbol(r).map_or("?", |target| target.name.as_str()))
                .collect();
            assert_eq!(relocated, [RUNG_LOCATION_FILE], "{what}");
        }
    }
}

/// The image [`string_pieces_module`] gives `rung_location_file`: three
/// NUL-terminated strings, the first two equal.
const STRING_PIECES: &[u8] = b"ab\0ab\0cd\0";

/// [`located_rung_module`] with [`STRING_PIECES`] for the file name and its
/// whole length in the record, so that the entry reads all of it.
fn string_pieces_module(target: F1Target) -> Module {
    let mut mb = ModBuilder::new("f1_located_rung_pieces");
    let entry_sig = mb.sig(&[Ty::Ptr], None);
    let entry = mb.declare(ADD_OVERFLOW_ENTRY, entry_sig);
    let rung_sig = mb.sig(&[Ty::U64], Some(Ty::U64));
    mb.m.target_info = Some(m_cg_target_info(target));
    image_global(&mut mb.m, RUNG_LOCATION_FILE, image_bytes(STRING_PIECES).collect(), 1);
    let mut record = vec![Constant::SymbolAddr { symbol: RUNG_LOCATION_FILE.into(), addend: 0 }];
    record.extend(image_bytes(&(STRING_PIECES.len() as u64).to_le_bytes()));
    record.extend(image_bytes(&RUNG_LINE.to_le_bytes()));
    record.extend(image_bytes(&RUNG_COL.to_le_bytes()));
    let location = image_global(&mut mb.m, RUNG_LOCATION, record, 8);
    checked_add_function_over(
        &mut mb.m,
        "rung",
        rung_sig,
        vec![(ValueId::new(0), Ty::U64)],
        AssertKind::Overflow(AssertOverflowOp::Add),
        Some(PanicSite { entry, location: PanicLocation::Global(location) }),
    );
    licensed(mb.finish())
}

/// Mark the section that defines `symbol` as one a linker SPLITS AND MERGES BY
/// CONTENT instead of keeping whole. Mach-O: `__TEXT,__const` becomes
/// `__TEXT,__cstring` of type `S_CSTRING_LITERALS`, the section a C compiler
/// puts its string literals in (the linker merges literals per output section,
/// so the name decides what they merge with; the reader classes both names as
/// data). ELF: `.rodata` gains `SHF_MERGE | SHF_STRINGS` with `sh_entsize` 1.
/// Only the section's header changes: no byte, symbol or relocation moves.
fn mark_string_literals(o: &mut [u8], symbol: &str) {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
    let parsed = CompiledObject::parse(o).expect("the object parses");
    let section = parsed
        .symbols
        .iter()
        .find(|y| y.name == symbol)
        .and_then(|y| y.section)
        .unwrap_or_else(|| panic!("no defined symbol `{symbol}`"));
    if is_macho(o) {
        // The section_64 headers of the LC_SEGMENT_64 commands, in order: the
        // 1-based ordinal a symbol names.
        const S_CSTRING_LITERALS: u32 = 2;
        let mut headers = Vec::new();
        let mut c = 32;
        for _ in 0..rd32(o, 16) {
            if rd32(o, c) == 0x19 {
                headers.extend((0..rd32(o, c + 64) as usize).map(|i| c + 72 + i * 80));
            }
            c += rd32(o, c + 4) as usize;
        }
        let header = headers[section - 1];
        assert_eq!(&o[header..header + 32], b"__const\0\0\0\0\0\0\0\0\0__TEXT\0\0\0\0\0\0\0\0\0\0");
        o[header..header + 16].copy_from_slice(b"__cstring\0\0\0\0\0\0\0");
        let flags = header + 64;
        let marked = (rd32(o, flags) & !0xff) | S_CSTRING_LITERALS;
        o[flags..flags + 4].copy_from_slice(&marked.to_le_bytes());
    } else {
        const SHF_MERGE_STRINGS: u64 = 0x10 | 0x20;
        let header = rd64(o, 40) as usize + section * usize::from(o[58]);
        let marked = rd64(o, header + 8) | SHF_MERGE_STRINGS;
        o[header + 8..header + 16].copy_from_slice(&marked.to_le_bytes());
        o[header + 56..header + 64].copy_from_slice(&1_u64.to_le_bytes());
    }
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation (2026-11-11). RED
/// against compiled_object.rs blob 7681fe547d: the reader BINDS these objects.
///
/// The admission's ground for a record's pointer is that it leads to bytes the
/// reader compared with `M_cg`'s image of the target global ("in initialized
/// data (so its bytes are compared)"). That holds only where the linker keeps
/// the target's section whole. A Mach-O section of type `S_CSTRING_LITERALS`
/// (or the 4/8/16-byte literal types) and an ELF section flagged
/// `SHF_MERGE` are split into pieces that the linker deduplicates and
/// reorders, and a relocation against a symbol in one is resolved to the
/// PIECE the symbol starts, so the bytes after that piece are not the rest of
/// the global. The reader classifies a section by its name (and, on ELF, the
/// alloc/exec/write flags) and never reads the section type or the merge
/// flags, so the object trust-cg compiles for [`string_pieces_module`], with
/// nothing changed but the header of the file name's section
/// ([`mark_string_literals`]), satisfies every condition the admission states.
///
/// What the linkers make of it, measured 2026-11-11, where `M_cg`'s image is
/// `616200616200636400`:
/// * Mach-O, Apple ld-27037.1, linked and run by
///   [`the_system_linker_splits_a_string_literal_section_under_a_record_pointer`]:
///   the record's pointer leads to `616200010000001c00`;
/// * ELF, LLD 23.1.1 (`rust-lld -flavor gnu`, this test's marked Linux object
///   beside an object that defines the entry and `_start`; linked by hand and
///   the output file read, not executed and not run by any test): the pointer
///   leads to `616200636400000014` at the default `-O1` and to
///   `616200000014000000` at `-O2`, with no second object's strings involved.
///   The unmarked object reads `616200616200636400` under both.
///
/// FAILS while the reader admits a record whose pointer's target lies in a
/// section the linker merges by content.
#[test]
fn a_record_pointer_into_a_string_literal_section_is_refused() {
    let mut bound = Vec::new();
    for target in [DARWIN_T, LINUX_T] {
        let mut module = string_pieces_module(target);
        set_gate(&mut module, "rung", None);
        let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let fx = Fixture::with_object(module, object, target.triple());
        fx.verify().unwrap_or_else(|e| panic!("{target:?}: the unmarked object is refused: {e}"));
        let marked = fx.patched(|o| mark_string_literals(o, RUNG_LOCATION_FILE));
        assert_ne!(marked.object, fx.object, "{target:?}: the mark changed nothing");
        if marked.verify().is_ok() {
            bound.push(target);
        }
    }
    assert!(
        bound.is_empty(),
        "BOUND on {bound:?}: the record's pointer leads into a section the linker splits and \
         merges by content, and the reader admitted it"
    );
}

/// The evidence behind
/// [`a_record_pointer_into_a_string_literal_section_is_refused`], LINKED AND
/// RUN on this host (measured 2026-11-11, Apple ld-27037.1). The Darwin object
/// [`string_pieces_module`] ships under allow-unknown is linked by the system
/// `cc` beside a C file that has the string literals "cd" and "ab" of its own;
/// the entry prints the `len` bytes its location argument's pointer leads to.
/// As shipped, they are `M_cg`'s image of the file name. With the file name's
/// section marked `S_CSTRING_LITERALS`, an object the reader binds the same,
/// they are "ab\0" followed by bytes of another section: the linker merged the
/// string into the other file's "ab" and resolved the record's relocation to
/// that piece.
/// FAILS if this linker stops splitting a string-literal section under a
/// relocated pointer (the refusal the other test asks for is then owed to the
/// ELF linkers alone), or if the shipped object stops reading its own image.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn the_system_linker_splits_a_string_literal_section_under_a_record_pointer() {
    use std::process::Command;
    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
struct location { const unsigned char *file; uint64_t len; uint32_t line; uint32_t col; };
extern uint64_t rung(uint64_t);
void panic_const_add_overflow(const struct location *loc) {
    for (uint64_t i = 0; i < loc->len; i++) printf("%02x", loc->file[i]);
    printf("\n");
    fflush(stdout);
    _exit(101);
}
int main(void) { return (int)rung(UINT64_MAX); }
"#;
    const OTHER: &str = "const char *other1 = \"cd\"; const char *other2 = \"ab\";\n";
    let case = Case::new(string_pieces_module(DARWIN_T));
    let cfg = config(DARWIN_T, F1OptLevel::O2, RelocationModel::Static);
    let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "the located rung");
    let mut marked = s.object.clone();
    mark_string_literals(&mut marked, RUNG_LOCATION_FILE);

    let dir = tempfile::tempdir().expect("the test's temp dir");
    std::fs::write(dir.path().join("driver.c"), DRIVER).expect("write the driver");
    std::fs::write(dir.path().join("other.c"), OTHER).expect("write the other file");
    let read_through_the_record = |name: &str, object: &[u8]| {
        let path = dir.path().join(format!("{name}.o"));
        let binary = dir.path().join(name);
        std::fs::write(&path, object).expect("write the object");
        let link = Command::new("cc")
            .arg(dir.path().join("other.c"))
            .arg(dir.path().join("driver.c"))
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run the system cc");
        assert!(link.status.success(), "{name}: cc failed: {link:?}");
        let out = Command::new(&binary).output().expect("run the linked binary");
        assert_eq!(out.status.code(), Some(101), "{name}: {out:?}");
        String::from_utf8_lossy(&out.stdout).trim_end().to_string()
    };
    let image: String = STRING_PIECES.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(read_through_the_record("shipped", &s.object), image);
    let read = read_through_the_record("marked", &marked);
    assert!(
        read.starts_with("616200") && read != image,
        "the marked object reads {read}, M_cg's image is {image}"
    );
}

/// The file offset of the header (Mach-O `section_64`, ELF `Elf64_Shdr`) of
/// the section that defines `symbol`.
fn section_header_of(o: &[u8], symbol: &str) -> usize {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let parsed = CompiledObject::parse(o).expect("the object parses");
    let section = parsed
        .symbols
        .iter()
        .find(|y| y.name == symbol)
        .and_then(|y| y.section)
        .unwrap_or_else(|| panic!("no defined symbol `{symbol}`"));
    if is_macho(o) {
        // The section_64 headers of the LC_SEGMENT_64 commands, in order: the
        // 1-based ordinal a symbol names.
        let mut headers = Vec::new();
        let mut c = 32;
        for _ in 0..rd32(16) {
            if rd32(c) == 0x19 {
                headers.extend((0..rd32(c + 64) as usize).map(|i| c + 72 + i * 80));
            }
            c += rd32(c + 4) as usize;
        }
        headers[section - 1]
    } else {
        let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
        shoff + section * usize::from(o[58])
    }
}

/// OR `bits` into the header flags word of the section that defines `symbol`:
/// the 32-bit Mach-O `flags` (section type in the low byte, attributes above)
/// or the 64-bit ELF `sh_flags`. Nothing else in the object changes.
fn or_section_flags(o: &mut [u8], symbol: &str, bits: u64) {
    let header = section_header_of(o, symbol);
    if is_macho(o) {
        let at = header + 64;
        let flags = u32::from_le_bytes(o[at..at + 4].try_into().unwrap()) | bits as u32;
        o[at..at + 4].copy_from_slice(&flags.to_le_bytes());
    } else {
        let at = header + 8;
        let flags = u64::from_le_bytes(o[at..at + 8].try_into().unwrap()) | bits;
        o[at..at + 8].copy_from_slice(&flags.to_le_bytes());
    }
}

/// PKG-CP: THE HEADER WORD ALONE refuses, through the real parser on the real
/// object. The object trust-cg compiles for [`located_rung_module`] binds; its
/// two data sections have the plain header words the admission asks for
/// (measured 2026-11-11: Mach-O `flags` 0 for both `__DATA,__const` and
/// `__TEXT,__const`; ELF `sh_flags` `WA` for `.data.rel.ro` and `A` for
/// `.rodata`). With ONE bit or type value added to the flags word of the
/// record's section or of the file name's, and no name, byte, symbol or
/// relocation changed, the gate refuses the whole object with the refusal
/// every relocated data section had before the admission. So do a file-header
/// flag the reader does not name and the file name in a writable section. The
/// unit tests in
/// `src/compiled_object/pointer_record_tests.rs` enumerate every word on
/// parsed objects; this shows the parser reads the word they set
/// ([`a_record_pointer_into_a_string_literal_section_is_refused`] changes the
/// Mach-O name together with the type, so it does not isolate the type).
/// FAILS if the reader stops reading a section's header flags, or admits a
/// record whose section, or whose target's section, is a literal, merge,
/// coalesced, group, thread-local, compressed or attribute-marked section, a
/// target the object puts in writable memory, or an object whose file-header
/// flags it does not name.
#[test]
fn a_section_header_that_is_not_ordinary_data_refuses_the_located_object() {
    for target in [DARWIN_T, LINUX_T] {
        let mut module = located_rung_module(target);
        set_gate(&mut module, "rung", None);
        let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let fx = Fixture::with_object(module, object, target.triple());
        fx.verify().unwrap_or_else(|e| panic!("{target:?}: the unpatched object is refused: {e}"));
        let refusal = data_relocation_refusal(target);
        let refused = |what: &str, patch: &dyn Fn(&mut Vec<u8>)| {
            let patched = fx.patched(patch);
            assert_ne!(patched.object, fx.object, "{target:?}: {what} changed nothing");
            let e = patched.verify().err().unwrap_or_else(|| panic!("{target:?}: {what}: BOUND"));
            assert_eq!(
                (e.kind, e.reason.as_str()),
                (ObjectRefusalKind::DataImage, refusal.as_str()),
                "{target:?}: {what}"
            );
        };
        let words: &[(&str, u64)] = if target.is_elf() {
            &[
                ("SHF_MERGE", 0x10),
                ("SHF_STRINGS", 0x20),
                ("SHF_MERGE | SHF_STRINGS", 0x30),
                ("SHF_LINK_ORDER", 0x80),
                ("SHF_GROUP", 0x200),
                ("SHF_TLS", 0x400),
                ("SHF_COMPRESSED", 0x800),
                ("SHF_GNU_RETAIN", 0x20_0000),
            ]
        } else {
            &[
                ("S_CSTRING_LITERALS", 0x2),
                ("S_4BYTE_LITERALS", 0x3),
                ("S_8BYTE_LITERALS", 0x4),
                ("S_LITERAL_POINTERS", 0x5),
                ("S_COALESCED", 0xb),
                ("S_16BYTE_LITERALS", 0xe),
                ("S_ATTR_NO_DEAD_STRIP", 0x1000_0000),
                ("S_ATTR_LIVE_SUPPORT", 0x0800_0000),
                ("S_ATTR_STRIP_STATIC_SYMS", 0x2000_0000),
            ]
        };
        for symbol in [RUNG_LOCATION, RUNG_LOCATION_FILE] {
            for (name, bits) in words {
                refused(&format!("{name} on the section of `{symbol}`"), &|o| {
                    or_section_flags(o, symbol, *bits);
                });
            }
        }
        // A file-header flag the reader does not name: Mach-O
        // `MH_HAS_TLV_DESCRIPTORS` (0x800000) beside the flag trust-cg sets;
        // ELF `e_flags` bit 0.
        refused("a file-header flag", &|o| {
            if target.is_elf() {
                o[48] |= 0x01;
            } else {
                o[26] |= 0x80;
            }
        });
        // The file name where the program may write.
        refused("the file name in writable memory", &|o| {
            if target.is_elf() {
                or_section_flags(o, RUNG_LOCATION_FILE, 0x1);
            } else {
                let header = section_header_of(o, RUNG_LOCATION_FILE);
                o[header..header + 32]
                    .copy_from_slice(b"__data\0\0\0\0\0\0\0\0\0\0__DATA\0\0\0\0\0\0\0\0\0\0");
            }
        });
    }
}

/// Link `inputs` (C sources and objects) with the system `cc` into
/// `dir/name`, run it, and return its standard output; the program must exit
/// with status 101.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn cc_link_and_run(dir: &std::path::Path, name: &str, inputs: &[&str]) -> String {
    use std::process::Command;
    let binary = dir.join(name);
    let link = Command::new("cc")
        .args(inputs.iter().map(|input| dir.join(input)))
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the system cc");
    assert!(link.status.success(), "{name}: cc failed: {link:?}");
    let out = Command::new(&binary).output().expect("run the linked binary");
    assert_eq!(out.status.code(), Some(101), "{name}: {out:?}");
    String::from_utf8_lossy(&out.stdout).trim_end().to_string()
}

/// The evidence behind the admission's rule that NO WEAK DEFINITION shares the
/// target's section (`src/compiled_object/pointer_record_tests.rs`,
/// `a_weak_definition_in_the_records_or_the_targets_section_is_refused`),
/// LINKED AND RUN on this host (measured 2026-11-11, Apple ld-27037.1). An
/// assembled object holds, in `__TEXT,__const`, the weak definition `_w` and
/// after it the local `_xfile` ("src/x.rs"), and in `__DATA,__const` a record
/// whose pointer is one `ARM64_RELOC_UNSIGNED` against `_xfile`: the shape the
/// admission binds, a local non-weak target in an ordinary read-only section.
/// A second object defines `_w` strongly. As assembled, the program reads
/// "src/x.rs" through the record. With `.alt_entry _xfile`, which sets
/// `N_ALT_ENTRY` in the symbol's `n_desc` (a bit the reader does not read;
/// setting that bit alone in the assembled object's symbol table was measured
/// by hand to give the same result), `_xfile` starts no piece of its own: the
/// linker drops it with the overridden weak definition and the same record
/// leads into the OTHER object's bytes ("strong-t", measured). The reader's
/// rule does not depend on that bit: it refuses a target that shares its
/// section with any weak definition (the unit test named above).
/// FAILS if this linker stops moving an alt-entry symbol with an overridden
/// weak definition (the rule is then owed to other linkers alone), or if a
/// plain local target after a weak definition stops reading its own bytes.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn the_system_linker_moves_an_alt_entry_target_with_an_overridden_weak_definition() {
    const RECORD: &str = r#"
    .section __TEXT,__const
    .globl _w
    .weak_definition _w
_w: .ascii "WEAKWEAK"
    ALT_ENTRY
_xfile: .asciz "src/x.rs"
    .section __DATA,__const
    .p2align 3
    .globl _loc
_loc: .quad _xfile
    .subsections_via_symbols
"#;
    const STRONG: &str = "const char w[24] = \"STRONG!!strong-tail-----\";\n";
    const DRIVER: &str = r#"
#include <stdio.h>
#include <unistd.h>
extern const char *const loc;
int main(void) { printf("%.8s\n", loc); fflush(stdout); _exit(101); }
"#;
    let dir = tempfile::tempdir().expect("the test's temp dir");
    let write = |name: &str, text: &str| {
        std::fs::write(dir.path().join(name), text).expect("write a source");
    };
    write("plain.s", &RECORD.replace("ALT_ENTRY", ""));
    write("alt.s", &RECORD.replace("ALT_ENTRY", ".alt_entry _xfile"));
    write("strong.c", STRONG);
    write("driver.c", DRIVER);
    for order in [["driver.c", "strong.c", "plain.s"], ["driver.c", "plain.s", "strong.c"]] {
        assert_eq!(cc_link_and_run(dir.path(), "plain", &order), "src/x.rs", "{order:?}");
    }
    for order in [["driver.c", "strong.c", "alt.s"], ["driver.c", "alt.s", "strong.c"]] {
        let read = cc_link_and_run(dir.path(), "alt", &order);
        assert_ne!(read, "src/x.rs", "{order:?}: the alt-entry target kept its own bytes");
    }
}

/// PKG-CP: the shipped object's record under BOTH settings of the Mach-O
/// header flag `MH_SUBSECTIONS_VIA_SYMBOLS`, LINKED AND RUN on this host
/// (measured 2026-11-11, Apple ld-27037.1). The reader admits a record under
/// either setting and under no other header flag. trust-cg sets exactly that
/// one flag (asserted here), which lets the linker cut every section at its
/// symbols and move the pieces; with it clear a section stays whole. The
/// Darwin object
/// [`string_pieces_module`] ships under allow-unknown, linked beside a C file
/// with string literals of its own, reads `M_cg`'s image of the file name
/// through the record either way: the admitted pointer stays inside its own
/// target's piece (`0 <= addend < len`), in a section that is not merged by
/// content and holds no weak definition.
/// FAILS if trust-cg sets another header flag, or if this linker stops
/// resolving the record's pointer to the file name under either setting.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn the_system_linker_keeps_the_record_pointer_with_and_without_subsections_via_symbols() {
    const MH_SUBSECTIONS_VIA_SYMBOLS: u32 = 0x2000;
    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
struct location { const unsigned char *file; uint64_t len; uint32_t line; uint32_t col; };
extern uint64_t rung(uint64_t);
void panic_const_add_overflow(const struct location *loc) {
    for (uint64_t i = 0; i < loc->len; i++) printf("%02x", loc->file[i]);
    printf("\n");
    fflush(stdout);
    _exit(101);
}
int main(void) { return (int)rung(UINT64_MAX); }
"#;
    const OTHER: &str = "const char *other1 = \"cd\"; const char *other2 = \"ab\";\n";
    let case = Case::new(string_pieces_module(DARWIN_T));
    let cfg = config(DARWIN_T, F1OptLevel::O2, RelocationModel::Static);
    let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "the located rung");
    let flags = u32::from_le_bytes(s.object[24..28].try_into().unwrap());
    assert_eq!(flags, MH_SUBSECTIONS_VIA_SYMBOLS, "the shipped object's Mach-O header flags");
    let mut whole = s.object.clone();
    whole[24..28].copy_from_slice(&0_u32.to_le_bytes());

    let dir = tempfile::tempdir().expect("the test's temp dir");
    std::fs::write(dir.path().join("driver.c"), DRIVER).expect("write the driver");
    std::fs::write(dir.path().join("other.c"), OTHER).expect("write the other file");
    std::fs::write(dir.path().join("split.o"), &s.object).expect("write the object");
    std::fs::write(dir.path().join("whole.o"), &whole).expect("write the object");
    let image: String = STRING_PIECES.iter().map(|b| format!("{b:02x}")).collect();
    for object in ["split.o", "whole.o"] {
        let read = cc_link_and_run(dir.path(), "driver", &["other.c", "driver.c", object]);
        assert_eq!(read, image, "{object}");
    }
}

/// Give the Mach-O object `o` a SECOND `LC_SYMTAB`. The new command takes the
/// place of the object's `LC_BUILD_VERSION` (both are 24 bytes, so no file
/// offset moves) and names a copy of the symbol table, appended to the file,
/// that differs from the original in one entry: `moved` lies where `onto`
/// lies (it takes `onto`'s `n_sect` and `n_value`). The copy's command is
/// written FIRST in load-command order and the original's LAST, and both
/// tables use the original string table. No section byte, relocation record
/// or other header word changes.
fn add_a_second_symbol_table(o: &mut Vec<u8>, moved: &str, onto: &str) {
    const LC_SYMTAB: u32 = 0x2;
    const LC_BUILD_VERSION: u32 = 0x32;
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    assert!(is_macho(o), "a Mach-O object");
    let (mut symtab, mut build_version) = (None, None);
    let mut c = 32;
    for _ in 0..rd32(o, 16) {
        match (rd32(o, c), rd32(o, c + 4)) {
            (LC_SYMTAB, 24) => assert!(symtab.replace(c).is_none(), "one LC_SYMTAB to start with"),
            (LC_BUILD_VERSION, 24) => build_version = Some(c),
            _ => {}
        }
        c += rd32(o, c + 4) as usize;
    }
    let symtab = symtab.expect("the object's LC_SYMTAB");
    let build_version = build_version.expect("a 24-byte LC_BUILD_VERSION to overwrite");
    let original: [u8; 24] = o[symtab..symtab + 24].try_into().unwrap();
    let (symoff, nsyms) = (rd32(o, symtab + 8) as usize, rd32(o, symtab + 12) as usize);
    let (moved, onto) = (symbol_index(o, moved) * 16, symbol_index(o, onto) * 16);
    // nlist_64: n_strx @0, n_type @4, n_sect @5, n_desc @6, n_value @8.
    let mut copy = o[symoff..symoff + nsyms * 16].to_vec();
    copy[moved + 5] = copy[onto + 5];
    copy.copy_within(onto + 8..onto + 16, moved + 8);
    o.resize(o.len().next_multiple_of(8), 0);
    let mut second = original;
    second[8..12].copy_from_slice(&(o.len() as u32).to_le_bytes());
    o.extend_from_slice(&copy);
    let (first, last) = (symtab.min(build_version), symtab.max(build_version));
    o[first..first + 24].copy_from_slice(&second);
    o[last..last + 24].copy_from_slice(&original);
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, second
/// adjudication (2026-11-11). RED against compiled_object.rs blob f2416b8a64:
/// the reader BINDS this object.
///
/// The admission binds a record's pointer by the SYMBOL its relocation names
/// ("against the LOCAL symbol that is this object's definition ... of the
/// `M_cg` global the initializer names"), and a relocation names a symbol by
/// its index in the object's symbol table. The Mach-O parser keeps whichever
/// `LC_SYMTAB` command it reads LAST and says nothing about an earlier one
/// (`symtab = Some(..)` in `parse_macho`; the ELF parser refuses a second
/// table: "more than one ELF symbol table"). So an object with two tables
/// that give one index two different definitions satisfies every condition of
/// the admission when the last table is the honest one: which definition the
/// record's pointer leads to is then decided by which table the LINKER reads.
///
/// The object here is the one trust-cg compiles for [`located_rung_module`]
/// with a second table added by [`add_a_second_symbol_table`]: in the table
/// named FIRST, `rung_location_file` lies where the record `rung_location`
/// lies; the table named LAST is the object's own. Nothing else changes.
///
/// What linkers make of it, measured by hand on 2026-11-11 and run by no
/// test (the object written by this test's patch, `rung(u64::MAX)` called,
/// the 11 bytes behind the delivered record's pointer printed by the entry):
/// * LLD 23.1.1 (`rust-lld -flavor darwin ... -dylib -undefined
///   dynamic_lookup`, the image loaded with `dlopen` on this host) reads the
///   FIRST table: the record's pointer leads to the record itself, and the
///   entry reads the record's own first 11 bytes where `M_cg`'s image is
///   `src/rung.rs`. The unpatched object reads `src/rung.rs` the same way.
/// * Apple ld-27037.1 refuses the object: "multiple LC_SYMTAB load commands
///   found". So the system linker of this host does not link it at all.
///
/// The pin had the same last-table rule, and it stands behind every text
/// relocation's callee too; the admission is the first place a DATA pointer
/// depends on it, and the waiver row's residual (iv) does not list it.
///
/// FAILS while the reader binds an object that carries more than one
/// `LC_SYMTAB`.
#[test]
fn a_second_symbol_table_refuses_the_located_object() {
    let target = DARWIN_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    let doubled = fx.patched(|o| add_a_second_symbol_table(o, RUNG_LOCATION_FILE, RUNG_LOCATION));
    let symtabs = {
        let rd32 = |at: usize| u32::from_le_bytes(doubled.object[at..at + 4].try_into().unwrap());
        let mut c = 32;
        let mut tables = Vec::new();
        for _ in 0..rd32(16) {
            if rd32(c) == 0x2 {
                tables.push(rd32(c + 8));
            }
            c += rd32(c + 4) as usize;
        }
        tables
    };
    assert_eq!(symtabs.len(), 2, "the patched object carries two LC_SYMTAB commands");
    assert_ne!(symtabs[0], symtabs[1], "and they name two different tables");
    assert!(
        doubled.verify().is_err(),
        "BOUND: the object carries two symbol tables that put `{RUNG_LOCATION_FILE}` in two \
         different places, the reader read only the last one, and it admitted the record's \
         pointer"
    );
}

/// PKG-CP, the answer to [`a_second_symbol_table_refuses_the_located_object`]:
/// the PARSER refuses a Mach-O object that carries two `LC_SYMTAB` commands,
/// as malformed and by that name, WHICHEVER TABLE COMES LAST and even when the
/// two tables are the same bytes. That test asserts only that the object is
/// refused; this pins which refusal it is, so that it cannot pass by another
/// condition happening to refuse one arrangement.
/// FAILS if the reader binds any of the three objects, or refuses one for
/// another reason than its second symbol table.
#[test]
fn two_symbol_tables_refuse_the_located_object_in_either_order() {
    let target = DARWIN_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    // The file offsets of the object's LC_SYMTAB commands, in command order.
    let symtab_commands = |o: &[u8]| {
        let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        let mut c = 32;
        let mut commands = Vec::new();
        for _ in 0..rd32(16) {
            if rd32(c) == 0x2 {
                commands.push(c);
            }
            c += rd32(c + 4) as usize;
        }
        commands
    };
    // The altered table first and the object's own last (the adjudication's
    // object), the other way round, and the object's own table twice.
    let altered_first = |o: &mut Vec<u8>| {
        add_a_second_symbol_table(o, RUNG_LOCATION_FILE, RUNG_LOCATION);
    };
    let altered_last = |o: &mut Vec<u8>| {
        add_a_second_symbol_table(o, RUNG_LOCATION_FILE, RUNG_LOCATION);
        let [first, last] = symtab_commands(o)[..] else { panic!("two LC_SYMTAB commands") };
        let (a, b): ([u8; 24], [u8; 24]) =
            (o[first..first + 24].try_into().unwrap(), o[last..last + 24].try_into().unwrap());
        o[first..first + 24].copy_from_slice(&b);
        o[last..last + 24].copy_from_slice(&a);
    };
    let same_twice = |o: &mut Vec<u8>| {
        add_a_second_symbol_table(o, RUNG_LOCATION, RUNG_LOCATION);
    };
    let cases: [(&str, &dyn Fn(&mut Vec<u8>)); 3] = [
        ("the altered table first", &altered_first),
        ("the altered table last", &altered_last),
        ("two tables of the same bytes", &same_twice),
    ];
    for (what, patch) in cases {
        let doubled = fx.patched(patch);
        assert_eq!(symtab_commands(&doubled.object).len(), 2, "{what}: two LC_SYMTAB commands");
        let e = doubled.verify().err().unwrap_or_else(|| panic!("{what}: BOUND"));
        assert_eq!(
            (e.kind, e.reason.as_str()),
            (ObjectRefusalKind::Malformed, "more than one Mach-O symbol table (LC_SYMTAB)"),
            "{what}"
        );
    }
}

/// Move the relocation table of the section that defines `symbol` to the end
/// of the Mach-O object `o`, with one `ARM64_RELOC_ADDEND` entry (type 10, the
/// value in `r_symbolnum`, length 2, not extern, as trust-cg writes the
/// prefix record) for each of `addends` written before the section's one
/// relocation, at that relocation's `r_address`. With no addends the table
/// only moves. No section byte, symbol or other header word changes.
fn prefix_addend_entries(o: &mut Vec<u8>, symbol: &str, addends: &[i32]) {
    assert!(is_macho(o), "a Mach-O object");
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let header = section_header_of(o, symbol);
    // section_64: reloff @56, nreloc @60.
    let (reloff, nreloc) = (rd32(o, header + 56) as usize, rd32(o, header + 60));
    assert_eq!(nreloc, 1, "the section of `{symbol}` carries one relocation");
    let pointer: [u8; 8] = o[reloff..reloff + 8].try_into().unwrap();
    o.resize(o.len().next_multiple_of(8), 0);
    let table = o.len() as u32;
    for value in addends {
        o.extend_from_slice(&pointer[..4]);
        o.extend_from_slice(&((*value as u32 & 0x00ff_ffff) | 2 << 25 | 10 << 28).to_le_bytes());
    }
    o.extend_from_slice(&pointer);
    o[header + 56..header + 60].copy_from_slice(&table.to_le_bytes());
    o[header + 60..header + 64].copy_from_slice(&(addends.len() as u32 + 1).to_le_bytes());
}

/// PKG-CP, second adjudication (2026-11-11), its second problem: THE RECORD'S
/// POINTER TAKES NO `ARM64_RELOC_ADDEND` ENTRY, through the real parser on the
/// real object. On Mach-O the pointer's addend is the 8 bytes in place, which
/// the reader compares with `M_cg`'s image. Against compiled_object.rs blob
/// f2416b8a64 an `ARM64_RELOC_ADDEND` entry of value ZERO paired with the
/// pointer bound (it parsed as no entry), and so did a chain of two entries
/// whose last was zero (the later entry replaced the earlier in silence); the
/// adjudication measured that by hand and found no linker that made a
/// different pointer of it (Apple ld-27037.1 refuses both objects). The parser
/// now refuses the entry itself outside a code section, whatever its value.
/// The object is the one trust-cg compiles for [`located_rung_module`]; its
/// record's relocation table is rewritten by [`prefix_addend_entries`], and
/// with the table moved and no entry added it still binds (the control).
/// FAILS if the reader binds a record whose pointer carries an
/// `ARM64_RELOC_ADDEND` entry of any value, or stops binding the object when
/// only its relocation table's file offset changes.
#[test]
fn an_addend_entry_on_the_record_pointer_refuses_the_located_object() {
    let target = DARWIN_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    let moved = fx.patched(|o| prefix_addend_entries(o, RUNG_LOCATION, &[]));
    assert_ne!(moved.object, fx.object, "the control moved nothing");
    moved.verify().unwrap_or_else(|e| panic!("control: the moved relocation table: {e}"));
    let chains: [&[i32]; 7] = [&[0], &[4], &[-1], &[0x7f_ffff], &[5, 0], &[0, 0], &[0, 5]];
    for addends in chains {
        let paired = fx.patched(|o| prefix_addend_entries(o, RUNG_LOCATION, addends));
        let e = paired.verify().err().unwrap_or_else(|| panic!("ADDEND {addends:?}: BOUND"));
        assert_eq!(
            (e.kind, e.reason.as_str()),
            (
                ObjectRefusalKind::Malformed,
                "ARM64_RELOC_ADDEND in `__DATA,__const`, which is not a code section"
            ),
            "ADDEND {addends:?}"
        );
    }
}

/// The file offset of the `Elf64_Shdr` of the one `SHT_RELA` section whose
/// `sh_info` names the section that defines `symbol` in the ELF object `o`.
fn rela_header_of(o: &[u8], symbol: &str) -> usize {
    const SHT_RELA: u32 = 4;
    assert!(!is_macho(o), "an ELF object");
    let rd16 = |at: usize| usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()));
    let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
    // e_shentsize @58, e_shnum @60; Elf64_Shdr: sh_type @4, sh_info @44.
    let (shentsize, shnum) = (rd16(58), rd16(60));
    let relocated = (section_header_of(o, symbol) - shoff) / shentsize;
    let headers: Vec<usize> = (0..shnum)
        .map(|i| shoff + i * shentsize)
        .filter(|h| rd32(h + 4) == SHT_RELA && rd32(h + 44) as usize == relocated)
        .collect();
    let [header] = headers.as_slice() else {
        panic!("{} SHT_RELA sections for the section of `{symbol}`", headers.len())
    };
    *header
}

/// ELF `SHF_EXCLUDE`: "this section is excluded from the input to the link
/// edit of an executable or shared object".
const SHF_EXCLUDE: u64 = 0x8000_0000;

/// OR [`SHF_EXCLUDE`] into `sh_flags` (@8) of the `Elf64_Shdr` at `header`.
/// One bit of one header word changes and nothing else.
fn exclude_section(o: &mut [u8], header: usize) {
    let at = header + 8;
    let flags = u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
    assert_eq!(flags & SHF_EXCLUDE, 0, "the section is not excluded to start with");
    o[at..at + 8].copy_from_slice(&(flags | SHF_EXCLUDE).to_le_bytes());
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, third
/// adjudication (2026-11-11). RED against compiled_object.rs blob aea693b43b:
/// the reader BINDS this object.
///
/// The admission's ground is that the LINKED pointer of a record leads to the
/// bytes the reader compared for its target, and on ELF the pointer exists
/// only as an entry of a relocation section (the record's 8 bytes in place are
/// zero; `r_addend` carries the addend). The reader constrains the header
/// words of the record's section and of the target's (`ordinary_data` in
/// compiled_object.rs), but of the RELOCATION section it reads only the type,
/// the entry size, `sh_info` and that `SHF_ALLOC` is clear (`parse_elf`:
/// `SHT_SYMTAB | SHT_STRTAB | SHT_RELA if !alloc => Structural`). Every other
/// `sh_flags` bit of a relocation section is accepted unread.
///
/// The object here is the one trust-cg compiles for [`located_rung_module`]
/// (Linux, O2) with ONE BIT changed: `SHF_EXCLUDE` set in the header of
/// `.rela.data.rel.ro`, the section that holds the record's one relocation.
/// The reader still reads that relocation (asserted below) and admits it.
///
/// What a linker makes of it, measured by hand on 2026-11-11 and run by no
/// test (LLD is not provided by the repository): LLD 23.1.1 (`rust-lld
/// -flavor gnu --unresolved-symbols=ignore-all -e rung`, the output file read
/// and not executed) DROPS an `SHF_EXCLUDE` section before it attaches
/// relocation sections to their targets, says nothing, and links. In the
/// static image the record's first 8 bytes are then ZERO, where the unpatched
/// object's hold the address of the bytes `src/rung.rs`; under `-pie` the
/// unpatched object's image carries one `R_AARCH64_RELATIVE` for the record
/// and the patched object's carries none. So the entry receives a record
/// whose file pointer is null, where `M_cg` says it is the file name's
/// address. No GNU ld was run.
///
/// The pin reads relocation-section headers the same way, and
/// [`a_text_relocation_section_the_linker_drops_refuses_the_wrapper_object`]
/// states what that does to a certified call; the admission is the first
/// place a DATA pointer depends on it, and neither the exception block's
/// conditions (c) to (i) nor the waiver row's residual (iv) name a relocation
/// section's `sh_flags`.
///
/// FAILS while the reader binds a record whose relocation lies in a
/// relocation section a linker excludes from the link.
#[test]
fn a_relocation_section_the_linker_drops_refuses_the_located_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SectionClass};
    let target = LINUX_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    let header = rela_header_of(&fx.object, RUNG_LOCATION);
    let excluded = fx.patched(|o| exclude_section(o, header));
    let changed = fx.object.iter().zip(&excluded.object).filter(|(a, b)| a != b).count();
    assert_eq!(changed, 1, "one byte of the relocation section's header changes");
    // A reader that parses the object reads the record's relocation out of
    // the section; a reader may instead refuse the object at parse.
    if let Ok(parsed) = CompiledObject::parse(&excluded.object) {
        let data_relocations: usize = parsed
            .sections
            .iter()
            .filter(|s| s.class == SectionClass::Data)
            .map(|s| s.relocations.len())
            .sum();
        assert_eq!(data_relocations, 1, "the reader reads the excluded section's relocation");
    }
    assert!(
        excluded.verify().is_err(),
        "BOUND: the record's only relocation lies in a relocation section marked SHF_EXCLUDE, \
         which LLD drops from the link (the linked record's pointer is null), and the reader \
         admitted the record's pointer"
    );
}

/// ADJUDICATION FINDING, third adjudication (2026-11-11), the same reader
/// fact as [`a_relocation_section_the_linker_drops_refuses_the_located_object`]
/// where the PIN already had it: a TEXT relocation section marked
/// `SHF_EXCLUDE`. RED against compiled_object.rs blob aea693b43b and against
/// the pin bf45acdd08 alike; it is not a defect of the admission's arm, and
/// one refusal at parse answers both tests.
///
/// The object is the one trust-cg compiles for [`wrapper_module`] (Linux, O0:
/// `f` calls the co-emitted `g` through one `bl` relocated by
/// `R_AARCH64_CALL26` against `g`) with `SHF_EXCLUDE` set in the header of
/// `.rela.text`. The gate still grades `f` with its one call site paired with
/// `g` (asserted below for the unpatched object, and the patched one binds).
///
/// Measured by hand on 2026-11-11 and run by no test: LLD 23.1.1 (`rust-lld
/// -flavor gnu -e f`) drops the section and links; the `bl` keeps its bytes
/// in place (`94000000`) and branches to ITSELF (`bl <f+0x8>` at `f+0x8`),
/// where the unpatched object links to `bl <g>`.
///
/// FAILS while the reader binds an object whose text relocations lie in a
/// relocation section a linker excludes from the link.
#[test]
fn a_text_relocation_section_the_linker_drops_refuses_the_wrapper_object() {
    let target = LINUX_T;
    let mut module = wrapper_module(Linkage::Internal);
    set_gate(&mut module, "f", None);
    set_gate(&mut module, "g", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    assert_eq!(text_relocs(&fx.object).len(), 1, "the call is the object's one text relocation");
    let header = rela_header_of(&fx.object, "f");
    let excluded = fx.patched(|o| exclude_section(o, header));
    assert!(
        excluded.verify().is_err(),
        "BOUND: the call's relocation lies in a relocation section marked SHF_EXCLUDE, which \
         LLD drops from the link (the linked `bl` branches to itself), and the gate still \
         certifies `f` as calling `g`"
    );
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, fourth
/// adjudication (2026-11-12). RED against compiled_object.rs blob aea693b43b:
/// the reader BINDS each of these objects.
///
/// [`a_relocation_section_the_linker_drops_refuses_the_located_object`]
/// states the reader fact (of a relocation section's header the reader reads
/// only the type, the entry size, `sh_info` and that `SHF_ALLOC` is clear) for
/// one flag bit and one linker. This test states it for two more header words
/// on which a GNU linker decides that a `SHT_RELA` section is NOT a
/// relocation section, so that the record's pointer stays the zero bytes in
/// place:
/// * `sh_link` naming anything but the symbol table (here the null section);
/// * `SHF_COMPRESSED` in `sh_flags`.
///
/// What a linker makes of them is READ, NOT MEASURED: no GNU ld, gold or mold
/// is installed on this host and none was run. In binutils'
/// `bfd_section_from_shdr` (bfd/elf.c, case `SHT_REL`/`SHT_RELA`) a section
/// that has `SHF_COMPRESSED`, or whose `sh_link` is `SHN_UNDEF` or is not the
/// object's one symbol table, is "presented as a normal section" and is not
/// applied as relocations. MEASURED by hand on 2026-11-12, run by no test
/// (LLD is not provided by the repository): LLD 23.1.1 (`rust-lld -flavor
/// gnu`, the output read with objdump and not executed) applies such a
/// section regardless, on a hand-written object whose `.rela.data.rel.ro` had
/// `sh_link` 0, 1 (`.strtab`) or 4 (`.rodata`), or `SHF_COMPRESSED`: the
/// record held the file name's address each time. So these two words make a
/// divergence between linkers, not one between the reader and LLD; the
/// reader's acceptance is right for one linker and wrong, by the BFD source,
/// for the other. The waiver row's residual (iv) says that `sh_link` need not
/// be read because "there is one table or none, so an index has one table to
/// name"; under BFD the word decides whether the section is a relocation
/// section at all.
///
/// FAILS while the reader binds a record whose only relocation lies in a
/// `SHT_RELA` section whose `sh_link` is not the symbol table or that carries
/// `SHF_COMPRESSED`.
#[test]
fn a_relocation_section_a_gnu_linker_does_not_apply_refuses_the_located_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SectionClass};
    /// ELF `SHF_COMPRESSED`.
    const SHF_COMPRESSED: u64 = 0x800;
    let target = LINUX_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    let header = rela_header_of(&fx.object, RUNG_LOCATION);
    let patches: Vec<(&str, Box<dyn Fn(&mut Vec<u8>)>)> = vec![
        // Elf64_Shdr: sh_link @40 (u32).
        ("sh_link 0", Box::new(move |o| o[header + 40..header + 44].fill(0))),
        (
            "SHF_COMPRESSED",
            Box::new(move |o| {
                let at = header + 8;
                let flags = u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
                o[at..at + 8].copy_from_slice(&(flags | SHF_COMPRESSED).to_le_bytes());
            }),
        ),
    ];
    let mut bound = Vec::new();
    for (what, patch) in &patches {
        let patched = fx.patched(|o| patch(o));
        assert_ne!(patched.object, fx.object, "{what}: the patch changes the object");
        // A reader that parses the object reads the section's relocation; a
        // reader may instead refuse the object at parse.
        if let Ok(parsed) = CompiledObject::parse(&patched.object) {
            let data_relocations: usize = parsed
                .sections
                .iter()
                .filter(|s| s.class == SectionClass::Data)
                .map(|s| s.relocations.len())
                .sum();
            assert_eq!(data_relocations, 1, "{what}: the reader reads the section's relocation");
        }
        if patched.verify().is_ok() {
            bound.push(*what);
        }
    }
    assert!(
        bound.is_empty(),
        "BOUND with the record's only relocation in a SHT_RELA section that a GNU linker \
         presents as a normal section (not applied): {bound:?}"
    );
}

/// MUTATION SWEEP FINDING (2026-11-13): refusal (k) when the object has NO
/// symbol table. The object [`wrapper_call`] asserts on (Linux, O0) with its
/// one `SHT_SYMTAB` header retyped `SHT_STRTAB` (a structural section the
/// reader skips), so `.rela.text`'s `sh_link` names no symbol table: binutils
/// presents such a section as a normal one and does not apply it.
///
/// FAILS while the reader reads a RELA section of an object with no symbol
/// table instead of refusing it for its `sh_link`.
#[test]
fn a_relocation_section_in_an_object_without_a_symbol_table_refuses_the_object() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    const SHT_SYMTAB: u32 = 2;
    const SHT_STRTAB: u32 = 3;
    let (fx, _) = wrapper_call(LINUX_T);
    let patched = fx.patched(|o| {
        let rd16 = |o: &[u8], at: usize| usize::from(u16::from_le_bytes([o[at], o[at + 1]]));
        let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
        let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
        // Elf64_Shdr: sh_type @4.
        let symtabs: Vec<usize> = (0..shnum)
            .map(|i| shoff + i * shentsize)
            .filter(|&h| rd32(o, h + 4) == SHT_SYMTAB)
            .collect();
        let [symtab] = symtabs[..] else { panic!("{} symbol tables", symtabs.len()) };
        o[symtab + 4..symtab + 8].copy_from_slice(&SHT_STRTAB.to_le_bytes());
    });
    let refusal = match CompiledObject::parse(&patched.object) {
        Ok(_) => panic!("BOUND: `.rela.text` read in an object with no symbol table"),
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::UnclassifiedSection, "{}", refusal.reason);
    assert!(refusal.reason.contains("which is not the symbol table"), "{}", refusal.reason);
}

/// Give the ELF object `o` a SECOND `SHT_RELA` section for the section that
/// the `SHT_RELA` section whose header is at file offset `header` relocates,
/// and move every entry into it: the original section keeps its index, name,
/// `sh_flags` (0 or `SHF_INFO_LINK`), `sh_link` (the symbol table), `sh_info`
/// and `sh_entsize`, and its `sh_size` becomes 0; a byte-for-byte copy of its
/// original header is appended to the section-header table as the new last
/// section. The table is rewritten at the end of the file (`e_shoff`,
/// `e_shnum` + 1); no section's bytes and no other header change, and every
/// section keeps its index, so the symbol table's `st_shndx` words still
/// name the same sections.
fn split_relocation_section(o: &mut Vec<u8>, header: usize) {
    let rd16 =
        |o: &[u8], at: usize| usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()));
    let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
    let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
    let original = o[header..header + shentsize].to_vec();
    let mut table = o[shoff..shoff + shnum * shentsize].to_vec();
    // Elf64_Shdr: sh_size @32. The first section holds no entries.
    let at = header - shoff + 32;
    table[at..at + 8].copy_from_slice(&0u64.to_le_bytes());
    table.extend_from_slice(&original);
    while o.len() % 8 != 0 {
        o.push(0);
    }
    let new_shoff = o.len() as u64;
    o.extend_from_slice(&table);
    o[40..48].copy_from_slice(&new_shoff.to_le_bytes());
    o[60..62].copy_from_slice(&u16::try_from(shnum + 1).unwrap().to_le_bytes());
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, fifth
/// adjudication (2026-11-12). RED against compiled_object.rs blob e3b598ce90:
/// the reader BINDS this object.
///
/// `parse_elf` collects the entries of EVERY `SHT_RELA` section onto the
/// section its `sh_info` names (`relocs_for.entry(target).or_default()
/// .extend(list)`), so an object may split one section's relocations across
/// two relocation sections. (j) and (k) read each section's `sh_flags` and
/// `sh_link`, and both sections here pass them; nothing reads how many
/// relocation sections name one target.
///
/// The object is the one trust-cg compiles for [`located_rung_module`]
/// (Linux, O2), rewritten by [`split_relocation_section`]: `.rela.data.rel.ro`
/// keeps its index and header but holds no entry, and a second `SHT_RELA`
/// section, appended last, with the same name, `sh_flags`, `sh_link` (the one
/// symbol table) and `sh_info` (`.data.rel.ro`), holds the record's one
/// `R_AARCH64_ABS64`. The reader reads that relocation (asserted below) and
/// admits the record's pointer.
///
/// What a linker makes of it:
/// * LLD REFUSES it. READ from LLD's source in this repository
///   (src/llvm-project/lld/ELF/InputFiles.cpp, `ObjFile::initializeSections`:
///   `if (s->relSecIdx != 0) ... "multiple relocation sections to one section
///   are not supported"`), and MEASURED by hand on 2026-11-12, run by no test
///   (LLD is not provided by the repository): `rust-lld -flavor gnu`
///   (LLD 23.1.1, from a rustup toolchain) refuses this object with that
///   error and links the unpatched one.
/// * A GNU linker does NOT APPLY the second section. READ, NOT MEASURED (no
///   GNU ld, gold or mold is installed on this host; binutils' source is not
///   in this repository and was read from memory, not re-read here): in
///   binutils' `bfd_section_from_shdr` (bfd/elf.c, case `SHT_REL`/`SHT_RELA`)
///   sections are visited in index order and the FIRST relocation section of
///   a target becomes its `rela.hdr`; a later one is a "secondary relocation
///   section" (`init_secondary_reloc_section`, PR 24456), which objcopy and
///   strip carry but which the ELF final link does not apply
///   (`_bfd_elf_link_read_relocs` reads only `rel.hdr` and `rela.hdr`). The
///   applied section is then the EMPTY one, and the record's 8 bytes in place,
///   which are zero on ELF, are its linked file pointer: null, where `M_cg`
///   says it is the address of `src/rung.rs`.
///
/// So this is the shape of the fourth adjudication's `sh_link`/
/// `SHF_COMPRESSED` finding: one linker refuses or applies, the other links
/// a pointer the reader did not certify. The exception block's (j) and (k)
/// and the waiver row's residual (iv) ("On ELF a relocation section's
/// sh_flags and sh_link are now read") name each section's header words, not
/// that a target has one relocation section.
///
/// FAILS while the reader binds a record whose relocation lies in the second
/// of two relocation sections for its section.
#[test]
fn a_second_relocation_section_for_one_section_refuses_the_located_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SectionClass};
    let target = LINUX_T;
    let mut module = located_rung_module(target);
    set_gate(&mut module, "rung", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    fx.verify().unwrap_or_else(|e| panic!("the unpatched object is refused: {e}"));
    let header = rela_header_of(&fx.object, RUNG_LOCATION);
    let split = fx.patched(|o| split_relocation_section(o, header));
    // A reader that parses the object reads the record's one relocation, now
    // out of the second section; a reader may instead refuse it at parse.
    if let Ok(parsed) = CompiledObject::parse(&split.object) {
        let data_relocations: usize = parsed
            .sections
            .iter()
            .filter(|s| s.class == SectionClass::Data)
            .map(|s| s.relocations.len())
            .sum();
        assert_eq!(data_relocations, 1, "the reader reads the second section's relocation");
    }
    assert!(
        split.verify().is_err(),
        "BOUND: the record's only relocation lies in a second SHT_RELA section for \
         `.data.rel.ro`, which LLD refuses and a GNU linker does not apply (the first, empty \
         section is the one it applies: the linked record's pointer is null), and the reader \
         admitted the record's pointer"
    );
}

/// ADJUDICATION FINDING, fifth adjudication (2026-11-12), the same reader
/// fact as [`a_second_relocation_section_for_one_section_refuses_the_located_object`]
/// where the PIN already had it: the call's relocation moved into a second
/// `SHT_RELA` section for `.text`. RED against compiled_object.rs blob
/// e3b598ce90 and, by reading, against the pin bf45acdd08 (its `parse_elf`
/// collects relocation sections the same way); it is not a defect of the
/// admission's arm, and one refusal at parse answers both tests.
///
/// The object is the one trust-cg compiles for [`wrapper_module`] (Linux, O0:
/// `f` calls the co-emitted `g` through one `bl` relocated by
/// `R_AARCH64_CALL26` against `g`), rewritten by
/// [`split_relocation_section`] on `.rela.text`. LLD refuses it (READ from
/// its source, as above, and measured by hand with LLD 23.1.1 on 2026-11-12,
/// run by no test). By binutils' source (read from memory, not run), a GNU
/// linker applies only the first, empty section, so the `bl` keeps its bytes
/// in place (`94000000`) and branches to itself, where the gate certifies
/// `f` as calling `g`.
///
/// FAILS while the reader binds an object whose text relocations lie in the
/// second of two relocation sections for one section.
#[test]
fn a_second_text_relocation_section_refuses_the_wrapper_object() {
    let target = LINUX_T;
    let mut module = wrapper_module(Linkage::Internal);
    set_gate(&mut module, "f", None);
    set_gate(&mut module, "g", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    assert_eq!(text_relocs(&fx.object).len(), 1, "the call is the object's one text relocation");
    let header = rela_header_of(&fx.object, "f");
    let split = fx.patched(|o| split_relocation_section(o, header));
    assert!(
        split.verify().is_err(),
        "BOUND: the call's relocation lies in a second SHT_RELA section for `.text`, which LLD \
         refuses and a GNU linker does not apply (the linked `bl` branches to itself), and the \
         gate still certifies `f` as calling `g`"
    );
}

/// ELF: the file offset of the `Elf64_Sym` of symbol `index` in `o`.
fn elf_symbol_entry(o: &[u8], index: usize) -> usize {
    const SHT_SYMTAB: u32 = 2;
    let rd16 = |at: usize| usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()));
    let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
    let (shentsize, shnum) = (rd16(58), rd16(60));
    let tables: Vec<usize> =
        (0..shnum).map(|i| shoff + i * shentsize).filter(|h| rd32(h + 4) == SHT_SYMTAB).collect();
    let [table] = tables.as_slice() else { panic!("{} symbol tables", tables.len()) };
    // Elf64_Shdr: sh_offset @24.
    u64::from_le_bytes(o[table + 24..table + 32].try_into().unwrap()) as usize + index * 24
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, sixth
/// adjudication (2026-11-12). RED against compiled_object.rs blob 2970b18206
/// and, by reading, against the pin bf45acdd08: the movement changes none of
/// the lines involved (`parse_elf`'s symbol loop, `ObjectLayout::bind`'s
/// symbol inventory, `walk_window`'s call pairing). It is not a defect of the
/// admission's arm, which checks its target symbol by INDEX
/// (`data_syms.get(&target.name).is_some_and(|s| s.index == target.index)`);
/// the call path names its callee by the NAME of whatever symbol the
/// relocation indexes.
///
/// `parse_elf` gives every `STT_FILE` symbol `SymbolKind::File`, whatever its
/// binding and whatever section it names, and `bind` skips every `File`
/// symbol (`SymbolKind::Debug | SymbolKind::Section | SymbolKind::File =>
/// continue`), so a GLOBAL `STT_FILE` symbol DEFINED in `.text` is in no
/// inventory. A linker reads it as an ordinary global definition.
///
/// The object is the one trust-cg compiles for [`external_declaration_module`]
/// (Linux, O0, gates removed: `f(x) = g(x) + 1`, `g` a bodyless External
/// declaration, one `bl` relocated by `R_AARCH64_CALL26` against the
/// undefined `g`) with ONE symbol-table entry rewritten: `g`'s `st_info`
/// becomes `STB_GLOBAL | STT_FILE`, its `st_shndx` `.text` and its `st_value`
/// `f`'s offset. The relocation is unchanged. The gate still grades `f`
/// [PROVED] with its one call site paired with the declaration `g` (asserted
/// below; the unpatched object's `f` is the same).
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test (LLD is not provided by the repository): LLD 23.1.1 (`rust-lld
/// -flavor gnu -e f`, from a rustup toolchain, the output read with objdump
/// and not executed) refuses the unpatched object (`undefined symbol: g`) and
/// LINKS the patched one, with `g` resolved to `f`: the linked `f` is `bl
/// <f>`, a call to itself, where the gate certifies a call to the external
/// `g`. No GNU linker was run.
///
/// FAILS while the reader binds an object that defines, under a symbol kind
/// the reader skips, a global the call path pairs as an undefined declaration.
#[test]
fn a_global_file_symbol_that_defines_a_declaration_refuses_the_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolKind};
    let target = LINUX_T;
    let mut module = external_declaration_module(target);
    set_gate(&mut module, "f", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    let parsed = CompiledObject::parse(&fx.object).expect("parses");
    let g = parsed.symbols.iter().find(|y| y.name == "g").expect("g");
    assert_eq!(g.kind, SymbolKind::Undefined, "`g` is undefined in the unpatched object");
    let fs = parsed.symbols.iter().find(|y| y.name == "f").expect("f");
    let (g_index, text, f_at) = (g.index, fs.section.expect("defined"), fs.value);
    let patched = fx.patched(|o| {
        let e = elf_symbol_entry(o, g_index);
        // Elf64_Sym: st_info @4 (STB_GLOBAL << 4 | STT_FILE), st_shndx @6,
        // st_value @8.
        o[e + 4] = (1 << 4) | 4;
        o[e + 6..e + 8].copy_from_slice(&u16::try_from(text).unwrap().to_le_bytes());
        o[e + 8..e + 16].copy_from_slice(&f_at.to_le_bytes());
    });
    if let Ok(report) = patched.verify() {
        let f = report.certificate("f").expect("f certified");
        panic!(
            "BOUND: `g` is a GLOBAL STT_FILE symbol defined at `f` in `.text`, which LLD \
             resolves the call to (the linked `bl` calls `f` itself), and the gate pairs the \
             call with the external declaration `g`: {:?}\n{}",
            f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
            explain(&report)
        );
    }
}

/// ADJUDICATION FINDING, sixth adjudication (2026-11-12), the same class as
/// [`a_global_file_symbol_that_defines_a_declaration_refuses_the_object`]:
/// RED against compiled_object.rs blob 2970b18206 and, by reading, against
/// the pin bf45acdd08 (the lines involved are unchanged by the movement). Not
/// a defect of the admission's arm, which refuses a relocation against a
/// section symbol.
///
/// `walk_window` names the callee of an ELF call spelled `section symbol +
/// addend` by the ADDEND alone (`local_starts.get(&(section, addend))`); it
/// never reads the section symbol's `st_value`, and neither `parse_elf` (which
/// checks only `st_value <= sh_size`) nor `bind` (which skips `Section`
/// symbols) constrains it. A linker computes S + A with S = the section's
/// address + `st_value`, for a section symbol as for any other.
///
/// The object is the one trust-cg compiles for [`wrapper_module`] (Linux, O0,
/// gates removed: `f` calls the co-emitted Internal `g` through one `bl`),
/// with the call's relocation rewritten to `.text`'s `STT_SECTION` symbol +
/// `start(g)` (the spelling `a_section_relative_call_names_a_callee_only_at_an_extent_start`
/// in tests/call_event_gate.rs certifies) and then that section symbol's
/// `st_value` set to `start(f) - start(g)`. The gate still grades `f`
/// [PROVED], its one call site paired with `g`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test (LLD is not provided by the repository): LLD 23.1.1 (`rust-lld
/// -flavor gnu -e f`, the output read with objdump and not executed) links
/// the section-symbol spelling with `st_value` 0 to `bl <g>`, the same
/// spelling with `st_value` 4 to `bl <g+0x4>`, and this object to `bl <f>`, a
/// call to itself. No GNU linker was run.
///
/// FAILS while the reader pairs a section-relative call with a callee that
/// does not account for the section symbol's value.
#[test]
fn a_section_symbol_with_a_value_refuses_the_wrapper_object() {
    let target = LINUX_T;
    let mut module = wrapper_module(Linkage::Internal);
    set_gate(&mut module, "f", None);
    set_gate(&mut module, "g", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let section_form = fx.patched(|o| {
        let (section_sym, start) = elf_section_symbol_of(o, "g");
        let call = bl_offsets(o, "f")[0];
        let (record, _, _) = reloc_at(o, call);
        set_reloc_symbol(o, record, section_sym);
        set_elf_reloc_addend(o, record, start as i64);
    });
    let report = section_form.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g", "`.text + start(g)` names `g`");
    let (g_at, f_at) = (symbol_offset(&fx.object, "g"), symbol_offset(&fx.object, "f"));
    assert!(f_at > g_at, "`f` follows `g` in `.text`");
    let valued = section_form.patched(|o| {
        let (section_sym, _) = elf_section_symbol_of(o, "g");
        let e = elf_symbol_entry(o, section_sym);
        // Elf64_Sym: st_value @8.
        o[e + 8..e + 16].copy_from_slice(&(f_at - g_at).to_le_bytes());
    });
    if let Ok(report) = valued.verify() {
        let f = report.certificate("f").expect("f certified");
        panic!(
            "BOUND: the call's relocation is `.text`'s section symbol + start(g), and that \
             symbol's st_value is start(f) - start(g), so LLD links `bl <f>` (a call to \
             itself), and the gate pairs the call with `g`: {:?}\n{}",
            f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
            explain(&report)
        );
    }
}

#[test]
fn non_aarch64_and_other_aarch64_targets_are_refused() {
    for tuple in
        ["x86_64-apple-darwin", "aarch64-unknown-linux-musl", "riscv64gc-unknown-linux-gnu"]
    {
        assert_eq!(F1Target::from_rustc_tuple(tuple), None, "{tuple}");
    }
    assert_eq!(F1Target::from_rustc_tuple("aarch64-apple-darwin"), Some(DARWIN_T));
    assert_eq!(F1Target::from_rustc_tuple("aarch64-unknown-linux-gnu"), Some(LINUX_T));
    assert!(LINUX_T.is_elf() && !DARWIN_T.is_elf());
    // Mach-O is compiled `Static` whatever rustc's model says.
    let mut c = config(DARWIN_T, F1OptLevel::O0, RelocationModel::Pic);
    assert_eq!(c.compiled_relocation(), RelocationModel::Static);
    c.target = LINUX_T;
    assert_eq!(c.compiled_relocation(), RelocationModel::Pic);
}

// ===========================================================================
// 11-12. LINUX PIC (INC5.4-PIC)
// ===========================================================================

/// Linux `Pic`: `f` calls an External/Default `g` (preemptible: External) and
/// an Internal `h` (CoEmitted); strict ships, because the closure treats an
/// External premise as closed (EXTERNAL-CALLEE).
#[test]
fn pic_external_default_callee_is_external_internal_callee_is_coemitted() {
    let mut mb = ModBuilder::new("f1_pic_calls");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.define("g", s, Linkage::External, |fb| {
        let k = fb.konst(Ty::U64, 0x33);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    let h = mb.define("h", s, Linkage::Internal, |fb| {
        let k = fb.konst(Ty::U64, 0x44);
        let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
        fb.ret(out);
    });
    mb.define("f", s, Linkage::External, |fb| {
        let a = fb.call(g, &[fb.p(0)]);
        let c = fb.call(h, &[a]);
        fb.ret(c);
    });
    let case = Case::new(licensed(mb.finish()));
    for opt in [F1OptLevel::O0, F1OptLevel::O2] {
        let cfg = never_inline(config(LINUX_T, opt, RelocationModel::Pic), &["h"]);
        let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), "pic strict");
        let c = s.report.certificate("f").expect("f");
        let mut want = vec![Assumption::External("g".into()), Assumption::CoEmitted("h".into())];
        want.sort();
        let mut got = c.assumptions.clone();
        got.sort();
        assert_eq!(got, want, "{opt:?}\n{}", explain(&s.report));
        // Control: under `Static` the same `g` binds within the image (kept a
        // call: non-preemptible there, OPT-4 would otherwise inline it at O2).
        let st = never_inline(config(LINUX_T, opt, RelocationModel::Static), &["g", "h"]);
        let s = shipped(case.run(&st, EmitPolicy::StrictProvenOnly), "static strict");
        let c = s.report.certificate("f").expect("f");
        assert!(
            c.assumptions.contains(&Assumption::CoEmitted("g".into())),
            "{opt:?}: {:?}",
            c.assumptions
        );
    }
}

fn global(name: &str, init: Option<i128>) -> Global {
    Global {
        section: None,
        visibility: Visibility::Default,
        retained: false,
        name: name.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: init.map(Constant::Int),
        linkage: Linkage::External,
        tls: None,
        align: None,
    }
}

/// Linux `Pic`: reading an External immutable global goes through the GOT,
/// whose relocations the ELF reader does not model: the function is Unknown,
/// the object is NOT refused, and allow-unknown ships it (strict refuses).
#[test]
fn pic_got_relocation_is_unknown_not_an_object_refusal() {
    let mut mb = ModBuilder::new("f1_pic_got");
    mb.m.globals.push(global("G", Some(7)));
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define("f", s, Linkage::External, |fb| {
        let p = fb.push_inst(Inst::GlobalAddr { global: GlobalId::new(0) });
        let v = fb.push_inst(Inst::Load { ty: Ty::U64, ptr: p, volatile: false, align: None });
        let out = fb.bin(BinOp::Add, Ty::U64, fb.p(0), v);
        fb.ret(out);
    });
    let case = Case::new(licensed(mb.finish()));
    for opt in [F1OptLevel::O0, F1OptLevel::O2] {
        let cfg = config(LINUX_T, opt, RelocationModel::Pic);
        let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "pic got");
        let c = s.report.certificate("f").expect("f");
        assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{}", explain(&s.report));
        assert!(
            c.obligations.o1_binding.detail.contains("unmodeled relocation kind"),
            "{opt:?}: {}",
            explain(&s.report)
        );
        let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), "pic got strict");
        assert!(matches!(e, F1Refusal::Policy(_)), "{e}");
    }
}

// ===========================================================================
// 10. DENSE SWITCHES (INC5.4-JUMPTABLE)
// ===========================================================================

/// `f(x) = match x { 0 => x ^ 0x10, 1 => x ^ 0x21, ... 5 => x ^ 0x65, _ => 9 }`:
/// six dense cases, which trust-cg lowers through a jump table.
fn dense_switch_module() -> Module {
    let mut mb = ModBuilder::new("f1_switch");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define("f", s, Linkage::External, |fb| {
        let x = fb.p(0);
        let arms: Vec<BlockId> = (0..6).map(|_| fb.block(&[]).0).collect();
        let (default, _) = fb.block(&[]);
        fb.push_inst_void(Inst::Switch {
            value: x,
            default,
            default_args: vec![],
            cases: arms
                .iter()
                .enumerate()
                .map(|(i, b)| SwitchCase {
                    value: Constant::Int(i as i128),
                    target: *b,
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        });
        for (i, b) in arms.iter().enumerate() {
            fb.switch_to(*b);
            let k = fb.konst(Ty::U64, 0x10 * (i as i128 + 1) + i as i128);
            let out = fb.bin(BinOp::Xor, Ty::U64, x, k);
            fb.ret(out);
        }
        fb.switch_to(default);
        let nine = fb.konst(Ty::U64, 9);
        fb.ret(nine);
    });
    licensed(mb.finish())
}

/// A dense switch is an Unknown FUNCTION, not a refused object: allow-unknown
/// ships it with the table named, strict refuses it. MEASURED at trust-cg
/// 7ace0c56b: the ELF `st_size` covers the table (192 bytes at O0, 160 at O2:
/// the whole extent), so Linux behaves like Darwin. FAILS before step 5.4.1
/// (and with the reader's idiom disabled) with
/// `Object(UncoveredTextByte)` on both formats.
#[test]
fn dense_switch_function_is_unknown_not_an_object_refusal() {
    let case = Case::new(dense_switch_module());
    for (target, relocation) in LEGS {
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let cfg = config(target, opt, relocation);
            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "dense switch");
            let c = s.report.certificate("f").expect("f");
            assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{}", explain(&s.report));
            let o1 = &c.obligations.o1_binding.detail;
            assert!(
                o1.contains("dense-switch jump table")
                    && o1.contains("(6 entries)")
                    && o1.contains("INC5.4-JUMPTABLE"),
                "{target:?} {relocation:?} {opt:?}: {o1}"
            );
            assert_eq!(s.unclosed, vec!["f: Unknown; blocked by []".to_string()]);
            let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), "dense switch strict");
            let F1Refusal::Policy(why) = &e else {
                panic!("{target:?}: not a policy refusal: {e}")
            };
            assert!(why.contains("f (Unknown"), "{why}");
        }
    }
}

// ===========================================================================
// 9. FRAME RECORDS (INC5.4-FRAME, critique L4)
// ===========================================================================

/// Whether `words` (one function's instructions) save the frame record and
/// point `x29` at it: `stp x29, x30, [sp, #k]!` then `mov x29, sp`, or
/// `stp x29, x30, [sp, #k]` then `add x29, sp, #k`.
fn saves_frame_record(words: &[u32]) -> bool {
    // STP (64-bit GPR pair), every field but imm7 (bits 21:15).
    const IMM7_CLEARED: u32 = 0xFFC0_7FFF;
    const FP_LR_AT_SP: u32 = (30 << 10) | (31 << 5) | 29;
    const STP_PRE_INDEX: u32 = 0xA980_0000 | FP_LR_AT_SP;
    const STP_SIGNED_OFFSET: u32 = 0xA900_0000 | FP_LR_AT_SP;
    // ADD (immediate, 64-bit) `x29, sp, #imm12`.
    let add_x29_sp = |imm12: u32| 0x9100_0000 | (imm12 << 10) | (31 << 5) | 29;
    words.iter().any(|&w| match w & IMM7_CLEARED {
        STP_PRE_INDEX => words.contains(&add_x29_sp(0)),
        STP_SIGNED_OFFSET => {
            let k = ((w >> 15) & 0x7F) * 8;
            k < 4096 && words.contains(&add_x29_sp(k))
        }
        _ => false,
    })
}

/// The default NonLeaf policy remains: a function that CALLS saves its frame
/// record on both formats. The explicit Always setting is tested separately. run-make
/// `trust-cg-f1-real-calls` measures it on Darwin through trustc; this sysroot
/// has no Linux std to drive trustc with, so this measures the SAME compile (the
/// plugin's only path to trust-cg, `compile_and_verify_trust_ir_module`) on
/// Linux ELF `Static` and `Pic` too, at every opt level, over the shipped bytes
/// of a caller whose one call is a real `bl`. FAILS if any leg's caller makes
/// its call without storing `x29, x30` and pointing `x29` at them. The Darwin
/// leg is the control that ties this reading to the run-make one.
#[test]
fn a_calling_function_saves_its_frame_record_on_both_formats() {
    let case = Case::new(wrapper_module(Linkage::Internal));
    for (target, relocation) in LEGS {
        for opt in [F1OptLevel::O0, F1OptLevel::O1, F1OptLevel::O2, F1OptLevel::O3] {
            let cfg = never_inline(config(target, opt, relocation), &["g"]);
            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "frame record");
            let c = s.report.certificate("f").expect("f certified");
            assert!(
                c.call_sites.iter().any(|site| site.kind == CallSiteKind::Direct),
                "{target:?} {relocation:?} {opt:?}: `f` makes no real call: {:?}",
                c.call_sites
            );
            let object = trust_cg_bridge::compiled_object::CompiledObject::parse(&s.object)
                .expect("the shipped object parses");
            let section = object
                .sections
                .iter()
                .find(|sec| sec.name == c.section)
                .unwrap_or_else(|| panic!("{target:?}: no section `{}`", c.section));
            let (start, end) = (c.extent.0 as usize, c.extent.1 as usize);
            let words: Vec<u32> = section.bytes[start..end]
                .chunks_exact(4)
                .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                .collect();
            assert!(
                saves_frame_record(&words),
                "{target:?} {relocation:?} {opt:?}: `f` calls without a frame record \
                 (INC5.4-FRAME):\n{}",
                disassemble(&s.object)
            );
        }
    }
    // The reader itself: a frame-record-free caller is not read as one.
    assert!(!saves_frame_record(&[0x9400_0000, 0xD65F_03C0]), "`bl; ret` has no record");
    assert!(saves_frame_record(&[0xA9BF_7BFD, 0x9100_03FD]), "`stp x29, x30, [sp, #-16]!; mov`");
    assert!(!saves_frame_record(&[0xA9BF_7BFD]), "a record x29 never points at");
}

/// The public Compiler lane propagates Always into real object generation.
/// Hand-built, explicitly licensed IR fixtures do not establish Rust refinement.
#[test]
fn force_frame_pointers_gives_leaf_and_caller_entry_records() {
    let case = Case::new(wrapper_module(Linkage::Internal));
    for (target, relocation) in LEGS {
        for opt in [F1OptLevel::O0, F1OptLevel::O3] {
            let mut cfg = never_inline(config(target, opt, relocation), &["g"]);
            for force in [false, true] {
                cfg.force_frame_pointers = force;
                let result = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), "frame pointers");
                assert_eq!(result.report.certificates.len(), 2, "complete caller/leaf denominator");
                let object =
                    trust_cg_bridge::compiled_object::CompiledObject::parse(&result.object)
                        .expect("actual shipped object");
                for certificate in &result.report.certificates {
                    let section = object
                        .sections
                        .iter()
                        .find(|section| section.name == certificate.section)
                        .expect("section");
                    let (start, end) = certificate.extent;
                    let words: Vec<u32> = section.bytes[start as usize..end as usize]
                        .chunks_exact(4)
                        .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                        .collect();
                    if force || certificate.symbol == "f" {
                        assert!(
                            saves_frame_record(if force {
                                &words[..words.len().min(4)]
                            } else {
                                &words
                            }),
                            "{target:?} {opt:?} force={force} {}: {words:08x?}",
                            certificate.symbol
                        );
                    } else {
                        assert!(!saves_frame_record(&words), "ordinary storage-free leaf control");
                    }
                }
                let retained = std::env::var_os("TRUST_F1_FRAME_OUTPUT_DIR").map(|root| {
                    let directory = std::path::PathBuf::from(root)
                        .join(format!("{target:?}-{relocation:?}-{opt:?}-force{force}"));
                    std::fs::create_dir_all(&directory).expect("owned output directory");
                    std::fs::write(directory.join("subject.o"), &result.object).unwrap();
                    std::fs::write(directory.join("report.json"), result.report.to_json()).unwrap();
                    std::fs::write(directory.join("disassembly.txt"), disassemble(&result.object))
                        .unwrap();
                    directory
                });
                #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
                let _ = &retained;
                let digest: String =
                    Sha256::digest(&result.object).iter().map(|b| format!("{b:02x}")).collect();
                assert_eq!(digest, result.report.object_sha256);
                #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                if target == DARWIN_T {
                    let directory = tempfile::tempdir().expect("owned native temporary directory");
                    let native_dir = retained.as_deref().unwrap_or(directory.path());
                    let object = native_dir.join("subject.o");
                    let source = native_dir.join("driver.c");
                    let executable = native_dir.join("driver");
                    std::fs::write(&object, &result.object).unwrap();
                    std::fs::write(
                        &source,
                        r#"
#include <stdint.h>
extern uint64_t f(uint64_t);
int main(void) {
    const uint64_t values[] = {0, 1, 255, 0x8000000000000000ULL, UINT64_MAX};
    for (unsigned i = 0; i < sizeof(values)/sizeof(values[0]); ++i) {
        uint64_t sp0, fp0, sp1, fp1;
        __asm__ volatile("mov %0, sp\nmov %1, x29" : "=r"(sp0), "=r"(fp0));
        uint64_t actual = f(values[i]);
        __asm__ volatile("mov %0, sp\nmov %1, x29" : "=r"(sp1), "=r"(fp1));
        if (actual != ((values[i] ^ 0x33ULL) + 1) || sp0 != sp1 || fp0 != fp1) return 1;
    }
    return 0;
}
"#,
                    )
                    .unwrap();
                    let linked = std::process::Command::new("cc")
                        .arg("-O0")
                        .arg("-fno-omit-frame-pointer")
                        .arg(&source)
                        .arg(&object)
                        .arg("-o")
                        .arg(&executable)
                        .output()
                        .expect("native linker");
                    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
                    assert!(
                        std::process::Command::new(&executable).status().unwrap().success(),
                        "native return/SP/FP control {opt:?} force={force}"
                    );
                }
            }
        }
    }
    let mut unlicensed = wrapper_module(Linkage::Internal);
    set_gate(&mut unlicensed, "g", None);
    let mut cfg = config(DARWIN_T, F1OptLevel::O3, RelocationModel::Static);
    cfg.force_frame_pointers = true;
    let error = refused(Case::new(unlicensed).run(&cfg, EmitPolicy::AllowUnknown), "license");
    assert!(
        census_variants(&error)
            .iter()
            .any(|(name, variant)| name == "g" && variant.contains("UnlicensedBody")),
        "forcing frames does not confer a body license: {error}"
    );
}

// ===========================================================================
// 5.6.1(a). AN EXTERNAL DECLARATION THROUGH THE CONSUMER
// (docs/design/2026-10-13-step2-inc5-step6-instance-links-plan.md §2(a))
// ===========================================================================

/// The `target_info` the rustc plugin's M_cg carries when it compiles for
/// `target` (`compiler/rustc_codegen_trust_cg/src/trust_ir_frontend/codegen_module.rs`,
/// rule 7: 8-byte pointers, little-endian, `struct_passing = unclassified`;
/// M_cg copies the producer's). One field differs: production's triple is
/// rustc's `llvm_target`, which for Apple is the unversioned LLVM spelling
/// (`arm64-apple-macosx`), while this stamps `F1Target::triple()`. Neither the
/// F1 consumer nor trust-cg's `Compiler::compile` reads the triple's text.
fn m_cg_target_info(target: F1Target) -> TargetInfo {
    TargetInfo {
        triple: target.triple().to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    }
}

/// `f(x) = g(x) + 1`, `g` a bodyless External declaration (the shape of the
/// `Linked` declarations 5.6.2 and 5.6.3 put in M_cg), with the natural P, and
/// NO `target_info`: see [`external_declaration_module`].
fn untargeted_external_declaration_module() -> Module {
    let mut mb = ModBuilder::new("f1_extern_decl");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    let g = mb.declare("g", s);
    mb.define("f", s, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(0)]);
        let one = fb.konst(Ty::U64, 1);
        let out = fb.bin(BinOp::Add, Ty::U64, r, one);
        fb.ret(out);
    });
    licensed(mb.finish())
}

/// [`untargeted_external_declaration_module`] carrying the `target_info` M_cg
/// carries for `target`. A bodyless declaration is an FFI boundary, and trust-ir
/// refuses one in a module without a `target_info` (`TargetInfoRequired`), as
/// trust-cg's ingestion admission does since WS7.3; the plugin never builds
/// such an M_cg (rule 7 refuses a producer without one), so the fixture states
/// the target each leg compiles for.
fn external_declaration_module(target: F1Target) -> Module {
    let mut m = untargeted_external_declaration_module();
    m.target_info = Some(m_cg_target_info(target));
    m
}

/// An External declaration ships under strict through the consumer on all
/// four legs at O0 and O2: `f`'s certificate pairs its one site with `g`, it
/// rests on exactly `[External(g)]`, and `g` is undefined in the shipped object.
/// FAILS if the closure stops treating `External` as closed (`closure_report`,
/// call_event.rs: `Assumption::External(_) => true`); measured, strict then
/// refuses `f ([PROVED]; blocked by [])`. It also fails if the consumer adds
/// any shipping decision beside `CerReport::ships` that refuses a declaration
/// call (the plan's second clause; not measured by a mutation).
#[test]
fn external_declaration_ships_strict_through_the_consumer() {
    for (target, relocation) in DECLARATION_LEGS {
        let case = Case::new(external_declaration_module(target));
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);
            let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            let c = s.report.certificate("f").expect("f certified");
            assert!(kernel_proved(&s.report, "f"), "{what}\n{}", explain(&s.report));
            assert_eq!(c.call_sites.len(), 1, "{what}\n{}", explain(&s.report));
            assert_eq!(c.call_sites[0].symbol, "g", "{what}");
            assert_eq!(c.call_sites[0].kind, CallSiteKind::Direct, "{what}");
            assert_eq!(c.assumptions, vec![Assumption::External("g".into())], "{what}");
            assert!(s.unclosed.is_empty(), "{what}: {:?}", s.unclosed);
            assert!(s.report.certificate("g").is_none(), "{what}: `g` has a certificate");
            let object = trust_cg_bridge::compiled_object::CompiledObject::parse(&s.object)
                .expect("the shipped object parses");
            let g_syms: Vec<_> = object.symbols.iter().filter(|y| y.name == "g").collect();
            assert!(!g_syms.is_empty(), "{what}: `g` is not in the symbol table");
            assert!(
                g_syms.iter().all(|y| y.section.is_none()),
                "{what}: `g` is defined in the object: {g_syms:?}"
            );
        }
    }
}

/// NEGATIVE CONTROL for [`external_declaration_module`]'s `target_info`: the
/// same M_cg WITHOUT one ships nothing on any leg, refused by trust-ir's
/// `TargetInfoRequired` naming the declaration `g`. FAILS if the consumer, or
/// trust-cg under it, starts supplying a target for an untargeted FFI boundary
/// (the guess that refusal exists for: trust-cg LD-53), and so shows the
/// fixture's `target_info` is what the declaration tests need, not a
/// loosening.
#[test]
fn an_untargeted_external_declaration_is_refused_target_info_required() {
    let case = Case::new(untargeted_external_declaration_module());
    for (target, relocation) in DECLARATION_LEGS {
        let what = format!("{target:?} {relocation:?}");
        let cfg = config(target, F1OptLevel::O0, relocation);
        let e = refused(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
        assert!(matches!(e, F1Refusal::Census(_) | F1Refusal::Compile(_)), "{what}: {e}");
        let text = e.to_string();
        assert!(text.contains("TargetInfoRequired"), "{what}: {e}");
        assert!(text.contains("`g`"), "{what}: the refusal names the declaration: {e}");
    }
}

/// The same subject with no `placements["g"]`: P does not place the
/// callee, so `f` is Unknown (call_event.rs: "P has no placement for the
/// callee"). Strict refuses with `Policy` naming `f`; allow-unknown ships and
/// discloses `f` as unclosed.
/// FAILS if a call to a callee P does not place is graded on any other
/// placement (measured: falling back to the caller's own P proves `f`).
#[test]
fn a_declaration_without_a_placement_is_unknown_and_strict_refuses() {
    for (target, relocation) in DECLARATION_LEGS {
        let mut case = Case::new(external_declaration_module(target));
        assert!(case.placements.remove("g").is_some(), "the natural P places `g`");
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);
            let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            let F1Refusal::Policy(why) = &e else { panic!("{what}: not a policy refusal: {e}") };
            assert!(why.contains("f (Unknown; blocked by [])"), "{what}: {why}");
            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
            assert_eq!(s.unclosed, vec!["f: Unknown; blocked by []".to_string()], "{what}");
            let c = s.report.certificate("f").expect("f");
            assert!(
                c.obligations.o3_events.detail.contains("P has no placement for the callee `g`"),
                "{what}: {}",
                explain(&s.report)
            );
        }
    }
}

// ===========================================================================
// PTR.0 11-12. POINTER SLOTS THROUGH THE CONSUMER
// (docs/design/2026-10-13-step2-inc5-pointer-args-plan.md §2; the gate-level
// tests 1-10 are tests/pointer_slots.rs)
// ===========================================================================

/// `g(q: ptr, y: u64) -> ptr = q` (Internal) and `f(x: u64, p: ptr) -> ptr =
/// g(p, x)`: the pointer moves X1 -> X0 at the call and comes back out.
fn pointer_pass_through_module() -> Module {
    let mut mb = ModBuilder::new("f1_ptr_pass_through");
    let sg = mb.sig(&[Ty::Ptr, Ty::U64], Some(Ty::Ptr));
    let sf = mb.sig(&[Ty::U64, Ty::Ptr], Some(Ty::Ptr));
    let g = mb.define("g", sg, Linkage::Internal, |fb| fb.ret(fb.p(0)));
    mb.define("f", sf, Linkage::External, |fb| {
        let r = fb.call(g, &[fb.p(1), fb.p(0)]);
        fb.ret(r);
    });
    licensed(mb.finish())
}

/// PTR.0 test 11. A pointer pass-through ships under strict on every leg
/// at O0 and O2, closed on `g`'s certificate.
/// FAILS without `scalar_reg_width`'s `Ty::Ptr => 64` arm
/// (verify_output_trust_ir.rs): P places neither signature, and `f` is Unknown.
#[test]
fn a_pointer_pass_through_ships_strict_on_every_leg() {
    let case = Case::new(pointer_pass_through_module());
    for (target, relocation) in LEGS {
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = never_inline(config(target, opt, relocation), &["g"]);
            let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            assert!(kernel_proved(&s.report, "f"), "{what}\n{}", explain(&s.report));
            assert!(kernel_proved(&s.report, "g"), "{what}\n{}", explain(&s.report));
            let c = s.report.certificate("f").unwrap();
            assert_eq!(c.assumptions, vec![Assumption::CoEmitted("g".into())], "{what}");
            assert!(s.unclosed.is_empty(), "{what}: {:?}", s.unclosed);
        }
    }
}

/// PTR.0 test 12. `f(p: ptr, v: u64) -> u64 { *p = v; v }` is refused
/// under strict with `Policy` naming `f`, and ships under allow-unknown with
/// `f` disclosed as unclosed and its certificate naming why the `Store` is
/// refused. Each leg's module states the target the producer states, so the
/// `Store` reaches the source byte-memory model (af4b2d3abd), whose PTR.3b
/// frontier (`ResultMemory::missing_integration`) sends `f` to the
/// bounded-leaf route: on Linux that route has no evidence, and on Darwin its
/// joint kernel goal is declined (`cer_common::pointer_memory_refusal` pins
/// each leg's refusal). FAILS when that frontier is removed or the gate grades
/// `f` Proven (measured 2026-11-06 by its hostile review: without the frontier
/// only the refusal assertion fails, and with O5's "outside the function's
/// frame" clause removed as well, strict shipped `f` on every leg). On Darwin
/// the refusal rests on that kernel decline; a leaf grade there would be a
/// kernel proof, so this test moves with a recorded decision if the leaf
/// kernel learns to close it. Before af4b2d3abd the refusal was the spec
/// walk's catch-all.
#[test]
fn a_store_through_a_pointer_parameter_is_refused_under_strict_and_named() {
    let mut mb = ModBuilder::new("f1_ptr_store");
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
    let module = licensed(mb.finish());
    for (target, relocation) in LEGS {
        // The target M_cg states for this leg: without one the spec side refuses
        // before the memory model is reached, a refusal production never takes.
        let mut stated = module.clone();
        stated.target_info = Some(m_cg_target_info(target));
        let case = Case::new(stated);
        for opt in [F1OptLevel::O0, F1OptLevel::O2] {
            let what = format!("{target:?} {relocation:?} {opt:?}");
            let cfg = config(target, opt, relocation);
            let e = refused(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            let F1Refusal::Policy(why) = &e else { panic!("{what}: not a policy refusal: {e}") };
            assert!(why.contains("f (Unknown; blocked by [])"), "{what}: {why}");
            let s = shipped(case.run(&cfg, EmitPolicy::AllowUnknown), &what);
            assert_eq!(s.unclosed, vec!["f: Unknown; blocked by []".to_string()], "{what}");
            let c = s.report.certificate("f").expect("f");
            assert!(matches!(c.verdict, OutputVerdict::Unknown { .. }), "{what}");
            if let Err(e) = pointer_memory_refusal(c, target == DARWIN_T) {
                panic!("{what}: {e}\n{}", explain(&s.report));
            }
        }
    }
}

// ===========================================================================
// PKG-C5c: MULTIPLY THEN ADD (the AArch64 MADD shape)
// ===========================================================================

/// `rung(x) = x * mul + add` over `ty`: the trust-ir the producer emits for
/// ladder rung `s02_mul_add` (`x * 3 + 7` at u64) and for `h` of `s09_u32`
/// (`a * 7 + 3` at u32).
fn mul_then_add_const_module(ty: Ty, mul: i128, add: i128) -> Module {
    let mut mb = ModBuilder::new("f1_mul_add");
    let s = mb.sig(&[ty.clone()], Some(ty.clone()));
    mb.define("rung", s, Linkage::External, |fb| {
        let k = fb.konst(ty.clone(), mul);
        let product = fb.bin(BinOp::Mul, ty.clone(), fb.p(0), k);
        let c = fb.konst(ty.clone(), add);
        let out = fb.bin(BinOp::Add, ty.clone(), product, c);
        fb.ret(out);
    });
    licensed(mb.finish())
}

/// `rung(a, b) = a * b + a`: `h` of ladder rung `s08_two_args`.
fn mul_then_add_two_args_module() -> Module {
    let mut mb = ModBuilder::new("f1_mul_add2");
    let s = mb.sig(&u64s(2), Some(Ty::U64));
    mb.define("rung", s, Linkage::External, |fb| {
        let product = fb.bin(BinOp::Mul, Ty::U64, fb.p(0), fb.p(1));
        let out = fb.bin(BinOp::Add, Ty::U64, product, fb.p(0));
        fb.ret(out);
    });
    licensed(mb.finish())
}

/// `rung(x) = k - x * 3` or `x * 3 - k`: the Sub twin of the shape above.
fn mul_then_sub_module(k: i128, k_first: bool) -> Module {
    let mut mb = ModBuilder::new("f1_mul_sub");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    mb.define("rung", s, Linkage::External, |fb| {
        let three = fb.konst(Ty::U64, 3);
        let product = fb.bin(BinOp::Mul, Ty::U64, fb.p(0), three);
        let c = fb.konst(Ty::U64, k);
        let out = if k_first {
            fb.bin(BinOp::Sub, Ty::U64, c, product)
        } else {
            fb.bin(BinOp::Sub, Ty::U64, product, c)
        };
        fb.ret(out);
    });
    licensed(mb.finish())
}

/// PKG-C5c. The three ladder shapes that strict refused only for the MADD
/// operand order ship under strict on every leg: `x * 3 + 7` (s02_mul_add),
/// `a * 7 + 3` at u32 (`h` of s09_u32) and `a * b + a` (`h` of s08_two_args).
/// Each is kernel-[PROVED] by the structured route, whose evidence names the
/// commutation theorem the kernel checked.
/// FAILS without the Add-commutation retry in `try_o1_instantiation_discharge`:
/// each grades [VALIDATED] (the wide-multiply citation) and strict refuses it
/// with `[f1-output-gate:policy] strict: not closed-[PROVED]: rung ([VALIDATED]; blocked by [])`.
#[test]
fn mul_then_add_ships_strict_kernel_proved() {
    let cases = [
        ("x * 3 + 7 (u64)", mul_then_add_const_module(Ty::U64, 3, 7)),
        ("a * 7 + 3 (u32)", mul_then_add_const_module(Ty::U32, 7, 3)),
        ("a * b + a (u64)", mul_then_add_two_args_module()),
    ];
    for (what, module) in cases {
        let case = Case::new(module);
        for (target, relocation) in LEGS {
            let what = format!("{what} {target:?} {relocation:?}");
            let cfg = config(target, F1OptLevel::O0, relocation);
            let started = std::time::Instant::now();
            let s = shipped(case.run(&cfg, EmitPolicy::StrictProvenOnly), &what);
            // Wall time of compile + gate + kernel check, printed for the
            // record (`--nocapture`); host load decides it, so no assertion.
            eprintln!("[mul-then-add] {what}: compile+gate {:?}", started.elapsed());
            assert!(s.unclosed.is_empty(), "{what}: {:?}", s.unclosed);
            let c = s.report.certificate("rung").expect("rung certified");
            assert!(c.is_kernel_proved(), "{what}\n{}", explain(&s.report));
            let OutputVerdict::Proven {
                evidence: ProvenEvidence::KernelInstantiated { theorem, original: None },
            } = &c.verdict
            else {
                panic!("{what}: not a kernel instantiation: {:?}", c.verdict);
            };
            assert!(theorem.contains("Trust.BVC.addRecM_comm"), "{what}: {theorem}");
        }
    }
}

/// The commutation proves nothing else. The producer says `x * 3 + 8` and
/// M_cg computes `x * 3 + 7`; the producer says `x * 3 - 7` and M_cg computes
/// `7 - x * 3` (Sub at the node the retry reorders for Add). Both are Refuted
/// and refused under both policies.
#[test]
fn mul_then_add_mismatches_are_refuted_under_both_policies() {
    let pairs = [
        (
            "addend 8 specified, 7 computed",
            mul_then_add_const_module(Ty::U64, 3, 7),
            mul_then_add_const_module(Ty::U64, 3, 8),
        ),
        (
            "x * 3 - 7 specified, 7 - x * 3 computed",
            mul_then_sub_module(7, true),
            mul_then_sub_module(7, false),
        ),
    ];
    for (what, m_cg, producer) in pairs {
        let case = Case::with_producer(m_cg, producer);
        for (target, relocation) in LEGS {
            let cfg = config(target, F1OptLevel::O0, relocation);
            for policy in [EmitPolicy::StrictProvenOnly, EmitPolicy::AllowUnknown] {
                let e = refused(case.run(&cfg, policy), what);
                let F1Refusal::Policy(why) = &e else {
                    panic!("{what} {target:?}: not a policy refusal: {e}")
                };
                assert!(
                    why.contains("Refuted") && why.contains("rung"),
                    "{what} {target:?} {policy:?}: {why}"
                );
            }
        }
    }
}

/// Not an assertion: prints what trust-cg emits for the dense switch, so the
/// reader's accepted idiom can be read off the bytes. `--ignored --nocapture`.
#[test]
#[ignore]
fn dump_dense_switch_shapes() {
    // `cer_common::compile` states the fixture license (trust-cg's default with claim-less
    // bodies permitted), which does not recognize the direct-lane authority: the body goes
    // claim-less.
    let mut m = dense_switch_module();
    set_gate(&mut m, "f", None);
    for triple in BOTH {
        for opt in
            [trust_cg_codegen::pipeline::OptLevel::O0, trust_cg_codegen::pipeline::OptLevel::O2]
        {
            let obj = compile(&m, triple, opt);
            eprintln!("==== {triple} {opt:?}\n{:?}\n{}", section_names(&obj), disassemble(&obj));
            if triple == LINUX {
                let o = trust_cg_bridge::compiled_object::CompiledObject::parse(&obj).unwrap();
                for s in &o.symbols {
                    eprintln!(
                        "  sym {:?} {:?} value={:#x} size={:?}",
                        s.raw_name, s.kind, s.value, s.size
                    );
                }
            }
        }
    }
    let _ = ObjectRefusalKind::UncoveredTextByte;
}

// ===========================================================================
// SEVENTH ADJUDICATION (2026-11-12): a call named through a symbol the
// inventory never sees
// ===========================================================================
//
// `walk_window` names the callee of a relocated `bl`/`b` by the NAME of
// whatever symbol the relocation indexes (`callee: Some(s.name.clone())` for
// any symbol that is not a section symbol, at addend 0). `ObjectLayout::bind`
// inventories bodies only among the symbols it puts in `body_syms` (a code
// section's), skips `Debug`, `Section` and `File` symbols, and asks of a
// symbol defined in an unwind or structural section only that it be LOCAL. A
// linker resolves the relocation through the symbol it indexes: its section
// and value, or, for an undefined one, its raw name and binding. The tests
// below give the relocation a symbol whose NAME is the callee's and whose
// section, value, raw name or binding a linker reads differently. Each is RED
// against compiled_object.rs blob 3ac05cb1e3 and, by reading, against the pin
// bf45acdd08 (the movement changes no line of `walk_window` or of `bind`'s
// symbol inventory, and the pin took a FILE symbol of any form). None is a
// defect of the admission's arm, which checks its target symbol by INDEX.

/// ELF: insert a LOCAL symbol whose `st_name` is symbol `like`'s (so it
/// carries the same name), with `st_info` `STB_LOCAL | st_type` and the given
/// `st_shndx` and `st_value`, as the last local (at `.symtab`'s `sh_info`).
/// The table is rewritten at the end of the file with `sh_info` one larger,
/// and every relocation that names a symbol at or after the new index is
/// renumbered; nothing else changes. Returns the new symbol's index.
fn insert_elf_local_symbol(
    o: &mut Vec<u8>,
    like: usize,
    st_type: u8,
    shndx: u16,
    value: u64,
) -> usize {
    const SHT_SYMTAB: u32 = 2;
    const SHT_RELA: u32 = 4;
    let rd16 =
        |o: &[u8], at: usize| usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()));
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
    let shoff = rd64(o, 40) as usize;
    let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
    let headers: Vec<usize> = (0..shnum).map(|i| shoff + i * shentsize).collect();
    let [table] =
        headers.iter().copied().filter(|h| rd32(o, h + 4) == SHT_SYMTAB).collect::<Vec<_>>()[..]
    else {
        panic!("not one symbol table")
    };
    // Elf64_Shdr: sh_offset @24, sh_size @32, sh_info @44.
    let (offset, size) = (rd64(o, table + 24) as usize, rd64(o, table + 32) as usize);
    let at = rd32(o, table + 44) as usize;
    let mut entries: Vec<Vec<u8>> =
        (0..size / 24).map(|i| o[offset + i * 24..offset + (i + 1) * 24].to_vec()).collect();
    // Elf64_Sym: st_name @0, st_info @4, st_other @5, st_shndx @6, st_value @8, st_size @16.
    let mut new = vec![0u8; 24];
    new[0..4].copy_from_slice(&entries[like][0..4]);
    new[4] = st_type;
    new[6..8].copy_from_slice(&shndx.to_le_bytes());
    new[8..16].copy_from_slice(&value.to_le_bytes());
    entries.insert(at, new);
    let relas: Vec<usize> =
        headers.iter().copied().filter(|&h| rd32(o, h + 4) == SHT_RELA).collect();
    for h in relas {
        let (ro, rs) = (rd64(o, h + 24) as usize, rd64(o, h + 32) as usize);
        for e in (ro..ro + rs).step_by(24) {
            // Elf64_Rela: r_info @8, the symbol in its high 32 bits.
            let info = rd64(o, e + 8);
            if (info >> 32) as usize >= at {
                o[e + 8..e + 16].copy_from_slice(&(info + (1 << 32)).to_le_bytes());
            }
        }
    }
    while o.len() % 8 != 0 {
        o.push(0);
    }
    let moved = o.len() as u64;
    o.extend(entries.concat());
    o[table + 24..table + 32].copy_from_slice(&moved.to_le_bytes());
    o[table + 32..table + 40].copy_from_slice(&(size as u64 + 24).to_le_bytes());
    o[table + 44..table + 48].copy_from_slice(&(at as u32 + 1).to_le_bytes());
    at
}

/// The object trust-cg compiles for [`wrapper_module`] (O0, gates removed: `f`
/// calls the co-emitted Internal `g` through one relocated `bl`), the gate's
/// report on it asserted (`f` [PROVED], its one site paired with `g`, through
/// a relocation that names `g`'s own symbol), and that relocation's record.
fn wrapper_call(target: F1Target) -> (Fixture, usize) {
    let mut module = wrapper_module(Linkage::Internal);
    set_gate(&mut module, "f", None);
    set_gate(&mut module, "g", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.grade.to_string(), "[PROVED]", "{}", explain(&report));
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    let (record, _, sym) = reloc_at(&fx.object, bl_offsets(&fx.object, "f")[0]);
    assert_eq!(sym, symbol_index(&fx.object, "g"), "the call names `g`'s own symbol");
    (fx, record)
}

/// Panic if `fx` binds with `f`'s call paired with `g`: `why` says what a
/// linker links instead.
fn assert_call_not_paired_with_g(fx: &Fixture, why: &str) {
    if let Ok(report) = fx.verify() {
        let f = report.certificate("f").expect("f certified");
        panic!(
            "BOUND: {why}; the gate grades `f` {} with its call sites paired with {:?}\n{}",
            f.grade,
            f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
            explain(&report)
        );
    }
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, seventh
/// adjudication (2026-11-12): the sixth adjudication's class is not closed by
/// refusal (m). (m) gives an ELF `STT_FILE` symbol the one form the gABI
/// gives it (LOCAL, in `SHN_ABS`), but a FILE symbol of that form is still in
/// no inventory (`bind` skips `File`), and `walk_window` still names a call
/// through it by its NAME. A linker resolves a relocation against an absolute
/// symbol to its `st_value`.
///
/// The object is the one [`wrapper_call`] asserts on (Linux, O0) with ONE
/// symbol added, a LOCAL `STT_FILE` symbol in `SHN_ABS`, `st_value` 0, whose
/// `st_name` is `g`'s (the form (m) admits; asserted below to parse as a
/// `File` symbol), and the call's `R_AARCH64_CALL26` retargeted to it. The
/// gate still grades `f` [PROVED] with its one site paired with `g`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test (LLD is not provided by the repository): LLD 23.1.1 and LLD 22.1.6
/// (`rust-lld -flavor gnu -e f`, from rustup toolchains, the output read with
/// objdump and not executed) link the unpatched object's call to `bl <g>`
/// and this object's to `bl 0x0`; with the FILE symbol's `st_value` set to the
/// address the linked `f` gets (0x210184) they link `bl <f>`, a call to
/// itself. No GNU linker was run.
///
/// FAILS while the reader pairs a call through a symbol it keeps out of every
/// inventory with the body of the same name.
#[test]
fn a_local_absolute_file_symbol_named_like_the_callee_refuses_the_wrapper_object() {
    const STT_FILE: u8 = 4;
    const SHN_ABS: u16 = 0xfff1;
    let (fx, record) = wrapper_call(LINUX_T);
    let g = symbol_index(&fx.object, "g");
    let mut file = 0;
    let patched = fx.patched(|o| {
        file = insert_elf_local_symbol(o, g, STT_FILE, SHN_ABS, 0);
        set_reloc_symbol(o, record, file);
    });
    let parsed = trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object)
        .expect("a LOCAL FILE symbol in SHN_ABS is the form refusal (m) admits");
    let symbol = &parsed.symbols[file];
    assert_eq!(
        (symbol.name.as_str(), symbol.kind, symbol.section),
        ("g", trust_cg_bridge::compiled_object::SymbolKind::File, None)
    );
    assert_call_not_paired_with_g(
        &patched,
        "the call's relocation names a LOCAL absolute STT_FILE symbol called `g` at value 0, \
         which LLD links as `bl 0x0`",
    );
}

/// Refusal (p), named by the twenty-second adjudication (2026-11-13), which
/// found no test reaching it. A body symbol that starts at its code section's
/// end has an empty extent. The pin indexed the next symbol (`syms[i + 1]`)
/// to name the overlap and panicked there; the reader refuses the object as
/// `OverlappingExtents`, naming "the section's end".
///
/// The object is the one [`wrapper_call`] asserts on (Linux, O0) with the
/// LAST body symbol's `st_value` moved to `.text`'s size and the FIRST body
/// symbol's `st_size` grown to `.text`'s size, nothing else changed: the
/// first body still starts at 0 and its whole extent is its own, so no
/// uncovered-byte refusal fires before (p).
///
/// FAILS (by panicking) while the reader indexes past the last body symbol.
#[test]
fn a_body_symbol_at_its_section_end_is_refused_as_an_empty_extent() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let (fx, _) = wrapper_call(LINUX_T);
    let parsed = CompiledObject::parse(&fx.object).expect("parses");
    let text = parsed.sections.iter().find(|s| s.name == ".text").expect(".text");
    let size = text.size;
    let (f_at, g_at) = (symbol_offset(&fx.object, "f"), symbol_offset(&fx.object, "g"));
    let (first, last) = if f_at < g_at { ("f", "g") } else { ("g", "f") };
    assert_eq!(f_at.min(g_at), 0, "the first body opens `.text`");
    let (index, first_index) = (symbol_index(&fx.object, last), symbol_index(&fx.object, first));
    let patched = fx.patched(|o| {
        // Elf64_Sym: st_value @8, st_size @16. The last body moves to the
        // section's end, and the first body's st_size grows to the whole
        // section, so its extent is all its own and nothing before (p) refuses.
        let e = elf_symbol_entry(o, index);
        o[e + 8..e + 16].copy_from_slice(&size.to_le_bytes());
        let e = elf_symbol_entry(o, first_index);
        o[e + 16..e + 24].copy_from_slice(&size.to_le_bytes());
    });
    let parsed = CompiledObject::parse(&patched.object).expect("the patched object parses");
    assert_eq!(parsed.symbols[index].value, size, "`{last}` now starts at `.text`'s end");
    let refusal = match patched.verify() {
        Ok(_) => panic!("BOUND: `{last}` starts at `.text`'s end, an empty extent"),
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::OverlappingExtents, "{}", refusal.reason);
    assert!(refusal.reason.contains("the section's end"), "{}", refusal.reason);
}

/// Refusal (o)'s kind restriction for a symbol with no section, named by the
/// twenty-second adjudication (2026-11-13), which found that widening
/// `(SymbolKind::Undefined, None)` to any kind survived every test. The only
/// symbols the parsers give no section besides undefined ones are an ELF
/// STT_FILE symbol (LOCAL, refused by the global-binding check too) and a
/// Mach-O stab (`SymbolKind::Debug`). A stab whose `n_type` carries `N_EXT`
/// reads as GLOBAL and non-weak, so only the kind keeps it from naming the
/// callee.
///
/// The object is the one [`wrapper_call`] asserts on (Darwin, O0) with ONE
/// symbol added, an `N_FUN | N_EXT` stab (`n_type` 0x25) whose `n_strx` is
/// `_g`'s, and the call's `ARM64_RELOC_BRANCH26` (external) retargeted to it.
/// No linker was run on this object; the `N_FUN` stab without `N_EXT`
/// ([`a_stab_entry_named_like_the_callee_refuses_the_wrapper_object`]) was
/// linked by hand to `bl 0x0` by LLD and refused by Apple ld.
///
/// FAILS while the reader names a callee through a global non-undefined
/// symbol with no section.
#[test]
fn an_external_stab_entry_named_like_the_callee_refuses_the_wrapper_object() {
    const N_FUN_EXT: u8 = 0x25;
    let (fx, record) = wrapper_call(DARWIN_T);
    let g = symbol_index(&fx.object, "g");
    let f_at = symbol_offset(&fx.object, "f");
    let parsed =
        trust_cg_bridge::compiled_object::CompiledObject::parse(&fx.object).expect("parses");
    let text = parsed.sections.iter().find(|s| s.name == "__TEXT,__text").expect("__text");
    let (text_ordinal, text_address) = (u8::try_from(text.index).unwrap(), text.address);
    let mut stab = 0;
    let patched = fx.patched(|o| {
        stab = insert_macho_local_symbol(o, g, N_FUN_EXT, text_ordinal, text_address + f_at);
        set_reloc_symbol(o, record, stab);
    });
    let parsed = trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object)
        .expect("the patched object parses");
    let s = &parsed.symbols[stab];
    assert_eq!(
        (s.name.as_str(), s.kind, s.section, s.binding, s.weak),
        (
            "g",
            trust_cg_bridge::compiled_object::SymbolKind::Debug,
            None,
            trust_cg_bridge::compiled_object::SymbolBinding::Global,
            false
        ),
        "an external stab reads as a global, non-weak debugging entry with no section"
    );
    assert_call_not_paired_with_g(
        &patched,
        "the call's relocation names an external N_FUN stab called `_g`",
    );
}

/// ELF: append a symbol after the last one (above `.symtab`'s `sh_info`, so
/// the binding in `st_info` must be GLOBAL or WEAK) whose `st_name` is symbol
/// `like`'s, with the given `st_info`, `st_shndx` and `st_value`. The table is
/// rewritten at the end of the file; no relocation is renumbered.
fn append_elf_symbol(o: &mut Vec<u8>, like: usize, st_info: u8, shndx: u16, value: u64) {
    const SHT_SYMTAB: u32 = 2;
    let rd16 =
        |o: &[u8], at: usize| usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()));
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
    let shoff = rd64(o, 40) as usize;
    let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
    let table = (0..shnum)
        .map(|i| shoff + i * shentsize)
        .find(|h| rd32(o, h + 4) == SHT_SYMTAB)
        .expect("one symbol table");
    // Elf64_Shdr: sh_offset @24, sh_size @32.
    let (offset, size) = (rd64(o, table + 24) as usize, rd64(o, table + 32) as usize);
    let mut entries = o[offset..offset + size].to_vec();
    // Elf64_Sym: st_name @0, st_info @4, st_other @5, st_shndx @6, st_value @8.
    let mut new = vec![0u8; 24];
    new[0..4].copy_from_slice(&o[offset + like * 24..offset + like * 24 + 4]);
    new[4] = st_info;
    new[6..8].copy_from_slice(&shndx.to_le_bytes());
    new[8..16].copy_from_slice(&value.to_le_bytes());
    entries.extend(new);
    while o.len() % 8 != 0 {
        o.push(0);
    }
    let moved = o.len() as u64;
    o.extend(entries);
    o[table + 24..table + 32].copy_from_slice(&moved.to_le_bytes());
    o[table + 32..table + 40].copy_from_slice(&(size as u64 + 24).to_le_bytes());
}

/// Refusals (m) and (n), each condition, named by the twenty-third
/// adjudication (2026-11-13), which found five of their conditions caught by
/// no test: (m)'s LOCAL and `SHN_ABS` requirements and its refusal of a FILE
/// symbol in an ordinary section, and (n)'s defined and LOCAL requirements.
/// Each object below gives the ELF parser one symbol called `g` of a form the
/// gABI does not give a FILE or SECTION symbol, and each must be refused at
/// parse as `Malformed`.
///
/// The three GLOBAL forms are added to the object trust-cg compiles for
/// [`external_declaration_module`] (Linux, O0), whose call stays relocated
/// against the undefined `g`: a linker resolves that undefined `g` to the
/// added definition. The twenty-third adjudication MEASURED BY HAND (LLD
/// 23.1.1, `rust-lld -flavor gnu -static -e f`, read with objdump and not
/// executed) that LLD links the call to `bl <f>` for the GLOBAL FILE symbol in
/// `.text` at `f`'s offset, `bl 0x1234` for the GLOBAL FILE symbol in
/// `SHN_ABS` at 0x1234, and `bl <f>` for the GLOBAL SECTION symbol in `.text`
/// (value 0, where `f` is), and that with the condition removed the reader
/// parses each and binds it with `f` [PROVED] and its call paired with `g`.
/// The two LOCAL forms (a FILE symbol in `SHN_COMMON` and an undefined
/// SECTION symbol) are inserted into the object [`wrapper_call`] asserts on
/// (Linux, O0), the call retargeted to them; no linker was run on those.
///
/// FAILS while the parser admits a FILE symbol that is not LOCAL in
/// `SHN_ABS`, or a SECTION symbol that is not LOCAL and defined.
#[test]
fn file_and_section_symbols_of_any_other_form_refuse_the_object() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    const STB_GLOBAL: u8 = 1 << 4;
    const STT_SECTION: u8 = 3;
    const STT_FILE: u8 = 4;
    const SHN_UNDEF: u16 = 0;
    const SHN_ABS: u16 = 0xfff1;
    const SHN_COMMON: u16 = 0xfff2;
    let refused = |label: &str, object: &[u8], says: &str| match CompiledObject::parse(object) {
        Ok(p) => {
            let s = p.symbols.iter().rev().find(|y| y.name == "g").expect("g");
            panic!(
                "PARSED {label}: `g` reads as {:?} in {:?}, {:?}; a linker resolves a \
                 relocation against it through its section and value, or by name if undefined",
                s.kind, s.section, s.binding
            )
        }
        Err(e) => {
            assert_eq!(e.kind, ObjectRefusalKind::Malformed, "{label}: {}", e.reason);
            assert!(e.reason.contains(says), "{label}: {}", e.reason);
        }
    };

    let target = LINUX_T;
    let mut module = external_declaration_module(target);
    set_gate(&mut module, "f", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let decl = Fixture::with_object(module, object, target.triple());
    let report = decl.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.grade.to_string(), "[PROVED]", "{}", explain(&report));
    assert_eq!(
        f.call_sites.iter().map(|c| c.symbol.as_str()).collect::<Vec<_>>(),
        ["g"],
        "the unpatched object pairs `f`'s call with the declared `g`"
    );
    let parsed = CompiledObject::parse(&decl.object).expect("parses");
    let g = parsed.symbols.iter().find(|y| y.name == "g").expect("g");
    assert_eq!(g.kind, trust_cg_bridge::compiled_object::SymbolKind::Undefined);
    let fs = parsed.symbols.iter().find(|y| y.name == "f").expect("f");
    let (text, f_at) = (u16::try_from(fs.section.expect("f is defined")).unwrap(), fs.value);
    for (label, info, shndx, value, says) in [
        // (m): a FILE symbol in an ordinary section.
        ("global FILE in .text", STB_GLOBAL | STT_FILE, text, f_at, "FILE symbol"),
        // (m): a FILE symbol in SHN_ABS that is not LOCAL.
        ("global FILE in SHN_ABS", STB_GLOBAL | STT_FILE, SHN_ABS, 0x1234, "special section"),
        // (n): a SECTION symbol that is not LOCAL.
        ("global SECTION in .text", STB_GLOBAL | STT_SECTION, text, 0, "SECTION symbol"),
    ] {
        let patched = decl.patched(|o| append_elf_symbol(o, g.index, info, shndx, value));
        refused(label, &patched.object, says);
    }

    let (fx, record) = wrapper_call(LINUX_T);
    let g = symbol_index(&fx.object, "g");
    for (label, st_type, shndx, says) in [
        // (m): a LOCAL FILE symbol in a reserved index other than SHN_ABS.
        ("local FILE in SHN_COMMON", STT_FILE, SHN_COMMON, "special section"),
        // (n): a LOCAL SECTION symbol that is undefined.
        ("local undefined SECTION", STT_SECTION, SHN_UNDEF, "SECTION symbol"),
    ] {
        let patched = fx.patched(|o| {
            let added = insert_elf_local_symbol(o, g, st_type, shndx, 0);
            set_reloc_symbol(o, record, added);
        });
        refused(label, &patched.object, says);
    }
}

/// Refusal (o)'s kind restriction for a symbol WITH a section, named by the
/// twenty-third adjudication (2026-11-13), which found that widening
/// `(SymbolKind::Function | SymbolKind::NoType, Some(section))` to any kind
/// survived every test, and that the record's argument that no parsed object
/// reaches it was false. A LOCAL ELF null symbol (index 0) with an ordinary
/// section index reads as `Undefined` whatever its type and value, except that
/// a FILE type, or a SECTION type at a nonzero value, meets (m) or (n) first (a
/// non-LOCAL one meets (bb) unless `.symtab`'s sh_info is 0),
/// and `bind`'s inventory skips it, so a LOCAL `STT_NOTYPE` null symbol given a
/// body's name, section and value reaches (o) and only the kind turns it away. (The same adjudication also reached (o) through a LOCAL
/// `STT_NOTYPE` symbol named `$x`, which the parser reads as a code mapping
/// symbol and the inventory skips.)
///
/// The object is the one [`wrapper_call`] asserts on (Linux, O0) with symbol
/// 0's `st_name`, `st_shndx` and `st_value` set to `g`'s (`st_info` LOCAL
/// `STT_NOTYPE`), and the call's `R_AARCH64_CALL26` retargeted to symbol 0.
/// The twenty-third adjudication MEASURED BY HAND that LLD 23.1.1 (`rust-lld
/// -flavor gnu -static -e f`, read with objdump and not executed) links it to
/// `bl <g>`, the body the reader would pair it with: the refusal is fail-closed
/// rather than a defence against a linker resolving elsewhere.
///
/// FAILS while the reader names a callee through a symbol with a section that
/// is neither a function nor untyped.
#[test]
fn the_null_symbol_given_the_callee_s_name_and_place_refuses_the_wrapper_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolKind};
    let (fx, record) = wrapper_call(LINUX_T);
    let g = symbol_index(&fx.object, "g");
    let patched = fx.patched(|o| {
        let eg = elf_symbol_entry(o, g);
        let e0 = elf_symbol_entry(o, 0);
        // Elf64_Sym: st_name @0, st_info @4, st_other @5, st_shndx @6, st_value @8.
        let name: [u8; 4] = o[eg..eg + 4].try_into().unwrap();
        let shndx: [u8; 2] = o[eg + 6..eg + 8].try_into().unwrap();
        let value: [u8; 8] = o[eg + 8..eg + 16].try_into().unwrap();
        o[e0..e0 + 4].copy_from_slice(&name);
        o[e0 + 4] = 0;
        o[e0 + 5] = 0;
        o[e0 + 6..e0 + 8].copy_from_slice(&shndx);
        o[e0 + 8..e0 + 16].copy_from_slice(&value);
        set_reloc_symbol(o, record, 0);
    });
    let parsed = CompiledObject::parse(&patched.object).expect("the patched object parses");
    let (s, body) = (&parsed.symbols[0], &parsed.symbols[g]);
    assert_eq!(
        (s.name.as_str(), s.kind, s.section, s.value),
        ("g", SymbolKind::Undefined, body.section, body.value),
        "symbol 0 reads as undefined, with `g`'s name, section and value"
    );
    let refusal = match patched.verify() {
        Ok(report) => {
            let f = report.certificate("f").expect("f certified");
            panic!(
                "BOUND: the call names symbol 0 (undefined, at `g`'s place); the gate grades \
                 `f` {} with its call sites paired with {:?}",
                f.grade,
                f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>()
            )
        }
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{}", refusal.reason);
    assert!(refusal.reason.contains("neither the one opening a body"), "{}", refusal.reason);
}

/// Refusal (o)'s GLOBAL condition on an undefined declaration, named by the
/// twenty-fourth adjudication (2026-11-13), which found that dropping
/// `s.binding == SymbolBinding::Global` (keeping `!s.weak`) failed no test: the
/// weak-undefined test is refused by `!s.weak` first. The objects are the ones
/// [`declaration_call`] asserts on, with the undefined `g` made LOCAL: on
/// Darwin `N_EXT` cleared in its `n_type`, on Linux its binding made LOCAL with
/// the table reordered for (bb). Each must be refused as `Malformed` by (o).
/// With the condition removed both bound, `f` [PROVED] with its call paired
/// with `g` and resting on `External(g)`.
///
/// What a linker makes of it, MEASURED BY HAND by that adjudication: LLD 23.1.1
/// (`rust-lld -flavor gnu -static`) refuses the Linux object linked with a
/// definition of `g` ("undefined symbol: g"), and Apple ld-27037.1 links the
/// Darwin one to `bl <_g>` as it does the unpatched object. No wrong-bytes link
/// was measured: the refusal is fail-closed on a symbol a linker does not
/// resolve as a strong external declaration.
///
/// FAILS while the reader names a callee through an undefined symbol that is
/// not GLOBAL.
#[test]
fn an_undefined_local_symbol_does_not_declare_the_callee() {
    for target in [DARWIN_T, LINUX_T] {
        let (fx, g) = declaration_call(target);
        let patched = fx.patched(|o| {
            if target == DARWIN_T {
                // nlist_64: n_type @4; N_EXT is bit 0.
                let e = macho_symbol_entry(o, g);
                assert_eq!(o[e + 4] & 1, 1, "`_g` is external");
                o[e + 4] &= !1;
            } else {
                elf_make_symbol_local(o, "g");
            }
        });
        let parsed = trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object)
            .expect("the patched object parses");
        let s = parsed.symbols.iter().find(|y| y.name == "g").expect("g");
        assert_eq!(
            (s.kind, s.section, s.binding, s.weak),
            (
                trust_cg_bridge::compiled_object::SymbolKind::Undefined,
                None,
                trust_cg_bridge::compiled_object::SymbolBinding::Local,
                false
            ),
            "{target:?}: `g` reads as a LOCAL, non-weak undefined symbol"
        );
        let refusal = match patched.verify() {
            Ok(report) => {
                let f = report.certificate("f").expect("f certified");
                panic!(
                    "BOUND {target:?}: the call names a LOCAL undefined `g`; the gate grades \
                     `f` {} with its call sites paired with {:?}",
                    f.grade,
                    f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>()
                )
            }
            Err(e) => e,
        };
        assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{}", refusal.reason);
        assert!(refusal.reason.contains("nor a strong external declaration"), "{}", refusal.reason);
    }
}

/// Refusal (o)'s `None` section on an undefined declaration, named by the
/// mutation sweep of 2026-11-13: widening `(SymbolKind::Undefined, None)` to
/// `(SymbolKind::Undefined, _)` failed no test, because the null-symbol test's
/// symbol 0 is LOCAL and the GLOBAL condition refuses it first. The only
/// parsed symbol that is Undefined and has a section is ELF symbol 0 with a
/// non-zero `st_shndx`. For it to be GLOBAL, `.symtab`'s `sh_info` must be 0,
/// so the table may hold no LOCAL symbol at all.
///
/// The object is the one [`declaration_call`] asserts on (Linux, O0). Every
/// LOCAL symbol but 0 is dropped, and each relocation that named one (the
/// `.eh_frame` relocations against the `.text` anchor) now names symbol 0.
/// Symbol 0 is GLOBAL `STT_NOTYPE`, has `g`'s `st_name`, and sits in `f`'s
/// section at 0 (where the anchor was). `sh_info` is set to 0 and the call's
/// `R_AARCH64_CALL26` names symbol 0. A relocation against symbol 0 is a
/// relocation against no symbol (gABI `STN_UNDEF`); no linker was run.
///
/// FAILS while the reader names a callee through an undefined symbol that has
/// a section.
#[test]
fn a_global_null_symbol_in_code_does_not_declare_the_callee() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolBinding, SymbolKind};
    const SHT_SYMTAB: u32 = 2;
    const SHT_RELA: u32 = 4;
    const STB_GLOBAL: u8 = 1 << 4;
    let (fx, g) = declaration_call(LINUX_T);
    let (record, _, sym) = reloc_at(&fx.object, bl_offsets(&fx.object, "f")[0]);
    assert_eq!(sym, g, "the call names the undefined `g`");
    let f = symbol_index(&fx.object, "f");
    let patched = fx.patched(|o| {
        let rd16 = |o: &[u8], at: usize| {
            usize::from(u16::from_le_bytes(o[at..at + 2].try_into().unwrap()))
        };
        let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
        let shoff = rd64(o, 40) as usize;
        let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
        let headers: Vec<usize> = (0..shnum).map(|i| shoff + i * shentsize).collect();
        let table = *headers.iter().find(|&&h| rd32(o, h + 4) == SHT_SYMTAB).expect("a .symtab");
        // Elf64_Shdr: sh_offset @24, sh_size @32, sh_info @44.
        let (offset, size) = (rd64(o, table + 24) as usize, rd64(o, table + 32) as usize);
        let first_global = rd32(o, table + 44) as usize;
        let entry = |k: usize| offset + k * 24;
        assert!(g >= first_global && f >= first_global, "`f` and `g` are not LOCAL");
        // Elf64_Sym: st_name @0, st_info @4, st_other @5, st_shndx @6, st_value @8.
        let mut symbols = vec![0u8; 24];
        symbols[0..4].copy_from_slice(&o[entry(g)..entry(g) + 4]);
        symbols[4] = STB_GLOBAL;
        symbols[6..8].copy_from_slice(&o[entry(f) + 6..entry(f) + 8]);
        for k in first_global..size / 24 {
            symbols.extend_from_slice(&o[entry(k)..entry(k) + 24]);
        }
        let renumbered = |k: usize| if k < first_global { 0 } else { k - first_global + 1 };
        let relas: Vec<usize> =
            headers.iter().copied().filter(|&h| rd32(o, h + 4) == SHT_RELA).collect();
        for h in relas {
            let (ro, rs) = (rd64(o, h + 24) as usize, rd64(o, h + 32) as usize);
            for e in (ro..ro + rs).step_by(24) {
                // Elf64_Rela: r_info @8, the symbol in its high 32 bits.
                let info = rd64(o, e + 8);
                let s = renumbered((info >> 32) as usize) as u64;
                o[e + 8..e + 16].copy_from_slice(&((s << 32) | (info & 0xffff_ffff)).to_le_bytes());
            }
        }
        o[offset..offset + symbols.len()].copy_from_slice(&symbols);
        o[table + 32..table + 40].copy_from_slice(&(symbols.len() as u64).to_le_bytes());
        o[table + 44..table + 48].copy_from_slice(&0u32.to_le_bytes());
        set_reloc_symbol(o, record, 0);
    });
    let parsed = CompiledObject::parse(&patched.object).expect("the patched object parses");
    let s = &parsed.symbols[0];
    assert_eq!(
        (s.name.as_str(), s.kind, s.section.is_some(), s.binding, s.weak),
        ("g", SymbolKind::Undefined, true, SymbolBinding::Global, false),
        "symbol 0 reads as a GLOBAL, non-weak undefined `g` with a section"
    );
    let refusal = match patched.verify() {
        Ok(report) => {
            let f = report.certificate("f").expect("f certified");
            panic!(
                "BOUND: the call names symbol 0 (STN_UNDEF); the gate grades `f` {} with its \
                 call sites paired with {:?}, resting on {:?}",
                f.grade,
                f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
                f.assumptions
            )
        }
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{}", refusal.reason);
    assert!(refusal.reason.contains("neither the one opening a body"), "{}", refusal.reason);
}

/// Refusal (o)'s `!s.weak` conjunct at `ObjectLayout::bind`'s public boundary,
/// named by the mutation sweep of 2026-11-13: dropping it failed no test,
/// because both parsers give a weak symbol `SymbolBinding::Weak`, so
/// `binding == Global` already excludes it for every parsed object. `bind`
/// is public and takes any `CompiledObject` (compiled_object_reader.rs builds
/// one by hand), so the conjunct is what refuses a symbol the caller marks
/// weak while leaving it GLOBAL.
///
/// The object is the one [`declaration_call`] asserts on (Linux, O0), parsed,
/// with only the undefined `g`'s `weak` set. The unedited object binds.
///
/// FAILS while the reader names a callee through an undefined symbol marked
/// weak.
#[test]
fn a_weak_marked_global_undefined_symbol_handed_to_bind_does_not_declare_the_callee() {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, ObjectExpectations, ObjectFormat, ObjectLayout, SymbolBinding, SymbolKind,
    };
    let (fx, g) = declaration_call(LINUX_T);
    let mut parsed = CompiledObject::parse(&fx.object).expect("parses");
    {
        let s = &parsed.symbols[g];
        assert_eq!(
            (s.kind, s.section, s.binding, s.weak),
            (SymbolKind::Undefined, None, SymbolBinding::Global, false)
        );
    }
    let expect = ObjectExpectations::from_module(&fx.m_cg, ObjectFormat::Elf, fx.model)
        .expect("expectations");
    ObjectLayout::bind(parsed.clone(), &expect).expect("the unedited object binds");
    parsed.symbols[g].weak = true;
    let refusal = match ObjectLayout::bind(parsed, &expect) {
        Ok(layout) => panic!(
            "BOUND: a weak-marked undefined `g` declares the callee; `f`'s sites name {:?}",
            layout.windows.get("f").map(|w| w
                .sites
                .iter()
                .map(|s| s.callee.clone())
                .collect::<Vec<_>>())
        ),
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{}", refusal.reason);
    assert!(refusal.reason.contains("neither the one opening a body"), "{}", refusal.reason);
}

/// Refusal (o)'s Mach-O name equality at `ObjectLayout::bind`'s public
/// boundary, named by the mutation sweep of 2026-11-13: weakening
/// `raw_name.strip_prefix('_') == Some(name)` to `.is_some()` failed no test,
/// because `parse_macho` derives `name` from `raw_name` by that very strip.
/// `bind` is public and takes any `CompiledObject`, so the equality is what
/// refuses an undefined symbol whose raw name a linker resolves (`_h`) is not
/// the declaration it is named as (`g`).
///
/// The object is the one [`declaration_call`] asserts on (Darwin, O0), parsed,
/// with only the undefined `g`'s `raw_name` set to `_h`. The unedited object
/// binds.
///
/// FAILS while the reader accepts any `_`-prefixed raw name for a declaration.
#[test]
fn a_mach_o_undefined_symbol_whose_raw_name_is_another_declaration_handed_to_bind_is_refused() {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, ObjectExpectations, ObjectFormat, ObjectLayout, SymbolKind,
    };
    let (fx, g) = declaration_call(DARWIN_T);
    let mut parsed = CompiledObject::parse(&fx.object).expect("parses");
    assert_eq!(
        (
            parsed.symbols[g].raw_name.as_str(),
            parsed.symbols[g].name.as_str(),
            parsed.symbols[g].kind
        ),
        ("_g", "g", SymbolKind::Undefined)
    );
    let expect = ObjectExpectations::from_module(&fx.m_cg, ObjectFormat::MachO, fx.model)
        .expect("expectations");
    ObjectLayout::bind(parsed.clone(), &expect).expect("the unedited object binds");
    parsed.symbols[g].raw_name = "_h".into();
    let refusal = match ObjectLayout::bind(parsed, &expect) {
        Ok(layout) => panic!(
            "BOUND: the raw `_h` declares `g`; `f`'s sites name {:?}",
            layout.windows.get("f").map(|w| w
                .sites
                .iter()
                .map(|s| s.callee.clone())
                .collect::<Vec<_>>())
        ),
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::Malformed, "{}", refusal.reason);
    assert!(refusal.reason.contains("neither the one opening a body"), "{}", refusal.reason);
}

/// Refusal (x) for an ELF relocation type the width table does not list,
/// named by the twenty-fourth adjudication (2026-11-13), which found that
/// reading such a type as 4 bytes (`_ => 2`) in place of 16 failed no test.
/// The leaves of [`a_relocation_wider_than_its_instruction_refuses_the_object`]
/// (Linux, O2), with one relocation in `.text` at `h1`'s `ret` (offset 8)
/// against `.text`'s section symbol, of type 580 (`R_AARCH64_AUTH_ABS64`) or
/// 281 (unassigned), neither of which the table lists. Each must be refused
/// as `UnconsumedRelocation`, reading the relocation as 16 bytes. With the
/// default narrowed to 4 bytes both bound with `h2` proved.
///
/// The mutation sweep of 2026-11-13 added a row for every boundary of the
/// table's arms: the unlisted 294, 298, 316 and 317 at the edges of its
/// ranges read as 16 bytes and refuse the same way, and the listed 32-bit
/// (258, 261, 308, 314, 315) and 16-bit (259, 262) data types read as the 4
/// and 2 bytes they write (`Relocation::length`, log2), so no type is read as
/// narrower or, for a listed one, wider than it is.
///
/// What a linker makes of it, MEASURED BY HAND by that adjudication: LLD
/// 23.1.1 `-static` refuses both (580: "AUTH_ABS64 cannot be used against
/// symbol '.text'"; 281: "unknown relocation (281)").
///
/// FAILS while the reader reads an unlisted relocation type as narrower than
/// the widest any AArch64 relocation writes, or a listed one at any width but
/// its own.
#[test]
fn an_unlisted_elf_relocation_type_in_code_reads_as_sixteen_bytes() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolKind};
    const SHT_RELA: u32 = 4;
    // (r_type, log2 of the bytes the reader says it writes): every boundary
    // of elf_relocation_length's arms, the unlisted types as 4 (16 bytes).
    for (r_type, length) in [
        (580u64, 4u8),
        (281, 4),
        (294, 4),
        (298, 4),
        (316, 4),
        (317, 4),
        (258, 2),
        (261, 2),
        (308, 2),
        (314, 2),
        (315, 2),
        (259, 1),
        (262, 1),
    ] {
        let fx = two_leaves(LINUX_T);
        let parsed = CompiledObject::parse(&fx.object).expect("the unpatched object parses");
        let h1 = parsed.symbols.iter().find(|y| y.name == "h1").expect("h1");
        let text = h1.section.expect("h1 is defined");
        let section_symbol = parsed
            .symbols
            .iter()
            .find(|y| y.kind == SymbolKind::Section && y.section == Some(text))
            .expect(".text's section symbol")
            .index as u64;
        let patched = fx.patched(|o| {
            let rd16 = |o: &[u8], at: usize| usize::from(u16::from_le_bytes([o[at], o[at + 1]]));
            let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
            let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
            let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
            let relas: Vec<usize> = (0..shnum)
                .map(|i| shoff + i * shentsize)
                .filter(|&h| rd32(o, h + 4) == SHT_RELA)
                .collect();
            let [rela] = relas[..] else { panic!("{} relocation sections", relas.len()) };
            // Elf64_Shdr: sh_offset @24, sh_size @32, sh_info @44. Elf64_Rela:
            // r_offset, r_info (symbol << 32 | type), r_addend.
            let at = u64::from_le_bytes(o[rela + 24..rela + 32].try_into().unwrap()) as usize;
            o[at..at + 8].copy_from_slice(&8u64.to_le_bytes());
            o[at + 8..at + 16].copy_from_slice(&(section_symbol << 32 | r_type).to_le_bytes());
            o[at + 16..at + 24].copy_from_slice(&0u64.to_le_bytes());
            o[rela + 32..rela + 40].copy_from_slice(&24u64.to_le_bytes());
            o[rela + 44..rela + 48].copy_from_slice(&(text as u32).to_le_bytes());
        });
        let reparsed = CompiledObject::parse(&patched.object).expect("the patched object parses");
        let read: Vec<u8> =
            reparsed.section(text).expect(".text").relocations.iter().map(|r| r.length).collect();
        assert_eq!(read, [length], "type {r_type}: log2 of the bytes it writes");
        if length < 4 {
            continue;
        }
        let refusal = match patched.verify() {
            Ok(report) => panic!(
                "BOUND: type {r_type} at `h1`'s `ret`; h2 proved: {}",
                report.certificate("h2").is_some_and(|c| c.is_kernel_proved())
            ),
            Err(e) => e,
        };
        assert_eq!(refusal.kind, ObjectRefusalKind::UnconsumedRelocation, "{}", refusal.reason);
        assert!(refusal.reason.contains("writes 16 bytes"), "type {r_type}: {}", refusal.reason);
    }
}

/// Refusal (v)'s alignment condition, named by the twenty-third adjudication
/// (2026-11-13), which found that dropping `align >= 2` from the Mach-O
/// `__TEXT,__text` classification survived every test. The object is the one
/// [`wrapper_call`] asserts on (Darwin, O0), `__text` at address 0, with its
/// `align` lowered from 2^2 to 2^1. Apple ld places a section at an address
/// congruent to its object address modulo 2^align
/// ([`a_code_section_at_an_address_off_its_instruction_alignment_refuses_the_object`]),
/// so with 2^1 nothing in the object puts the instructions on a 4-byte
/// boundary. No linker was run on this object: the reader refuses it because
/// the format gives no guarantee, not because a run misplaced it.
///
/// FAILS while the reader proves code in a Mach-O `__text` aligned below 2^2.
#[test]
fn a_mach_o_code_section_aligned_below_its_instructions_refuses_the_object() {
    let (fx, _) = wrapper_call(DARWIN_T);
    let header = section_header_of(&fx.object, "f");
    let patched = fx.patched(|o| {
        // section_64: addr @32, align @52.
        let addr = u64::from_le_bytes(o[header + 32..header + 40].try_into().unwrap());
        let align = u32::from_le_bytes(o[header + 52..header + 56].try_into().unwrap());
        assert_eq!((addr, align), (0, 2), "`__text` at address 0, aligned to 2^2");
        o[header + 52..header + 56].copy_from_slice(&1u32.to_le_bytes());
    });
    assert_no_function_of_the_section_is_proved(
        &patched,
        "`__text` is aligned to 2^1, so nothing places its instructions on a 4-byte boundary",
    );
}

/// Refusal (w)'s power-of-two condition, named by the twenty-third
/// adjudication (2026-11-13), which found that dropping
/// `s.addralign.is_power_of_two()` from the ELF code classification survived
/// every test. The leaves of
/// [`an_elf_code_section_aligned_below_its_instructions_refuses_the_object`]
/// (Linux, O2) with `.text`'s `sh_addralign` set to 12: at least 4 and a
/// multiple of 4, but not a power of two, which the gABI requires of a
/// nonzero `sh_addralign`. No linker was run on this object.
///
/// FAILS while the reader proves code in an ELF section whose alignment is not
/// a power of two.
#[test]
fn an_elf_code_section_alignment_that_is_not_a_power_of_two_refuses_the_object() {
    let fx = two_leaves(LINUX_T);
    let patched = fx.patched(|o| {
        // Elf64_Shdr: sh_addralign @48.
        let h = section_header_of(o, "h1");
        o[h + 48..h + 56].copy_from_slice(&12u64.to_le_bytes());
    });
    assert_no_function_of_the_section_is_proved(
        &patched,
        "`.text` has sh_addralign 12, which is not a power of two",
    );
}

/// ADJUDICATION FINDING, seventh adjudication (2026-11-12), the same class as
/// [`a_local_absolute_file_symbol_named_like_the_callee_refuses_the_wrapper_object`],
/// through a symbol DEFINED in a section the gate does not verify: `bind` asks
/// of a symbol defined in an unwind or structural section only that it be
/// LOCAL, and never compares its name with the bodies'.
///
/// The object is the one [`wrapper_call`] asserts on (Linux, O0) with ONE
/// symbol added, a LOCAL `STT_NOTYPE` symbol whose `st_name` is `g`'s, defined
/// in `.eh_frame` (classified `Unwind`, asserted below) at value 0, and the
/// call's `R_AARCH64_CALL26` retargeted to it. The gate still grades `f`
/// [PROVED] with its one site paired with `g`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 and LLD 22.1.6 (`rust-lld -flavor gnu -e f`, the output
/// read with objdump and not executed) link this object's call to `bl
/// 0x200120`, the first byte of the output `.eh_frame` (a CIE), where the
/// unpatched object's is `bl <g>`; the symbol typed `STT_FUNC` at value 0x18
/// links `bl 0x200138`, inside the same section. The same symbol defined in
/// the empty `.note.GNU-stack` (structural) is refused by LLD (`relocation
/// refers to a symbol in a discarded section`). The Mach-O counterparts in
/// `__LD,__compact_unwind` are refused by Apple ld-27037.1 (`B/BL out of
/// range`) and by LLD 23.1.1 `-flavor darwin` (out of range), also by hand. No
/// GNU linker was run.
///
/// FAILS while the reader pairs a call through a symbol defined outside every
/// code section with the body of the same name.
#[test]
fn a_symbol_named_like_the_callee_in_an_unwind_section_refuses_the_wrapper_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SectionClass};
    const STT_NOTYPE: u8 = 0;
    let (fx, record) = wrapper_call(LINUX_T);
    let g = symbol_index(&fx.object, "g");
    let parsed = CompiledObject::parse(&fx.object).expect("parses");
    let eh_frame = parsed
        .sections
        .iter()
        .find(|s| s.name == ".eh_frame")
        .expect("trust-cg writes .eh_frame on Linux");
    assert_eq!(eh_frame.class, SectionClass::Unwind);
    let shndx = u16::try_from(eh_frame.index).unwrap();
    let patched = fx.patched(|o| {
        let named_g = insert_elf_local_symbol(o, g, STT_NOTYPE, shndx, 0);
        set_reloc_symbol(o, record, named_g);
    });
    assert_call_not_paired_with_g(
        &patched,
        "the call's relocation names a LOCAL symbol called `g` defined at the start of \
         `.eh_frame`, which LLD links as a branch into the output `.eh_frame`",
    );
}

/// Mach-O: insert an `nlist_64` entry with `n_strx` symbol `like`'s (so it
/// carries the same name) and the given `n_type`, `n_sect` and `n_value`, as
/// the last LOCAL symbol: `LC_DYSYMTAB`'s local range grows by one and its
/// defined-external and undefined ranges move up by one. The table is
/// rewritten at the end of the file, and every external relocation that names
/// a symbol at or after the new index is renumbered; nothing else changes.
/// Returns the new symbol's index.
fn insert_macho_local_symbol(
    o: &mut Vec<u8>,
    like: usize,
    n_type: u8,
    n_sect: u8,
    n_value: u64,
) -> usize {
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let wr32 = |o: &mut [u8], at: usize, v: u32| o[at..at + 4].copy_from_slice(&v.to_le_bytes());
    let (mut symtab, mut dysymtab, mut headers) = (None, None, Vec::new());
    let mut c = 32;
    for _ in 0..rd32(o, 16) {
        match rd32(o, c) {
            0x2 => symtab = Some(c),
            0xb => dysymtab = Some(c),
            0x19 => headers.extend((0..rd32(o, c + 64) as usize).map(|i| c + 72 + i * 80)),
            _ => {}
        }
        c += rd32(o, c + 4) as usize;
    }
    let (symtab, dysymtab) = (symtab.expect("LC_SYMTAB"), dysymtab.expect("LC_DYSYMTAB"));
    // symtab_command: symoff @8, nsyms @12. dysymtab_command: ilocalsym @8,
    // nlocalsym @12, iextdefsym @16, nextdefsym @20, iundefsym @24.
    let (symoff, nsyms) = (rd32(o, symtab + 8) as usize, rd32(o, symtab + 12) as usize);
    let at = (rd32(o, dysymtab + 8) + rd32(o, dysymtab + 12)) as usize;
    let mut entries: Vec<Vec<u8>> =
        (0..nsyms).map(|i| o[symoff + i * 16..symoff + (i + 1) * 16].to_vec()).collect();
    // nlist_64: n_strx @0, n_type @4, n_sect @5, n_desc @6, n_value @8.
    let mut new = vec![0u8; 16];
    new[0..4].copy_from_slice(&entries[like][0..4]);
    new[4] = n_type;
    new[5] = n_sect;
    new[8..16].copy_from_slice(&n_value.to_le_bytes());
    entries.insert(at, new);
    for h in headers {
        // section_64: reloff @56, nreloc @60.
        let (reloff, nreloc) = (rd32(o, h + 56) as usize, rd32(o, h + 60) as usize);
        for e in (reloff..reloff + nreloc * 8).step_by(8) {
            let w1 = rd32(o, e + 4);
            let (symbol, external, kind) = (w1 & 0xff_ffff, (w1 >> 27) & 1 == 1, w1 >> 28);
            if external && kind != 10 && symbol as usize >= at {
                wr32(o, e + 4, (w1 & 0xff00_0000) | (symbol + 1));
            }
        }
    }
    while o.len() % 8 != 0 {
        o.push(0);
    }
    let moved = u32::try_from(o.len()).unwrap();
    o.extend(entries.concat());
    wr32(o, symtab + 8, moved);
    wr32(o, symtab + 12, nsyms as u32 + 1);
    for field in [12, 16, 24] {
        let v = rd32(o, dysymtab + field);
        wr32(o, dysymtab + field, v + 1);
    }
    at
}

/// ADJUDICATION FINDING, seventh adjudication (2026-11-12): the Mach-O
/// counterpart of [`a_local_absolute_file_symbol_named_like_the_callee_refuses_the_wrapper_object`].
/// `parse_macho` gives every entry with an `N_STAB` bit `SymbolKind::Debug`
/// with no section, whatever its `n_sect` and `n_value`; `bind` skips `Debug`
/// symbols, and `walk_window` names a call through one by its NAME.
///
/// The object is the one [`wrapper_call`] asserts on (Darwin, O0) with ONE
/// symbol added, an `N_FUN` stab (`n_type` 0x24) whose `n_strx` is `_g`'s,
/// `n_sect` 1 and `n_value` `f`'s address, and the call's
/// `ARM64_RELOC_BRANCH26` (external) retargeted to it. The gate still grades
/// `f` [PROVED] with its one site paired with `g`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor darwin -arch arm64 -dylib`, from a
/// rustup toolchain, the output read with objdump and not loaded) links the
/// unpatched object's call to `bl <_g>` and this object's to `bl 0x0`. Apple
/// ld-27037.1 refuses this object (`invalid r_symbolnum=1`). So one of the two
/// Mach-O linkers run links it to a call the gate did not certify.
///
/// FAILS while the reader pairs a call through a debugging entry with the
/// body of the same name.
#[test]
fn a_stab_entry_named_like_the_callee_refuses_the_wrapper_object() {
    const N_FUN: u8 = 0x24;
    let (fx, record) = wrapper_call(DARWIN_T);
    let g = symbol_index(&fx.object, "g");
    let f_at = symbol_offset(&fx.object, "f");
    let parsed =
        trust_cg_bridge::compiled_object::CompiledObject::parse(&fx.object).expect("parses");
    let text = parsed.sections.iter().find(|s| s.name == "__TEXT,__text").expect("__text");
    let (text_ordinal, text_address) = (u8::try_from(text.index).unwrap(), text.address);
    let patched = fx.patched(|o| {
        let stab = insert_macho_local_symbol(o, g, N_FUN, text_ordinal, text_address + f_at);
        set_reloc_symbol(o, record, stab);
    });
    assert_call_not_paired_with_g(
        &patched,
        "the call's relocation names an N_FUN stab called `_g`, which LLD links as `bl 0x0`",
    );
}

/// The object trust-cg compiles for [`external_declaration_module`] (O0, `f`'s
/// gate removed: `f(x) = g(x) + 1`, `g` a bodyless External declaration), the
/// gate's report on it asserted (`f`'s one site paired with `g`, resting on
/// `External(g)`), and the symbol index of the undefined `g`.
fn declaration_call(target: F1Target) -> (Fixture, usize) {
    let mut module = external_declaration_module(target);
    set_gate(&mut module, "f", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    assert_eq!(f.assumptions, vec![Assumption::External("g".into())]);
    let g = symbol_index(&fx.object, "g");
    (fx, g)
}

/// ADJUDICATION FINDING, seventh adjudication (2026-11-12): a call to an
/// external declaration resolved by a raw name other than the declaration's.
/// `parse_macho` names a symbol by its raw name with ONE leading `_` removed
/// when there is one (`strip_prefix('_').unwrap_or(&raw_name)`), so the raw
/// names `_g` and `g` both read as `g`. A linker resolves an undefined symbol
/// by its raw name, and on Mach-O the declaration `g` is the raw `_g`.
///
/// The object is the one [`declaration_call`] asserts on (Darwin, O0) with the
/// undefined symbol's `n_strx` advanced by one, so its raw name is `g` (the
/// same string table entry without its `_`; asserted below). The gate still
/// grades `f` with its one site paired with the declaration `g`, resting on
/// `External(g)`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: with a second object assembled from `_g: mov x0, #1; ret` and `g: mov
/// x0, #2; ret` (both global), Apple ld-27037.1 (`ld -e _f ... -lSystem`, the
/// output read with objdump and not run) links the unpatched object's call to
/// `bl <_g>` and this object's to `bl <g>`, the other definition.
///
/// FAILS while the reader binds an undefined symbol to the declaration whose
/// name it reads after removing a `_` the symbol does not have.
#[test]
fn an_undefined_symbol_without_the_mach_o_underscore_refuses_the_declaration_object() {
    let (fx, g) = declaration_call(DARWIN_T);
    let patched = fx.patched(|o| {
        let symoff = {
            let mut c = 32;
            let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
            while rd32(c) != 0x2 {
                c += rd32(c + 4) as usize;
            }
            rd32(c + 8) as usize
        };
        // nlist_64: n_strx @0.
        let e = symoff + g * 16;
        let strx = u32::from_le_bytes(o[e..e + 4].try_into().unwrap());
        o[e..e + 4].copy_from_slice(&(strx + 1).to_le_bytes());
    });
    let parsed =
        trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object).expect("parses");
    assert_eq!((parsed.symbols[g].raw_name.as_str(), parsed.symbols[g].name.as_str()), ("g", "g"));
    if let Ok(report) = patched.verify() {
        let f = report.certificate("f").expect("f certified");
        panic!(
            "BOUND: the call's undefined symbol is the raw `g`, which Apple ld resolves to a \
             definition of `g` and not of the declaration's `_g`, and the gate pairs it with \
             the declaration: {:?} resting on {:?}",
            f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
            f.assumptions
        );
    }
}

/// ADJUDICATION FINDING, seventh adjudication (2026-11-12): a call to an
/// external declaration through a WEAK undefined symbol. `bind` reads of an
/// undefined symbol only its name, never its binding; the certificate's
/// `External(g)` assumption is discharged at link time by the linker's
/// refusal to link a call to a `g` no input defines, and a weak reference
/// removes that refusal.
///
/// The object is the one [`declaration_call`] asserts on (Linux, O0) with the
/// undefined `g`'s binding set to `STB_WEAK`. The gate still grades `f` with
/// its one site paired with `g`, resting on `External(g)`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor gnu -e f`, the object linked alone, the
/// output read with objdump and not executed) refuses the unpatched object
/// (`undefined symbol: g`) and links this one, its call to `bl` the next
/// instruction (`bl <f+0xc>`): no call happens and `x0` is not `g`'s result.
/// Where an input defines `g`, the two link alike; that was not measured.
///
/// FAILS while the reader binds a weak undefined reference as a call to the
/// declaration.
#[test]
fn a_weak_undefined_declaration_refuses_the_object() {
    let (fx, g) = declaration_call(LINUX_T);
    let patched = fx.patched(|o| {
        let e = elf_symbol_entry(o, g);
        // Elf64_Sym: st_info @4 (STB_WEAK << 4 | its type).
        o[e + 4] = (2 << 4) | (o[e + 4] & 0xf);
    });
    let parsed =
        trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object).expect("parses");
    assert!(parsed.symbols[g].weak && parsed.symbols[g].section.is_none());
    if let Ok(report) = patched.verify() {
        let f = report.certificate("f").expect("f certified");
        panic!(
            "BOUND: the call's undefined `g` is WEAK, which LLD links with no definition as a \
             branch to the next instruction, and the gate pairs it with the declaration: {:?} \
             resting on {:?}",
            f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
            f.assumptions
        );
    }
}

// ===========================================================================
// EIGHTH ADJUDICATION (2026-11-12): what a Mach-O symbol's other words say
// ===========================================================================
//
// Refusal (o) of blob 0f8d12bf99 (`names_a_callee`) lets a relocated call
// name its callee through exactly two forms of symbol: the one that opens a
// body window, and an undefined, global, non-weak declaration. `parse_macho`
// reads of an `nlist_64` the `N_STAB`, `N_TYPE` and `N_EXT`/`N_PEXT` bits of
// `n_type`, the two weak bits of `n_desc`, and `n_value` only for an `N_SECT`
// symbol. Two words it does not read change what a Mach-O linker links a
// call against a symbol of either admitted form to: `n_value` of an `N_UNDF`
// symbol (non-zero: a COMMON symbol, a tentative definition) and the
// `N_SYMBOL_RESOLVER` bit of `n_desc` (the symbol is a resolver, ELF's
// `STT_GNU_IFUNC`, which the ELF parser refuses). Both inputs are RED against
// 0f8d12bf99 and, by reading, against the pin bf45acdd08 (the movement
// changes no line that reads an `nlist_64`'s `n_value` or `n_desc` for a
// call). Neither is a defect of the admission's arm.

/// Mach-O: the file offset of the `nlist_64` of symbol `index` in `o`.
fn macho_symbol_entry(o: &[u8], index: usize) -> usize {
    let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let mut c = 32;
    while rd32(c) != 0x2 {
        c += rd32(c + 4) as usize;
    }
    // symtab_command: symoff @8.
    rd32(c + 8) as usize + index * 16
}

/// Panic if `fx` binds with `f` proved or with a call site of `f` paired
/// with `g`: `why` says what a linker links instead. A refusal of the object,
/// or `f` left Unknown with no site paired with `g`, both pass.
fn assert_f_rests_on_no_call_to_g(fx: &Fixture, why: &str) {
    if let Ok(report) = fx.verify() {
        let f = report.certificate("f").expect("f certified");
        if f.is_kernel_proved() || f.call_sites.iter().any(|c| c.symbol == "g") {
            panic!(
                "BOUND: {why}; the gate grades `f` {} with its call sites paired with {:?}, \
                 resting on {:?}\n{}",
                f.grade,
                f.call_sites.iter().map(|c| &c.symbol).collect::<Vec<_>>(),
                f.assumptions,
                explain(&report)
            );
        }
    }
}

/// ADJUDICATION FINDING, PKG-CP location-record relocation, eighth
/// adjudication (2026-11-12): a call to an external declaration through a
/// Mach-O COMMON symbol. An `nlist_64` of type `N_UNDF | N_EXT` with a
/// non-zero `n_value` is not an undefined reference but a tentative
/// definition of `n_value` bytes (Mach-O `<mach-o/nlist.h>`: "undefined
/// symbols with a non-zero n_value are common symbols"), which a static
/// linker turns into zero-filled data in `__DATA,__common` unless a strong
/// definition in an OBJECT overrides it; a definition in a dylib does not
/// (ld64's `-commons ignore_dylibs` default). `parse_macho` reads `n_value`
/// only for an `N_SECT` symbol and gives every `N_UNDF` symbol value 0, so
/// the symbol reads as an undefined, global, non-weak declaration, the form
/// refusal (o) admits, and the call pairs with the declaration `g`, its
/// certificate resting on `External(g)`.
///
/// The object is the one [`declaration_call`] asserts on (Darwin, O0) with
/// the undefined `_g`'s `n_value` set to 8 (asserted below to parse as an
/// undefined, global, non-weak `g`). Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test, with a dylib `libg.dylib` built from `unsigned long g(unsigned long
/// x) { return x * 2; }`: Apple ld-27037.1 (`cc -dynamiclib ... -L. -lg`)
/// links the unpatched object's call to the stub of libg's `_g`, and this
/// object's to `bl <_g>` at a symbol it defines in `__DATA,__common` (`nm
/// -m`: `(__DATA,__common) external _g`); with no `-lg` it refuses the
/// unpatched object (`Undefined symbols ... "_g"`) and links this one the
/// same way. LLD 23.1.1 (`rust-lld -flavor darwin -arch arm64 -dylib ...
/// ./libg.dylib`, from a rustup toolchain) links the same two calls the same
/// two ways. Loaded with dlopen and called, the unpatched Apple ld image
/// returns f(5) = 0xb and this object's image dies of SIGBUS (exit 138),
/// branching into zero-filled data. No other linker was run.
///
/// FAILS while the reader binds a common symbol as a call to the declaration.
#[test]
fn a_common_symbol_named_like_the_declaration_refuses_the_object() {
    let (fx, g) = declaration_call(DARWIN_T);
    // 8, the size the linker was measured with, and 1, the smallest common
    // symbol (the mutation sweep of 2026-11-13 found `n_value > 1` passed with
    // 8 alone).
    for n_value in [8u64, 1] {
        let patched = fx.patched(|o| {
            // nlist_64: n_value @8.
            let e = macho_symbol_entry(o, g);
            assert_eq!(o[e + 4], 0x1, "the declaration is N_UNDF | N_EXT");
            o[e + 8..e + 16].copy_from_slice(&n_value.to_le_bytes());
        });
        // A reader that refuses the object at parse passes; one that parses it
        // must read the symbol as the form refusal (o) admits, so the call below
        // is the one the gate decides.
        if let Ok(parsed) = trust_cg_bridge::compiled_object::CompiledObject::parse(&patched.object)
        {
            let symbol = &parsed.symbols[g];
            assert_eq!(
                (symbol.name.as_str(), symbol.section, symbol.binding, symbol.weak),
                ("g", None, trust_cg_bridge::compiled_object::SymbolBinding::Global, false),
                "the common symbol reads as the form refusal (o) admits"
            );
        }
        assert_f_rests_on_no_call_to_g(
            &patched,
            &format!(
                "the call's symbol `_g` is a COMMON symbol (N_UNDF | N_EXT, n_value {n_value}), which \
             Apple ld and LLD link as a branch into zero-filled `__DATA,__common` even where a \
             dylib defines `_g`"
            ),
        );
    }
}

/// The object trust-cg compiles for [`wrapper_module`] with `g` External
/// (Darwin, O0, gates removed: `f` calls the co-emitted global `g` through
/// one relocated `bl`), the gate's report on it asserted (`f` [PROVED], its
/// one site paired with `g` through `g`'s own symbol), and `g`'s symbol index.
fn external_wrapper_call_darwin() -> (Fixture, usize) {
    let mut module = wrapper_module(Linkage::External);
    set_gate(&mut module, "f", None);
    set_gate(&mut module, "g", None);
    let object = compile(&module, DARWIN_T.triple(), trust_cg_codegen::pipeline::OptLevel::O0);
    let fx = Fixture::with_object(module, object, DARWIN_T.triple());
    let report = fx.report();
    let f = report.certificate("f").expect("f certified");
    assert_eq!(f.grade.to_string(), "[PROVED]", "{}", explain(&report));
    assert_eq!(f.call_sites.len(), 1, "{}", explain(&report));
    assert_eq!(f.call_sites[0].symbol, "g");
    let g = symbol_index(&fx.object, "g");
    let (_, _, sym) = reloc_at(&fx.object, bl_offsets(&fx.object, "f")[0]);
    assert_eq!(sym, g, "the call names `g`'s own symbol");
    (fx, g)
}

/// ADJUDICATION FINDING, eighth adjudication (2026-11-12): a call through the
/// symbol that opens a body window, when that symbol is a Mach-O RESOLVER.
/// `N_SYMBOL_RESOLVER` (0x0100 in `n_desc`, `<mach-o/nlist.h>`) marks a
/// defined external symbol as a resolver function: the static linker routes
/// every call to it through a stub and a lazy pointer whose first use calls
/// the symbol's code and then jumps to the ADDRESS IT RETURNS. It is the
/// Mach-O form of ELF `STT_GNU_IFUNC`, which `parse_elf` refuses ("unsupported
/// type 10"). `parse_macho` reads of `n_desc` only the two weak bits, so the
/// symbol is still the one that opens `g`'s body window, the form refusal (o)
/// admits, and `f`'s call pairs with the co-emitted `g` (`CoEmitted(g)`).
///
/// The object is the one [`external_wrapper_call_darwin`] asserts on (Darwin,
/// O0, `g` External and default visibility, which the reader takes as
/// non-preemptible on Mach-O) with `N_SYMBOL_RESOLVER` set in `_g`'s `n_desc`.
/// Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: Apple ld-27037.1 (`cc -dynamiclib`) links the unpatched object's
/// call to `bl <_g>` and this object's to `bl` into `__TEXT,__stubs` (`adrp
/// x16; ldr x16, [x16]; br x16`), whose lazy pointer starts at a
/// `__TEXT,__resolver_help` thunk that calls `_g` and `br`s to its result.
/// Loaded with dlopen and called, the unpatched image returns f(5) = 0x37
/// and this one dies of SIGBUS (exit 138): it jumps to the address g(5) =
/// 0x36. LLD 23.1.1 (`rust-lld -flavor darwin -dylib`) ignores the bit and
/// links `bl <_g>` for both, so one of the two Mach-O linkers run, the
/// system's, links a call the gate did not certify. With `g` Internal (a
/// local symbol) Apple ld ignores the bit too. No other linker was run.
///
/// FAILS while the reader pairs a call through a resolver symbol with the body
/// the symbol opens.
#[test]
fn a_resolver_symbol_that_opens_the_callee_refuses_the_wrapper_object() {
    const N_SYMBOL_RESOLVER: u16 = 0x0100;
    let (fx, g) = external_wrapper_call_darwin();
    let patched = fx.patched(|o| {
        // nlist_64: n_type @4, n_desc @6.
        let e = macho_symbol_entry(o, g);
        assert_eq!(o[e + 4] & 0x0f, 0x0f, "`_g` is N_SECT | N_EXT");
        let desc = u16::from_le_bytes([o[e + 6], o[e + 7]]) | N_SYMBOL_RESOLVER;
        o[e + 6..e + 8].copy_from_slice(&desc.to_le_bytes());
    });
    assert_f_rests_on_no_call_to_g(
        &patched,
        "the call's symbol `_g` carries N_SYMBOL_RESOLVER, which Apple ld links as a call \
         through a stub to the address `g` returns",
    );
}

// ===========================================================================
// NINTH ADJUDICATION (2026-11-12): what a CODE section's header and layout say
// ===========================================================================
//
// Blob 0baae449a1 reads a data section's whole header word before it admits a
// record in it (`ordinary_data`, conditions (c) and (d)), because a linker
// splits and merges a literal or merge section by content. It reads no more of
// a CODE section's header than the pin did: on Mach-O the name `__TEXT,__text`,
// an instruction attribute and that the type is not zero-fill; on ELF the name
// `.text`/`.text.*`, `SHF_ALLOC | SHF_EXECINSTR` and no `SHF_WRITE`. And it
// names an UNRELOCATED `bl`/`b` to the start of another non-preemptible extent
// as a call to that body, as the pin did, without reading the Mach-O header
// flag `MH_SUBSECTIONS_VIA_SYMBOLS` that lets a linker cut the section at
// every symbol and drop or move the pieces (the admission reads that flag only
// for a record). Three inputs follow, each kernel-proved and shipped under
// strict by the gate, each linked by a linker to code the gate did not check.
// All three are RED against 0baae449a1 and, by reading, against the pin
// bf45acdd08 (the movement changes no line of the code-section classification
// or of the unrelocated-branch arm). None is a defect of the admission's arm.

/// `h1(x) = x ^ 0x55` and `h2(x) = x ^ 0x66`, two External leaves (gates
/// removed), compiled by trust-cg for `target` at O2: on both formats one code
/// section holding `mov x1, #k; eor x0, x0, x1; ret` twice, the two `eor` and
/// the two `ret` words identical. The gate's report on it is asserted: both
/// proved by the kernel, the object shipped under strict.
fn two_leaves(target: F1Target) -> Fixture {
    let mut mb = ModBuilder::new("f1_two_leaves");
    let s = mb.sig(&u64s(1), Some(Ty::U64));
    for (name, k) in [("h1", 0x55), ("h2", 0x66)] {
        mb.define(name, s, Linkage::External, |fb| {
            let k = fb.konst(Ty::U64, k);
            let out = fb.bin(BinOp::Xor, Ty::U64, fb.p(0), k);
            fb.ret(out);
        });
    }
    let mut module = licensed(mb.finish());
    set_gate(&mut module, "h1", None);
    set_gate(&mut module, "h2", None);
    let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module, object, target.triple());
    let report = fx.report();
    assert!(kernel_proved(&report, "h1") && kernel_proved(&report, "h2"), "{}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", explain(&report));
    fx
}

/// Panic if the gate binds `fx` with any function proved, or ships it under
/// strict: `why` says what a linker links instead. A refusal of the object,
/// or every function of the section left unproved, both pass.
fn assert_no_function_of_the_section_is_proved(fx: &Fixture, why: &str) {
    if let Ok(report) = fx.verify() {
        let proved: Vec<&str> = report
            .certificates
            .iter()
            .filter(|c| c.is_kernel_proved())
            .map(|c| c.symbol.as_str())
            .collect();
        let strict = report.ships(EmitPolicy::StrictProvenOnly).is_ok();
        if !proved.is_empty() || strict {
            panic!(
                "BOUND: {why}; the gate proves {proved:?} and strict ships: {strict}\n{}",
                explain(&report)
            );
        }
    }
}

/// ADJUDICATION FINDING, ninth adjudication (2026-11-12): a Mach-O code
/// section whose TYPE is a literal type. `parse_macho` classifies
/// `__TEXT,__text` as code when its `flags` word has an instruction attribute
/// and is not `S_ZEROFILL`; the section type in the low byte is otherwise
/// unread. With type `S_4BYTE_LITERALS` (3), the type the admission's
/// condition (c) refuses for a record's section, the object below binds and
/// both leaves are kernel-proved and ship under strict, as unpatched.
///
/// The object is the one [`two_leaves`] asserts on (Darwin, O2) with the
/// `__text` header's type byte set to 3 (`flags` 0x80000400 -> 0x80000403,
/// asserted below to keep its instruction attribute). Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor darwin -arch arm64 -platform_version
/// macos 14.0 14.0 -dylib`, from a rustup toolchain) emits the section as a
/// 16-byte `__TEXT,__literals` holding the words `mov x1, #0x55; eor x0, x0,
/// x1; ret; mov x1, #0x66`: it split the code into 4-byte literals and kept
/// one of each, so `h2` is `mov x1, #0x66` followed by bytes outside the
/// section. Loaded with dlopen and called, the unpatched image returns h1(5) =
/// 0x50 and h2(5) = 0x63; this one returns h1(5) = 0x50 and dies of SIGILL
/// (exit 132) in h2. Apple ld-27037.1 (`cc -dynamiclib`) warns that the
/// section is "not a code section (missing 'regular,pure_instructions' section
/// flag)" and links both leaves intact. No other linker was run.
///
/// FAILS while the reader proves code in a section a linker merges by
/// content.
#[test]
fn a_code_section_of_a_literal_type_refuses_the_object() {
    const S_4BYTE_LITERALS: u32 = 0x3;
    let fx = two_leaves(DARWIN_T);
    let patched = fx.patched(|o| {
        // section_64: flags @64.
        let at = section_header_of(o, "h1") + 64;
        let flags = u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        assert_eq!(flags & 0xff, 0, "`__text` is S_REGULAR");
        assert_ne!(flags & 0x8000_0400, 0, "`__text` carries an instruction attribute");
        o[at..at + 4].copy_from_slice(&(flags | S_4BYTE_LITERALS).to_le_bytes());
    });
    assert_no_function_of_the_section_is_proved(
        &patched,
        "`__text` has section type S_4BYTE_LITERALS, which LLD splits into 4-byte literals \
         and merges by content: h2 links as `mov x1, #0x66` and runs off the section",
    );
}

/// MUTATION SWEEP FINDING (2026-11-13): the attribute half of the exact code
/// flags word. The reader admits `__TEXT,__text` as code only when its `flags`
/// word is exactly trust-cg's, S_REGULAR with `S_ATTR_PURE_INSTRUCTIONS |
/// S_ATTR_SOME_INSTRUCTIONS`; [`a_code_section_of_a_literal_type_refuses_the_object`]
/// changes only the type byte, so a reader that compared the type and the two
/// instruction attributes and ignored every other attribute bit passed every
/// test. Each attribute below is one trust-cg never sets, ORed alone into the
/// `__text` header of the object [`two_leaves`] asserts on (Darwin, O2);
/// `S_ATTR_SELF_MODIFYING_CODE` says outright that the bytes are not what runs.
/// No linker was run for this test: it pins the reader's rule, not a linker's
/// reading of each bit.
///
/// FAILS while the reader proves code in a section whose attributes are not
/// exactly trust-cg's.
#[test]
fn a_code_section_with_an_attribute_trust_cg_does_not_set_refuses_the_object() {
    let fx = two_leaves(DARWIN_T);
    for (name, bit) in [
        ("S_ATTR_NO_TOC", 0x4000_0000u32),
        ("S_ATTR_STRIP_STATIC_SYMS", 0x2000_0000),
        ("S_ATTR_NO_DEAD_STRIP", 0x1000_0000),
        ("S_ATTR_LIVE_SUPPORT", 0x0800_0000),
        ("S_ATTR_SELF_MODIFYING_CODE", 0x0400_0000),
        ("S_ATTR_DEBUG", 0x0200_0000),
    ] {
        let patched = fx.patched(|o| {
            // section_64: flags @64.
            let at = section_header_of(o, "h1") + 64;
            let flags = u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
            assert_eq!(flags, 0x8000_0400, "`__text` carries exactly trust-cg's flags word");
            o[at..at + 4].copy_from_slice(&(flags | bit).to_le_bytes());
        });
        assert_no_function_of_the_section_is_proved(
            &patched,
            &format!("`__text` carries {name}, an attribute trust-cg never sets"),
        );
    }
}

/// ADJUDICATION FINDING, ninth adjudication (2026-11-12): an ELF code section
/// marked mergeable. `parse_elf` classifies `.text` as code from its name and
/// `SHF_ALLOC | SHF_EXECINSTR` without `SHF_WRITE`; every other `sh_flags`
/// bit and `sh_entsize` are unread. With `SHF_MERGE` (0x10) and `sh_entsize`
/// 4, the flag the admission's condition (c) refuses for a record's section,
/// the object below binds and both leaves are kernel-proved and ship under
/// strict, as unpatched.
///
/// The object is the one [`two_leaves`] asserts on (Linux, O2) with
/// `SHF_MERGE` ORed into `.text`'s `sh_flags` and its `sh_entsize` set to 4.
/// Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor gnu -shared`, from a rustup toolchain,
/// default `-O1`; lld/ELF's `shouldMerge` makes any `SHF_MERGE` section with a
/// non-zero `sh_entsize` a merge section) links the unpatched object's
/// `.text` as the six words it compiled and this one's as four, `mov x1,
/// #0x55; ret; mov x1, #0x66; eor x0, x0, x1`, with `h1` at the first and
/// `h2` at the third: `h1` returns its argument unchanged and `h2` runs off
/// the end of `.text`. The output was read, not executed (the host runs no
/// ELF). No GNU linker was run.
///
/// FAILS while the reader proves code in a section a linker merges by
/// content.
#[test]
fn a_mergeable_code_section_refuses_the_object() {
    const SHF_MERGE: u64 = 0x10;
    let fx = two_leaves(LINUX_T);
    let patched = fx.patched(|o| {
        // Elf64_Shdr: sh_flags @8, sh_entsize @56.
        let h = section_header_of(o, "h1");
        let flags = u64::from_le_bytes(o[h + 8..h + 16].try_into().unwrap());
        assert_eq!(flags, 0x6, "`.text` is SHF_ALLOC | SHF_EXECINSTR");
        o[h + 8..h + 16].copy_from_slice(&(flags | SHF_MERGE).to_le_bytes());
        o[h + 56..h + 64].copy_from_slice(&4u64.to_le_bytes());
    });
    assert_no_function_of_the_section_is_proved(
        &patched,
        "`.text` is SHF_MERGE with sh_entsize 4, which LLD merges by content: h1 links as \
         `mov x1, #0x55; ret` and h2 runs off the section",
    );
}

/// MUTATION SWEEP FINDING (2026-11-13): the exact ELF code flags word. The
/// reader admits `.text` as code only when `sh_flags` is SHF_ALLOC |
/// SHF_EXECINSTR, with SHF_GNU_RETAIN the one bit tolerated beside them;
/// [`a_mergeable_code_section_refuses_the_object`] sets only SHF_MERGE. Each
/// bit below, ORed alone into `.text` of the object [`two_leaves`] asserts on
/// (Linux, O2), is one trust-cg never sets: SHF_WRITE (writable code), and
/// SHF_GROUP (a linker may keep another object's copy instead). No linker was
/// run: it pins the reader's rule.
///
/// FAILS while the reader proves code in an ELF section whose flags are not
/// exactly trust-cg's.
#[test]
fn an_elf_code_section_with_a_flag_trust_cg_does_not_set_refuses_the_object() {
    let fx = two_leaves(LINUX_T);
    for (name, bit) in [("SHF_WRITE", 0x1u64), ("SHF_GROUP", 0x200)] {
        let patched = fx.patched(|o| {
            // Elf64_Shdr: sh_flags @8.
            let h = section_header_of(o, "h1");
            let flags = u64::from_le_bytes(o[h + 8..h + 16].try_into().unwrap());
            assert_eq!(flags, 0x6, "`.text` is SHF_ALLOC | SHF_EXECINSTR");
            or_section_flags(o, "h1", bit);
        });
        assert_no_function_of_the_section_is_proved(
            &patched,
            &format!("`.text` carries {name}, a flag trust-cg never sets"),
        );
    }
}

/// MUTATION SWEEP FINDING (2026-11-13): the one bit the ELF code word
/// tolerates. SHF_GNU_RETAIN only keeps a section from garbage collection, so
/// `.text` of the object [`two_leaves`] asserts on (Linux, O2) with it ORed in
/// is still code: both leaves are kernel-proved and ship under strict.
///
/// FAILS if the reader refuses a code section only for SHF_GNU_RETAIN.
#[test]
fn an_elf_code_section_kept_by_shf_gnu_retain_is_still_proved() {
    const SHF_GNU_RETAIN: u64 = 0x20_0000;
    let fx = two_leaves(LINUX_T);
    let patched = fx.patched(|o| or_section_flags(o, "h1", SHF_GNU_RETAIN));
    assert_ne!(patched.object, fx.object, "the flag changes the object");
    let report = patched.report();
    assert!(kernel_proved(&report, "h1") && kernel_proved(&report, "h2"), "{}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", explain(&report));
}

/// The ELF counterpart of
/// [`a_code_section_at_an_address_off_its_instruction_alignment_refuses_the_object`]:
/// the same leaves (Linux, O2) with `.text`'s `sh_addralign` lowered from 4
/// to 1. A linker places an input section only at a multiple of its
/// `sh_addralign`, so with 1 nothing in the object puts `.text`, or the
/// instruction offsets the reader checks for 4-byte alignment, on a 4-byte
/// boundary. No linker was run on this object: the reader refuses it because
/// the format gives no guarantee, not because a run misplaced it. The mutation
/// sweep of 2026-11-13 found that lowering the bound to `>= 2` passed with 1
/// alone, so 2, the largest power of two below the instruction size, is
/// lowered to as well.
#[test]
fn an_elf_code_section_aligned_below_its_instructions_refuses_the_object() {
    let fx = two_leaves(LINUX_T);
    // 1, and 2: the largest power of two below the instruction size.
    for lowered in [1u64, 2] {
        let patched = fx.patched(|o| {
            // Elf64_Shdr: sh_addralign @48.
            let h = section_header_of(o, "h1");
            let align = u64::from_le_bytes(o[h + 48..h + 56].try_into().unwrap());
            assert!(align >= 4, "`.text` is emitted with sh_addralign {align}");
            o[h + 48..h + 56].copy_from_slice(&lowered.to_le_bytes());
        });
        assert_no_function_of_the_section_is_proved(
            &patched,
            &format!(
                "`.text` has sh_addralign {lowered}, so nothing places its instructions on a \
                 4-byte boundary"
            ),
        );
    }
}

/// ADJUDICATION FINDING, ninth adjudication (2026-11-12): an UNRELOCATED call
/// between two pieces of a Mach-O section a linker may cut at its symbols.
/// trust-cg sets `MH_SUBSECTIONS_VIA_SYMBOLS` in every Mach-O object (asserted
/// below and by
/// [`the_system_linker_keeps_the_record_pointer_with_and_without_subsections_via_symbols`]),
/// which tells the static linker that each symbol starts a piece it may move
/// or drop; with `-dead_strip`, which rustc passes to every macOS link
/// (rustc_codegen_ssa `GccLinker::gc_sections`, read in this tree), it drops
/// every piece no relocation or export reaches. The reader names an
/// unrelocated `bl` to the start of a non-preemptible extent as a call to
/// that body (the module comment's UNRELOCATED BRANCHES, pinned by
/// compiled_object_reader.rs `unrelocated_bl_to_window_start_is_a_call` and
/// cer_branch26_operands.rs
/// `resolved_unrelocated_nonzero_local_branch_retains_its_actual_target`, both
/// of which this finding contradicts on Mach-O) and, on the pin, never read
/// the header flag for it, so `f` [PROVED] paired the call with `g`. The
/// reader now grades that call Unknown when the flag is set (NEWLY UNKNOWN
/// (u)); this test passes on a refusal, or on `f` unproved with no call site
/// paired with `g` ([`assert_f_rests_on_no_call_to_g`]).
///
/// The object is the one [`wrapper_call`] asserts on (Darwin, O0, `g`
/// Internal, laid out before `f`) with `f`'s `ARM64_RELOC_BRANCH26` deleted
/// and its `bl` encoded with the displacement to `g`'s start, the shape
/// `unrelocated_bl_to_window_start_is_a_call` builds. Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: Apple ld-27037.1 (`cc -dynamiclib`) and LLD 23.1.1 (`rust-lld
/// -flavor darwin -dylib`) link it, without `-dead_strip`, to an image whose
/// f(5) = 0x37, as the relocated object's. With `-dead_strip` both drop `g`,
/// which no relocation names, and keep `f` with the `bl` it was given, now
/// aimed 0x10 bytes before `f` outside `__text`: loaded with dlopen and
/// called, both images die of SIGILL (exit 132). The relocated object links
/// to f(5) = 0x37 under `-dead_strip` too. No other linker was run.
///
/// FAILS while the reader pairs an unrelocated branch with a body that a
/// Mach-O linker may move or drop away from it.
#[test]
fn an_unrelocated_call_between_subsections_refuses_the_wrapper_object() {
    const MH_SUBSECTIONS_VIA_SYMBOLS: u32 = 0x2000;
    let (fx, record) = wrapper_call(DARWIN_T);
    let header_flags = u32::from_le_bytes(fx.object[24..28].try_into().unwrap());
    assert_eq!(header_flags, MH_SUBSECTIONS_VIA_SYMBOLS, "trust-cg's Mach-O header flags");
    let bl = bl_offsets(&fx.object, "f")[0];
    let g = symbol_offset(&fx.object, "g") as i64;
    let patched = fx.patched(|o| {
        delete_reloc(o, record);
        patch_word(o, bl, enc_bl(g - bl as i64));
    });
    assert_f_rests_on_no_call_to_g(
        &patched,
        "`f`'s `bl` to `g` carries no relocation in an MH_SUBSECTIONS_VIA_SYMBOLS object, so \
         Apple ld and LLD under -dead_strip drop `g` and keep the `bl` aimed outside `__text`",
    );
}

// ===========================================================================
// TENTH ADJUDICATION (2026-11-12): where a Mach-O linker PUTS the code
// ===========================================================================
//
// `parse_macho` reads a section's `addr` only to turn each symbol's `n_value`
// into an offset in its section, and never reads the section's `align`. Every
// check of a code window (a symbol's 4-byte alignment, the walk, the
// relocation offsets) is made on those offsets. Apple's static linker places a
// piece of a section at an address congruent to the piece's ADDRESS IN THE
// OBJECT modulo the section's alignment, so a `__text` whose `addr` is not a
// multiple of 4 links every instruction off its 4-byte boundary. The object
// below is RED against blob a4a1b3f463 and, by reading, against the pin
// bf45acdd08 (the movement changes no line that reads `addr` or `align`).
// It is not a defect of the admission's arm.

/// Move the Mach-O section that defines `symbol` by `shift` bytes in the
/// object's address space: its `section_64.addr` and the `n_value` of every
/// non-stab `N_SECT` symbol defined in it. File offsets, bytes, relocations
/// (whose `r_address` is an offset in the section) and every other field are
/// unchanged, so every symbol keeps its offset in its section.
fn shift_macho_section_address(o: &mut [u8], symbol: &str, shift: u64) {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let ordinal = CompiledObject::parse(o)
        .expect("the object parses")
        .symbols
        .iter()
        .find(|y| y.name == symbol)
        .and_then(|y| y.section)
        .unwrap_or_else(|| panic!("no defined symbol `{symbol}`"));
    // section_64: addr @32.
    let header = section_header_of(o, symbol);
    let addr = u64::from_le_bytes(o[header + 32..header + 40].try_into().unwrap());
    o[header + 32..header + 40].copy_from_slice(&(addr + shift).to_le_bytes());
    let mut c = 32;
    for _ in 0..rd32(o, 16) {
        // LC_SYMTAB: symoff @8, nsyms @12.
        if rd32(o, c) == 0x2 {
            let (symoff, nsyms) = (rd32(o, c + 8) as usize, rd32(o, c + 12) as usize);
            for e in (symoff..symoff + 16 * nsyms).step_by(16) {
                // nlist_64: n_type @4 (N_STAB 0xe0, N_TYPE 0x0e, N_SECT 0x0e),
                // n_sect @5, n_value @8.
                if o[e + 4] & 0xe0 == 0
                    && o[e + 4] & 0x0e == 0x0e
                    && usize::from(o[e + 5]) == ordinal
                {
                    let v = u64::from_le_bytes(o[e + 8..e + 16].try_into().unwrap());
                    o[e + 8..e + 16].copy_from_slice(&(v + shift).to_le_bytes());
                }
            }
        }
        c += rd32(o, c + 4) as usize;
    }
}

/// ADJUDICATION FINDING, tenth adjudication (2026-11-12): a Mach-O `__text`
/// at an address in the object that is not a multiple of 4. `parse_macho`
/// keeps a symbol's offset in its section (`n_value - addr`) and never reads
/// the section's `addr` or `align` otherwise, and `bind` checks each body's
/// 4-byte alignment on that offset. So the object below reads, symbol for
/// symbol and byte for byte, as the unpatched one (asserted), and the gate
/// proves `f` and `g` and ships them under strict as before.
///
/// The object is the one [`wrapper_call`] asserts on (Darwin, O0: `__text`
/// at `addr` 0 with `align` 2^2, `g` at offset 0 and `f` at 0x10, `f`
/// calling `g` through a relocated `bl`), with `__text`'s `addr` set to 2 and
/// the `n_value` of `g` and `f` raised by 2. Nothing else changes.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: Apple ld-27037.1 (`cc -dynamiclib`, with and without
/// `-Wl,-dead_strip`) places each piece at an address congruent to its
/// address in the object modulo 2^align: `g` and `f` at addresses 2 modulo
/// 4, two bytes off the instruction boundary (for one output name, `g` at
/// 0x2ca and `f` at 0x2da, where the unpatched object links them at 0x2d0 and
/// 0x2e0; the output's name moves the layout). Loaded with dlopen and called,
/// `f` dies of SIGBUS (exit 138); the unpatched image returns f(5) = 0x37. The same happens with `addr` 6 under
/// `align` 2^2 and with `addr` 2 under `align` 2^3; `addr` 2 under `align`
/// 2^0 or 2^1, and `addr` 4, link aligned. LLD 23.1.1 (`rust-lld -flavor
/// darwin -dylib`) links every one of these aligned, f(5) = 0x37. These were
/// measured on objects dumped from the same fixture with the same patch; no
/// other linker was run.
///
/// It passes if the object is refused, or if no function of `__text` is
/// proved. FAILS while the reader proves code that Apple's linker places off
/// its instruction alignment.
#[test]
fn a_code_section_at_an_address_off_its_instruction_alignment_refuses_the_object() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let (fx, _) = wrapper_call(DARWIN_T);
    let header = section_header_of(&fx.object, "f");
    // section_64: addr @32, align @52.
    let addr = u64::from_le_bytes(fx.object[header + 32..header + 40].try_into().unwrap());
    let align = u32::from_le_bytes(fx.object[header + 52..header + 56].try_into().unwrap());
    assert_eq!((addr, align), (0, 2), "`__text` at address 0, aligned to 2^2");
    let patched = fx.patched(|o| shift_macho_section_address(o, "f", 2));
    // A reader that refuses the object at parse passes; one that parses it
    // must see the same symbol offsets as for the unpatched object, so the
    // functions below are the ones the gate decides.
    let offsets = |o: &[u8]| {
        CompiledObject::parse(o).ok().map(|parsed| {
            parsed.symbols.iter().map(|y| (y.name.clone(), y.section, y.value)).collect::<Vec<_>>()
        })
    };
    let control = offsets(&fx.object).expect("the unpatched object parses");
    if let Some(patched_offsets) = offsets(&patched.object) {
        assert_eq!(patched_offsets, control, "the reader sees the same offsets");
    }
    assert_ne!(patched.object, fx.object);
    assert_no_function_of_the_section_is_proved(
        &patched,
        "`__text` lies at address 2 under alignment 2^2, which Apple ld keeps modulo 4: it \
         links `g` and `f` two bytes off the instruction boundary, and `f` dies of SIGBUS",
    );
}

// ===========================================================================
// ELEVENTH ADJUDICATION (2026-11-12): a relocation WIDER than the instruction
// it sits on
// ===========================================================================
//
// `walk_window` matches a relocation to the one instruction at its offset and,
// when its kind is not one the reader models, consumes it there and makes THAT
// function Unknown. It never reads how many bytes the relocation writes. An
// 8-byte relocation (ELF `R_AARCH64_PREL64` or `R_AARCH64_ABS64`, Mach-O
// `ARM64_RELOC_UNSIGNED` of length 3) on a function's last word writes the
// first word of the NEXT function too, and the reader proves that function
// on the bytes the object holds. The object below is RED against blob
// 494c67e142 and, by reading, against the pin bf45acdd08 (the movement
// changes no line of the walk's relocation matching). It is not a defect of
// the admission's arm.

/// ADJUDICATION FINDING, eleventh adjudication (2026-11-12): a relocation that
/// writes past its own instruction into the next function.
///
/// The object is the one [`two_leaves`] asserts on (Linux, O2: `h1` is `mov
/// x1, #0x55; eor x0, x0, x1; ret` at `.text` offsets 0..0xc and `h2` is `mov
/// x1, #0x66; eor x0, x0, x1; ret` at 0xc..0x18), with its one relocation
/// section, `.rela.eh_frame`, retargeted to `.text` (`sh_info`) and cut to ONE
/// entry: `R_AARCH64_PREL64` (260) at offset 8, `h1`'s `ret`, against `.text`'s
/// section symbol with addend 0xd2800ee1_d65f03c8. A linker writes the 8 bytes
/// `S + A - P` = 0xd2800ee1_d65f03c0 at offset 8 (S is `.text`, P is `.text`
/// + 8, so the value does not depend on where `.text` lands): the low word is
/// `ret` again, and the high word, at offset 0xc, replaces `h2`'s first
/// instruction with `mov x1, #0x77`. `.eh_frame` keeps its bytes with no
/// relocation. Nothing else changes.
///
/// The reader parses that object and binds it: the relocation is not a kind
/// it models, so the `ret` at 8 consumes it and `h1` is Unknown, while `h2`'s
/// window holds no relocation and the gate proves it computes `x ^ 0x66`.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor gnu`, from a rustup toolchain, with
/// `-static -e h1`, `-pie -e h1` and `-shared`) links every variant with
/// `h1` unchanged and `h2` as `mov x1, #0x77; eor x0, x0, x1; ret`, which
/// returns `x ^ 0x77` (h2(5) = 0x72, not 0x63). The outputs were read with
/// llvm-objdump, not executed (the host runs no ELF). No GNU linker was run.
/// The Mach-O counterpart (`ARM64_RELOC_UNSIGNED`, length 3, on `h1`'s `ret`)
/// is refused by Apple ld-27037.1 ("8 byte relocaton ... is not fully within
/// bounds of atom"); LLD 23.1.1 `-flavor darwin -dylib -no_fixup_chains`
/// links it with `h2` starting `mov x1, #0x77`, an image dyld then refuses
/// to load (a rebase in `__TEXT`).
///
/// It passes if the object is refused, or if `h2` is not proved and strict
/// does not ship. FAILS while the reader proves a function whose bytes a
/// relocation of another instruction rewrites.
#[test]
fn a_relocation_wider_than_its_instruction_refuses_the_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolKind};
    const SHT_RELA: u32 = 4;
    const R_AARCH64_PREL64: u64 = 260;
    // `mov x1, #0x77` above `ret`, with P - S = 8 added back.
    const ADDEND: u64 = 0xd280_0ee1_d65f_03c8;
    let fx = two_leaves(LINUX_T);
    let parsed = CompiledObject::parse(&fx.object).expect("the unpatched object parses");
    let h1 = parsed.symbols.iter().find(|y| y.name == "h1").expect("h1");
    let h2 = parsed.symbols.iter().find(|y| y.name == "h2").expect("h2");
    let text = h1.section.expect("h1 is defined");
    assert_eq!((h1.value, h2.value, h2.section), (0, 0xc, Some(text)), "h2 follows h1");
    let text_bytes = &parsed.section(text).expect(".text").bytes;
    assert_eq!(&text_bytes[8..12], &0xd65f_03c0_u32.to_le_bytes(), "h1 ends in `ret`");
    assert_eq!(&text_bytes[12..16], &0xd280_0cc1_u32.to_le_bytes(), "h2 opens `mov x1, #0x66`");
    let section_symbol = parsed
        .symbols
        .iter()
        .find(|y| y.kind == SymbolKind::Section && y.section == Some(text))
        .expect(".text's section symbol")
        .index as u64;
    let patched = fx.patched(|o| {
        let rd16 = |o: &[u8], at: usize| usize::from(u16::from_le_bytes([o[at], o[at + 1]]));
        let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
        let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
        let relas: Vec<usize> = (0..shnum)
            .map(|i| shoff + i * shentsize)
            .filter(|&h| rd32(o, h + 4) == SHT_RELA)
            .collect();
        let [rela] = relas[..] else { panic!("{} relocation sections", relas.len()) };
        // Elf64_Shdr: sh_offset @24, sh_size @32, sh_info @44.
        let at = u64::from_le_bytes(o[rela + 24..rela + 32].try_into().unwrap()) as usize;
        assert_ne!(rd32(o, rela + 44) as usize, text, "the section relocates `.eh_frame`");
        // Elf64_Rela: r_offset, r_info (symbol << 32 | type), r_addend.
        o[at..at + 8].copy_from_slice(&8u64.to_le_bytes());
        o[at + 8..at + 16]
            .copy_from_slice(&(section_symbol << 32 | R_AARCH64_PREL64).to_le_bytes());
        o[at + 16..at + 24].copy_from_slice(&ADDEND.to_le_bytes());
        o[rela + 32..rela + 40].copy_from_slice(&24u64.to_le_bytes());
        o[rela + 44..rela + 48].copy_from_slice(&(text as u32).to_le_bytes());
    });
    if let Ok(report) = patched.verify() {
        let h2_proved = report.certificate("h2").is_some_and(|c| c.is_kernel_proved());
        let strict = report.ships(EmitPolicy::StrictProvenOnly).is_ok();
        assert!(
            !h2_proved && !strict,
            "BOUND: an R_AARCH64_PREL64 on h1's last word writes h2's first word, which LLD \
             links as `mov x1, #0x77`; the gate proves h2: {h2_proved}, strict ships: {strict}\n{}",
            explain(&report)
        );
    }
}

/// Refusal (x) on Mach-O, named by the twenty-fifth adjudication (2026-11-13): every other
/// test of the code-relocation width reads it from an ELF type, so none fed (x) a length that
/// `parse_macho` read from `r_length`. The leaves of
/// [`a_relocation_wider_than_its_instruction_refuses_the_object`] for Darwin (O2), with one
/// relocation appended to `__text`, which has none: an extern `ARM64_RELOC_UNSIGNED` of
/// `r_length` 3 (8 bytes) at offset 8, `h1`'s `ret`, against `h1`. The doc above records what
/// the linkers make of this counterpart (Apple ld refuses it; LLD links `h2` as
/// `mov x1, #0x77`); this object was linked by neither.
///
/// FAILS while the reader binds a Mach-O code relocation wider than one instruction.
#[test]
fn a_mach_o_relocation_wider_than_its_instruction_refuses_the_object() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    const ARM64_RELOC_UNSIGNED: u32 = 0;
    let fx = two_leaves(DARWIN_T);
    let parsed = CompiledObject::parse(&fx.object).expect("the unpatched object parses");
    let h1 = parsed.symbols.iter().find(|y| y.name == "h1").expect("h1");
    let h2 = parsed.symbols.iter().find(|y| y.name == "h2").expect("h2");
    assert_eq!((h1.value, h2.value, h2.section), (0, 0xc, h1.section), "h2 follows h1");
    let h1_index = u32::try_from(h1.index).expect("a 24-bit symbol index");
    let header = section_header_of(&fx.object, "h1");
    let patched = fx.patched(|o| {
        // section_64: reloff @56, nreloc @60.
        let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        assert_eq!(rd32(o, header + 60), 0, "`__text` of two leaves has no relocation");
        while o.len() % 8 != 0 {
            o.push(0);
        }
        let at = u32::try_from(o.len()).expect("a 32-bit offset");
        // relocation_info: r_address, then r_symbolnum:24 r_pcrel:1 r_length:2 r_extern:1
        // r_type:4.
        o.extend_from_slice(&8i32.to_le_bytes());
        let info = h1_index | (3 << 25) | (1 << 27) | (ARM64_RELOC_UNSIGNED << 28);
        o.extend_from_slice(&info.to_le_bytes());
        o[header + 56..header + 60].copy_from_slice(&at.to_le_bytes());
        o[header + 60..header + 64].copy_from_slice(&1u32.to_le_bytes());
    });
    let reparsed = CompiledObject::parse(&patched.object).expect("the patched object parses");
    let text = reparsed.section(h1.section.expect("h1 is defined")).expect("`__text`");
    let [reloc] = &text.relocations[..] else {
        panic!("{} relocations in `__text`", text.relocations.len())
    };
    assert_eq!((reloc.offset, reloc.length), (8, 3), "8 bytes at h1's `ret`, from r_length");
    let refusal = match patched.verify() {
        Ok(report) => panic!(
            "BOUND: an 8-byte relocation on h1's last word writes h2's first word\n{}",
            explain(&report)
        ),
        Err(e) => e,
    };
    assert_eq!(refusal.kind, ObjectRefusalKind::UnconsumedRelocation, "{}", refusal.reason);
    assert!(refusal.reason.contains("writes 8 bytes"), "{}", refusal.reason);
}

// ===========================================================================
// TWELFTH ADJUDICATION (2026-11-12): a 64-bit ELF relocation type the width
// table reads as one instruction
// ===========================================================================
//
// Blob 0d2b808fcc refuses a code relocation wider than 4 bytes and reads an
// ELF relocation's width from its type (`elf_relocation_length`). Its table
// gives 8 bytes only to R_AARCH64_ABS64 (257) and R_AARCH64_PREL64 (260) and
// 4 bytes to "every static instruction type (263 to 313)". That range holds
// R_AARCH64_GOTREL64 (307, 0x133), a 64-bit DATA relocation (S + A - GOT,
// AArch64 ELF ABI; LLVM's ELFRelocs/AArch64.def and the `object` crate's
// `R_AARCH64_GOTREL64 = 307`, "GOT-relative 64-bit"), and the unassigned
// numbers 281 and 294 to 298, which the table's own comment says a type the
// reader does not know is never taken to be. The pin bf45acdd08 recorded 4
// bytes for every ELF type, so it binds the object below the same way.

/// ADJUDICATION FINDING, twelfth adjudication (2026-11-12): an
/// `R_AARCH64_GOTREL64` on a function's last word, which the reader reads as
/// writing that one word.
///
/// The object is the one [`two_leaves`] asserts on (Linux, O2: `h1` at
/// `.text` 0..0xc ending in `ret` at 8, `h2` at 0xc..0x18), patched exactly as
/// [`a_relocation_wider_than_its_instruction_refuses_the_object`] patches it
/// but with the relocation's type `R_AARCH64_GOTREL64` (307) in place of
/// `R_AARCH64_PREL64` (260): one entry at offset 8 against `.text`'s section
/// symbol. The AArch64 ELF ABI defines GOTREL64 as a 64-bit data relocation,
/// `S + A - GOT`, written over 8 bytes: the high word lands on `h2`'s first
/// instruction, whatever value the GOT's placement gives it.
///
/// The reader parses that object and binds it: `elf_relocation_length(307)` is
/// 2 (4 bytes), so the code-width refusal (x) passes it, the `ret` at 8
/// consumes it as an unmodeled kind and makes `h1` Unknown, and the gate
/// proves `h2` on the bytes the object holds. That is the defect (x) was
/// written to close, for a type the table misfiles.
///
/// What a linker makes of it, MEASURED BY HAND on 2026-11-12 and run by no
/// test: LLD 23.1.1 (`rust-lld -flavor gnu -shared`, from a rustup toolchain)
/// refuses it ("unknown relocation (307) against symbol .text"); it refuses
/// 308 and 281 the same way. No GNU ld, gold or mold was available or run, so
/// no linker was seen to write GOTREL64's 8 bytes; the finding rests on the
/// ABI's definition of the type, which is what the width table claims to
/// encode.
///
/// It passes if the object is refused (at parse or at bind), or if `h2` is
/// not proved and strict does not ship. FAILS while the reader proves a
/// function whose first word a 64-bit relocation of another function writes.
#[test]
fn a_64_bit_got_relative_relocation_in_code_refuses_the_object() {
    use trust_cg_bridge::compiled_object::{CompiledObject, SymbolKind};
    const SHT_RELA: u32 = 4;
    const R_AARCH64_GOTREL64: u64 = 307;
    const ADDEND: u64 = 0xd280_0ee1_d65f_03c8;
    let fx = two_leaves(LINUX_T);
    let parsed = CompiledObject::parse(&fx.object).expect("the unpatched object parses");
    let h1 = parsed.symbols.iter().find(|y| y.name == "h1").expect("h1");
    let h2 = parsed.symbols.iter().find(|y| y.name == "h2").expect("h2");
    let text = h1.section.expect("h1 is defined");
    assert_eq!((h1.value, h2.value, h2.section), (0, 0xc, Some(text)), "h2 follows h1");
    let text_bytes = &parsed.section(text).expect(".text").bytes;
    assert_eq!(&text_bytes[8..12], &0xd65f_03c0_u32.to_le_bytes(), "h1 ends in `ret`");
    let section_symbol = parsed
        .symbols
        .iter()
        .find(|y| y.kind == SymbolKind::Section && y.section == Some(text))
        .expect(".text's section symbol")
        .index as u64;
    let patched = fx.patched(|o| {
        let rd16 = |o: &[u8], at: usize| usize::from(u16::from_le_bytes([o[at], o[at + 1]]));
        let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
        let shoff = u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize;
        let (shentsize, shnum) = (rd16(o, 58), rd16(o, 60));
        let relas: Vec<usize> = (0..shnum)
            .map(|i| shoff + i * shentsize)
            .filter(|&h| rd32(o, h + 4) == SHT_RELA)
            .collect();
        let [rela] = relas[..] else { panic!("{} relocation sections", relas.len()) };
        let at = u64::from_le_bytes(o[rela + 24..rela + 32].try_into().unwrap()) as usize;
        assert_ne!(rd32(o, rela + 44) as usize, text, "the section relocates `.eh_frame`");
        o[at..at + 8].copy_from_slice(&8u64.to_le_bytes());
        o[at + 8..at + 16]
            .copy_from_slice(&(section_symbol << 32 | R_AARCH64_GOTREL64).to_le_bytes());
        o[at + 16..at + 24].copy_from_slice(&ADDEND.to_le_bytes());
        o[rela + 32..rela + 40].copy_from_slice(&24u64.to_le_bytes());
        o[rela + 44..rela + 48].copy_from_slice(&(text as u32).to_le_bytes());
    });
    if let Ok(report) = patched.verify() {
        let h2_proved = report.certificate("h2").is_some_and(|c| c.is_kernel_proved());
        let strict = report.ships(EmitPolicy::StrictProvenOnly).is_ok();
        assert!(
            !h2_proved && !strict,
            "BOUND: an R_AARCH64_GOTREL64 (a 64-bit data relocation) on h1's last word writes \
             h2's first word; the reader reads it as 4 bytes. The gate proves h2: {h2_proved}, \
             strict ships: {strict}\n{}",
            explain(&report)
        );
    }
}

// ===========================================================================
// THIRTEENTH ADJUDICATION (2026-11-12): a plain global in a section the
// linker splits and merges by content
// ===========================================================================
//
// Conditions (c) and (d) of the location-record admission (`ordinary_data`)
// keep a record's pointer, and its target, out of a section the linker splits
// into pieces and merges by content: the first adjudication measured that the
// bytes after a piece are then not the rest of the global. The same reader
// fact holds for EVERY initialized global, record or not: `parse_macho`
// classes `__TEXT,__const`, `__TEXT,__cstring` and `__TEXT,__literal4/8/16`
// as data whatever the section TYPE (only zero-fill and the instruction
// attributes are read), and `parse_elf` classes `.rodata*` and `.data*` by
// name and the ALLOC, EXECINSTR bits, never SHF_MERGE or SHF_STRINGS. `bind`
// then compares the bytes after the global's symbol with `M_cg`'s image and
// lists it in `verified_globals`. Neither line is in the movement from the
// pin bf45acdd08; the admission reads `ordinary_data` only inside the loop
// over a data section's relocations, and a plain global has none.

/// `h(x) = x ^ 0x55` (gate removed) beside an immutable, EXTERNAL global
/// `plain` whose image is [`STRING_PIECES`] (three NUL-terminated strings, the
/// first two equal). Nothing reads `plain`; it is external so that a C driver
/// can read the linked bytes under its symbol.
fn plain_string_global_module() -> Module {
    let mut module = leaf_module("h");
    set_gate(&mut module, "h", None);
    let id = image_global(&mut module, "plain", image_bytes(STRING_PIECES).collect(), 1);
    module.globals[id.as_usize()].linkage = Linkage::External;
    module
}

/// ADJUDICATION FINDING, thirteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob 78ccaf4028 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm.
///
/// INPUT: the object trust-cg compiles for [`plain_string_global_module`]
/// (Darwin and Linux, O2) with nothing changed but the header of `plain`'s
/// section, marked by [`mark_string_literals`]: Mach-O `__TEXT,__const`
/// becomes `__TEXT,__cstring` of type `S_CSTRING_LITERALS`; ELF `.rodata`
/// gains `SHF_MERGE | SHF_STRINGS` with `sh_entsize` 1. The reader parses and
/// binds it and lists `plain` in `verified_globals`: it compared the 9 bytes
/// after `plain`'s symbol with `M_cg`'s image `616200616200636400`.
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test:
/// * Apple ld-27037.1 (the system `cc`, the object linked beside a C driver
///   that prints the 9 bytes at `plain` and a C file holding the literals
///   "cd" and "ab"): the unmarked object reads `616200616200636400`, with and
///   without `-dead_strip`; the marked one reads `61620000010000001c`, and
///   `616200000000010000` under `-dead_strip`.
/// * LLD 23.1.1 (`rust-lld -flavor gnu -e _start`, from a rustup toolchain,
///   beside an assembled object whose `.rodata.str1.1` holds "cd" and "ab" and
///   whose `_start` takes `plain`'s address; the output file read, not
///   executed): the unmarked object reads `616200616200636400` at `-O1` and
///   `-O2`; the marked one `616200636400000014` at `-O1` and
///   `616200000014000000` at `-O2`.
/// So the linked bytes under `plain` are the first piece `ab\0` and then
/// other bytes, where the reader certified the whole image.
///
/// FAILS while the reader lists a global as verified whose section the linker
/// splits and merges by content. A refusal at parse or at bind, or `plain`
/// left out of `verified_globals`, passes.
#[test]
fn a_global_in_a_section_the_linker_merges_by_content_is_not_verified() {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, ObjectExpectations, ObjectFormat, ObjectLayout,
    };
    let mut bound = Vec::new();
    for (target, format) in [(DARWIN_T, ObjectFormat::MachO), (LINUX_T, ObjectFormat::Elf)] {
        let module = plain_string_global_module();
        let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let bind = |o: &[u8]| {
            CompiledObject::parse(o).and_then(|parsed| {
                let expect =
                    ObjectExpectations::from_module(&module, format, RelocationModel::Static)?;
                ObjectLayout::bind(parsed, &expect)
            })
        };
        let layout = bind(&object)
            .unwrap_or_else(|e| panic!("{target:?}: the unmarked object is refused: {e}"));
        assert_eq!(layout.verified_globals, ["plain"], "{target:?}: the unmarked object");
        let mut marked = object.clone();
        mark_string_literals(&mut marked, "plain");
        assert_ne!(marked, object, "{target:?}: the mark changed nothing");
        if let Ok(layout) = bind(&marked)
            && layout.verified_globals.iter().any(|g| g == "plain")
        {
            bound.push(target);
        }
    }
    assert!(
        bound.is_empty(),
        "BOUND on {bound:?}: `plain` lies in a section the linker splits into pieces and merges \
         by content, and the reader lists it as verified against its whole image"
    );
}

// ===========================================================================
// FOURTEENTH ADJUDICATION (2026-11-12): globals listed as verified whose
// linked bytes are not the image
// ===========================================================================
//
// The answer to the thirteenth adjudication (blob a22b90c282) lists a data
// global in `verified_globals` only when its section is ordinary data or
// ZERO-FILL. Two reader facts, both on the pin bf45acdd08 and unchanged by the
// movement, still let a global be listed whose linked bytes are not `M_cg`'s
// image of it:
// * `bind` compares nothing for a global in a zero-fill section (only a
//   Data section's bytes are compared with the image; the zero-fill arm does
//   not read the image at all, nor its length), and lists it;
// * `bind` never compares a data symbol's binding with its `M_cg` linkage,
//   so a WEAK definition of a global `M_cg` gives strong external linkage is
//   compared and listed, while a linker resolves the name to another
//   object's strong definition.

/// `h(x) = x ^ 0x55` (gate removed) beside an EXTERNAL global `zed` holding
/// [`ZED_IMAGE`], mutable or not. Nothing reads `zed`; it is external so that
/// a C driver can read the linked bytes under its symbol. trust-cg puts it in
/// `__DATA,__data` / `.data` when mutable and `__TEXT,__const` / `.rodata`
/// when not.
fn external_image_global_module(mutable: bool) -> Module {
    let mut module = leaf_module("h");
    set_gate(&mut module, "h", None);
    let id = image_global(&mut module, "zed", image_bytes(&ZED_IMAGE).collect(), 8);
    module.globals[id.as_usize()].linkage = Linkage::External;
    module.globals[id.as_usize()].mutable = mutable;
    module
}

/// `zed`'s image: eight non-zero bytes.
const ZED_IMAGE: [u8; 8] = *b"\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31";

/// The file offset of the header (`section_64` / `Elf64_Shdr`) of the
/// section that defines `symbol`.
fn defining_section_header(o: &[u8], symbol: &str) -> usize {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let rd32 = |at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let parsed = CompiledObject::parse(o).expect("the object parses");
    let section = parsed
        .symbols
        .iter()
        .find(|y| y.name == symbol)
        .and_then(|y| y.section)
        .unwrap_or_else(|| panic!("no defined symbol `{symbol}`"));
    if is_macho(o) {
        // The section_64 headers of the LC_SEGMENT_64 commands, in order: the
        // 1-based ordinal a symbol names.
        let mut headers = Vec::new();
        let mut c = 32;
        for _ in 0..rd32(16) {
            if rd32(c) == 0x19 {
                headers.extend((0..rd32(c + 64) as usize).map(|i| c + 72 + i * 80));
            }
            c += rd32(c + 4) as usize;
        }
        headers[section - 1]
    } else {
        u64::from_le_bytes(o[40..48].try_into().unwrap()) as usize + section * usize::from(o[58])
    }
}

/// Turn the writable data section that defines `symbol` into ZERO-FILL, the
/// section a C compiler gives a zero-initialized global. Mach-O:
/// `__DATA,__data` becomes `__DATA,__bss` of type `S_ZEROFILL` with file
/// offset 0. ELF: `.data` becomes `.bss` of type `SHT_NOBITS` (its name
/// string rewritten in place). No byte of the section, symbol or relocation
/// moves; only the header says the bytes are zero.
fn turn_into_zero_fill(o: &mut [u8], symbol: &str) {
    let header = defining_section_header(o, symbol);
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    if is_macho(o) {
        const S_ZEROFILL: u32 = 1;
        assert_eq!(
            &o[header..header + 32],
            b"__data\0\0\0\0\0\0\0\0\0\0__DATA\0\0\0\0\0\0\0\0\0\0"
        );
        o[header..header + 16].copy_from_slice(b"__bss\0\0\0\0\0\0\0\0\0\0\0");
        let flags = header + 64;
        let marked = (rd32(o, flags) & !0xff) | S_ZEROFILL;
        o[flags..flags + 4].copy_from_slice(&marked.to_le_bytes());
        o[header + 48..header + 52].copy_from_slice(&0_u32.to_le_bytes());
    } else {
        const SHT_NOBITS: u32 = 8;
        let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
        let shstrndx = usize::from(u16::from_le_bytes(o[62..64].try_into().unwrap()));
        let names = rd64(o, rd64(o, 40) as usize + shstrndx * usize::from(o[58]) + 24) as usize;
        let name = names + rd32(o, header) as usize;
        assert_eq!(&o[name..name + 6], b".data\0");
        o[name..name + 6].copy_from_slice(b".bss\0\0");
        o[header + 4..header + 8].copy_from_slice(&SHT_NOBITS.to_le_bytes());
    }
}

/// Make the defined, external symbol `symbol` a WEAK definition: Mach-O
/// `N_WEAK_DEF` (0x80) in `n_desc`, ELF binding `STB_WEAK`. Nothing else
/// changes.
fn make_weak_definition(o: &mut [u8], symbol: &str) {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let parsed = CompiledObject::parse(o).expect("the object parses");
    let index = parsed
        .symbols
        .iter()
        .find(|y| y.name == symbol && y.section.is_some())
        .unwrap_or_else(|| panic!("no defined symbol `{symbol}`"))
        .index;
    if is_macho(o) {
        const N_EXT: u8 = 1;
        const N_WEAK_DEF: u16 = 0x80;
        let e = macho_symbol_entry(o, index);
        assert_ne!(o[e + 4] & N_EXT, 0, "`{symbol}` is not external");
        let desc = u16::from_le_bytes(o[e + 6..e + 8].try_into().unwrap()) | N_WEAK_DEF;
        o[e + 6..e + 8].copy_from_slice(&desc.to_le_bytes());
    } else {
        const STB_GLOBAL: u8 = 1;
        const STB_WEAK: u8 = 2;
        let e = elf_symbol_entry(o, index);
        assert_eq!(o[e + 4] >> 4, STB_GLOBAL, "`{symbol}` is not global");
        o[e + 4] = (STB_WEAK << 4) | (o[e + 4] & 0xf);
    }
}

/// Compile `module` for both formats at O2, check that the reader binds the
/// unchanged object and lists `zed`, apply `patch`, and return the targets on
/// which the reader still binds the patched object AND lists `zed` as
/// verified.
fn targets_listing_zed_after(module: &Module, patch: fn(&mut [u8], &str)) -> Vec<F1Target> {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, ObjectExpectations, ObjectFormat, ObjectLayout,
    };
    let mut listed = Vec::new();
    for (target, format) in [(DARWIN_T, ObjectFormat::MachO), (LINUX_T, ObjectFormat::Elf)] {
        let object = compile(module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let bind = |o: &[u8]| {
            CompiledObject::parse(o).and_then(|parsed| {
                let expect =
                    ObjectExpectations::from_module(module, format, RelocationModel::Static)?;
                ObjectLayout::bind(parsed, &expect)
            })
        };
        let layout = bind(&object)
            .unwrap_or_else(|e| panic!("{target:?}: the unchanged object is refused: {e}"));
        assert_eq!(layout.verified_globals, ["zed"], "{target:?}: the unchanged object");
        let mut patched = object.clone();
        patch(&mut patched, "zed");
        assert_ne!(patched, object, "{target:?}: the patch changed nothing");
        if let Ok(layout) = bind(&patched)
            && layout.verified_globals.iter().any(|g| g == "zed")
        {
            listed.push(target);
        }
    }
    listed
}

/// ADJUDICATION FINDING, fourteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob a22b90c282 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm.
///
/// INPUT: the object trust-cg compiles for
/// [`external_image_global_module`]`(true)` (Darwin and Linux, O2), whose
/// mutable global `zed` has the image [`ZED_IMAGE`] `2a2b2c2d2e2f3031`, with
/// nothing changed but the header of `zed`'s section, turned into zero-fill
/// by [`turn_into_zero_fill`] (Mach-O `__DATA,__bss` of type `S_ZEROFILL`;
/// ELF `.bss` of type `SHT_NOBITS`). The reader parses and binds it and lists
/// `zed` in `verified_globals`: for a zero-fill section `bind` reads neither
/// the image nor its length, and the listing condition of blob a22b90c282
/// admits every zero-fill global.
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test:
/// * Apple ld-27037.1 (the system `cc`, the object linked beside a C driver
///   that prints the 8 bytes at `zed`): the unchanged object reads
///   `2a2b2c2d2e2f3031`; the zero-filled one reads `0000000000000000`, with
///   and without `-dead_strip`.
/// * LLD 23.1.1 (`rust-lld -flavor gnu -e _start`, from a rustup toolchain,
///   beside an assembled `_start` that takes `zed`'s address; the output file
///   read, not executed): the unchanged object puts `zed` in `.data` holding
///   `2a2b2c2d2e2f3031`; the zero-filled one in the `SHT_NOBITS` `.bss`,
///   whose bytes are zero.
/// So the linked bytes under `zed` are zeros where the reader lists `zed` as
/// verified against an image that is not.
///
/// FAILS while the reader lists a zero-fill global as verified without
/// comparing its image. A refusal at parse or at bind, or `zed` left out of
/// `verified_globals`, passes.
#[test]
fn a_zero_fill_global_whose_image_is_not_zero_is_not_verified() {
    let listed =
        targets_listing_zed_after(&external_image_global_module(true), turn_into_zero_fill);
    assert!(
        listed.is_empty(),
        "LISTED on {listed:?}: `zed` lies in a zero-fill section, which links as zeros, and the \
         reader lists it as verified against the image 2a2b2c2d2e2f3031 it never compared"
    );
}

/// ADJUDICATION FINDING, fourteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob a22b90c282 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm (whose condition (e) refuses a weak symbol
/// in the record's or the target's section).
///
/// INPUT: the object trust-cg compiles for
/// [`external_image_global_module`]`(false)` (Darwin and Linux, O2), whose
/// immutable global `zed`, external and strong in `M_cg`, has the image
/// [`ZED_IMAGE`] `2a2b2c2d2e2f3031` in `__TEXT,__const` / `.rodata`, with
/// nothing changed but `zed`'s symbol, made a weak definition by
/// [`make_weak_definition`] (Mach-O `N_WEAK_DEF`; ELF `STB_WEAK`). The
/// reader parses and binds it and lists `zed` in `verified_globals`: it
/// compares the bytes after the symbol with the image and never compares a
/// data symbol's binding with the global's `M_cg` linkage.
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test,
/// with a second object that defines a strong `zed` holding
/// `1122334455667788`:
/// * Apple ld-27037.1 (the system `cc`, a C driver printing the 8 bytes at
///   `zed`, and a C file defining `const unsigned char zed[8]`): the
///   unchanged object and the C file do not link (`1 duplicate symbols`);
///   the weak one links and reads `1122334455667788`, with and without
///   `-dead_strip`. Alone it reads `2a2b2c2d2e2f3031`. The same holds for
///   the mutable `zed` in `__DATA,__data`.
/// * LLD 23.1.1 (`rust-lld -flavor gnu -e _start`, beside an assembled
///   `_start` that takes `zed`'s address and an assembled `.rodata` defining
///   a global `zed`; the output file read, not executed): the unchanged
///   object fails with `duplicate symbol: zed`; the weak one links, and `zed`
///   resolves to the other object's `.rodata`, reading `1122334455667788`.
///   The same holds for the mutable `zed` in `.data`.
/// So the linked bytes under `zed` are another object's where the reader
/// lists `zed` as verified against its own image.
///
/// FAILS while the reader lists as verified a global whose symbol a linker
/// may resolve to another object's definition. A refusal at parse or at
/// bind, or `zed` left out of `verified_globals`, passes.
#[test]
fn a_weak_definition_of_a_strong_global_is_not_verified() {
    let listed =
        targets_listing_zed_after(&external_image_global_module(false), make_weak_definition);
    assert!(
        listed.is_empty(),
        "LISTED on {listed:?}: `zed` is a weak definition, which a linker replaces with another \
         object's strong `zed`, and the reader lists it as verified against `M_cg`'s strong \
         external global"
    );
}

// ===========================================================================
// FIFTEENTH ADJUDICATION (2026-11-12): globals listed as verified whose
// linked bytes are not the image, after `verified_global`
// ===========================================================================
//
// Blob d01a775626 lists a data global in `verified_globals` only when its own
// symbol is not weak and its section is ordinary data or ordinary zero-fill
// (`verified_global`). Two Mach-O reader facts, both on the pin bf45acdd08 and
// unchanged by the movement, still let a global be listed whose linked bytes
// are not `M_cg`'s image of it:
// * `bind` reads no `n_desc` bit of a data symbol but the two weak ones, so a
//   STRONG global marked `N_ALT_ENTRY` after a WEAK one in the same section is
//   listed, while the linker treats it as part of the weak definition's piece
//   and discards both when another object overrides the weak one;
// * `parse_macho` names a symbol by its raw name with a leading `_` removed IF
//   there is one, so a defined data symbol spelled without the C prefix is
//   taken as `M_cg`'s external global, while a linker resolves that global's
//   name (`_zed`) elsewhere.

/// `h(x) = x ^ 0x55` (gate removed) beside two immutable EXTERNAL globals,
/// `zed` holding [`ZED_IMAGE`] and `zee` holding [`ZEE_IMAGE`], which
/// trust-cg puts one after the other in `__TEXT,__const` (`zed` at 0x10,
/// `zee` at 0x18 at O2). Nothing reads them; they are external so that a C
/// driver can read the linked bytes under their symbols.
fn two_external_globals_module() -> Module {
    let mut module = leaf_module("h");
    set_gate(&mut module, "h", None);
    for (name, image) in [("zed", &ZED_IMAGE), ("zee", &ZEE_IMAGE)] {
        let id = image_global(&mut module, name, image_bytes(image).collect(), 8);
        module.globals[id.as_usize()].linkage = Linkage::External;
    }
    module
}

/// `zee`'s image: eight non-zero bytes other than [`ZED_IMAGE`]'s.
const ZEE_IMAGE: [u8; 8] = *b"\x41\x42\x43\x44\x45\x46\x47\x48";

/// Parse and bind `o` against `module` for Darwin (static relocation model).
fn bind_darwin(
    module: &Module,
    o: &[u8],
) -> Result<
    trust_cg_bridge::compiled_object::ObjectLayout,
    trust_cg_bridge::compiled_object::ObjectRefusal,
> {
    use trust_cg_bridge::compiled_object::{
        CompiledObject, ObjectExpectations, ObjectFormat, ObjectLayout,
    };
    CompiledObject::parse(o).and_then(|parsed| {
        let expect =
            ObjectExpectations::from_module(module, ObjectFormat::MachO, RelocationModel::Static)?;
        ObjectLayout::bind(parsed, &expect)
    })
}

/// ADJUDICATION FINDING, fifteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob d01a775626 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm (whose condition (e) refuses any weak
/// symbol in the record's or the target's section).
///
/// INPUT: the Mach-O object trust-cg compiles for
/// [`two_external_globals_module`] (Darwin, O2; its header sets
/// `MH_SUBSECTIONS_VIA_SYMBOLS`), with nothing changed but two `n_desc`
/// words: `_zed` (at 0x10) gains `N_WEAK_DEF` (0x80), and `_zee` (at 0x18,
/// strong, external) gains `N_ALT_ENTRY` (0x200), which tells the linker
/// that `_zee` starts no piece of its own but belongs to `_zed`'s. The
/// reader parses and binds it and lists `zee` in `verified_globals`:
/// `verified_global` asks whether `zee`'s OWN symbol is weak, and no reader
/// line reads `N_ALT_ENTRY`.
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test,
/// with a C file defining a strong `const unsigned char zed[8]` =
/// `8877665544332211`, and a C driver printing the 8 bytes at `zed` and at
/// `zee`:
/// * Apple ld-27037.1 (the system `cc`): the unchanged object and the C file
///   do not link (`1 duplicate symbols`). The patched one links, with and
///   without `-dead_strip`, and prints `zed` = `8877665544332211` and `zee` =
///   `000000010000001c`, not [`ZEE_IMAGE`] `4142434445464748`: the linker
///   discarded `_zed`'s piece, `_zee`'s bytes with it, and left `_zee` at
///   eight bytes past the other object's `zed`. Alone the patched object
///   prints both images. With only `N_WEAK_DEF` on `_zed` (no
///   `N_ALT_ENTRY`), `zee` prints `4142434445464748`.
/// * LLD 23.1.1 (`rust-lld -flavor darwin`, from a rustup toolchain, beside
///   an assembled `_start` taking both addresses; the output read, not run)
///   keeps `zee`'s bytes `4142434445464748` in the same link: the two
///   linkers differ, and the reader follows neither's rule.
/// So under Apple ld the linked bytes under `zee` are not its image, where
/// the reader lists `zee` as verified.
///
/// FAILS while the reader lists as verified a global that a linker may
/// discard with a weak definition's piece. A refusal at parse or at bind, or
/// `zee` left out of `verified_globals`, passes.
#[test]
fn a_strong_global_in_a_weak_definitions_piece_is_not_verified() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    const N_WEAK_DEF: u16 = 0x80;
    const N_ALT_ENTRY: u16 = 0x200;
    let module = two_external_globals_module();
    let object = compile(&module, DARWIN_T.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let mut listed = bind_darwin(&module, &object)
        .unwrap_or_else(|e| panic!("the unchanged object is refused: {e}"))
        .verified_globals;
    listed.sort();
    assert_eq!(listed, ["zed", "zee"], "the unchanged object");
    let parsed = CompiledObject::parse(&object).expect("the object parses");
    let symbol = |name: &str| {
        parsed
            .symbols
            .iter()
            .find(|y| y.name == name && y.section.is_some())
            .unwrap_or_else(|| panic!("no defined `{name}`"))
    };
    let (zed, zee) = (symbol("zed"), symbol("zee"));
    assert!(
        zed.section == zee.section && zed.value < zee.value,
        "the fixture needs `zed` before `zee` in one section: {zed:?} {zee:?}"
    );
    let mut patched = object.clone();
    for (index, bit) in [(zed.index, N_WEAK_DEF), (zee.index, N_ALT_ENTRY)] {
        let e = macho_symbol_entry(&patched, index);
        let desc = u16::from_le_bytes(patched[e + 6..e + 8].try_into().unwrap()) | bit;
        patched[e + 6..e + 8].copy_from_slice(&desc.to_le_bytes());
    }
    if let Ok(layout) = bind_darwin(&module, &patched) {
        assert!(
            !layout.verified_globals.iter().any(|g| g == "zee"),
            "LISTED: `zee` is an alternate entry of the weak definition `zed`'s piece, which \
             Apple ld discards with `zee`'s bytes when another object defines `zed`, and the \
             reader lists `zee` as verified against {ZEE_IMAGE:02x?}"
        );
    }
}

/// ADJUDICATION FINDING, fifteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob d01a775626 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm (whose record and target are LOCAL).
///
/// INPUT: the Mach-O object trust-cg compiles for
/// [`external_image_global_module`]`(false)` (Darwin, O2), whose immutable
/// global `zed`, external in `M_cg`, has the image [`ZED_IMAGE`]
/// `2a2b2c2d2e2f3031` under the symbol `_zed`, with nothing changed but that
/// symbol's `n_strx`, moved one byte on so that its name reads `zed`. The
/// reader parses and binds it and lists `zed` in `verified_globals`:
/// `parse_macho` names a symbol by its raw name with a leading `_` stripped
/// when there is one and kept whole when there is not, so `zed` and `_zed`
/// both name `M_cg`'s `zed`. (The call path already refuses an undefined
/// callee spelled without `_`; a defined data symbol has no such check.)
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test,
/// with Apple ld-27037.1 (the system `cc`) and a C driver printing the 8
/// bytes at `zed` (the C symbol `_zed`): the unchanged object links alone and
/// prints `2a2b2c2d2e2f3031`. The patched one alone does not link
/// (`Undefined symbols: "_zed"`); beside a C file defining `const unsigned
/// char zed[8]` = `8877665544332211` it links, with and without
/// `-dead_strip`, and prints `8877665544332211`, where the unchanged object
/// and that file fail with `1 duplicate symbols`.
/// So the linked program's `zed`, the external global `M_cg` defines, is
/// another object's bytes, where the reader lists `zed` as verified.
///
/// FAILS while the reader takes a Mach-O data symbol spelled without the C
/// prefix as `M_cg`'s external global and lists it. A refusal at parse or at
/// bind, or `zed` left out of `verified_globals`, passes.
#[test]
fn a_mach_o_global_spelled_without_the_c_prefix_is_not_verified() {
    use trust_cg_bridge::compiled_object::CompiledObject;
    let module = external_image_global_module(false);
    let object = compile(&module, DARWIN_T.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let layout =
        bind_darwin(&module, &object).unwrap_or_else(|e| panic!("the unchanged object: {e}"));
    assert_eq!(layout.verified_globals, ["zed"], "the unchanged object");
    let index = CompiledObject::parse(&object)
        .expect("the object parses")
        .symbols
        .iter()
        .find(|y| y.raw_name == "_zed" && y.section.is_some())
        .expect("a defined `_zed`")
        .index;
    let mut patched = object.clone();
    let e = macho_symbol_entry(&patched, index);
    let strx = u32::from_le_bytes(patched[e..e + 4].try_into().unwrap());
    patched[e..e + 4].copy_from_slice(&(strx + 1).to_le_bytes());
    let raw = CompiledObject::parse(&patched)
        .map(|p| p.symbols.iter().any(|y| y.raw_name == "zed"))
        .unwrap_or(true);
    assert!(raw, "the patch did not rename `_zed` to `zed`");
    if let Ok(layout) = bind_darwin(&module, &patched) {
        assert!(
            !layout.verified_globals.iter().any(|g| g == "zed"),
            "LISTED: the symbol is `zed`, not `_zed`, so a linker resolves `M_cg`'s external \
             `zed` to another object's definition, and the reader lists `zed` as verified"
        );
    }
}

// ===========================================================================
// SIXTEENTH ADJUDICATION (2026-11-12): an object the reader binds whose
// definitions a linker does not give the program
// ===========================================================================
//
// Blob ec5cbdef32 lists a data global in `verified_globals` when its symbol and
// every symbol of its section are not weak and its section is ordinary data
// (or ordinary zero-fill with an all-zero image), and it refuses a Mach-O
// external definition spelled without `_`. Two reader facts, both on the pin
// bf45acdd08 and unchanged by the movement, still let the program a linker
// builds take `M_cg`'s external names from another object while the reader
// lists or proves this object's definitions under them:
// * `bind` never compares a data symbol's binding with its `M_cg` linkage
//   (it refuses a weak one only), so a LOCAL definition of a global `M_cg`
//   makes external is listed, while a linker resolves every other object's
//   reference to that name elsewhere;
// * `parse_macho` reads the Mach-O header's `cputype` but not its
//   `cpusubtype`, and Apple ld IGNORES an object of a subtype other than the
//   one it links for (a warning, not an error), so every definition in it is
//   absent from the program and another object's answers to its names.

/// Parse and bind `o` against `module` for `format` (static relocation model).
fn bind_as(
    module: &Module,
    o: &[u8],
    format: trust_cg_bridge::compiled_object::ObjectFormat,
) -> Result<
    trust_cg_bridge::compiled_object::ObjectLayout,
    trust_cg_bridge::compiled_object::ObjectRefusal,
> {
    use trust_cg_bridge::compiled_object::{CompiledObject, ObjectExpectations, ObjectLayout};
    CompiledObject::parse(o).and_then(|parsed| {
        let expect = ObjectExpectations::from_module(module, format, RelocationModel::Static)?;
        ObjectLayout::bind(parsed, &expect)
    })
}

/// ELF: give the GLOBAL symbol `name` LOCAL binding and keep the symbol table
/// well formed: it is moved to the first global slot (`.symtab`'s `sh_info`),
/// swapped with the symbol there, `sh_info` is raised by one, and every
/// relocation naming either of the two is renumbered.
fn elf_make_symbol_local(o: &mut [u8], name: &str) {
    let rd16 = |o: &[u8], at: usize| u16::from_le_bytes(o[at..at + 2].try_into().unwrap());
    let rd32 = |o: &[u8], at: usize| u32::from_le_bytes(o[at..at + 4].try_into().unwrap());
    let rd64 = |o: &[u8], at: usize| u64::from_le_bytes(o[at..at + 8].try_into().unwrap());
    let shoff = rd64(o, 40) as usize;
    let shnum = usize::from(rd16(o, 60));
    let headers: Vec<usize> = (0..shnum).map(|i| shoff + i * 64).collect();
    let symtab = *headers.iter().find(|h| rd32(o, **h + 4) == 2).expect("a .symtab");
    let (off, size) = (rd64(o, symtab + 24) as usize, rd64(o, symtab + 32) as usize);
    let strtab = rd64(o, shoff + rd32(o, symtab + 40) as usize * 64 + 24) as usize;
    let first_global = rd32(o, symtab + 44) as usize;
    let sym_name = |o: &[u8], k: usize| {
        let at = strtab + rd32(o, off + k * 24) as usize;
        let end = at + o[at..].iter().position(|b| *b == 0).unwrap();
        String::from_utf8(o[at..end].to_vec()).unwrap()
    };
    let k = (0..size / 24).find(|k| sym_name(o, *k) == name).expect("the symbol");
    assert!(k >= first_global && o[off + k * 24 + 4] >> 4 == 1, "`{name}` is GLOBAL");
    let (a, b) = (off + first_global * 24, off + k * 24);
    if a != b {
        let entry_a: Vec<u8> = o[a..a + 24].to_vec();
        o.copy_within(b..b + 24, a);
        o[b..b + 24].copy_from_slice(&entry_a);
    }
    o[a + 4] &= 0x0f; // STB_LOCAL, type kept
    o[symtab + 44..symtab + 48].copy_from_slice(&(first_global as u32 + 1).to_le_bytes());
    let relas: Vec<usize> = headers.iter().copied().filter(|h| rd32(o, *h + 4) == 4).collect();
    for h in relas {
        let (ro, rs) = (rd64(o, h + 24) as usize, rd64(o, h + 32) as usize);
        for e in (ro..ro + rs).step_by(24) {
            let info = rd64(o, e + 8);
            let s = (info >> 32) as usize;
            let s = if s == k {
                first_global
            } else if s == first_global {
                k
            } else {
                s
            };
            let info = ((s as u64) << 32) | (info & 0xffff_ffff);
            o[e + 8..e + 16].copy_from_slice(&info.to_le_bytes());
        }
    }
}

/// ADJUDICATION FINDING, sixteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob ec5cbdef32 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect, not one of the
/// location-record admission's arm (whose record and target must be LOCAL
/// and are compared as this object's bytes, which is what a pointer to a
/// local symbol leads to).
///
/// INPUT: the object trust-cg compiles for
/// [`external_image_global_module`]`(false)` (O2), whose immutable global
/// `zed`, EXTERNAL in `M_cg`, has the image [`ZED_IMAGE`] `2a2b2c2d2e2f3031`,
/// with nothing changed but the binding of `zed`'s symbol, made LOCAL:
/// * Mach-O (Darwin): `_zed`'s `n_type` loses `N_EXT` (0x0f -> 0x0e);
/// * ELF (Linux): `zed` becomes STB_LOCAL, moved to `.symtab`'s first global
///   slot with `sh_info` raised past it ([`elf_make_symbol_local`]), so the
///   table stays in the order the format requires.
/// The reader parses and binds each and lists `zed` in `verified_globals`:
/// no line of `bind` compares a data symbol's binding with `M_cg`'s linkage
/// (`verified_global` refuses only a weak one).
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test:
/// * Apple ld-27037.1 (the system `cc`), with a C driver printing the 8 bytes
///   at `zed` (`extern const unsigned char zed[8]`): the unchanged object
///   links alone and prints `2a2b2c2d2e2f3031`, and beside a C file defining
///   `zed` = `8877665544332211` fails with `1 duplicate symbols`. The Mach-O
///   object above alone does not link (`Undefined symbols: "_zed"`); beside
///   that C file it links, with and without `-dead_strip`, and prints
///   `8877665544332211`.
/// * LLD 23.1.1 (`rust-lld -flavor gnu -static`, from a rustup toolchain; the
///   output read with objdump, not run), with a C object (clang
///   `-target aarch64-unknown-linux-gnu`) holding `zed_ptr = zed` and one
///   defining `zed` = `8877665544332211`, on the ELF object above (the same
///   patch, made by a script outside the tree): the unchanged object fails
///   with `duplicate symbol: zed`; the patched one alone fails with
///   `undefined symbol: zed`, and beside the C object links with `zed_ptr`
///   pointing at the C object's bytes `8877665544332211`, the patched
///   object's `2a2b2c2d2e2f3031` kept under its local `zed`.
/// So the linked program's `zed`, the external global `M_cg` defines, is
/// another object's bytes, where the reader lists `zed` as verified.
///
/// FAILS while the reader lists a global whose symbol's binding is not the
/// one `M_cg`'s linkage gives it. A refusal at parse or at bind, or `zed` left
/// out of `verified_globals`, passes.
#[test]
fn a_global_whose_symbol_is_local_is_not_verified() {
    use trust_cg_bridge::compiled_object::{CompiledObject, ObjectFormat, SymbolBinding};
    const N_EXT: u8 = 0x01;
    let module = external_image_global_module(false);
    let mut listed = Vec::new();
    for (target, format) in [(DARWIN_T, ObjectFormat::MachO), (LINUX_T, ObjectFormat::Elf)] {
        let object = compile(&module, target.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
        let layout = bind_as(&module, &object, format)
            .unwrap_or_else(|e| panic!("{format:?}: the unchanged object: {e}"));
        assert_eq!(layout.verified_globals, ["zed"], "{format:?}: the unchanged object");
        let index = CompiledObject::parse(&object)
            .expect("the object parses")
            .symbols
            .iter()
            .find(|y| y.name == "zed" && y.section.is_some())
            .expect("a defined `zed`")
            .index;
        let mut patched = object.clone();
        match format {
            ObjectFormat::MachO => {
                let e = macho_symbol_entry(&patched, index);
                assert_ne!(patched[e + 4] & N_EXT, 0, "`_zed` is external");
                patched[e + 4] &= !N_EXT;
            }
            ObjectFormat::Elf => elf_make_symbol_local(&mut patched, "zed"),
        }
        let local = CompiledObject::parse(&patched).map_or(true, |p| {
            p.symbols.iter().any(|y| {
                y.name == "zed" && y.section.is_some() && y.binding == SymbolBinding::Local
            })
        });
        assert!(local, "{format:?}: the patch did not make `zed` local");
        if bind_as(&module, &patched, format)
            .is_ok_and(|layout| layout.verified_globals.iter().any(|g| g == "zed"))
        {
            listed.push(format);
        }
    }
    assert!(
        listed.is_empty(),
        "LISTED on {listed:?}: `zed`'s symbol is LOCAL while M_cg's `zed` is external, so a \
         linker resolves the program's `zed` to another object's definition, and the reader \
         lists `zed` as verified"
    );
}

/// ADJUDICATION FINDING, sixteenth adjudication (2026-11-12). RED against
/// compiled_object.rs blob ec5cbdef32 and, MEASURED, against the pin
/// bf45acdd08 (the pin blob with only the blob's `all_padding` helper
/// appended so the crate builds): a pre-existing defect of the whole Mach-O
/// reader, not one of the location-record admission's arm (whose record and
/// target are LOCAL, so no other object can name them, and an ignored
/// object's record is in no image).
///
/// INPUT: the Mach-O object trust-cg compiles for
/// [`external_image_global_module`]`(false)` (Darwin, O2): the External
/// leaf `h(x) = x ^ 0x55` (gate removed), kernel-proved and shipped under
/// strict, and the immutable external `zed` holding [`ZED_IMAGE`], listed as
/// verified; with nothing changed but the header's `cpusubtype` (offset 8),
/// CPU_SUBTYPE_ARM64_ALL (0) -> CPU_SUBTYPE_ARM64_V8 (1). The pin's
/// `parse_macho` checked the magic, `cputype` and `filetype` and never read
/// `cpusubtype`, so it bound this object as before; the reader now refuses
/// any cpusubtype but CPU_SUBTYPE_ARM64_ALL (refusal (aa)).
///
/// WHAT A LINKER DOES, MEASURED BY HAND on 2026-11-12 and run by no test,
/// with Apple ld-27037.1 (the system `cc`, linking for arm64) and a C driver
/// printing the bytes at `zed` and `h(5)`: the unchanged object links alone
/// and prints `2a2b2c2d2e2f3031 h(5)=0x50`, and beside a C file defining `zed`
/// = `8877665544332211` and `h(x) = x + 1` fails with duplicate symbols. The
/// patched object draws `ld: warning: ignoring file '..': found architecture
/// 'arm64', required architecture 'arm64'`: alone it does not link
/// (`Undefined symbols`); beside that C file it links, with and without
/// `-dead_strip`, and prints `8877665544332211 h(5)=0x6`. Subtypes 2
/// (`arm64e.old`), 0x80000002 (`arm64e`) and 3 (`arm64.x1`) are ignored the
/// same way. (The eleventh adjudication's hand runs recorded that LLD
/// 23.1.1 links such an object unchanged; this one did not repeat them.)
/// So the program's `h` and `zed`, the external definitions `M_cg` gives,
/// are another object's, where the gate proves `h`, ships it under strict and
/// lists `zed` as verified.
///
/// FAILS while the reader binds a Mach-O object of a CPU subtype the linker
/// does not link. A refusal at parse or at bind, or `h` left unproved, not
/// shipped under strict and `zed` left out of `verified_globals`, passes.
#[test]
fn a_mach_o_object_of_another_cpu_subtype_proves_and_lists_nothing() {
    const CPU_SUBTYPE_ARM64_V8: u32 = 1;
    let module = external_image_global_module(false);
    let object = compile(&module, DARWIN_T.triple(), trust_cg_codegen::pipeline::OptLevel::O2);
    let fx = Fixture::with_object(module.clone(), object.clone(), DARWIN_T.triple());
    let report = fx.report();
    assert!(kernel_proved(&report, "h"), "the unchanged object: {}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", explain(&report));
    let layout =
        bind_darwin(&module, &object).unwrap_or_else(|e| panic!("the unchanged object: {e}"));
    assert_eq!(layout.verified_globals, ["zed"], "the unchanged object");
    assert_eq!(u32::from_le_bytes(object[8..12].try_into().unwrap()), 0, "CPU_SUBTYPE_ARM64_ALL");
    let patched = fx.patched(|o| o[8..12].copy_from_slice(&CPU_SUBTYPE_ARM64_V8.to_le_bytes()));
    let listed = bind_darwin(&module, &patched.object)
        .is_ok_and(|layout| layout.verified_globals.iter().any(|g| g == "zed"));
    let (proved, strict) = patched.verify().map_or((false, false), |report| {
        (kernel_proved(&report, "h"), report.ships(EmitPolicy::StrictProvenOnly).is_ok())
    });
    assert!(
        !listed && !proved && !strict,
        "BOUND: Apple ld ignores an object of cpusubtype 1 when it links arm64, so the \
         program's `zed` and `h` are another object's (h(5) = 0x6, not 0x50); the reader lists \
         `zed` as verified: {listed}, the gate proves `h`: {proved}, strict ships: {strict}"
    );
}
