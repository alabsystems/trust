//! BOOL-RET-EDGE-1 withdrawal: own-definition C2 remains kernel checked,
//! while every Bool call edge stays Unknown pending a Lean-owned relation.
//!
//! A callee's C1/C2 proof does not prove caller state transport. Preserve all
//! original fixture cells and byte/producer mutants under the precise refusal. The fixture is ladder rung s11: `h` (Rust, `u64 -> bool`,
//! `icmp ne (and a, 4), 0`) called by `rung` (C, `u64 -> u64`), which branches
//! on the result. Its own compile helper (u16_tests.rs precedent) compiles for
//! both triples, at O0 and O3.

use std::sync::Arc;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_lower::RelocationModel as CgRelocationModel;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst};
use trust_ir::value::FuncId;
use trust_ir::{Linkage, StructPassingPolicy, TargetInfo};

use super::super::{
    BOOL_C2, CerReport, FunctionCertificate, Grade, PlacementRefusal, ProducerModule, Signature,
    bool_range_decision, check_placement,
};
use super::*;
use crate::compiled_object::RelocationModel;
use crate::verify_output::{Discharge, EmitPolicy, OutputVerdict};

#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;

const H: &str = "h";
const RUNG: &str = "rung";
/// A caller that uses `h`'s result as a number: `h(a) as u64`.
const WIDEN: &str = "widen";
const OPTS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O3];
/// `discharge_under`'s O4 text for a function with a result.
const ORDINARY_O4: &str = "the result equals the IR's wherever the IR returns";
/// `Source::read`'s refusal of a `bool` result (`source_memory::width`).
const LEAF_REFUSAL: &str = "leaf source is not one unconditional scalar call-free returning block";

const MOV_W0_2: u32 = 0x5280_0040; // mov w0,#2
const MVN_W0: u32 = 0x2a20_03e0; // mvn w0,w0
const AND_X0_4: u32 = 0x927e_0000; // and x0,x0,#4

fn bool_ret() -> ReturnPlace {
    ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::Zext })
}

/// What `h` computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Callee {
    /// `icmp ne (and a, 4), 0`: the s11 callee, a 0/1 carrier.
    Mask,
    /// `Cast Trunc u64 -> Bool`: the carrier is a[31:0], not 0/1 (F4 (a)).
    Trunc,
    /// `Const { Bool, Int(2) }`: the carrier is 2 (F4 (b)).
    Two,
}

fn module(callee: Callee, h_conv: CallingConv) -> Module {
    let mut builder = ModBuilder::new("s11_bool_ret");
    let h = define_h(&mut builder, callee);
    let word = builder.sig(&[Ty::U64], Some(Ty::U64));
    let rung = builder.define(RUNG, word, Linkage::External, |f| {
        let flag = f.call(h, &[f.p(0)]);
        let (yes, _) = f.block(&[]);
        let (no, _) = f.block(&[]);
        f.cond_br(flag, yes, &[], no, &[]);
        f.switch_to(yes);
        let nine = f.konst(Ty::U64, 9);
        f.ret(nine);
        f.switch_to(no);
        let four = f.konst(Ty::U64, 4);
        f.ret(four);
    });
    let mut module = builder.finish();
    module.functions[h.as_usize()].calling_conv = h_conv;
    module.functions[rung.as_usize()].calling_conv = CallingConv::C;
    module
}

/// `h` (Rust) and `widen` (C, `u64 -> u64`), which returns `h(a) as u64`
/// (`Cast ZExt Bool -> U64`): the bool result used as a number, where a 0/1
/// carrier and, for example, a 0/-1 one differ (the A3 binding is zext32).
fn widen_module() -> Module {
    let mut builder = ModBuilder::new("s11_bool_widen");
    let h = define_h(&mut builder, Callee::Mask);
    let word = builder.sig(&[Ty::U64], Some(Ty::U64));
    let widen = builder.define(WIDEN, word, Linkage::External, |f| {
        let flag = f.call(h, &[f.p(0)]);
        let wide = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::Bool,
            dst_ty: Ty::U64,
            operand: flag,
        });
        f.ret(wide);
    });
    let mut module = builder.finish();
    module.functions[h.as_usize()].calling_conv = CallingConv::Rust;
    module.functions[widen.as_usize()].calling_conv = CallingConv::C;
    module
}

/// `h: u64 -> bool` computing `callee`.
fn define_h(builder: &mut ModBuilder, callee: Callee) -> FuncId {
    let predicate = builder.sig(&[Ty::U64], Some(Ty::Bool));
    builder.define(H, predicate, Linkage::External, |f| {
        let value = match callee {
            Callee::Mask => {
                let four = f.konst(Ty::U64, 4);
                let masked = f.bin(BinOp::And, Ty::U64, f.p(0), four);
                let zero = f.konst(Ty::U64, 0);
                f.icmp(ICmpOp::Ne, Ty::U64, masked, zero)
            }
            Callee::Trunc => f.push_inst(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U64,
                dst_ty: Ty::Bool,
                operand: f.p(0),
            }),
            Callee::Two => f.konst(Ty::Bool, 2),
        };
        f.ret(value);
    })
}

/// `module` stating `triple` as its target.
fn targeted_at(mut module: Module, triple: &str) -> Module {
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}

fn compile_with(
    module: Module,
    opt: OptLevel,
    triple: &str,
    never_inline: &[&str],
    model: RelocationModel,
) -> Fixture {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    let module = targeted_at(module, triple);
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            relocation_model: match model {
                RelocationModel::Static => CgRelocationModel::Static,
                RelocationModel::Pie => CgRelocationModel::Pie,
                RelocationModel::Pic => CgRelocationModel::Pic,
            },
            never_inline: never_inline.iter().map(|s| (*s).into()).collect(),
            ..Default::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap_or_else(|e| panic!("{triple} {opt:?}: Compiler::compile failed: {e}"))
    .object_code;
    let mut fixture = Fixture::with_object(module, object, triple);
    fixture.model = model;
    fixture
}

/// The module-local compile helper (F4): `h` is never inlined, so `rung`
/// keeps its `bl h`.
fn compile(module: Module, opt: OptLevel, triple: &str, never_inline: &[&str]) -> Fixture {
    compile_with(module, opt, triple, never_inline, RelocationModel::Static)
}

fn s11(opt: OptLevel, triple: &str) -> Fixture {
    compile(module(Callee::Mask, CallingConv::Rust), opt, triple, &[H])
}

/// The same object, gated against another producer `h` (spec side), with
/// `h`'s bytes patched by `bytes`: its words become `nop`s, then `bytes` writes.
fn with_callee(
    good: &Fixture,
    callee: Callee,
    bytes: impl FnOnce(&mut Vec<u8>, &[(u64, u32)]),
) -> Fixture {
    let mut object = good.object.clone();
    let words = function_words(&object, H);
    assert!(words.len() >= 2, "{}", disassemble(&good.object));
    for (offset, _) in &words {
        patch_word(&mut object, *offset, NOP);
    }
    bytes(&mut object, &words);
    let mut fixture = Fixture::with_object(
        targeted_at(module(callee, CallingConv::Rust), &good.triple),
        object,
        &good.triple,
    );
    fixture.model = good.model;
    fixture
}

fn save(label: &str, fixture: &Fixture, report: &CerReport) {
    if let Some(out) = std::env::var_os("TRUST_CER_BOOL_EDGE_OUTPUT_DIR") {
        let path = std::path::PathBuf::from(out).join(label);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("object.o"), &fixture.object).unwrap();
        std::fs::write(path.join("certificates.json"), report.to_json()).unwrap();
        std::fs::write(path.join("disassembly.txt"), disassemble(&fixture.object)).unwrap();
    }
}

fn certificate<'r>(report: &'r CerReport, symbol: &str) -> &'r FunctionCertificate {
    report.certificate(symbol).unwrap_or_else(|| panic!("no certificate for `{symbol}`"))
}

fn closed(report: &CerReport, symbol: &str) -> bool {
    report.closure.closed_proven.iter().any(|s| s == symbol)
}

fn closed_kernel(report: &CerReport, symbol: &str) -> bool {
    report.closure.closed_kernel.iter().any(|s| s == symbol)
}

/// The original fixture still contains its callee and machine call. Neither
/// custody nor the callee's own C2 grants the missing semantic edge relation.
fn assert_bool_edge_withdrawn(report: &CerReport, symbol: &str, why: &str) {
    let caller = certificate(report, symbol);
    assert!(matches!(caller.verdict, OutputVerdict::Unknown { .. }), "{why}");
    assert_eq!(caller.obligations.o3_events.grade, Grade::Unknown, "{why}");
    assert!(caller.obligations.o3_events.detail.contains("BOOL-RET-EDGE-1 withdrawn"), "{why}");
    assert!(caller.obligations.o3_events.detail.contains("Lean-owned"), "{why}");
    assert!(!caller.is_kernel_proved(), "{why}");
    assert!(!closed(report, symbol) && !closed_kernel(report, symbol), "{why}");
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err(), "{why}");
    assert!(report.ships(EmitPolicy::AllowUnknown).is_ok(), "{why}");
}

/// Every step-(5) conjunction the gate built, with the symbol it was built for.
type Step5 = Vec<(String, Vec<(Formula, Formula)>)>;

/// `fixture.report()` with the step-(5) conjunctions recorded. The recorder is
/// thread-local, so the gate runs and records on one thread, with the 8 MiB
/// stack `Fixture::verify` gives it.
fn report_recording_step5(fixture: &Fixture) -> (CerReport, Step5) {
    let (verdict, recorded) = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                super::super::step5_record::record(|| {
                    super::super::verify_compiled_module(&super::super::CerInput {
                        m_cg: &fixture.m_cg,
                        producers: &fixture.producers,
                        bodies: &fixture.bodies,
                        placements: &fixture.placements,
                        object: &fixture.object,
                        relocation_model: fixture.model,
                    })
                })
            })
            .expect("spawn the gate thread")
            .join()
            .expect("the gate thread panicked")
    });
    let report = verdict.unwrap_or_else(|e| {
        panic!("{}: object refused: {e}\n{}", fixture.triple, disassemble(&fixture.object))
    });
    (report, recorded)
}

/// The `uxtb Wd,Ws` that reads `h`'s result after `rung`'s `bl`, as its
/// offset, destination and source.
fn result_extract(object: &[u8]) -> (u64, u32, u32) {
    result_extract_in(object, RUNG)
}

/// The `uxtb Wd,Ws` that reads `h`'s result after `caller`'s `bl`.
fn result_extract_in(object: &[u8], caller: &str) -> (u64, u32, u32) {
    let words = function_words(object, caller);
    let call = words
        .iter()
        .find(|(_, word)| is_bl(*word))
        .unwrap_or_else(|| panic!("`{caller}` keeps no `bl`:\n{}", disassemble(object)))
        .0;
    let (offset, word) = words
        .iter()
        .copied()
        .find(|(offset, word)| {
            *offset > call
                && word & 0xffc0_0000 == 0x5300_0000
                && (word >> 16) & 63 == 0
                && (word >> 10) & 63 == 7
        })
        .unwrap_or_else(|| panic!("no `uxtb` after `{caller}`'s call:\n{}", disassemble(object)));
    (offset, word & 31, (word >> 5) & 31)
}

// ---------------------------------------------------------------------------
// Unit: the carrier, the shape, the tail
// ---------------------------------------------------------------------------

/// Own-definition shape recognition never supplies caller transport.
#[test]
fn an_own_bool_shape_is_not_a_callee_transport_proof() {
    assert!(is_bool_result(&bool_ret()));
    let placement =
        FnPlacement { params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))], ret: bool_ret() };
    for conv in [CallingConv::Rust, CallingConv::C] {
        let module = Module::new("own_bool_is_not_transport");
        assert!(Plan::new(&module, conv, &[Ty::U64], &[Ty::Bool], &placement, true).is_ok());
        assert!(Plan::new(&module, conv, &[Ty::U64], &[Ty::Bool], &placement, false).is_err());
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn bool_tail_shape_does_not_grant_call_transport() {
    let placement =
        FnPlacement { params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))], ret: bool_ret() };
    // A refusal-only tail guard may succeed structurally, but it is never
    // proof of caller transport and cannot widen call placement.
    assert!(check_tail_transport(&bool_ret(), &bool_ret()).is_ok());
    for triple in BOTH {
        let module = targeted_at(module(Callee::Mask, CallingConv::Rust), triple);
        let signature = (vec![Ty::U64], vec![Ty::Bool], false);
        assert!(matches!(
            check_placement(&module, &signature, CallingConv::Rust, &placement, false),
            Err(PlacementRefusal::Unplaced(_))
        ));
    }
}

/// Preserve own-definition placement checks and every prior shape mutation.
/// No calling convention, result slot or width earns the missing call relation.
#[test]
fn own_bool_placement_does_not_authorize_a_call_edge() {
    let m = Module::new("bool_edge_shapes");
    let place = |ret: ReturnPlace| FnPlacement {
        params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))],
        ret,
    };
    let boolean: Signature = (vec![Ty::U64], vec![Ty::Bool], false);
    let exact = place(bool_ret());
    assert_eq!(check_placement(&m, &boolean, CallingConv::Rust, &exact, true), Ok(()));
    assert!(matches!(
        check_placement(&m, &boolean, CallingConv::Rust, &exact, false),
        Err(PlacementRefusal::Unplaced(_))
    ));
    assert!(check_placement(&m, &boolean, CallingConv::C, &exact, false).is_err());

    let word: Signature = (vec![Ty::U64], vec![Ty::U32], false);
    assert!(check_placement(&m, &word, CallingConv::Rust, &exact, false).is_err());
    assert!(check_placement(&m, &word, CallingConv::Rust, &exact, true).is_err());

    let narrow =
        place(ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 8, ext: AbiExt::Zext }));
    assert!(check_placement(&m, &boolean, CallingConv::Rust, &narrow, false).is_err());
    assert!(check_placement(&m, &boolean, CallingConv::Rust, &narrow, true).is_err());

    let second = place(ReturnPlace::Scalar(ScalarPlace {
        slot: Slot::Gpr(1),
        width: 32,
        ext: AbiExt::Zext,
    }));
    assert!(check_placement(&m, &boolean, CallingConv::Rust, &second, false).is_err());

    // A bool PARAMETER never takes the result exemption.
    let parameter: Signature = (vec![Ty::Bool], vec![], false);
    let zext_parameter = FnPlacement {
        params: vec![ParamPlace::Scalar(ScalarPlace {
            slot: Slot::Gpr(0),
            width: 32,
            ext: AbiExt::Zext,
        })],
        ret: ReturnPlace::Void,
    };
    assert!(check_placement(&m, &parameter, CallingConv::Rust, &zext_parameter, true).is_err());
}

/// Removing extension metadata must not reopen the missing Bool relation.
#[test]
fn stripped_bool_call_placement_is_refused() {
    let module = Module::new("stripped_bool_call_extension");
    let signature: Signature = (vec![Ty::U64], vec![Ty::Bool], false);
    let placement = FnPlacement {
        params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))],
        ret: ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::None }),
    };
    let outcomes: Vec<_> = [CallingConv::Rust, CallingConv::C]
        .into_iter()
        .map(|conv| {
            assert_eq!(check_placement(&module, &signature, conv, &placement, true), Ok(()));
            (conv, check_placement(&module, &signature, conv, &placement, false).is_err())
        })
        .collect();
    assert!(outcomes.iter().all(|(_, refused)| *refused), "{outcomes:?}");
}

/// Direct plan users must receive the same refusal before generic transport.
#[test]
fn stripped_bool_direct_call_plan_is_refused() {
    let module = Module::new("stripped_bool_direct_plan");
    let placement = FnPlacement {
        params: vec![ParamPlace::Scalar(ScalarPlace::gpr(0, 64))],
        ret: ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::None }),
    };
    let outcomes: Vec<_> = [CallingConv::Rust, CallingConv::C]
        .into_iter()
        .map(|conv| {
            assert!(Plan::new(&module, conv, &[Ty::U64], &[Ty::Bool], &placement, true).is_ok());
            (conv, Plan::new(&module, conv, &[Ty::U64], &[Ty::Bool], &placement, false).is_err())
        })
        .collect();
    assert!(outcomes.iter().all(|(_, refused)| *refused), "{outcomes:?}");
}

/// Bool refusal cannot demote an unknown variadic split from Blocked/Refuted
/// to an ordinary Unknown. Known C prefixes keep their existing variadic reason.
#[test]
fn bool_call_refusal_preserves_variadic_split_precedence() {
    let module = Module::new("bool_variadic_precedence");
    for conv in [CallingConv::Rust, CallingConv::C] {
        for fixed in [0, 1] {
            for is_definition in [false, true] {
                let signature = (vec![Ty::U64; fixed], vec![Ty::Bool], true);
                let placement = FnPlacement {
                    params: (0..fixed)
                        .map(|r| ParamPlace::Scalar(ScalarPlace::gpr(r as u8, 64)))
                        .collect(),
                    ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 32)),
                };
                let refusal = check_placement(&module, &signature, conv, &placement, is_definition)
                    .unwrap_err();
                if fixed == 0 || conv == CallingConv::Rust {
                    assert!(matches!(&refusal, PlacementRefusal::UnknownSplit(_)));
                    assert_eq!(refusal.grade("bool callee", |e| e).grade, Grade::Refuted);
                } else {
                    assert_eq!(refusal, PlacementRefusal::Unplaced("variadic".into()));
                    assert_eq!(refusal.grade("bool callee", |e| e).grade, Grade::Unknown);
                }
            }
        }
    }
}

/// Exercise the actual object analysis, retaining both functions and changing
/// only the Bool result's extension metadata. No caller conjunction is built.
#[test]
fn stripped_bool_call_objects_keep_the_lean_relation_refusal() {
    for triple in BOTH {
        for opt in OPTS {
            for conv in [CallingConv::Rust, CallingConv::C] {
                let mut fixture = compile(module(Callee::Mask, conv), opt, triple, &[H]);
                fixture.placements.get_mut(H).unwrap().ret =
                    ReturnPlace::Scalar(ScalarPlace::gpr(0, 32));
                let (report, recorded) = report_recording_step5(&fixture);
                save(&format!("stripped-extension-{conv:?}-{triple}-{opt:?}"), &fixture, &report);
                let why = format!("{conv:?} {triple} {opt:?}\n{}", explain(&report));
                assert_bool_edge_withdrawn(&report, RUNG, &why);
                assert!(recorded.iter().all(|(symbol, _)| symbol != RUNG), "{why}");
            }
        }
    }
}

/// N8: a bool tail return inherits its 0/1 zero extension only from a bool
/// callee result; the C-u8/u16 arms are unchanged.
#[test]
fn bool_tail_return_inherits_only_a_bool_callee_result() {
    let own = bool_ret();
    assert!(check_tail_transport(&own, &own).is_ok());
    let plain32 = ReturnPlace::Scalar(ScalarPlace::gpr(0, 32));
    let refusal = check_tail_transport(&own, &plain32).unwrap_err();
    assert!(refusal.contains("0/1 zero extension"), "{refusal}");
    assert!(check_tail_transport(&own, &ReturnPlace::Void).is_err());
    assert!(check_tail_transport(&own, &ReturnPlace::Scalar(ScalarPlace::gpr(0, 64))).is_err());
    assert!(check_tail_transport(&plain32, &own).is_ok());
    let byte = ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 8, ext: AbiExt::Zext });
    let plain8 = ReturnPlace::Scalar(ScalarPlace::gpr(0, 8));
    assert!(check_tail_transport(&byte, &plain8).is_err());
    assert!(check_tail_transport(&byte, &byte).is_ok());
    assert!(check_tail_transport(&plain8, &byte).is_ok());
}

// ---------------------------------------------------------------------------
// Gate: ladder rung s11 and its mutants, both triples, O0 and O3
// ---------------------------------------------------------------------------

/// Preserve all four original s11 cells. The own callee's C2 can close;
/// the caller must retain O3 Unknown and strict refusal until Lean transport.
#[test]
fn s11_shape_keeps_the_bool_call_edge_unknown() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple);
            let report = fixture.report();
            save(&format!("s11-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            let h = certificate(&report, H);
            assert!(h.verdict.is_proven(), "{why}");
            assert!(h.abi_contracts.is_empty(), "{why}");
            assert!(closed(&report, H), "{why}");
            if cfg!(feature = "kernel-recheck") {
                assert!(h.is_kernel_proved() && closed_kernel(&report, H), "{why}");
            }
            assert_bool_edge_withdrawn(&report, RUNG, &why);
            assert!(certificate(&report, RUNG).abi_contracts.is_empty(), "{why}");
        }
    }
}

/// C2 is in the step-(5) kernel conjunction, not only decided by ay at (4c):
/// every conjunction built for the s11 `h` holds the C2 item, `bad == 0` with
/// `bad` reading the carrier's bits 31..1 against a 31-bit zero (no other item
/// of `h` has one), and `rung`'s (a u64 result) none. Without it a kernel
/// grade of `h` would not cover the 0/1 promise its callers rely on.
#[test]
fn c2_joins_the_kernel_conjunction() {
    let c2_item = |(machine, spec): &(Formula, Formula)| {
        let text = format!("{machine:?}");
        *spec == bv(0, 1)
            && text.contains("high: 31, low: 1")
            && text.contains("BitVec { value: 0, width: 31 }")
    };
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple);
            let (report, recorded) = report_recording_step5(&fixture);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert!(certificate(&report, H).verdict.is_proven(), "{why}");
            let h: Vec<_> = recorded.iter().filter(|(symbol, _)| symbol == H).collect();
            assert!(!h.is_empty(), "no step-(5) conjunction for `h`\n{why}");
            for (_, conj) in &h {
                assert_eq!(conj.iter().filter(|item| c2_item(item)).count(), 1, "{why}");
            }
            let rung: Vec<_> = recorded.iter().filter(|(symbol, _)| symbol == RUNG).collect();
            assert!(rung.is_empty(), "withdrawn bool caller reached step-(5)\n{why}");
            assert!(rung.iter().all(|(_, conj)| !conj.iter().any(c2_item)), "{why}");
        }
    }
}

/// N9 (the F2 premise): a call-free `bool` leaf is refused by the leaf original
/// lane (`source_memory::width` has no Bool arm), so the ordinary lane, which
/// states C2, is what grades it.
#[test]
fn a_bool_leaf_is_graded_by_the_ordinary_lane() {
    for triple in BOTH {
        for opt in OPTS {
            let report = s11(opt, triple).report();
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            let h = certificate(&report, H);
            let leaf = h.leaf_memory.as_ref().map(|d| d.status.as_str()).unwrap_or("");
            assert!(leaf.contains(LEAF_REFUSAL), "{leaf}\n{why}");
            assert_eq!(h.obligations.o4_return.grade, Grade::Proven, "{why}");
            assert_eq!(h.obligations.o4_return.detail, ORDINARY_O4, "{why}");
        }
    }
}

/// Preserve the W0 byte mutation under the same missing-relation refusal.
#[test]
fn w0_reader_still_requires_the_lean_bool_relation() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple).patched(|object| {
                let (offset, rd, rn) = result_extract(object);
                patch_word(object, offset, 0x2a00_03e0 | (rn << 16) | rd); // mov wD,wS
            });
            let report = fixture.report();
            save(&format!("w0-reader-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert_bool_edge_withdrawn(&report, RUNG, &why);
        }
    }
}

/// Preserve the full-X0 byte mutation; refusal precedes any new poststate.
#[test]
fn x0_reader_depends_on_callee_padding() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple).patched(|object| {
                let (offset, rd, rn) = result_extract(object);
                patch_word(object, offset, 0xaa00_03e0 | (rn << 16) | rd); // mov xD,xS
            });
            let report = fixture.report();
            save(&format!("x0-reader-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert_bool_edge_withdrawn(&report, RUNG, &why);
        }
    }
}

/// N2: `h` returning `a & 4` (4, not 1) is Refuted at O4; `rung` does not close.
#[test]
fn a_callee_returning_four_is_refuted() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple).patched(|object| {
                let words = function_words(object, H);
                for (offset, _) in &words {
                    patch_word(object, *offset, NOP);
                }
                patch_word(object, words[0].0, AND_X0_4);
                patch_word(object, words.last().unwrap().0, RET);
            });
            let report = fixture.report();
            save(&format!("and-four-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            let h = certificate(&report, H);
            assert!(matches!(h.verdict, OutputVerdict::Refuted { .. }), "{why}");
            assert_eq!(h.obligations.o4_return.grade, Grade::Refuted, "{why}");
            assert!(!closed(&report, RUNG), "{why}");
            assert!(report.ships(EmitPolicy::AllowUnknown).is_err(), "{why}");
        }
    }
}

/// N3 (F4): a carrier that is not 0/1 under bytes that keep value(return)
/// TRUE, so C2 is what fails: `Cast Trunc u64 -> Bool` with `h` returning X0
/// untouched (W0 = a[31:0], the spec carrier), and `Const { Bool, Int(2) }`
/// with `mov w0,#2`. `h` is Unknown with the C2 detail, never Refuted, and
/// `rung` does not close.
#[test]
fn a_carrier_that_is_not_zero_or_one_is_unknown_at_c2() {
    for triple in BOTH {
        for opt in OPTS {
            let good = s11(opt, triple);
            for (label, mutant) in [
                (
                    "trunc-raw-x0",
                    with_callee(&good, Callee::Trunc, |object, words| {
                        patch_word(object, words.last().unwrap().0, RET);
                    }),
                ),
                (
                    "const-two",
                    with_callee(&good, Callee::Two, |object, words| {
                        patch_word(object, words[0].0, MOV_W0_2);
                        patch_word(object, words.last().unwrap().0, RET);
                    }),
                ),
            ] {
                let report = mutant.report();
                save(&format!("{label}-{triple}-{opt:?}"), &mutant, &report);
                let why = format!("{label} {triple} {opt:?}\n{}", explain(&report));
                let h = certificate(&report, H);
                assert!(matches!(h.verdict, OutputVerdict::Unknown { .. }), "{why}");
                assert_eq!(h.obligations.o4_return.grade, Grade::Unknown, "{why}");
                assert!(h.obligations.o4_return.detail.contains("BOOL-RET-EDGE-1 C2"), "{why}");
                assert!(!closed(&report, H) && !closed(&report, RUNG), "{why}");
                assert!(report.ships(EmitPolicy::AllowUnknown).is_ok(), "{why}");
                assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err(), "{why}");
            }
        }
    }
}

/// N4 (F1): the Trunc carrier with bytes that ALSO violate value(return)
/// (`mvn w0,w0`). C2 is decided after step (4), so the byte counterexample is
/// Refuted, not masked as Unknown.
#[test]
fn c2_does_not_mask_a_value_counterexample() {
    for triple in BOTH {
        for opt in OPTS {
            let good = s11(opt, triple);
            let mutant = with_callee(&good, Callee::Trunc, |object, words| {
                patch_word(object, words[0].0, MVN_W0);
                patch_word(object, words.last().unwrap().0, RET);
            });
            let report = mutant.report();
            save(&format!("trunc-mvn-{triple}-{opt:?}"), &mutant, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            let h = certificate(&report, H);
            assert!(matches!(h.verdict, OutputVerdict::Refuted { .. }), "{why}");
            assert_eq!(h.obligations.o4_return.grade, Grade::Refuted, "{why}");
            assert!(report.ships(EmitPolicy::AllowUnknown).is_err(), "{why}");
        }
    }
}

/// Missing-body and preemptible variants retain the same Lean-relation refusal.
#[test]
fn a_bool_callee_that_is_not_co_emitted_is_unknown() {
    let bodiless = |opt| {
        let mut fixture = s11(opt, DARWIN);
        fixture.bodies.remove(H);
        fixture
    };
    for opt in OPTS {
        for (label, fixture) in [
            ("no-body", bodiless(opt)),
            (
                "linux-pic",
                compile_with(
                    module(Callee::Mask, CallingConv::Rust),
                    opt,
                    LINUX,
                    &[H],
                    RelocationModel::Pic,
                ),
            ),
        ] {
            let report = fixture.report();
            save(&format!("{label}-{opt:?}"), &fixture, &report);
            let why = format!("{label} {opt:?}\n{}", explain(&report));
            let rung = certificate(&report, RUNG);
            assert!(!rung.verdict.is_proven(), "{why}");
            assert_eq!(rung.obligations.o3_events.grade, Grade::Unknown, "{why}");
            let detail = &rung.obligations.o3_events.detail;
            assert!(detail.contains("BOOL-RET-EDGE-1"), "{why}");
            assert!(detail.contains("Lean-owned"), "{why}");
        }
    }
}

/// An extern-C Bool callee also lacks the Lean-owned transport relation.
#[test]
fn an_extern_c_bool_callee_is_unknown() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = compile(module(Callee::Mask, CallingConv::C), opt, triple, &[H]);
            let report = fixture.report();
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert_bool_edge_withdrawn(&report, RUNG, &why);
        }
    }
}

/// Keep the wrong-result-slot case and its caller/own-callee refusals.
#[test]
fn a_bool_result_outside_w0_is_unknown_at_the_edge() {
    for triple in BOTH {
        let mut fixture = s11(OptLevel::O0, triple);
        fixture.placements.get_mut(H).unwrap().ret =
            ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(1), width: 32, ext: AbiExt::Zext });
        let report = fixture.report();
        let why = format!("{triple}\n{}", explain(&report));
        let rung = certificate(&report, RUNG);
        assert!(!rung.verdict.is_proven(), "{why}");
        assert_eq!(rung.obligations.o3_events.grade, Grade::Unknown, "{why}");
        assert!(!certificate(&report, H).verdict.is_proven(), "{why}");
    }
}

/// The producer `h` and the M_cg `h` are one module in every fixture above;
/// a test that swaps the spec side must not read a stale `M_cg`: the good
/// fixture's `h` has no Cast, the mutant's has one, and the mutant's bytes
/// differ from the good ones.
#[test]
fn the_mutant_fixture_reads_its_own_producer() {
    let has_cast = |fixture: &Fixture| {
        let h = fixture.m_cg.functions.iter().find(|f| f.name == H).unwrap();
        h.blocks[0].body.iter().any(|node| matches!(node.inst, Inst::Cast { .. }))
    };
    let good = s11(OptLevel::O0, DARWIN);
    let mutant = with_callee(&good, Callee::Trunc, |object, words| {
        patch_word(object, words.last().unwrap().0, RET);
    });
    assert!(!has_cast(&good));
    assert!(has_cast(&mutant));
    assert!(Arc::ptr_eq(&mutant.m_cg, &mutant.producers[0].module));
    assert_ne!(mutant.object, good.object);
}

// ---------------------------------------------------------------------------
// Review pins (two non-author reviews of 061b530be3)
// ---------------------------------------------------------------------------

/// A3 (review mutant rb): the IR's bool result is bound to zext32(R1), and a
/// caller that uses it as a number sees exactly that. `widen` returns
/// Preserve the numeric Bool consumer in all four original cells. Co-emission
/// and a separately closed callee never authorize its missing call relation.
#[test]
fn a_caller_that_widens_the_bool_keeps_the_edge_unknown() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = compile(widen_module(), opt, triple, &[H]);
            let report = fixture.report();
            save(&format!("widen-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert!(certificate(&report, H).verdict.is_proven() && closed(&report, H), "{why}");
            assert_bool_edge_withdrawn(&report, WIDEN, &why);
        }
    }
}

/// Preserve the sign-extension byte mutant, with no replacement post-call
/// abstraction or false O4 counterexample claimed before the O3 refusal.
#[test]
fn a_caller_that_sign_extends_the_bool_is_not_proven() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = compile(widen_module(), opt, triple, &[H]).patched(|object| {
                let (offset, rd, rn) = result_extract_in(object, WIDEN);
                patch_word(object, offset, 0x1300_0000 | (rn << 5) | rd); // sbfx wD,wS,#0,#1
            });
            let report = fixture.report();
            save(&format!("widen-sbfx-{triple}-{opt:?}"), &fixture, &report);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert_bool_edge_withdrawn(&report, WIDEN, &why);
        }
    }
}

/// Preserve the caller-declaration/body-convention mismatch. Body custody
/// and convention observations do not replace the missing semantic relation.
#[test]
fn a_rust_declared_callee_over_a_c_body_is_unknown() {
    for triple in BOTH {
        for opt in OPTS {
            let mut fixture = s11(opt, triple);
            let c_body = Arc::new(targeted_at(module(Callee::Mask, CallingConv::C), triple));
            let func = c_body.functions.iter().find(|f| f.name == H).unwrap().id;
            fixture.producers.push(ProducerModule::named_by_symbols(c_body));
            let body = fixture.bodies.get_mut(H).unwrap();
            body.producer = fixture.producers.len() - 1;
            body.func = func;
            let report = fixture.report();
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            let rung = certificate(&report, RUNG);
            assert!(!rung.verdict.is_proven(), "{why}");
            assert_eq!(rung.obligations.o3_events.grade, Grade::Unknown, "{why}");
            let detail = &rung.obligations.o3_events.detail;
            assert!(detail.contains("BOOL-RET-EDGE-1"), "{why}");
            assert!(detail.contains("Lean-owned"), "{why}");
            assert!(!closed(&report, RUNG), "{why}");
        }
    }
}

/// The withdrawn caller constructs no semantic poststate/kernel conjunction;
/// the separately verified own callee still reaches its real C2 conjunction.
#[test]
fn a_withdrawn_bool_edge_builds_no_caller_kernel_conjunction() {
    for triple in BOTH {
        for opt in OPTS {
            let fixture = s11(opt, triple);
            let (report, recorded) = report_recording_step5(&fixture);
            let why = format!("{triple} {opt:?}\n{}", explain(&report));
            assert_bool_edge_withdrawn(&report, RUNG, &why);
            assert!(recorded.iter().any(|(symbol, _)| symbol == H), "{why}");
            assert!(recorded.iter().all(|(symbol, _)| symbol != RUNG), "{why}");
        }
    }
}

/// C2 at (4c) (review mutant rn): only an ay `Proven` yields the item that
/// step (5) joins; a counterexample and an ay Unknown are both the O4
/// Unknown detail, so no grade is ever given without C2 in the conjunction.
#[test]
fn c2_is_granted_only_on_proven() {
    let bad = Formula::Var("BAD".into(), Sort::Bool);
    assert_eq!(bool_range_decision(Discharge::Proven, bad.clone()), Ok(bad.clone()));
    assert_eq!(bool_range_decision(Discharge::CounterExample, bad.clone()), Err(BOOL_C2.into()));
    let unknown = bool_range_decision(Discharge::Unknown("ay timed out".into()), bad);
    let detail = unknown.unwrap_err();
    assert!(detail.starts_with(BOOL_C2) && detail.ends_with("ay timed out"), "{detail}");
}
