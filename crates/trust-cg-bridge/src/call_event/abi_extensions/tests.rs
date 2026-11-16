use trust_ir::{StructPassingPolicy, TargetInfo};

use super::*;

fn module() -> Module {
    let mut module = Module::new("c_u8");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}
fn byte(register: u8) -> ScalarPlace {
    ScalarPlace { slot: Slot::Gpr(register), width: 8, ext: AbiExt::Zext }
}
fn placement() -> FnPlacement {
    FnPlacement { params: vec![ParamPlace::Scalar(byte(0))], ret: ReturnPlace::Scalar(byte(0)) }
}
fn c_plan() -> Plan {
    Plan::new(&module(), CallingConv::C, &[Ty::U8], &[Ty::U8], &placement(), true).unwrap()
}
fn x() -> Formula {
    Formula::Var("X0".into(), Sort::BitVec(64))
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn qualified_entry_domain_is_exact_and_kernel_checked() {
    let plan = c_plan();
    let record = plan.record().unwrap();
    assert_eq!(record.slots.len(), 2);
    assert_eq!(record.slots[0].declared_width, 8);
    assert_eq!(record.slots[0].required_width, 32);
    assert_eq!(record.placement_sha256, placement().digest());
    let equations = plan.entry_equations();
    assert_eq!(equations.len(), 4);
    assert!(
        crate::verify_output::try_kernel_recheckable_conjunction(&equations)
            .is_some_and(|evidence| crate::verify_output::OutputVerdict::Proven { evidence }
                .is_kernel_proved()),
        "entry domain must carry a real kernel artifact"
    );
    let mut state = MachineState::symbolic();
    plan.apply_entry(&mut state);
    assert_eq!(plan.source_entry(x()), state.gpr[0]);
    // The actual concrete machine evaluator sees unchanged low8 and high32,
    // with only the caller-owned W[31:8] cleared.
    let mut concrete = trust_machine_sem::ConcreteState::new();
    concrete.gpr[0] = 0xdead_beef_a5c3_9e71;
    assert_eq!(concrete.eval_bv(&state.gpr[0], 64).unwrap(), 0xdead_beef_0000_0071);
}

#[test]
fn rust_none_keeps_every_incoming_w0_bit_unrestricted() {
    let mut p = placement();
    if let ParamPlace::Scalar(s) = &mut p.params[0] {
        s.ext = AbiExt::None;
    }
    if let ReturnPlace::Scalar(s) = &mut p.ret {
        s.ext = AbiExt::None;
    }
    let plan = Plan::new(&module(), CallingConv::Rust, &[Ty::U8], &[Ty::U8], &p, true).unwrap();
    assert!(plan.record().is_none());
    assert!(plan.entry_equations().is_empty());
    let mut state = MachineState::symbolic();
    let before = state.gpr.clone();
    plan.apply_entry(&mut state);
    assert_eq!(state.gpr, before);
    assert_eq!(plan.source_entry(x()), x());
    let mut concrete = trust_machine_sem::ConcreteState::new();
    concrete.gpr[0] = 0x1234_5678_a5c3_9e71;
    assert_eq!(concrete.eval_bv(&state.gpr[0], 64).unwrap(), 0x1234_5678_a5c3_9e71);
}

#[test]
fn missing_or_forged_extension_authority_refuses() {
    let base = module();
    for mode in 0..8 {
        let mut m = base.clone();
        let mut p = placement();
        let mut conv = CallingConv::C;
        let mut parameter = Ty::U8;
        match mode {
            0 => m.target_info = None,
            1 => m.target_info.as_mut().unwrap().triple = "aarch64-unknown-linux-gnu".into(),
            2 => conv = CallingConv::Rust,
            3 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.ext = AbiExt::None;
                }
            }
            4 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.ext = AbiExt::Sext;
                }
            }
            5 => {
                parameter = Ty::U32;
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.width = 32;
                }
            }
            6 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.slot = Slot::Stack { offset: 0 };
                }
            }
            _ => m.target_info.as_mut().unwrap().endianness = Endianness::Big,
        }
        assert!(Plan::new(&m, conv, &[parameter], &[Ty::U8], &p, true).is_err(), "mode{mode}");
    }
    let mut p = placement();
    p.params.push(ParamPlace::Scalar(ScalarPlace::gpr(0, 64)));
    assert!(Plan::new(&base, CallingConv::C, &[Ty::U8, Ty::U64], &[Ty::U8], &p, true).is_err());
    let mut p = placement();
    if let ReturnPlace::Scalar(s) = &mut p.ret {
        s.slot = Slot::Gpr(1);
    }
    assert!(Plan::new(&base, CallingConv::C, &[Ty::U8], &[Ty::U8], &p, true).is_err());
}

/// `Plan::new` refuses an arity mismatch first and names both counts.
/// `check_fixed_placement` gives the same text, so the variadic gate's test
/// cannot tell which of the two refused; this one reads `Plan::new` alone.
#[test]
fn an_arity_mismatch_names_both_counts() {
    let one = placement();
    let mut two = placement();
    two.params.push(ParamPlace::Scalar(byte(1)));
    for (params, place, expected) in [
        (&[Ty::U8, Ty::U8][..], &one, "2 parameter(s) but P places 1"),
        (&[][..], &one, "0 parameter(s) but P places 1"),
        (&[Ty::U8][..], &two, "1 parameter(s) but P places 2"),
    ] {
        for conv in [CallingConv::C, CallingConv::Rust] {
            let refusal = Plan::new(&module(), conv, params, &[Ty::U8], place, true).err();
            assert_eq!(refusal.as_deref(), Some(expected), "{conv:?}");
        }
    }
}

#[test]
fn physical_call_and_return_values_keep_declared_width_but_check_w0() {
    let scalar = byte(0);
    let value = bv(0xa5, 8);
    let physical = physical_value(&scalar, value.clone()).unwrap();
    assert_eq!(scalar.width, 8);
    assert_eq!(physical_width(&scalar), 32);
    assert_eq!(trust_types::smt_logic::check_formula_sort(&physical).unwrap(), Sort::BitVec(32));
    assert!(physical_value(&scalar, bv(0xa5, 32)).is_err());
    let plain = ScalarPlace { ext: AbiExt::None, ..scalar };
    assert_eq!(physical_width(&plain), 8);
    assert_eq!(physical_value(&plain, value.clone()).unwrap(), value);
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn shared_r8_guarantees_w0_and_keeps_high32_independent() {
    let result = Formula::Var("R8".into(), Sort::BitVec(8));
    let high = Formula::Var("X9".into(), Sort::BitVec(64));
    let post = post_call_unsigned(result.clone(), high.clone(), 8).unwrap();
    let equations = [
        (extract(post.clone(), 31, 0), Formula::BvZeroExt(b(result), 24)),
        (extract(post, 63, 32), extract(high, 63, 32)),
    ];
    assert!(
        crate::verify_output::try_kernel_recheckable_conjunction(&equations)
            .is_some_and(|evidence| crate::verify_output::OutputVerdict::Proven { evidence }
                .is_kernel_proved()),
        "post-call carrier must be kernel checked"
    );
    assert!(post_call_unsigned(bv(1, 32), x(), 8).is_err());
    assert!(post_call_unsigned(bv(1, 8), bv(0, 32), 8).is_err());
}

#[test]
fn legacy_bool_result_does_not_admit_an_extended_call_edge() {
    let p = FnPlacement {
        params: vec![],
        ret: ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::Zext }),
    };
    assert!(
        Plan::new(&module(), CallingConv::Rust, &[], &[Ty::Bool], &p, true)
            .unwrap()
            .record()
            .is_none()
    );
    assert!(Plan::new(&module(), CallingConv::Rust, &[], &[Ty::Bool], &p, false).is_err());
}

#[test]
fn weaker_tail_padding_is_unknown_not_an_invented_c_extension() {
    let own = ReturnPlace::Scalar(byte(0));
    let plain = ReturnPlace::Scalar(ScalarPlace { ext: AbiExt::None, ..byte(0) });
    assert!(check_tail_transport(&own, &plain).is_err());
    assert!(check_tail_transport(&own, &own).is_ok());
    assert!(check_tail_transport(&plain, &own).is_ok());
    let padding = Formula::Var("CER_RHI@8".into(), Sort::BitVec(56));
    assert!(observes_callee_padding(&padding));
    assert!(!observes_callee_padding(&x()));
}

#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;

fn native_fixture(opt: trust_cg_codegen::pipeline::OptLevel) -> cer_common::Fixture {
    use cer_common::*;
    use trust_ir::inst::{BinOp, CastOp, Inst, UnOp};
    let mut builder = ModBuilder::new("c_u8_full_boundary");
    let byte = builder.sig(&[Ty::U8], Some(Ty::U8));
    builder.define("c_u8_id", byte, trust_ir::Linkage::External, |f| f.ret(f.p(0)));
    let not = builder.define("c_u8_not", byte, trust_ir::Linkage::External, |f| {
        let value = f.push_inst(Inst::UnOp { op: UnOp::Not, ty: Ty::U8, operand: f.p(0) });
        f.ret(value);
    });
    builder.define("c_u8_xor", byte, trust_ir::Linkage::External, |f| {
        let k = f.konst(Ty::U8, 0xa5);
        let value = f.bin(BinOp::Xor, Ty::U8, f.p(0), k);
        f.ret(value);
    });
    builder.define("c_u8_constant", byte, trust_ir::Linkage::External, |f| {
        let value = f.konst(Ty::U8, 0xd3);
        f.ret(value);
    });
    builder.define("c_u8_via", byte, trust_ir::Linkage::External, |f| {
        let value = f.call(not, &[f.p(0)]);
        f.ret(value);
    });
    let wide = builder.sig(&[Ty::U32], Some(Ty::U8));
    builder.define("c_u8_trunc", wide, trust_ir::Linkage::External, |f| {
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U32,
            dst_ty: Ty::U8,
            operand: f.p(0),
        });
        f.ret(value);
    });
    let mut module = builder.finish();
    module.target_info = self::module().target_info;
    for function in &mut module.functions {
        function.calling_conv = CallingConv::C;
    }
    compile_fixture(module, opt, &["c_u8_not"])
}

fn compile_fixture(
    module: Module,
    opt: trust_cg_codegen::pipeline::OptLevel,
    never_inline: &[&str],
) -> cer_common::Fixture {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: never_inline.iter().map(|name| (*name).into()).collect(),
            ..CompilerConfig::default()
        },
        TargetSpec::parse(cer_common::DARWIN).unwrap(),
    )
    .with_codegen_license(cer_common::fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    let mut fixture = cer_common::Fixture::with_object(module, object, cer_common::DARWIN);
    for function in &fixture.m_cg.functions {
        if function.calling_conv != CallingConv::C {
            continue;
        }
        let signature = fixture.m_cg.func_type(function.ty).unwrap();
        let placement = fixture.placements.get_mut(&function.name).unwrap();
        for (ty, place) in signature.params.iter().zip(&mut placement.params) {
            if *ty == Ty::U8 {
                let ParamPlace::Scalar(scalar) = place else {
                    panic!("direct byte");
                };
                scalar.ext = AbiExt::Zext;
            }
        }
        if signature.returns == [Ty::U8] {
            let ReturnPlace::Scalar(scalar) = &mut placement.ret else {
                panic!("direct byte");
            };
            scalar.ext = AbiExt::Zext;
        }
    }
    fixture
}

fn save_native(name: &str, fixture: &cer_common::Fixture, report: &super::super::CerReport) {
    if let Some(path) = std::env::var_os("TRUST_CER_C_U8_OUTPUT_DIR") {
        let path = std::path::PathBuf::from(path).join(name);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("object.o"), &fixture.object).unwrap();
        std::fs::write(path.join("certificates.json"), report.to_json()).unwrap();
        std::fs::write(path.join("disassembly.txt"), cer_common::disassemble(&fixture.object))
            .unwrap();
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn actual_full_compiler_c_u8_objects_close_kernel_and_bad_mvn_refutes() {
    use trust_cg_codegen::pipeline::OptLevel;

    use crate::verify_output::{EmitPolicy, OutputVerdict};
    for opt in [OptLevel::O0, OptLevel::O3] {
        let fixture = native_fixture(opt);
        let report = fixture.report();
        save_native(&format!("c-only-{opt:?}"), &fixture, &report);
        eprintln!("{}", cer_common::explain(&report));
        for certificate in &report.certificates {
            assert!(certificate.is_kernel_proved(), "{opt:?}: {}", cer_common::explain(&report));
            assert!(certificate.abi_contracts.contains_key(&certificate.symbol));
        }
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        let mutant = fixture.patched(|object| {
            let words = cer_common::function_words(object, "c_u8_not");
            assert!(words.len() >= 2);
            // Keep the whole bound extent reachable: no object-gate waiver.
            for (offset, _) in &words {
                cer_common::patch_word(object, *offset, 0xd503_201f);
            }
            cer_common::patch_word(object, words[0].0, 0x2a20_03e0); // mvn w0,w0
            cer_common::patch_word(object, words.last().unwrap().0, 0xd65f_03c0); // ret
        });
        let bad = mutant.report();
        save_native(&format!("bad-mvn-{opt:?}"), &mutant, &bad);
        assert!(
            matches!(bad.certificate("c_u8_not").unwrap().verdict, OutputVerdict::Refuted { .. }),
            "{}",
            cer_common::explain(&bad)
        );
        assert!(bad.ships(EmitPolicy::AllowUnknown).is_err());
    }
}

fn rust_caller_fixture(opt: trust_cg_codegen::pipeline::OptLevel) -> cer_common::Fixture {
    use cer_common::*;
    use trust_ir::inst::{CastOp, Inst};
    let mut builder = ModBuilder::new("rust_none_to_c_byte");
    let byte = builder.sig(&[Ty::U8], Some(Ty::U8));
    let observe = builder.declare("c_byte_observer", byte);
    let high = builder.declare("c_byte_high_result", byte);
    builder.define("rust_byte_caller", byte, trust_ir::Linkage::External, |f| {
        let result = f.call(observe, &[f.p(0)]);
        f.ret(result);
    });
    let wide = builder.sig(&[Ty::U8], Some(Ty::U64));
    builder.define("rust_byte_widen", wide, trust_ir::Linkage::External, |f| {
        let result = f.call(high, &[f.p(0)]);
        let result = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: result,
        });
        f.ret(result);
    });
    let mut module = builder.finish();
    module.target_info = self::module().target_info;
    for function in &mut module.functions {
        function.calling_conv = CallingConv::Rust;
    }
    module.functions[observe.as_usize()].calling_conv = CallingConv::C;
    module.functions[high.as_usize()].calling_conv = CallingConv::C;
    compile_fixture(module, opt, &[])
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn actual_rust_none_dirty_w0_to_c_byte_observer_and_padding() {
    use trust_cg_codegen::pipeline::OptLevel;

    use crate::verify_output::EmitPolicy;
    for opt in [OptLevel::O0, OptLevel::O3] {
        let fixture = rust_caller_fixture(opt);
        let report = fixture.report();
        save_native(&format!("rust-caller-{opt:?}"), &fixture, &report);
        eprintln!("{}", cer_common::explain(&report));
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path();
        std::fs::write(path.join("object.o"), &fixture.object).unwrap();
        std::fs::write(path.join("observer.S"), OBSERVER).unwrap();
        std::fs::write(path.join("driver.c"), RUST_CALLER_DRIVER).unwrap();
        let output = std::process::Command::new("/usr/bin/cc")
            .current_dir(path)
            .args([
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "driver.c",
                "observer.S",
                "object.o",
                "-o",
                "driver",
            ])
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let output = std::process::Command::new(path.join("driver")).output().unwrap();
        assert!(
            output.status.success(),
            "real native Rust-None/C transport {opt:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            report.ships(EmitPolicy::StrictProvenOnly).is_ok(),
            "{}",
            cer_common::explain(&report)
        );
        for certificate in &report.certificates {
            assert!(certificate.is_kernel_proved());
            assert!(
                !certificate.abi_contracts.contains_key(&certificate.symbol),
                "Rust-None entry must not acquire a C entry premise"
            );
        }
    }
}

const OBSERVER: &str = r#"
.text
.globl _observe_rust_byte_caller
_observe_rust_byte_caller:
    stp x29,x30,[sp,#-16]!
    mov x29,sp
    bl _rust_byte_caller
    and w0,w0,#255
    ldp x29,x30,[sp],#16
    ret
.globl _observe_rust_byte_widen
_observe_rust_byte_widen:
    stp x29,x30,[sp,#-16]!
    mov x29,sp
    bl _rust_byte_widen
    ldp x29,x30,[sp],#16
    ret
.globl _c_byte_observer
_c_byte_observer:
    and w8,w0,#255
    cmp w8,w0
    b.ne 1f
    mvn w0,w0
    and w0,w0,#255
    ret
1:  mov w0,#256
    ret
.globl _c_byte_high_result
_c_byte_high_result:
    and w8,w0,#255
    cmp w8,w0
    b.ne 2f
    mov w8,#0x5c
    eor w0,w0,w8
    mov x8,#0xdead
    lsl x8,x8,#32
    orr x0,x0,x8
    ret
2:  mov w0,#256
    ret
"#;
const RUST_CALLER_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern uint32_t observe_rust_byte_caller(uint64_t);
extern uint64_t observe_rust_byte_widen(uint64_t);
int main(void) {
    for (uint32_t x=0;x<256;++x) {
        uint64_t raw=UINT64_C(0xfedcba98a5c39e00)|x; /*valid Rust None, dirty W[31:8]*/
        uint32_t byte=observe_rust_byte_caller(raw);
        uint64_t wide=observe_rust_byte_widen(raw);
        if(byte!=(x^255u) || wide!=(x^0x5cu)) {
            fprintf(stderr,"input=%08x byte=%08x wide=%016llx\n",x,byte,(unsigned long long)wide); return 1;
        }
    }
    return 0;
}
"#;

fn is_byte_extract(word: u32) -> bool {
    word & 0xffc0_0000 == 0x5300_0000 && (word >> 16) & 63 == 0 && (word >> 10) & 63 == 7
}
fn remove_byte_extracts(object: &mut [u8], name: &str, before_call: bool) -> usize {
    let words = cer_common::function_words(object, name);
    let call = words.iter().find(|(_, word)| word & 0xfc00_0000 == 0x9400_0000).unwrap().0;
    let mut count = 0;
    for (offset, word) in words {
        if (offset < call) == before_call && is_byte_extract(word) {
            // MOV Wdst,Wsrc keeps the low byte but leaves legal dirty W padding.
            let dst = word & 31;
            let src = (word >> 5) & 31;
            cer_common::patch_word(object, offset, 0x2a00_03e0 | (src << 16) | dst);
            count += 1;
        }
    }
    assert!(count > 0, "the actual object must contain the relevant extension");
    count
}

#[test]
fn actual_dirty_rust_argument_without_c_extension_is_refuted() {
    use trust_cg_codegen::pipeline::OptLevel;

    use crate::verify_output::{EmitPolicy, OutputVerdict};
    for opt in [OptLevel::O0, OptLevel::O3] {
        let fixture = rust_caller_fixture(opt);
        let mut mutant = fixture.patched(|object| {
            remove_byte_extracts(object, "rust_byte_caller", true);
        });
        // Retain the full object/source/P binding; omit unrelated body proofs
        // so this mutation checks the one changed function without re-proving
        // the already-qualified sibling.
        mutant.bodies.retain(|name, _| name == "rust_byte_caller");
        let report = mutant.report();
        save_native(&format!("bad-call-argument-{opt:?}"), &mutant, &report);
        let certificate = report.certificate("rust_byte_caller").unwrap();
        assert!(
            matches!(certificate.verdict, OutputVerdict::Refuted { .. }),
            "{}",
            cer_common::explain(&report)
        );
        assert_eq!(certificate.obligations.o3_events.grade, super::super::Grade::Refuted);
        assert!(!certificate.abi_contracts.contains_key("rust_byte_caller"));
        assert!(report.ships(EmitPolicy::AllowUnknown).is_err());
    }
}

fn weaker_callee_fixture(opt: trust_cg_codegen::pipeline::OptLevel) -> cer_common::Fixture {
    use cer_common::*;
    let mut builder = ModBuilder::new("weaker_rust_padding");
    let byte = builder.sig(&[Ty::U8], Some(Ty::U8));
    let callee =
        builder.define("rust_none_identity", byte, trust_ir::Linkage::External, |f| f.ret(f.p(0)));
    let caller = builder.define("c_byte_from_rust", byte, trust_ir::Linkage::External, |f| {
        let result = f.call(callee, &[f.p(0)]);
        f.ret(result);
    });
    let mut module = builder.finish();
    module.target_info = self::module().target_info;
    for function in &mut module.functions {
        function.calling_conv = CallingConv::Rust;
    }
    module.functions[caller.as_usize()].calling_conv = CallingConv::C;
    compile_fixture(module, opt, &["rust_none_identity"])
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn actual_weaker_return_padding_and_tail_stay_unknown() {
    use trust_cg_codegen::pipeline::OptLevel;

    use crate::verify_output::{EmitPolicy, OutputVerdict};
    for opt in [OptLevel::O0, OptLevel::O3] {
        let fixture = weaker_callee_fixture(opt);
        let good = fixture.report();
        assert!(good.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", cer_common::explain(&good));
        let unmasked = fixture.patched(|object| {
            remove_byte_extracts(object, "c_byte_from_rust", false);
        });
        let report = unmasked.report();
        save_native(&format!("unspecified-return-padding-{opt:?}"), &unmasked, &report);
        let certificate = report.certificate("c_byte_from_rust").unwrap();
        assert!(
            matches!(certificate.verdict, OutputVerdict::Unknown { .. }),
            "{}",
            cer_common::explain(&report)
        );
        assert!(
            certificate.obligations.o4_return.detail.contains("unspecified callee result padding")
        );
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        let tail = fixture.patched(|object| {
            let words = cer_common::function_words(object, "c_byte_from_rust");
            let (call, word) =
                words.iter().find(|(_, word)| word & 0xfc00_0000 == 0x9400_0000).copied().unwrap();
            for (offset, _) in words {
                cer_common::patch_word(object, offset, 0xd503_201f);
            }
            // The existing BRANCH26 relocation still names the same real
            // callee. A bare tail B cannot repair its unspecified return bits.
            cer_common::patch_word(object, call, 0x1400_0000 | (word & 0x03ff_ffff));
        });
        let report = tail.report();
        save_native(&format!("weaker-tail-{opt:?}"), &tail, &report);
        let certificate = report.certificate("c_byte_from_rust").unwrap();
        assert!(
            matches!(certificate.verdict, OutputVerdict::Unknown { .. }),
            "{}",
            cer_common::explain(&report)
        );
        assert!(certificate.obligations.o4_return.detail.contains("cannot inherit zero extension"));
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unextended_r8_preserves_all_fifty_six_padding_bits() {
    let result = Formula::Var("R8".into(), Sort::BitVec(8));
    let high = Formula::Var("X9".into(), Sort::BitVec(64));
    let post = post_call_unextended_small(result.clone(), high.clone(), 8).unwrap();
    let equations =
        [(extract(post.clone(), 7, 0), result), (extract(post, 63, 8), extract(high, 63, 8))];
    assert!(crate::verify_output::try_kernel_recheckable_conjunction(&equations).is_some_and(
        |evidence| crate::verify_output::OutputVerdict::Proven { evidence }.is_kernel_proved()
    ));
    let word = post_call_unextended_small(bv(0x71, 8), x(), 8).unwrap();
    let mut concrete = trust_machine_sem::ConcreteState::new();
    concrete.gpr[0] = 0xdead_beef_a5c3_9e00;
    assert_eq!(concrete.eval_bv(&word, 64).unwrap(), 0xdead_beef_a5c3_9e71);
}
