use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::{Inst, UnOp};
use trust_ir::{Linkage, TargetInfo};

fn module() -> Module {
    let mut m = Module::new("signed_c_physical");
    m.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    m
}
fn scalar(width: u32, ext: AbiExt) -> ScalarPlace {
    ScalarPlace { slot: Slot::Gpr(0), width, ext }
}
fn place(width: u32, ext: AbiExt) -> FnPlacement {
    FnPlacement {
        params: vec![ParamPlace::Scalar(scalar(width, ext))],
        ret: ReturnPlace::Scalar(scalar(width, ext)),
    }
}
fn kernel(items: &[(Formula, Formula)]) {
    assert!(crate::verify_output::try_kernel_recheckable_conjunction(items).is_some_and(|e| {
        crate::verify_output::OutputVerdict::Proven { evidence: e }.is_kernel_proved()
    }));
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn signed_entry_domain_physical_return_and_all_high_padding_are_checked() {
    for (ty, width) in [(Ty::I8, 8), (Ty::I16, 16)] {
        let p = place(width, AbiExt::Sext);
        let plan =
            Plan::new(&module(), CallingConv::C, &[ty.clone()], &[ty.clone()], &p, true).unwrap();
        kernel(&plan.entry_equations());
        let record = plan.record().unwrap();
        assert!(record.slots.iter().all(|s| s.declared_width == width
            && s.required_width == 32
            && s.extension == AbiExt::Sext));
        assert_eq!(record.placement_sha256, p.digest());
        let raw = Formula::Var("X0".into(), Sort::BitVec(64));
        let mut state = MachineState::symbolic();
        plan.apply_entry(&mut state);
        assert_eq!(state.gpr[0], plan.source_entry(raw.clone()));
        for low in [0, 1, (1u64 << (width - 1)) - 1, 1u64 << (width - 1), (1u64 << width) - 1] {
            let mut concrete = trust_machine_sem::ConcreteState::new();
            concrete.gpr[0] = 0xdead_beef_a5c3_0000 | low;
            // All low declared bits plus independent high32 are retained.
            let value = concrete.gpr[0] & ((1u64 << width) - 1);
            let extended = ((value << (64 - width)) as i64 >> (64 - width)) as u32;
            assert_eq!(
                concrete.eval_bv(&state.gpr[0], 64).unwrap(),
                u128::from(0xdead_beef_0000_0000 | u64::from(extended))
            );
        }
        let result = Formula::Var("RESULT".into(), Sort::BitVec(width));
        let high = Formula::Var("ANY_HIGH32".into(), Sort::BitVec(64));
        let post = post_call_signed(result.clone(), high.clone(), width).unwrap();
        kernel(&[
            (extract(post.clone(), 31, 0), Formula::BvSignExt(b(result.clone()), 32 - width)),
            (extract(post, 63, 32), extract(high.clone(), 63, 32)),
        ]);
        let none = post_call_unextended_small(result.clone(), high.clone(), width).unwrap();
        kernel(&[
            (extract(none.clone(), width - 1, 0), result),
            (extract(none, 63, width), extract(high, 63, width)),
        ]);
        let rust = Plan::new(
            &module(),
            CallingConv::Rust,
            &[ty.clone()],
            &[ty],
            &place(width, AbiExt::None),
            true,
        )
        .unwrap();
        let mut state = MachineState::symbolic();
        let before = state.gpr.clone();
        rust.apply_entry(&mut state);
        assert_eq!(state.gpr, before);
        assert_eq!(rust.source_entry(raw.clone()), raw);
        assert!(rust.record().is_none() && rust.entry_equations().is_empty());
    }
    // U32 already has a full physical32 result, with no extension premise.
    let p = place(32, AbiExt::None);
    let u32plan = Plan::new(&module(), CallingConv::C, &[Ty::U32], &[Ty::U32], &p, true).unwrap();
    assert!(u32plan.record().is_none());
    assert_eq!(physical_width(&scalar(32, AbiExt::None)), 32);
    assert!(
        Plan::new(
            &module(),
            CallingConv::C,
            &[Ty::U32],
            &[Ty::U32],
            &place(32, AbiExt::Zext),
            true
        )
        .is_err()
    );
}
#[test]
fn signed_authority_and_weaker_callee_contracts_refuse() {
    for (ty, width) in [(Ty::I8, 8), (Ty::I16, 16)] {
        for mutation in 0..9 {
            let mut m = module();
            let mut p = place(width, AbiExt::Sext);
            let mut conv = CallingConv::C;
            let mut ty = ty.clone();
            match mutation {
                0 => m.target_info = None,
                1 => m.target_info.as_mut().unwrap().triple = "aarch64-unknown-linux-gnu".into(),
                2 => m.target_info.as_mut().unwrap().pointer_size = 4,
                3 => conv = CallingConv::Rust,
                4 => ty = if width == 8 { Ty::U8 } else { Ty::U16 },
                5 => {
                    let ParamPlace::Scalar(s) = &mut p.params[0] else { unreachable!() };
                    s.ext = AbiExt::None;
                }
                6 => {
                    let ParamPlace::Scalar(s) = &mut p.params[0] else { unreachable!() };
                    s.ext = AbiExt::Zext;
                }
                7 => {
                    let ParamPlace::Scalar(s) = &mut p.params[0] else { unreachable!() };
                    s.slot = Slot::Stack { offset: 0 };
                }
                _ => m.target_info.as_mut().unwrap().endianness = Endianness::Big,
            }
            assert!(
                Plan::new(&m, conv, &[ty.clone()], &[ty], &p, true).is_err(),
                "width{width} mutation{mutation}"
            );
        }
        assert!(
            check_tail_transport(&place(width, AbiExt::Sext).ret, &place(width, AbiExt::None).ret)
                .is_err()
        );
        assert!(
            check_tail_transport(&place(width, AbiExt::Sext).ret, &place(width, AbiExt::Zext).ret)
                .is_err()
        );
        assert!(
            check_tail_transport(&place(width, AbiExt::Sext).ret, &place(width, AbiExt::Sext).ret)
                .is_ok()
        );
        assert_eq!(physical_width(&scalar(width, AbiExt::Sext)), 32);
        assert!(post_call_signed(bv(1, 32), bv(0, 64), width).is_err());
    }
}
fn compile(mut m: Module, opt: OptLevel, never: &[&str]) -> Fixture {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    m.target_info = module().target_info;
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: never.iter().map(|s| (*s).into()).collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&m)
    .unwrap()
    .object_code;
    let mut f = Fixture::with_object(m, object, DARWIN);
    for fun in &f.m_cg.functions {
        if fun.calling_conv != CallingConv::C {
            continue;
        }
        let sig = f.m_cg.func_type(fun.ty).unwrap();
        let p = f.placements.get_mut(&fun.name).unwrap();
        for (ty, pp) in sig.params.iter().zip(&mut p.params) {
            if signed_small_width(ty).is_some() {
                let ParamPlace::Scalar(s) = pp else { panic!("signed scalar") };
                s.ext = AbiExt::Sext;
            }
        }
        if sig.returns.len() == 1 && signed_small_width(&sig.returns[0]).is_some() {
            let ReturnPlace::Scalar(s) = &mut p.ret else { panic!("signed scalar result") };
            s.ext = AbiExt::Sext;
        }
    }
    f
}
fn values(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("signed_values");
    for (ty, width) in [(Ty::I8, 8), (Ty::I16, 16)] {
        let sig = b.sig(&[ty.clone()], Some(ty.clone()));
        b.define(&format!("c_i{width}_id"), sig, Linkage::External, |f| f.ret(f.p(0)));
        let not = b.define(&format!("c_i{width}_not"), sig, Linkage::External, |f| {
            let v = f.push_inst(Inst::UnOp { op: UnOp::Not, ty: ty.clone(), operand: f.p(0) });
            f.ret(v)
        });
        b.define(&format!("c_i{width}_via"), sig, Linkage::External, |f| {
            let v = f.call(not, &[f.p(0)]);
            f.ret(v)
        });
    }
    let mut m = b.finish();
    for f in &mut m.functions {
        f.calling_conv = CallingConv::C;
    }
    compile(m, opt, &["c_i8_not", "c_i16_not"])
}
fn save(label: &str, f: &Fixture, r: &super::super::CerReport) {
    if let Some(out) = std::env::var_os("TRUST_CER_C_SIGNED_OUTPUT_DIR") {
        let p = std::path::PathBuf::from(out).join(label);
        std::fs::create_dir_all(&p).unwrap();
        std::fs::write(p.join("object.o"), &f.object).unwrap();
        std::fs::write(p.join("certificates.json"), r.to_json()).unwrap();
        std::fs::write(p.join("disassembly.txt"), disassemble(&f.object)).unwrap();
    }
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn signed_actual_compiler_full_w0_and_tail_call() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let f = values(opt);
        let r = f.report();
        save(&format!("values-{opt:?}"), &f, &r);
        assert_eq!(r.certificates.len(), 6);
        assert_eq!(r.closure.closed_kernel.len(), 6, "{}", explain(&r));
        assert!(r.certificates.iter().all(|c| c.is_kernel_proved()), "{}", explain(&r));
        assert!(r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
        for width in [8, 16] {
            let bad = f.patched(|o| {
                let words = function_words(o, &format!("c_i{width}_not"));
                for (at, _) in &words {
                    patch_word(o, *at, 0xd503201f);
                }
                // Correct declared low bits, wrong required signed W0 padding.
                patch_word(o, words[0].0, 0x2a2003e0); // MVN W0,W0
                patch_word(o, words[1].0, if width == 8 { 0x53001c00 } else { 0x53003c00 }); // UXTB/UXTH W0,W0
                patch_word(o, words.last().unwrap().0, 0xd65f03c0);
            });
            let report = bad.report();
            save(&format!("wrong-zext-{width}-{opt:?}"), &bad, &report);
            assert!(
                matches!(
                    report.certificate(&format!("c_i{width}_not")).unwrap().verdict,
                    crate::verify_output::OutputVerdict::Refuted { .. }
                ),
                "{}",
                explain(&report)
            );
            assert!(report.ships(crate::verify_output::EmitPolicy::AllowUnknown).is_err());
        }
    }
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn signed_original_terms_keep_every_sign_and_padding_bit() {
    for invalid in [
        Formula::BvSignExt(b(Formula::Var("zero-width".into(), Sort::BitVec(0))), 1),
        Formula::BvSignExt(b(Formula::Var("too-wide".into(), Sort::BitVec(128))), 1),
        Formula::BvSignExt(b(Formula::Var("overflow".into(), Sort::BitVec(8))), u32::MAX),
    ] {
        assert!(
            crate::verify_output::try_kernel_recheckable_original_conjunction(&[(
                invalid.clone(),
                invalid
            )])
            .is_none()
        );
    }
    for width in [8, 16] {
        // MSB/LSB-opposite constants independently exercise the semantic encoder,
        // rather than proving only a reflexive expression with the same renderer.
        for value in [0, 1, (1u64 << (width - 1)) - 1, 1u64 << (width - 1), (1u64 << width) - 1] {
            let expected = if value & (1u64 << (width - 1)) != 0 {
                value | ((u32::MAX as u64) << width)
            } else {
                value
            } as u32;
            assert!(
                crate::verify_output::try_kernel_recheckable_original_conjunction(&[(
                    Formula::BvSignExt(b(bv(value, width)), 32 - width),
                    bv(u64::from(expected), 32)
                )])
                .is_some(),
                "signed constant{value:#x} width{width}"
            );
        }
        let value = Formula::Var(format!("raw_{width}"), Sort::BitVec(width));
        let sign = Formula::BvSignExt(b(value.clone()), 32 - width);
        let items = vec![(sign.clone(), sign.clone())];
        assert!(
            crate::verify_output::try_kernel_recheckable_original_conjunction(&items).is_some(),
            "actual sign-extension original goal"
        );
        assert!(
            crate::verify_output::try_kernel_recheckable_original_conjunction(&[(
                sign,
                Formula::BvZeroExt(b(value), 32 - width)
            )])
            .is_none(),
            "negative inputs distinguish sign/zero extension"
        );
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn signed_memory_leaves_retain_original_and_narrow_memory_tails_stay_unknown() {
    use trust_ir::inst::CastOp;
    let mut b = ModBuilder::new("signed_ret_memory");
    for (ty, width) in [(Ty::I8, 8), (Ty::I16, 16)] {
        let sig = b.sig(&[Ty::Ptr, Ty::U64], Some(ty.clone()));
        let leaf = b.define(&format!("signed_store_{width}"), sig, Linkage::External, |f| {
            let value = f.push_inst(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U64,
                dst_ty: Ty::U8,
                operand: f.p(1),
            });
            f.push_inst_void(Inst::Store {
                ty: Ty::U8,
                ptr: f.p(0),
                value,
                volatile: false,
                align: Some(1),
            });
            let v = f.konst(ty.clone(), -7);
            f.ret(v);
        });
        b.define(&format!("signed_tail_{width}"), sig, Linkage::External, |f| {
            let v = f.call(leaf, &[f.p(0), f.p(1)]);
            f.ret(v)
        });
    }
    let mut m = b.finish();
    for fun in &mut m.functions {
        fun.calling_conv = CallingConv::C;
    }
    let f = compile(m, OptLevel::O3, &["signed_store_8", "signed_store_16"]);
    let report = f.report();
    save("signed-original-memory-tail", &f, &report);
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 2, "{}", explain(&report));
    for width in [8, 16] {
        let leaf = report.certificate(&format!("signed_store_{width}")).unwrap();
        assert!(leaf.is_kernel_proved() && leaf.original_proof.is_some());
        let tail = report.certificate(&format!("signed_tail_{width}")).unwrap();
        assert!(matches!(tail.verdict, crate::verify_output::OutputVerdict::Unknown { .. }));
        assert!(tail.original_proof.is_none());
        assert!(tail.obligations.o5_frame.detail.contains("M5"));
    }
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
    let input = super::super::CerInput {
        m_cg: &f.m_cg,
        producers: &f.producers,
        bodies: &f.bodies,
        placements: &f.placements,
        object: &f.object,
        relocation_model: f.model,
    };
    let result = crate::original_conjunction_certificate::without_production(|| {
        super::super::replay_original_certificates(&input, report.to_json().as_bytes())
    })
    .unwrap();
    assert_eq!(result.rows.len(), 4);
    assert_eq!(result.rows.iter().filter(|r| r.replayed).count(), 2, "{result:?}");
    assert!(!result.all_replayed(), "narrow memory Tail remains outside full64 M5");
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn run_native(label: &str, f: &Fixture, expected: i32) {
    use std::fs;
    use std::process::Command;
    let temp = tempfile::tempdir().unwrap();
    let p = temp.path();
    let driver =
        include_str!("../../../../../tests/run-make/trust-cg-source-c-signed-abi/driver.c");
    let observer =
        include_str!("../../../../../tests/run-make/trust-cg-source-c-signed-abi/observe.S");
    // Test models use shorter symbols than the maintained Rust source fixture.
    let driver = format!(
        "#define SKIP_SIGNED_STORES 1\n{}",
        driver.replace("trust_c_i", "c_i").replace("_tail", "_via")
    );
    fs::write(p.join("object.o"), &f.object).unwrap();
    fs::write(p.join("driver.c"), driver).unwrap();
    fs::write(p.join("observe.S"), observer).unwrap();
    let build = Command::new("/usr/bin/cc")
        .current_dir(p)
        .args([
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "driver.c",
            "observe.S",
            "object.o",
            "-o",
            "driver",
        ])
        .output()
        .unwrap();
    assert!(build.status.success(), "{}", String::from_utf8_lossy(&build.stderr));
    let output = Command::new(p.join("driver")).output().unwrap();
    if let Some(out) = std::env::var_os("TRUST_CER_C_SIGNED_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out).join(label);
        fs::create_dir_all(&out).unwrap();
        for name in ["object.o", "driver.c", "observe.S", "driver"] {
            fs::copy(p.join(name), out.join(name)).unwrap();
        }
        fs::write(out.join("stdout.txt"), &output.stdout).unwrap();
        fs::write(out.join("stderr.txt"), &output.stderr).unwrap();
        fs::write(
            out.join("native-result.json"),
            serde_json::to_vec_pretty(
                &serde_json::json!({"expected_exit":expected,"actual_exit":output.status.code()}),
            )
            .unwrap(),
        )
        .unwrap();
    }
    assert_eq!(
        output.status.code(),
        Some(expected),
        "{label}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
#[test]
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn signed_native_exhaustive_w0_and_wrong_padding() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let f = values(opt);
        run_native(&format!("native-{opt:?}"), &f, 0);
        for width in [8, 16] {
            let bad = f.patched(|o| {
                let words = function_words(o, &format!("c_i{width}_not"));
                for (at, _) in &words {
                    patch_word(o, *at, 0xd503201f);
                }
                patch_word(o, words[0].0, 0x2a2003e0);
                patch_word(o, words[1].0, if width == 8 { 0x53001c00 } else { 0x53003c00 });
                patch_word(o, words.last().unwrap().0, 0xd65f03c0);
            });
            run_native(&format!("native-wrong-zext-{width}-{opt:?}"), &bad, 1);
        }
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn signed_actual_weaker_rust_padding_at_named_tail_remains_unknown() {
    let mut b = ModBuilder::new("signed_weaker_padding");
    for (ty, width) in [(Ty::I8, 8), (Ty::I16, 16)] {
        let sig = b.sig(&[ty.clone()], Some(ty.clone()));
        let callee = b.define(&format!("rust_signed_{width}"), sig, Linkage::External, |f| {
            let v = f.konst(ty.clone(), -(1i128 << (width - 1)));
            f.ret(v);
        });
        b.m.functions[callee.as_usize()].calling_conv = CallingConv::Rust;
        let caller =
            b.define(&format!("c_signed_from_rust_{width}"), sig, Linkage::External, |f| {
                let v = f.call(callee, &[f.p(0)]);
                f.ret(v);
            });
        b.m.functions[caller.as_usize()].calling_conv = CallingConv::C;
    }
    let f = compile(b.finish(), OptLevel::O3, &["rust_signed_8", "rust_signed_16"]);
    let bad = f.patched(|o| {
        for width in [8, 16] {
            let words = function_words(o, &format!("rust_signed_{width}"));
            for (at, _) in &words {
                patch_word(o, *at, 0xd503201f);
            }
            patch_word(o, words[0].0, 0x52800000 | ((1u32 << (width - 1)) << 5)); // MOVZ W0: correct Rust low value, arbitrary padding
            patch_word(o, words.last().unwrap().0, 0xd65f03c0);
            let words = function_words(o, &format!("c_signed_from_rust_{width}"));
            let (at, word) = words
                .iter()
                .find(|(_, w)| w & 0xfc000000 == 0x94000000 || w & 0xfc000000 == 0x14000000)
                .copied()
                .unwrap();
            assert_eq!(word & 0x03ffffff, 0, "retain canonical named BR26 operand");
            for (p, _) in words {
                patch_word(o, p, 0xd503201f);
            }
            patch_word(o, at, 0x14000000);
        }
    });
    let report = bad.report();
    save("weaker-signed-tail", &bad, &report);
    assert_eq!(report.certificates.len(), 4);
    for width in [8, 16] {
        assert!(report.certificate(&format!("rust_signed_{width}")).unwrap().is_kernel_proved());
        let caller = report.certificate(&format!("c_signed_from_rust_{width}")).unwrap();
        assert!(
            matches!(caller.verdict, crate::verify_output::OutputVerdict::Unknown { .. }),
            "{}",
            explain(&report)
        );
        assert!(
            caller.obligations.o4_return.detail.contains("cannot inherit sign extension"),
            "{}",
            explain(&report)
        );
    }
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        use std::fs;
        use std::process::Command;
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path();
        fs::write(p.join("object.o"), &bad.object).unwrap();
        fs::write(
            p.join("observe.S"),
            include_str!("../../../../../tests/run-make/trust-cg-source-c-signed-abi/observe.S"),
        )
        .unwrap();
        fs::write(p.join("driver.c"),r#"
#include <stdint.h>
#include <stdio.h>
extern int8_t c_signed_from_rust_8(int8_t);
extern int16_t c_signed_from_rust_16(int16_t);
extern uint32_t observe_signed_w0(uintptr_t,uint64_t);
int main(void) {
 uint32_t a=observe_signed_w0((uintptr_t)c_signed_from_rust_8,UINT64_C(0xdeadbeef00000000));
 uint32_t b=observe_signed_w0((uintptr_t)c_signed_from_rust_16,UINT64_C(0xdeadbeef00000000));
 printf("actual W0 i8=%08x i16=%08x; expected C signed W0 i8=%08x i16=%08x\n",a,b,(uint32_t)(int32_t)INT8_MIN,(uint32_t)(int32_t)INT16_MIN);
 return (a&255u)==128u&&(b&65535u)==32768u&&a==UINT32_C(0x80)&&b==UINT32_C(0x8000)&&a!=(uint32_t)(int32_t)INT8_MIN&&b!=(uint32_t)(int32_t)INT16_MIN?0:2;
}
"#).unwrap();
        let link = Command::new("/usr/bin/cc")
            .current_dir(p)
            .args([
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "driver.c",
                "observe.S",
                "object.o",
                "-o",
                "driver",
            ])
            .output()
            .unwrap();
        assert!(link.status.success(), "{}", String::from_utf8_lossy(&link.stderr));
        let output = Command::new(p.join("driver")).output().unwrap();
        if let Some(out) = std::env::var_os("TRUST_CER_C_SIGNED_OUTPUT_DIR") {
            let out = std::path::PathBuf::from(out).join("native-weaker-signed-tail");
            fs::create_dir_all(&out).unwrap();
            for name in ["object.o", "driver.c", "observe.S", "driver"] {
                fs::copy(p.join(name), out.join(name)).unwrap();
            }
            fs::write(out.join("stdout.txt"), &output.stdout).unwrap();
            fs::write(out.join("stderr.txt"), &output.stderr).unwrap();
            fs::write(out.join("native-result.json"),serde_json::to_vec(&serde_json::json!({"exit":output.status.code(),"stdout":String::from_utf8_lossy(&output.stdout),"expected_contract_mismatch":true})).unwrap()).unwrap();
        }
        assert!(
            output.status.success(),
            "native contract observation: {}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
}

#[test]
#[cfg(not(feature = "kernel-recheck"))]
fn signed_missing_kernel_cannot_grant_physical_abi_proof_grade() {
    let f = values(OptLevel::O3);
    let report = f.report();
    save("signed-missing-kernel", &f, &report);
    assert_eq!(report.certificates.len(), 6);
    assert!(
        report.certificates.iter().all(|c| !c.is_kernel_proved() && c.original_proof.is_none())
    );
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
}
