use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::inst::{BinOp, CastOp, Inst, UnOp};
use trust_ir::{StructPassingPolicy, TargetInfo};

fn module() -> Module {
    let mut m = Module::new("c_u16_boundary");
    m.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    m
}
fn scalar(width: u32, extension: AbiExt) -> ScalarPlace {
    ScalarPlace { slot: Slot::Gpr(0), width, ext: extension }
}
fn place(width: u32, extension: AbiExt) -> FnPlacement {
    FnPlacement {
        params: vec![ParamPlace::Scalar(scalar(width, extension))],
        ret: ReturnPlace::Scalar(scalar(width, extension)),
    }
}
fn kernel(equations: &[(Formula, Formula)]) {
    assert!(crate::verify_output::try_kernel_recheckable_conjunction(equations).is_some_and(|e| {
        crate::verify_output::OutputVerdict::Proven { evidence: e }.is_kernel_proved()
    }));
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unsigned16_domain_physical_result_and_every_padding_bit_are_kernel_checked() {
    for (ty, width) in [(Ty::U8, 8), (Ty::U16, 16)] {
        let p = place(width, AbiExt::Zext);
        let plan =
            Plan::new(&module(), CallingConv::C, &[ty.clone()], &[ty.clone()], &p, true).unwrap();
        kernel(&plan.entry_equations());
        let record = plan.record().unwrap();
        assert!(record.slots.iter().all(|slot| slot.declared_width == width
            && slot.required_width == 32
            && slot.extension == AbiExt::Zext));
        assert_eq!(record.placement_sha256, p.digest());
        let raw = Formula::Var("X0".into(), Sort::BitVec(64));
        let mut state = MachineState::symbolic();
        plan.apply_entry(&mut state);
        assert_eq!(state.gpr[0], plan.source_entry(raw.clone()));
        let mut concrete = trust_machine_sem::ConcreteState::new();
        concrete.gpr[0] = 0xdead_beef_a5c3_9e71;
        assert_eq!(
            concrete.eval_bv(&state.gpr[0], 64).unwrap(),
            u128::from(0xdead_beef_0000_0000 | (concrete.gpr[0] & ((1 << width) - 1)))
        );
        let result = Formula::Var("R".into(), Sort::BitVec(width));
        let high = Formula::Var("PAD".into(), Sort::BitVec(64));
        let post = post_call_unsigned(result.clone(), high.clone(), width).unwrap();
        kernel(&[
            (extract(post.clone(), 31, 0), Formula::BvZeroExt(b(result.clone()), 32 - width)),
            (extract(post, 63, 32), extract(high.clone(), 63, 32)),
        ]);
        let unextended = post_call_unextended_small(result.clone(), high.clone(), width).unwrap();
        kernel(&[
            (extract(unextended.clone(), width - 1, 0), result),
            (extract(unextended, 63, width), extract(high, 63, width)),
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
        assert!(rust.record().is_none() && rust.entry_equations().is_empty());
        let mut untouched = MachineState::symbolic();
        let before = untouched.gpr.clone();
        rust.apply_entry(&mut untouched);
        assert_eq!(untouched.gpr, before);
        assert_eq!(rust.source_entry(raw.clone()), raw);
    }
}
#[test]
fn unsigned16_authority_and_weaker_tail_contracts_fail_closed() {
    let p = place(16, AbiExt::Zext);
    for variant in 0..10 {
        let mut m = module();
        let mut p = p.clone();
        let mut conv = CallingConv::C;
        let mut ty = Ty::U16;
        match variant {
            0 => m.target_info = None,
            1 => m.target_info.as_mut().unwrap().triple = "aarch64-unknown-linux-gnu".into(),
            2 => m.target_info.as_mut().unwrap().pointer_size = 4,
            3 => conv = CallingConv::Rust,
            4 => ty = Ty::I16,
            5 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.ext = AbiExt::Sext
                }
            }
            6 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.ext = AbiExt::None
                }
            }
            7 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.width = 8
                }
            }
            8 => {
                if let ParamPlace::Scalar(s) = &mut p.params[0] {
                    s.slot = Slot::Stack { offset: 0 }
                }
            }
            _ => m.target_info.as_mut().unwrap().endianness = Endianness::Big,
        }
        assert!(Plan::new(&m, conv, &[ty], &[Ty::U16], &p, true).is_err(), "variant{variant}");
    }
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
    assert!(check_tail_transport(&p.ret, &place(16, AbiExt::None).ret).is_err());
    assert!(check_tail_transport(&p.ret, &place(8, AbiExt::Zext).ret).is_err());
    assert!(check_tail_transport(&p.ret, &p.ret).is_ok());
    assert_eq!(physical_width(&scalar(16, AbiExt::Zext)), 32);
    assert_eq!(physical_width(&scalar(16, AbiExt::None)), 16);
    assert!(physical_value(&scalar(16, AbiExt::Zext), bv(1, 32)).is_err());
    assert!(post_call_unsigned(bv(1, 16), bv(0, 64), 32).is_err());
}
fn compile(mut m: Module, opt: OptLevel, never_inline: &[&str]) -> Fixture {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    m.target_info = module().target_info;
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: never_inline.iter().map(|s| (*s).into()).collect(),
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
            if *ty == Ty::U16 {
                let ParamPlace::Scalar(s) = pp else { panic!("u16 scalar") };
                s.ext = AbiExt::Zext
            }
        }
        if sig.returns == [Ty::U16] {
            let ReturnPlace::Scalar(s) = &mut p.ret else { panic!("u16 result") };
            s.ext = AbiExt::Zext
        }
    }
    f
}
fn c_fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("c_u16_values");
    let sig = b.sig(&[Ty::U16], Some(Ty::U16));
    b.define("c_u16_id", sig, trust_ir::Linkage::External, |f| f.ret(f.p(0)));
    let not = b.define("c_u16_not", sig, trust_ir::Linkage::External, |f| {
        let v = f.push_inst(Inst::UnOp { op: UnOp::Not, ty: Ty::U16, operand: f.p(0) });
        f.ret(v)
    });
    b.define("c_u16_xor", sig, trust_ir::Linkage::External, |f| {
        let k = f.konst(Ty::U16, 0xa5c3);
        let v = f.bin(BinOp::Xor, Ty::U16, f.p(0), k);
        f.ret(v)
    });
    b.define("c_u16_constant", sig, trust_ir::Linkage::External, |f| {
        let v = f.konst(Ty::U16, 0x9e71);
        f.ret(v)
    });
    b.define("c_u16_via", sig, trust_ir::Linkage::External, |f| {
        let v = f.call(not, &[f.p(0)]);
        f.ret(v)
    });
    let wide = b.sig(&[Ty::U32], Some(Ty::U16));
    b.define("c_u16_trunc", wide, trust_ir::Linkage::External, |f| {
        let v = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U32,
            dst_ty: Ty::U16,
            operand: f.p(0),
        });
        f.ret(v)
    });
    let mut m = b.finish();
    for f in &mut m.functions {
        f.calling_conv = CallingConv::C
    }
    compile(m, opt, &["c_u16_not"])
}
fn save(label: &str, f: &Fixture, r: &super::super::CerReport) {
    if let Some(out) = std::env::var_os("TRUST_CER_C_U16_OUTPUT_DIR") {
        let p = std::path::PathBuf::from(out).join(label);
        std::fs::create_dir_all(&p).unwrap();
        std::fs::write(p.join("object.o"), &f.object).unwrap();
        std::fs::write(p.join("certificates.json"), r.to_json()).unwrap();
        std::fs::write(p.join("disassembly.txt"), disassemble(&f.object)).unwrap();
    }
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unsigned16_full_compiler_whole_w0_and_bad_mvn_contract() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let f = c_fixture(opt);
        let r = f.report();
        save(&format!("c-{opt:?}"), &f, &r);
        assert_eq!(r.certificates.len(), 6);
        assert_eq!(r.closure.closed_kernel.len(), 6);
        assert!(r.closure.unclosed.is_empty());
        assert!(r.certificates.iter().all(|c| c.is_kernel_proved()), "{}", explain(&r));
        assert!(r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
        let bad = f.patched(|object| {
            let words = function_words(object, "c_u16_not");
            for (at, _) in &words {
                patch_word(object, *at, 0xd503201f)
            }
            patch_word(object, words[0].0, 0x2a2003e0);
            patch_word(object, words.last().unwrap().0, 0xd65f03c0)
        });
        let r = bad.report();
        save(&format!("bad-mvn-{opt:?}"), &bad, &r);
        assert!(
            matches!(
                r.certificate("c_u16_not").unwrap().verdict,
                crate::verify_output::OutputVerdict::Refuted { .. }
            ),
            "{}",
            explain(&r)
        );
        assert!(r.ships(crate::verify_output::EmitPolicy::AllowUnknown).is_err());
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn native(label: &str, f: &Fixture, asm: &str, driver: &str, expected: i32) {
    use std::fs;
    use std::process::Command;
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path();
    fs::write(p.join("object.o"), &f.object).unwrap();
    fs::write(p.join("observer.S"), asm).unwrap();
    fs::write(p.join("driver.c"), driver).unwrap();
    let out = Command::new("/usr/bin/cc")
        .current_dir(p)
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
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let out = Command::new(p.join("driver")).output().unwrap();
    assert_eq!(
        out.status.code(),
        Some(expected),
        "{label}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let output_stdout = out.stdout;
    let output_stderr = out.stderr;
    let output_exit = out.status.code();
    if let Some(out) = std::env::var_os("TRUST_CER_C_U16_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out).join(label);
        fs::create_dir_all(&out).unwrap();
        fs::write(out.join("stdout.txt"), &output_stdout).unwrap();
        fs::write(out.join("stderr.txt"), &output_stderr).unwrap();
        fs::write(
            out.join("native-result.json"),
            serde_json::to_vec_pretty(
                &serde_json::json!({"expected_exit":expected,"actual_exit":output_exit}),
            )
            .unwrap(),
        )
        .unwrap();
        for name in ["object.o", "observer.S", "driver.c", "driver"] {
            fs::copy(p.join(name), out.join(name)).unwrap();
        }
    }
}
const OBSERVE_W0: &str = r#"
.text
.globl _observe_u16_w0
_observe_u16_w0:
 stp x29,x30,[sp,#-16]!
 mov x29,sp
 mov x16,x0
 mov x0,x1
 blr x16
 ldp x29,x30,[sp],#16
 ret
"#;
const C_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
typedef uint16_t (*narrow)(uint16_t);
extern uint16_t c_u16_id(uint16_t),c_u16_not(uint16_t),c_u16_xor(uint16_t),c_u16_constant(uint16_t),c_u16_via(uint16_t);
extern uint16_t c_u16_trunc(uint32_t);
extern uint32_t observe_u16_w0(uintptr_t,uint64_t);
int main(void){narrow f[]={c_u16_id,c_u16_not,c_u16_xor,c_u16_constant,c_u16_via};
 for(uint32_t x=0;x<65536;++x){uint32_t expected[]={x,x^65535u,x^0xa5c3u,0x9e71u,x^65535u};
  for(unsigned i=0;i<5;++i){uint64_t raw=UINT64_C(0xdeadbeef00000000)|x;
   uint32_t got=observe_u16_w0((uintptr_t)f[i],raw);
   if(x<2 || x==65535)printf("C fn=%u inputX0=%016llx observedW0=%08x expectedW0=%08x\n",i,(unsigned long long)raw,got,expected[i]);
   if(got!=expected[i] || f[i]((uint16_t)x)!=expected[i]){fprintf(stderr,"fn=%u x=%04x wholeW0=%08x expected=%08x\n",i,x,got,expected[i]);return 1;}}
  if(observe_u16_w0((uintptr_t)c_u16_trunc,UINT64_C(0xdeadbeefa5c30000)|x)!=x || c_u16_trunc(0xa5c30000u|x)!=x)return 2;
 }return 0;}
"#;
#[test]
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn unsigned16_native_all_values_and_raw_w0_observer() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let f = c_fixture(opt);
        native(&format!("native-c-{opt:?}"), &f, OBSERVE_W0, C_DRIVER, 0);
        let bad = f.patched(|object| {
            let w = function_words(object, "c_u16_not");
            for (at, _) in &w {
                patch_word(object, *at, 0xd503201f)
            }
            patch_word(object, w[0].0, 0x2a2003e0);
            patch_word(object, w.last().unwrap().0, 0xd65f03c0)
        });
        native(&format!("native-bad-mvn-{opt:?}"), &bad, OBSERVE_W0, C_DRIVER, 1);
    }
}
fn rust_fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("rust_none_to_c_u16");
    let sig = b.sig(&[Ty::U16], Some(Ty::U16));
    let observe = b.declare("c_u16_observer", sig);
    let high = b.declare("c_u16_high_result", sig);
    b.define("rust_half_caller", sig, trust_ir::Linkage::External, |f| {
        let r = f.call(observe, &[f.p(0)]);
        f.ret(r)
    });
    let wide = b.sig(&[Ty::U16], Some(Ty::U64));
    b.define("rust_half_widen", wide, trust_ir::Linkage::External, |f| {
        let r = f.call(high, &[f.p(0)]);
        let r = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U16,
            dst_ty: Ty::U64,
            operand: r,
        });
        f.ret(r)
    });
    let mut m = b.finish();
    for f in &mut m.functions {
        f.calling_conv = CallingConv::Rust
    }
    m.functions[observe.as_usize()].calling_conv = CallingConv::C;
    m.functions[high.as_usize()].calling_conv = CallingConv::C;
    compile(m, opt, &[])
}
const RUST_OBSERVER: &str = r#"
.text
.globl _observe_rust_half_caller
_observe_rust_half_caller:
 stp x29,x30,[sp,#-16]!
 mov x29,sp
 bl _rust_half_caller
 uxth w0,w0
 ldp x29,x30,[sp],#16
 ret
.globl _observe_rust_half_widen
_observe_rust_half_widen:
 stp x29,x30,[sp,#-16]!
 mov x29,sp
 bl _rust_half_widen
 ldp x29,x30,[sp],#16
 ret
.globl _c_u16_observer
_c_u16_observer:
 adrp x8,_last_half_argument@PAGE
 str w0,[x8,_last_half_argument@PAGEOFF]
 uxth w8,w0
 cmp w8,w0
 b.ne 1f
 mvn w0,w0
 uxth w0,w0
 ret
1: mov w0,#0
 ret
.globl _c_u16_high_result
_c_u16_high_result:
 adrp x8,_last_half_argument@PAGE
 str w0,[x8,_last_half_argument@PAGEOFF]
 uxth w8,w0
 cmp w8,w0
 b.ne 2f
 mov w8,#0x5ac3
 eor w0,w0,w8
 mov x8,#0xdead
 lsl x8,x8,#32
 orr x0,x0,x8
 ret
2: mov w0,#0
 ret
"#;
const RUST_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
uint32_t last_half_argument;
extern uint32_t observe_rust_half_caller(uint64_t);
extern uint64_t observe_rust_half_widen(uint64_t);
int main(void){for(uint32_t x=0;x<65536;++x){uint64_t raw=UINT64_C(0xfedcba98a5c30000)|x;
 uint32_t a=observe_rust_half_caller(raw);uint32_t argA=last_half_argument;
 uint64_t b=observe_rust_half_widen(raw);uint32_t argB=last_half_argument;
 if(x<2 || x==65535)printf("Rust inputX0=%016llx CargA=%08x CargB=%08x result16=%08x result64=%016llx\n",(unsigned long long)raw,argA,argB,a,(unsigned long long)b);
 if(a!=(x^65535u) || b!=(x^0x5ac3u) || argA!=x || argB!=x){fprintf(stderr,"input=%04x narrow=%08x wide=%016llx\n",x,a,(unsigned long long)b);return 1;}}
 return 0;}
"#;
fn remove_half_extracts(object: &mut [u8], name: &str, before_call: bool) {
    let words = function_words(object, name);
    let call = words.iter().find(|(_, w)| w & 0xfc000000 == 0x94000000).unwrap().0;
    let mut count = 0;
    for (at, w) in words {
        if (at < call) == before_call
            && w & 0xffc00000 == 0x53000000
            && (w >> 16) & 63 == 0
            && (w >> 10) & 63 == 15
        {
            let dst = w & 31;
            let src = (w >> 5) & 31;
            patch_word(object, at, 0x2a0003e0 | (src << 16) | dst);
            count += 1
        }
    }
    assert!(count > 0, "actual u16 extension must be present")
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unsigned16_rust_none_call_arguments_and_external_padding() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let f = rust_fixture(opt);
        let r = f.report();
        save(&format!("rust-{opt:?}"), &f, &r);
        assert_eq!(r.certificates.len(), 2);
        assert_eq!(r.closure.closed_kernel.len(), 2);
        assert!(
            r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok(),
            "{}",
            explain(&r)
        );
        assert!(
            r.certificates
                .iter()
                .all(|c| c.is_kernel_proved() && !c.abi_contracts.contains_key(&c.symbol))
        );
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        native(&format!("native-rust-{opt:?}"), &f, RUST_OBSERVER, RUST_DRIVER, 0);
        let bad = f.patched(|o| remove_half_extracts(o, "rust_half_caller", true));
        let r = bad.report();
        save(&format!("missing-caller-extension-{opt:?}"), &bad, &r);
        assert!(
            matches!(
                r.certificate("rust_half_caller").unwrap().verdict,
                crate::verify_output::OutputVerdict::Refuted { .. }
            ),
            "{}",
            explain(&r)
        );
        assert!(r.ships(crate::verify_output::EmitPolicy::AllowUnknown).is_err());
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        native(&format!("native-bad-call-{opt:?}"), &bad, RUST_OBSERVER, RUST_DRIVER, 1);
    }
}
#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unsigned16_weaker_result_padding_and_tail_remain_unknown() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let mut b = ModBuilder::new("u16_weaker_padding");
        let sig = b.sig(&[Ty::U16], Some(Ty::U16));
        let callee =
            b.define("rust_none_identity", sig, trust_ir::Linkage::External, |f| f.ret(f.p(0)));
        let caller = b.define("c_half_from_rust", sig, trust_ir::Linkage::External, |f| {
            let r = f.call(callee, &[f.p(0)]);
            f.ret(r)
        });
        let mut m = b.finish();
        for f in &mut m.functions {
            f.calling_conv = CallingConv::Rust
        }
        m.functions[caller.as_usize()].calling_conv = CallingConv::C;
        let f = compile(m, opt, &["rust_none_identity"]);
        let r = f.report();
        save(&format!("weaker-good-{opt:?}"), &f, &r);
        assert!(
            r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok(),
            "{}",
            explain(&r)
        );
        let bad = f.patched(|o| remove_half_extracts(o, "c_half_from_rust", false));
        let r = bad.report();
        save(&format!("weaker-unmasked-{opt:?}"), &bad, &r);
        let c = r.certificate("c_half_from_rust").unwrap();
        assert!(
            matches!(c.verdict, crate::verify_output::OutputVerdict::Unknown { .. }),
            "{}",
            explain(&r)
        );
        assert!(c.obligations.o4_return.detail.contains("unspecified callee result padding"));
        assert!(r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
        let tail = f.patched(|o| {
            let words = function_words(o, "c_half_from_rust");
            let (at, w) =
                words.iter().find(|(_, w)| w & 0xfc000000 == 0x94000000).copied().unwrap();
            for (p, _) in words {
                patch_word(o, p, 0xd503201f)
            }
            patch_word(o, at, 0x14000000 | (w & 0x03ffffff))
        });
        let r = tail.report();
        save(&format!("weaker-tail-{opt:?}"), &tail, &r);
        let c = r.certificate("c_half_from_rust").unwrap();
        assert!(
            matches!(c.verdict, crate::verify_output::OutputVerdict::Unknown { .. }),
            "{}",
            explain(&r)
        );
        assert!(c.obligations.o4_return.detail.contains("cannot inherit zero extension"));
        assert!(r.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn unsigned16_actual_input_output_snapshots_keep_legal_padding_countermodel_unknown() {
    let p = place(16, AbiExt::Zext);
    let plan = Plan::new(&module(), CallingConv::C, &[Ty::U16], &[Ty::U16], &p, true).unwrap();
    let mut actual = MachineState::symbolic();
    let entry_before = actual.gpr[0].clone();
    plan.apply_entry(&mut actual);
    let result = extract(Formula::Var("X0".into(), Sort::BitVec(64)), 15, 0);
    let high = Formula::Var("X9".into(), Sort::BitVec(64));
    let c = post_call_unsigned(result.clone(), high.clone(), 16).unwrap();
    let rust = post_call_unextended_small(result.clone(), high.clone(), 16).unwrap();
    let mut state = trust_machine_sem::ConcreteState::new();
    state.gpr[0] = 0xdead_beef_a5c3_9e71;
    state.gpr[9] = 0x1234_5678_a5c3_0000;
    let projected = state.eval_bv(&actual.gpr[0], 64).unwrap();
    let c_bits = state.eval_bv(&c, 64).unwrap();
    let rust_bits = state.eval_bv(&rust, 64).unwrap();
    assert_eq!(projected, 0xdead_beef_0000_9e71);
    assert_eq!(c_bits, 0x1234_5678_0000_9e71);
    assert_eq!(rust_bits, 0x1234_5678_a5c3_9e71);
    assert_ne!(rust_bits & 0xffff_ffff, 0x9e71);
    assert!(observes_callee_padding(&Formula::Var("CER_RHI@sample".into(), Sort::BitVec(64))));
    let mut equations = plan.entry_equations();
    equations.extend([
        (extract(c.clone(), 31, 0), Formula::BvZeroExt(b(result.clone()), 16)),
        (extract(c.clone(), 63, 32), extract(high.clone(), 63, 32)),
        (extract(rust.clone(), 15, 0), result),
        (extract(rust.clone(), 63, 16), extract(high, 63, 16)),
    ]);
    let evidence = crate::verify_output::try_kernel_recheckable_conjunction(&equations).unwrap();
    assert!(
        crate::verify_output::OutputVerdict::Proven { evidence: evidence.clone() }
            .is_kernel_proved()
    );
    if let Some(out) = std::env::var_os("TRUST_CER_C_U16_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        let record = serde_json::json!({"actual_entry_before":entry_before,"actual_entry_after":actual.gpr[0],"abi_record":plan.record(),"c_post_call":c,"rust_none_post_call":rust,
   "raw_input_x0":format!("{:016x}",state.gpr[0]),"raw_high_x9":format!("{:016x}",state.gpr[9]),"projected_entry_x0":format!("{projected:016x}"),"c_result_x0":format!("{c_bits:016x}"),"rust_none_result_x0":format!("{rust_bits:016x}"),
   "legal_unextended_padding_countermodel":"W[31:16] differs from C contract; unclosed abstract padding alone remains Unknown","kernel_equations":equations,"kernel_evidence":format!("{evidence:?}")});
        std::fs::write(
            out.join("actual-abi-model-snapshots.json"),
            serde_json::to_vec_pretty(&record).unwrap(),
        )
        .unwrap();
    }
}
