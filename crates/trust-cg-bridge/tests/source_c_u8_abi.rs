//! Exact Darwin C-u8 ABI diagnostic. Compiles real native-C objects and reads
//! W0 through assembly wrappers, so checking only the low byte cannot pass.
//! CER must independently prove the full physical contract without erasing P flags.
#![cfg(all(feature = "kernel-recheck", target_arch = "aarch64", target_os = "macos"))]

mod cer_common;

use std::fs;
use std::process::Command;

use cer_common::*;
use trust_cg_bridge::call_event::{AbiExt, ParamPlace, ReturnPlace};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::{CastOp, Inst, UnOp};
use trust_ir::{CallingConv, Linkage, Ty};

fn module() -> trust_ir::Module {
    let mut b = ModBuilder::new("darwin_c_u8_abi");
    let byte = b.sig(&[Ty::U8], Some(Ty::U8));
    b.define("trust_c_u8_id", byte, Linkage::External, |f| f.ret(f.p(0)));
    let not = b.define("trust_c_u8_not", byte, Linkage::External, |f| {
        let r = f.push_inst(Inst::UnOp { op: UnOp::Not, ty: Ty::U8, operand: f.p(0) });
        f.ret(r);
    });
    b.define("trust_c_u8_xor", byte, Linkage::External, |f| {
        let mask = f.konst(Ty::U8, 0xa5);
        let r = f.bin(trust_ir::inst::BinOp::Xor, Ty::U8, f.p(0), mask);
        f.ret(r);
    });
    b.define("trust_c_u8_constant", byte, Linkage::External, |f| {
        let r = f.konst(Ty::U8, 0xd3);
        f.ret(r);
    });
    b.define("trust_c_u8_rust_typed_not", byte, Linkage::External, |f| {
        let r = f.call(not, &[f.p(0)]);
        f.ret(r);
    });
    let wide = b.sig(&[Ty::U32], Some(Ty::U8));
    b.define("trust_c_u8_trunc", wide, Linkage::External, |f| {
        let r = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U32,
            dst_ty: Ty::U8,
            operand: f.p(0),
        });
        f.ret(r);
    });
    let mut module = b.finish();
    // Record the actual compile target for the C-u8 physical contract.
    module.target_info = Some(trust_ir::TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    for f in &mut module.functions {
        f.calling_conv = CallingConv::C;
    }
    module
}

fn command_ok(command: &mut Command) {
    let output = command.output().expect("run native diagnostic");
    assert!(
        output.status.success(),
        "{command:?}: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn actual_native_c_u8_values_satisfy_the_entire_w0_contract() {
    for opt in [OptLevel::O0, OptLevel::O3] {
        let m = module();
        let object = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: opt,
                parallel: false,
                emit_proofs: false,
                never_inline: ["trust_c_u8_not".into()].into_iter().collect(),
                ..CompilerConfig::default()
            },
            TargetSpec::parse(DARWIN).unwrap(),
        )
        .with_codegen_license(fixture_license())
        .compile(&m)
        .expect("actual fullCompiler scalar C ABI object")
        .object_code;
        assert!(
            function_words(&object, "trust_c_u8_rust_typed_not")
                .iter()
                .any(|(_, word)| word & 0xfc00_0000 == 0x9400_0000),
            "typed C call must stay a real BL at {opt:?}"
        );
        let mut fixture = Fixture::with_object(m, object.clone(), DARWIN);
        // This is the exact Darwin C-u8 shape independently observed through
        // rustc's real FnAbi: declared8 bits plus Zext to32, never a width32
        // producer type. Natural hand-built defaults MUST NOT erase the flags.
        for p in fixture.placements.values_mut() {
            if let Some(ParamPlace::Scalar(s)) = p.params.first_mut() {
                if s.width == 8 {
                    s.ext = AbiExt::Zext;
                }
            }
            let ReturnPlace::Scalar(s) = &mut p.ret else {
                panic!("scalar result");
            };
            assert_eq!(s.width, 8);
            s.ext = AbiExt::Zext;
        }
        for (name, placement) in &fixture.placements {
            let expected = if name.ends_with("trunc") {
                "d3df5de477cebb3d26a08785abcb0e25d3e871a85586758808c15789c07a29af"
            } else {
                "7e2f4e71c701a4e1e00732f67298ffb4594c3759eb6f41a457ce13cc6ebb8eec"
            };
            assert_eq!(placement.digest(), expected, "exact observed slot contract for {name}");
        }
        let report = fixture.report();
        for certificate in &report.certificates {
            assert!(certificate.is_kernel_proved(), "{}", explain(&report));
            assert!(certificate.abi_contracts.contains_key(&certificate.symbol));
        }
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        let temp = tempfile::tempdir().unwrap();
        fs::write(temp.path().join("native.o"), object).unwrap();
        fs::write(temp.path().join("driver.c"), DRIVER).unwrap();
        fs::write(temp.path().join("observe.S"), OBSERVE).unwrap();
        command_ok(Command::new("/usr/bin/cc").current_dir(temp.path()).args([
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "driver.c",
            "observe.S",
            "native.o",
            "-o",
            "driver",
        ]));
        command_ok(Command::new(temp.path().join("driver")).current_dir(temp.path()));

        // Hostile byte-only mutation: MVN W0,W0; RET computes the correct low8
        // complement, but violates the Darwin zero-extension contract. The
        // untyped W0 observer must reject it even though byte-only tests pass.
        let mut mutant = fixture.object.clone();
        let words = function_words(&mutant, "trust_c_u8_not");
        assert!(words.len() >= 2);
        for (offset, _) in &words { patch_word(&mut mutant, *offset, 0xd503_201f); }
        patch_word(&mut mutant, words[0].0, 0x2a20_03e0); // mvn w0,w0
        patch_word(&mut mutant, words.last().unwrap().0, 0xd65f_03c0); // ret
        let hostile = fixture.patched(|object| object.copy_from_slice(&mutant));
        let bad = hostile.report();
        assert!(matches!(bad.certificate("trust_c_u8_not").unwrap().verdict,
            OutputVerdict::Refuted { .. }), "{}", explain(&bad));
        assert!(bad.ships(EmitPolicy::AllowUnknown).is_err());
        fs::write(temp.path().join("mutant.o"), mutant).unwrap();
        fs::write(temp.path().join("mutant.c"), MUTANT_DRIVER).unwrap();
        command_ok(Command::new("/usr/bin/cc").current_dir(temp.path()).args([
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "mutant.c",
            "observe.S",
            "mutant.o",
            "-o",
            "mutant-driver",
        ]));
        let status = Command::new(temp.path().join("mutant-driver")).status().unwrap();
        assert_eq!(status.code(), Some(1), "mutant must preserve low8 yet fail wholeW0");
        if let Some(output) = std::env::var_os("TRUST_SOURCE_C_U8_EVIDENCE") {
            let output = std::path::PathBuf::from(output).join(format!("{opt:?}"));
            fs::create_dir_all(&output).unwrap();
            fs::write(output.join("certificates.json"), report.to_json()).unwrap();
            for name in [
                "native.o",
                "driver.c",
                "observe.S",
                "driver",
                "mutant.o",
                "mutant.c",
                "mutant-driver",
            ] {
                fs::copy(temp.path().join(name), output.join(name)).unwrap();
            }
        }
    }
}

const OBSERVE: &str = include_str!("../../../tests/run-make/trust-cg-source-c-u8-abi/observe.S");
const DRIVER: &str = include_str!("../../../tests/run-make/trust-cg-source-c-u8-abi/driver.c");

const MUTANT_DRIVER: &str = r#"
#include <stdint.h>
extern uint32_t observe_not_w0(uint8_t);
int main(void) {
    uint32_t result=observe_not_w0(0);
    if ((result & 255u) != 255u) return 2; /* a low8 disagreement is the wrong mutant */
    return result == 255u ? 0 : 1; /*1 means exactly the missed high-bit contract*/
}
"#;
