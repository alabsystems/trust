//! Relocation symbols do not erase the operand bits already in B/BL.
#![cfg(all(feature = "kernel-recheck", target_arch = "aarch64", target_os = "macos"))]
mod cer_common;
use std::process::{Command, Stdio};

use cer_common::*;
use trust_cg_bridge::compiled_object::{
    CompiledObject, MachineSiteKind, ObjectExpectations, ObjectLayout,
};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{Linkage, Ty};

fn fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("branch26_operand_model");
    let sig = b.sig(&[Ty::U64], Some(Ty::U64));
    let callee = b.define("constant_leaf", sig, Linkage::External, |f| {
        let answer = f.konst(Ty::U64, 7);
        f.ret(answer);
    });
    b.define("constant_caller", sig, Linkage::External, |f| {
        let result = f.call(callee, &[f.p(0)]);
        f.ret(result);
    });
    let module = targeted(&b.finish(), DARWIN);
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: ["constant_leaf".to_string()].into_iter().collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}
fn output(label: &str) -> std::path::PathBuf {
    let root =
        std::env::var_os("TRUST_BR26_OUTPUT_DIR").map(std::path::PathBuf::from).unwrap_or_else(
            || std::env::temp_dir().join(format!("trust-branch26-{}", std::process::id())),
        );
    let path = root.join(label);
    std::fs::create_dir_all(&path).unwrap();
    path
}
fn layout(f: &Fixture) -> ObjectLayout {
    let object = CompiledObject::parse(&f.object).unwrap();
    let expect = ObjectExpectations::from_module(&f.m_cg, object.format, f.model).unwrap();
    ObjectLayout::bind(object, &expect).unwrap()
}
fn native(object: &[u8], directory: &std::path::Path) -> serde_json::Value {
    std::fs::write(directory.join("subject.o"), object).unwrap();
    std::fs::write(
        directory.join("driver.c"),
        r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t constant_caller(uint64_t);
int main(void) {printf("%llu\n",(unsigned long long)constant_caller(11));return 0;}
"#,
    )
    .unwrap();
    let compile = Command::new("/usr/bin/clang")
        .current_dir(directory)
        .args(["driver.c", "subject.o", "-o", "native-driver"])
        .output()
        .unwrap();
    std::fs::write(directory.join("link.stdout"), &compile.stdout).unwrap();
    std::fs::write(directory.join("link.stderr"), &compile.stderr).unwrap();
    if !compile.status.success() {
        return serde_json::json!({"linked":false,"link_exit":compile.status.code()});
    }
    let stdout = std::fs::File::create(directory.join("native.stdout")).unwrap();
    let stderr = std::fs::File::create(directory.join("native.stderr")).unwrap();
    let mut child = Command::new(directory.join("native-driver"))
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .unwrap();
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > std::time::Duration::from_secs(5) {
            child.kill().unwrap();
            let _ = child.wait();
            return serde_json::json!({"linked":true,"timed_out":true});
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    let text = std::fs::read_to_string(directory.join("native.stdout")).unwrap();
    serde_json::json!({"linked":true,"exit":status.code(),"return_value":text.trim().parse::<u64>().ok(),"stdout":text})
}
#[test]
fn symbol_preserving_branch26_operands_require_canonical_zero() {
    let baseline = std::env::var_os("TRUST_BR26_BASELINE_OBSERVE").is_some();
    for (label, opt) in [("tail", OptLevel::O2), ("call", OptLevel::O0)] {
        let good = fixture(opt);
        let original = good.report();
        assert_eq!(original.certificates.len(), 2, "{}", explain(&original));
        assert!(
            original.certificates.iter().all(|c| c.is_kernel_proved()),
            "{}",
            explain(&original)
        );
        assert!(original.ships(EmitPolicy::StrictProvenOnly).is_ok());
        let bound = layout(&good);
        let site = &bound.windows["constant_caller"].sites[0];
        assert_eq!(site.reloc.map(|k| k.name()).as_deref(), Some("ARM64_RELOC_BRANCH26"));
        let word = word_at(&good.object, site.offset);
        assert_eq!(word & 0x03ffffff, 0);
        let (record, kind, symbol) = reloc_at(&good.object, site.offset);
        assert_eq!(kind, 2);
        let good_dir = output(&format!("{label}-original"));
        std::fs::write(good_dir.join("certificates.json"), original.to_json()).unwrap();
        std::fs::write(good_dir.join("subject.o"), &good.object).unwrap();
        let good_native = if label == "tail" {
            let n = native(&good.object, &good_dir);
            assert_eq!(n["return_value"], 7);
            n
        } else {
            serde_json::Value::Null
        };
        for immediate in [1u32, 0x03ffffff, 0x00100000] {
            let changed = good
                .patched(|bytes| patch_word(bytes, site.offset, (word & 0xfc000000) | immediate));
            assert_eq!(text_relocs(&good.object), text_relocs(&changed.object));
            assert_eq!(reloc_at(&changed.object, site.offset), (record, kind, symbol));
            let report = changed.report();
            let caller = report.certificate("constant_caller").unwrap();
            let directory = output(&format!("{label}-imm-{immediate:08x}"));
            std::fs::write(directory.join("subject.o"), &changed.object).unwrap();
            std::fs::write(directory.join("certificates.json"), report.to_json()).unwrap();
            let observed = if label == "tail" && immediate == 1 {
                native(&changed.object, &directory)
            } else {
                serde_json::json!({"executed":false,"reason":"only bounded +4 tail mutation is executed"})
            };
            std::fs::write(directory.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({"baseline_observation":baseline,"symbol":symbol,"relocation_record":record,"instruction_pc":site.offset,"original_word":word,"mutated_word":(word&0xfc000000)|immediate,"canonical_native":good_native,"mutated_native":observed,"kernel_proved":caller.is_kernel_proved(),"strict":report.ships(EmitPolicy::StrictProvenOnly).is_ok()})).unwrap()).unwrap();
            if baseline {
                assert!(
                    caller.is_kernel_proved(),
                    "old generic model observation: {}",
                    explain(&report)
                );
                assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
            } else {
                assert!(
                    matches!(&caller.verdict,OutputVerdict::Unknown{reason} if reason.contains("BRANCH26")&&reason.contains("operand")),
                    "{}",
                    explain(&report)
                );
                assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
            }
        }
    }
}
#[test]
fn resolved_unrelocated_nonzero_local_branch_retains_its_actual_target() {
    let good = fixture(OptLevel::O2);
    let bound = layout(&good);
    let site = &bound.windows["constant_caller"].sites[0];
    let delta = symbol_offset(&good.object, "constant_leaf") as i64 - site.offset as i64;
    assert_ne!(delta, 0);
    let (record, _, _) = reloc_at(&good.object, site.offset);
    // The fixture is Mach-O; the header's MH_SUBSECTIONS_VIA_SYMBOLS (0x2000
    // at offset 24) is cleared, since with it set the linker may cut `__text`
    // at `constant_leaf` and no relocation keeps the piece (the reader makes
    // such a branch Unknown, tests/compiled_object_reader.rs
    // unrelocated_bl_between_mach_o_subsections_is_unknown).
    let changed = good.patched(|bytes| {
        delete_reloc(bytes, record);
        patch_word(bytes, site.offset, enc_b(delta));
        let flags = u32::from_le_bytes(bytes[24..28].try_into().unwrap());
        assert_ne!(flags & 0x2000, 0, "trust-cg sets MH_SUBSECTIONS_VIA_SYMBOLS");
        bytes[24..28].copy_from_slice(&(flags & !0x2000).to_le_bytes());
    });
    let bound = layout(&changed);
    let window = &bound.windows["constant_caller"];
    assert!(window.unknown.is_empty(), "{:?}", window.unknown);
    assert_eq!(window.sites.len(), 1);
    assert_eq!(window.sites[0].kind, MachineSiteKind::Tail);
    assert_eq!(window.sites[0].callee.as_deref(), Some("constant_leaf"));
    assert!(window.sites[0].reloc.is_none());
    let report = changed.report();
    assert!(report.certificates.iter().all(|c| c.is_kernel_proved()), "{}", explain(&report));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
    let directory = output("resolved-local");
    std::fs::write(directory.join("subject.o"), &changed.object).unwrap();
    std::fs::write(directory.join("certificates.json"), report.to_json()).unwrap();
}
