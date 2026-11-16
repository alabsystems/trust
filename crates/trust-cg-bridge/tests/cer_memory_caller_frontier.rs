//! Memory callees need M5 at their callers, including callers without local loads.
#![cfg(feature = "kernel-recheck")]

mod cer_common;

use cer_common::{DARWIN, Fixture, ModBuilder, explain, fixture_license, targeted};
use trust_cg_bridge::verify_output::{EmitPolicy, OutputVerdict};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::{CastOp, Inst};
use trust_ir::{Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty};

fn fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("memory_caller_frontier");
    let sig = b.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    let leaf = b.define("memory_leaf", sig, Linkage::External, |f| {
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
        let value = f.konst(Ty::U64, 0);
        f.ret(value);
    });
    let caller = b.define("memory_caller", sig, Linkage::External, |f| {
        let value = f.call(leaf, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    b.define("memory_transitive_caller", sig, Linkage::External, |f| {
        let value = f.call(caller, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    let pure = b.define("pure_leaf", sig, Linkage::External, |f| f.ret(f.p(1)));
    b.define("pure_caller", sig, Linkage::External, |f| {
        let value = f.call(pure, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    let mut module = targeted(&b.finish(), DARWIN);
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: ["memory_leaf", "memory_caller", "pure_leaf"]
                .into_iter()
                .map(str::to_owned)
                .collect(),
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

#[test]
fn a_memory_leaf_cannot_close_callers_without_memory_call_premises() {
    for (label, opt) in [("o0", OptLevel::O0), ("o3", OptLevel::O3)] {
        let f = fixture(opt);
        let report = f.report();
        assert_eq!(report.certificates.len(), 5, "{}", explain(&report));
        for symbol in ["memory_leaf", "pure_leaf", "pure_caller"] {
            assert!(report.certificate(symbol).unwrap().is_kernel_proved(), "{}", explain(&report));
        }
        for symbol in ["memory_caller", "memory_transitive_caller"] {
            let certificate = report.certificate(symbol).unwrap();
            assert_eq!(certificate.call_sites.len(), 1, "{}", explain(&report));
            if label == "o3" && symbol == "memory_caller" {
                assert_eq!(
                    certificate.call_sites[0].kind,
                    trust_cg_bridge::call_event::CallSiteKind::Tail
                );
                assert!(certificate.is_kernel_proved(), "{}", explain(&report));
                assert!(certificate.original_proof.is_some());
                assert!(
                    certificate.obligations.o5_frame.detail.contains("M5 bounded Tail composition")
                );
                assert!(report.closure.closed_kernel.iter().any(|name| name == symbol));
            } else {
                assert!(
                    matches!(&certificate.verdict, OutputVerdict::Unknown { reason }
                    if reason.contains("M5 memory-call premises")),
                    "{}",
                    explain(&report)
                );
                assert!(!report.closure.closed_kernel.iter().any(|name| name == symbol));
            }
        }
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err(), "{}", explain(&report));
        if let Some(out) = std::env::var_os("TRUST_MEMORY_CALLER_EVIDENCE") {
            let out = std::path::PathBuf::from(out).join(label);
            std::fs::create_dir_all(&out).unwrap();
            std::fs::write(out.join("object.o"), &f.object).unwrap();
            std::fs::write(out.join("certificates.json"), report.to_json()).unwrap();
        }
    }
}
