#![cfg(all(feature = "ay-proofs", not(feature = "kernel-recheck")))]
mod cer_common;
use cer_common::*;
use trust_cg_bridge::call_event::CerInput;
use trust_cg_bridge::call_event::leaf_call_instance::prepare_leaf_calls;
use trust_cg_bridge::verify_output::EmitPolicy;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::{CastOp, Inst};
use trust_ir::{CallingConv, Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty};
fn fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("m5_actual_tail_instances");
    let store_sig = b.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    let store = b.define("memory_store", store_sig, Linkage::External, |f| {
        let byte = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    let copy_sig = b.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::U64));
    let copy = b.define("memory_copy", copy_sig, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: Ty::U8, ptr: f.p(1), volatile: false, align: Some(1) });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    b.define("tail_store", store_sig, Linkage::External, |f| {
        let value = f.call(store, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    b.define("tail_copy", copy_sig, Linkage::External, |f| {
        let value = f.call(copy, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    b.define("tail_alias", copy_sig, Linkage::External, |f| {
        let value = f.call(copy, &[f.p(0), f.p(0)]);
        f.ret(value);
    });
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for f in &mut module.functions {
        f.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: ["memory_store", "memory_copy"].into_iter().map(str::to_owned).collect(),
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
fn missing_kernel_cannot_prepare_any_favorable_leaf_call_instance() {
    let f = fixture(OptLevel::O2);
    let input = CerInput {
        m_cg: &f.m_cg,
        producers: &f.producers,
        bodies: &f.bodies,
        placements: &f.placements,
        object: &f.object,
        relocation_model: f.model,
    };
    let prepared = prepare_leaf_calls(&input).unwrap();
    assert_eq!(prepared.report().certificates.len(), 5);
    for callee in ["memory_store", "memory_copy"] {
        let row = prepared.report().certificate(callee).unwrap();
        assert!(!row.is_kernel_proved());
        assert!(row.original_proof.is_none());
    }
    for caller in ["tail_store", "tail_copy", "tail_alias"] {
        assert!(prepared.specialize(caller).is_err());
    }
    assert!(prepared.report().ships(EmitPolicy::StrictProvenOnly).is_err());
    let ordinary = f.report();
    assert_eq!(ordinary.certificates.len(), 5);
    for symbol in ["memory_store", "memory_copy", "tail_store", "tail_copy", "tail_alias"] {
        let row = ordinary.certificate(symbol).unwrap();
        assert!(!row.is_kernel_proved());
        assert!(row.original_proof.is_none());
    }
    assert!(ordinary.ships(EmitPolicy::StrictProvenOnly).is_err());

    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output);
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("absent-kernel-object.o"), &f.object).unwrap();
        std::fs::write(output.join("absent-kernel-ordinary-certificates.json"), ordinary.to_json())
            .unwrap();
        std::fs::write(output.join("absent-kernel-certificates.json"), prepared.report().to_json())
            .unwrap();
    }
}
