use trust_cg_bridge::call_event::{AbiExt, ParamPlace, ReturnPlace, ScalarPlace, Slot};
use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, ClosureTyId, FuncTy, Function, InstrNode, Ty, ValueId,
};

use super::*;

fn scalar(reg: u8, width: u32) -> ParamPlace {
    ParamPlace::Scalar(ScalarPlace::gpr(reg, width))
}
fn placement(params: Vec<ParamPlace>) -> FnPlacement {
    FnPlacement { params, ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)) }
}
fn classified() -> (Module, Vec<NativeWorkItem>) {
    let (module, mut items) = super::tests::fixture();
    for item in &mut items {
        item.placement = Some(placement(vec![scalar(0, 64)]));
    }
    (module, items)
}
fn build_all(module: &Module, items: &[NativeWorkItem], conserved: &[u32]) -> CodegenModuleOutput {
    build(&NativeModuleInput {
        producer: module,
        base: Some(module),
        items,
        conserved: &conserved.iter().copied().map(FuncId::new).collect(),
        source_ids: &BTreeSet::from([FuncId::new(0), FuncId::new(1)]),
        foreign_declarations: &BTreeSet::new(),
        has_statics: false,
        target: &ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 },
    })
}

#[test]
fn compiler_adapter_placement_adds_no_rust_instance_or_source_row() {
    let (module, items) = classified();
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(out.refusals.is_empty(), "{:?}", out.refusals);
    assert_eq!(out.placements["adapter"], placement(vec![scalar(0, 64)]));
    assert_eq!(out.m_cg, module);
    assert!(out.residue.is_empty());
    assert_eq!(items.len(), 2);
}

#[test]
fn conservation_protocol_and_selected_symbols_are_required_before_adapter_p() {
    let (module, items) = classified();
    for conserved in [vec![0, 1], vec![0, 2], vec![1, 2]] {
        let out = build_all(&module, &items, &conserved);
        assert!(!out.refusals.is_empty());
        assert!(!out.placements.contains_key("adapter"));
    }
    let mut changed = module.clone();
    changed.functions[2].blocks[0].body[1].inst =
        Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] };
    let out = build_all(&changed, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
    let mut changed = module.clone();
    changed.functions[2].blocks[0].body[0].inst =
        Inst::Const { ty: Ty::U64, value: trust_ir::Constant::Int(0) };
    let out = build_all(&changed, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
    let mut changed = module.clone();
    changed.functions[2].name = "owner".into();
    let out = build_all(&changed, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    let (_, mut items) = classified();
    items[1].symbol = "another_body".into();
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
}

#[test]
fn source_return_and_environment_slots_are_cross_checked_not_guessed() {
    let (module, mut items) = classified();
    items[1].placement.as_mut().unwrap().ret = ReturnPlace::Scalar(ScalarPlace::gpr(0, 32));
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
    let (_, mut items) = classified();
    items[1].placement.as_mut().unwrap().params[0] = scalar(3, 64);
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
    for unsupported in [
        ReturnPlace::Indirect,
        ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 64, ext: AbiExt::Zext }),
    ] {
        let (_, mut items) = classified();
        items[1].placement.as_mut().unwrap().ret = unsupported;
        let out = build_all(&module, &items, &[0, 1, 2]);
        assert!(out.refusals.is_empty(), "{:?}", out.refusals);
        assert!(!out.placements.contains_key("adapter"), "unsupported return stays Unknown");
    }
    let (_, mut items) = classified();
    items[1].placement = None;
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
}

#[test]
fn flat_capture_slots_are_distinct_from_observed_environment_field_order() {
    let (mut module, mut items) = classified();
    module.closure_types[0].captures = vec![Ty::U8, Ty::Ptr];
    module.closure_layouts[0].size = 16;
    module.closure_layouts[0].align = 8;
    module.closure_layouts[0].capture_offsets = vec![8, 0];
    module.func_types[1].params = vec![Ty::U8, Ty::Ptr];
    for id in [0, 2] {
        let mut block = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), Ty::U8)
            .with_param(ValueId::new(1), Ty::Ptr);
        block.body.push(
            InstrNode::new(Inst::MakeClosure {
                ty: ClosureTyId::new(0),
                func: FuncId::new(2),
                captures: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        );
        if id == 2 {
            block.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(2)] })
                    .with_result(ValueId::new(3)),
            );
        } else {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U64, value: trust_ir::Constant::Int(7) })
                    .with_result(ValueId::new(3)),
            );
        }
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }));
        module.functions[id].blocks = vec![block];
    }
    items[0].placement = Some(placement(vec![scalar(0, 8), scalar(1, 64)]));
    items[1].placement =
        Some(placement(vec![ParamPlace::Pair(ScalarPlace::gpr(1, 8), ScalarPlace::gpr(0, 64))]));
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(out.refusals.is_empty(), "{:?}", out.refusals);
    assert_eq!(out.placements["adapter"], placement(vec![scalar(0, 8), scalar(1, 64)]));
    items[1].placement.as_mut().unwrap().params[0] =
        ParamPlace::Pair(ScalarPlace::gpr(0, 8), ScalarPlace::gpr(1, 64));
    let out = build_all(&module, &items, &[0, 1, 2]);
    assert!(!out.refusals.is_empty());
    assert!(!out.placements.contains_key("adapter"));
}

fn pointer_probe() -> (Module, Vec<NativeWorkItem>) {
    let (mut module, mut items) = classified();
    for signature in &mut module.func_types {
        for ty in signature.params.iter_mut().chain(&mut signature.returns) {
            if *ty == Ty::U64 {
                *ty = Ty::Ptr;
            }
        }
    }
    module.closure_types[0].captures = vec![Ty::Ptr];
    for function in &mut module.functions {
        for block in &mut function.blocks {
            for (_, ty) in &mut block.params {
                if *ty == Ty::U64 {
                    *ty = Ty::Ptr;
                }
            }
        }
    }
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(3),
            captures: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(1)] })
            .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
    ];
    module.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::ExtractField { ty: Ty::Ptr, aggregate: ValueId::new(0), field: 0 })
            .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
    ];
    let mut adapter = module.functions.pop().unwrap();
    adapter.id = FuncId::new(3);
    adapter.blocks[0].body[0].inst = Inst::MakeClosure {
        ty: ClosureTyId::new(0),
        func: FuncId::new(3),
        captures: vec![ValueId::new(0)],
    };
    let mut probe = Function::new(FuncId::new(2), "invoke_adapter", adapter.ty, BlockId::new(0));
    probe.producer = Some(Producer::TRust);
    probe.calling_conv = CallingConv::Rust;
    probe.body_gate =
        Some(BodyGate::Gated { authority: "trust-direct-lane-structural".into(), evidence: None });
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    block.body = vec![
        InstrNode::new(Inst::Call { callee: FuncId::new(3), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
    ];
    probe.blocks = vec![block];
    module.functions.extend([probe, adapter]);
    items[1].never_inline = true;
    items.push(NativeWorkItem {
        func: FuncId::new(2),
        symbol: "invoke_adapter".into(),
        linkage: FunctionLinkage::External,
        never_inline: true,
        placement: Some(placement(vec![scalar(0, 64)])),
        inventory_residue: false,
    });
    (module, items)
}

#[test]
fn derived_adapter_p_closes_actual_native_object_without_reclassifying_producer() {
    use std::sync::Arc;

    use trust_cg_bridge::call_event::{CerInput, Grade, ProducerModule, verify_compiled_module};
    use trust_cg_bridge::compiled_object::RelocationModel;
    use trust_cg_bridge::f1_compile::{
        F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, compile_and_verify_trust_ir_module,
    };
    use trust_cg_bridge::verify_output::EmitPolicy;
    let (original, items) = pointer_probe();
    let mut out = build(&NativeModuleInput {
        producer: &original,
        base: Some(&original),
        items: &items,
        conserved: &BTreeSet::from([
            FuncId::new(0),
            FuncId::new(1),
            FuncId::new(2),
            FuncId::new(3),
        ]),
        source_ids: &BTreeSet::from([FuncId::new(0), FuncId::new(1), FuncId::new(2)]),
        foreign_declarations: &BTreeSet::new(),
        has_statics: false,
        target: &ExpectedTarget { triple: "arm64-apple-macosx".into(), pointer_size: 8 },
    });
    assert!(out.refusals.is_empty(), "{:?}", out.refusals);
    assert_eq!(out.placements["adapter"], placement(vec![scalar(0, 64)]));
    assert!(out.residue.is_empty());
    assert_eq!(
        original.target_info.as_ref().unwrap().struct_passing,
        StructPassingPolicy::Unclassified
    );
    // A hand-built test ABI, not a source FnAbi witness. Production earns
    // this separate M_cg classification through actual private witnesses.
    out.m_cg.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
    let producers = [ProducerModule { module: Arc::new(original), symbols: out.symbols }];
    let mut never_inline = out.never_inline;
    never_inline.insert("adapter".into());
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: RelocationModel::Static,
        never_inline,
        upstream_mir_lane: false,
    };
    let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
        m_cg: &out.m_cg,
        producers: &producers,
        bodies: &out.bodies,
        placements: &out.placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &config,
    })
    .unwrap();
    assert_eq!(shipped.report.certificates.len(), 4);
    assert_eq!(
        shipped.report.closure.closed_kernel,
        vec!["adapter", "body", "invoke_adapter", "owner"]
    );
    let mut missing = out.placements;
    missing.remove("adapter");
    let report = verify_compiled_module(&CerInput {
        m_cg: &out.m_cg,
        producers: &producers,
        bodies: &out.bodies,
        placements: &missing,
        object: &shipped.object,
        relocation_model: RelocationModel::Static,
    })
    .unwrap();
    let adapter = report.certificates.iter().find(|c| c.symbol == "adapter").unwrap();
    assert_eq!(adapter.obligations.o4_return.grade, Grade::Unknown);
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        use std::process::Command;
        let dir = std::env::var_os("TRUST_ADAPTER_NATIVE_OUTPUT_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| {
                std::env::temp_dir().join(format!("trust-adapter-p-{}", std::process::id()))
            });
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("module.o"), &shipped.object).unwrap();
        std::fs::write(
            dir.join("identity.c"),
            r#"#include <stdint.h>
#include <stddef.h>
extern void *owner(void *);
extern void *invoke_adapter(void *);
int main(void) {
    uintptr_t values[16];
    for (unsigned i=0; i<16; ++i) values[i]=17+i;
    for (unsigned i=0; i<16; ++i) {
        if (owner(&values[i]) != &values[i]) return 10+i;
        if (invoke_adapter(&values[i]) != &values[i]) return 40+i;
        if (values[i] != 17+i) return 70+i;
    }
    if (owner(NULL) != NULL || invoke_adapter(NULL) != NULL) return 100;
    return 0;
}
"#,
        )
        .unwrap();
        let linked = Command::new("/usr/bin/cc")
            .arg(dir.join("identity.c"))
            .arg(dir.join("module.o"))
            .arg("-o")
            .arg(dir.join("identity"))
            .output()
            .unwrap();
        assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
        let run = Command::new(dir.join("identity")).output().unwrap();
        assert!(run.status.success(), "native adapter ABI failed: {:?}", run.status);
    }
}
