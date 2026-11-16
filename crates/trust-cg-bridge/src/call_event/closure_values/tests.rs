use trust_ir::{Block, ClosureLayoutDescriptor, ClosureTy, FuncTy, Function, InstrNode, Ty};

use super::*;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn f(id: u32) -> FuncId {
    FuncId::new(id)
}
fn scalar(reg: u8, width: u32) -> ParamPlace {
    ParamPlace::Scalar(ScalarPlace::gpr(reg, width))
}
fn place(params: Vec<ParamPlace>) -> FnPlacement {
    FnPlacement { params, ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)) }
}

fn pointer_module() -> Module {
    let mut module = Module::new("cer_closure");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let physical = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let logical = module
        .add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0))],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    module.closure_types.push(ClosureTy { func: apparent, captures: vec![Ty::Ptr] });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let mut caller = Function::new(f(0), "caller", physical, BlockId::new(0));
    let mut caller_block = Block::new(BlockId::new(0)).with_param(v(0), Ty::Ptr);
    caller_block.body = vec![
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: f(2),
            captures: vec![v(0)],
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Copy { ty: Ty::Closure(ClosureTyId::new(0)), operand: v(1) })
            .with_result(v(2)),
        InstrNode::new(Inst::Call { callee: f(1), args: vec![v(2)] }).with_result(v(3)),
        InstrNode::new(Inst::Return { values: vec![v(3)] }),
    ];
    caller.blocks.push(caller_block);
    let mut body = Function::new(f(1), "body", logical, BlockId::new(0));
    let mut body_block =
        Block::new(BlockId::new(0)).with_param(v(0), Ty::Closure(ClosureTyId::new(0)));
    body_block.body = vec![
        InstrNode::new(Inst::ExtractField { ty: Ty::Ptr, aggregate: v(0), field: 0 })
            .with_result(v(1)),
        InstrNode::new(Inst::Return { values: vec![v(1)] }),
    ];
    body.blocks.push(body_block);
    let mut adapter = caller.clone();
    adapter.id = f(2);
    adapter.name = "adapter".into();
    for function in [&mut caller, &mut body, &mut adapter] {
        function.producer = Some(trust_ir::Producer::TRust);
        function.calling_conv = CallingConv::Rust;
    }
    module.functions = vec![caller, body, adapter];
    module
}

fn evaluate(
    module: &Module,
    function: u32,
    placement: &FnPlacement,
    called: bool,
) -> Result<SpecResult, String> {
    let maps = BTreeMap::new();
    let input = CerInput {
        m_cg: module,
        producers: &[],
        bodies: &maps,
        placements: &BTreeMap::new(),
        object: &[],
        relocation_model: RelocationModel::Static,
    };
    let function = module.function_by_id(f(function)).unwrap();
    let signature = signature_of(module, function.ty)?;
    check_placement(module, &signature, function.calling_conv, placement, true)
        .map_err(|e| format!("{e:?}"))?;
    let mut decisions = BTreeMap::new();
    if called {
        decisions.insert(
            (0, 2),
            SiteDecision::Called {
                symbol: "body".into(),
                place: place(vec![scalar(0, 64)]),
                result_width: Some(64),
            },
        );
    }
    eval_spec(&input, module, function, &signature, placement, &decisions)
}

#[test]
fn source_constructor_copy_and_direct_call_keep_original_pointer_as_event_argument() {
    let module = pointer_module();
    for function in [0, 2] {
        let spec = evaluate(&module, function, &place(vec![scalar(0, 64)]), true).unwrap();
        let events = &spec.events[&(0, 2)];
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].args, vec![xn(0)]);
        assert_eq!(spec.value, Formula::Var("CER_S#bb0.2".into(), Sort::BitVec(64)));
        assert!(matches!(spec.reach, Formula::Bool(true)));
        assert!(spec.side.is_empty());
    }
}

#[test]
fn incoming_environment_projects_exact_pointer_without_promoting_opaque_target() {
    let module = pointer_module();
    let spec = evaluate(&module, 1, &place(vec![scalar(0, 64)]), false).unwrap();
    assert_eq!(spec.value, xn(0));
    let incoming =
        ClosureValue::incoming(&module, ClosureTyId::new(0), v(7), &scalar(0, 64)).unwrap();
    assert_eq!(incoming.clone().target, TargetIdentity::Incoming(v(7)));
    assert_eq!(incoming.project(&Ty::Ptr, 0).unwrap().f, xn(0));
    assert!(incoming.project(&Ty::U64, 0).is_err());
    assert!(incoming.project(&Ty::Ptr, 1).is_err(), "target identity is not a capture");
}

#[test]
fn physical_adapter_signature_is_not_the_logical_closure_body_signature() {
    let module = pointer_module();
    let capture = || Capture::checked(Ty::Ptr, IrValue { f: xn(0), width: 64 }).unwrap();
    let value =
        ClosureValue::construct(&module, ClosureTyId::new(0), f(2), vec![capture()]).unwrap();
    assert_eq!(value.target, TargetIdentity::Known(f(2)));
    assert!(ClosureValue::construct(&module, ClosureTyId::new(0), f(1), vec![capture()]).is_err());
    assert!(value.arguments(&module, &Ty::Closure(ClosureTyId::new(1)), &scalar(0, 64)).is_err());
    let wrong_type = Capture::checked(Ty::U64, IrValue { f: xn(0), width: 64 }).unwrap();
    assert!(ClosureValue::construct(&module, ClosureTyId::new(0), f(2), vec![wrong_type]).is_err());
    assert!(Capture::checked(Ty::Ptr, IrValue { f: xn(0), width: 32 }).is_err());
    let mut no_target = module.clone();
    no_target.functions.pop();
    assert_eq!(
        value.project(&Ty::Ptr, 0).unwrap().f,
        xn(0),
        "projection does not invoke/resolve a target"
    );
    assert!(
        ClosureValue::construct(&no_target, ClosureTyId::new(0), f(2), vec![capture()]).is_err()
    );
}

#[test]
fn observed_pair_offsets_determine_register_order_instead_of_capture_ordinals() {
    let mut module = pointer_module();
    module.closure_types[0].captures = vec![Ty::U8, Ty::Ptr];
    module.closure_layouts[0] = ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    };
    let pair = ParamPlace::Pair(ScalarPlace::gpr(1, 8), ScalarPlace::gpr(0, 64));
    let incoming = ClosureValue::incoming(&module, ClosureTyId::new(0), v(0), &pair).unwrap();
    assert_eq!(incoming.project(&Ty::Ptr, 1).unwrap().f, xn(0));
    assert_eq!(incoming.project(&Ty::U8, 0).unwrap().width, 8);
    let wrong_order = ParamPlace::Pair(ScalarPlace::gpr(0, 8), ScalarPlace::gpr(1, 64));
    assert!(placement(&module, ClosureTyId::new(0), &wrong_order).is_err());
    module.closure_layouts[0].capture_offsets = vec![0, 8];
    assert!(placement(&module, ClosureTyId::new(0), &pair).is_err());
}

#[test]
fn missing_or_out_of_range_frames_and_packed_pair_word_drift_remain_unknown() {
    let mut module = pointer_module();
    module.closure_layouts.clear();
    assert!(placement(&module, ClosureTyId::new(0), &scalar(0, 64)).is_err());
    module = pointer_module();
    module.closure_layouts[0].capture_offsets = vec![8];
    assert!(placement(&module, ClosureTyId::new(0), &scalar(0, 64)).is_err());
    module = pointer_module();
    module.closure_types[0].captures = vec![Ty::U32, Ty::U32];
    module.closure_layouts[0].capture_offsets = vec![0, 4];
    let pair = ParamPlace::Pair(ScalarPlace::gpr(0, 32), ScalarPlace::gpr(1, 32));
    assert!(placement(&module, ClosureTyId::new(0), &pair).is_err());
    module = pointer_module();
    let mut extended = ScalarPlace::gpr(0, 64);
    extended.ext = AbiExt::Zext;
    assert!(placement(&module, ClosureTyId::new(0), &ParamPlace::Scalar(extended)).is_err());
}

#[test]
fn poison_and_nonframe_memory_are_not_given_a_logical_capture_value() {
    let mut module = pointer_module();
    module.functions[1].blocks[0].body[0].inst = Inst::Undef { ty: Ty::Ptr };
    assert!(evaluate(&module, 1, &place(vec![scalar(0, 64)]), false).is_err());
    module = pointer_module();
    module.functions[1].blocks[0].body[0].inst =
        Inst::ExtractField { ty: Ty::Ptr, aggregate: v(0), field: 1 };
    assert!(evaluate(&module, 1, &place(vec![scalar(0, 64)]), false).is_err());
    // PTR.3b now evaluates the scalar byte read, but the projected pointer
    // supplies no validity/frame premise and no logical closure result. The
    // pending-memory guard must withhold the actual object's proof grade.
    module = pointer_module();
    let load = InstrNode::new(Inst::Load { ty: Ty::U64, ptr: v(1), volatile: false, align: None })
        .with_result(v(2));
    module.functions[1].blocks[0].body.insert(1, load);
    let spec = evaluate(&module, 1, &place(vec![scalar(0, 64)]), false).unwrap();
    assert_eq!(spec.value, xn(0), "the scalar load does not replace the capture by a fresh R");
    assert_eq!(spec.memory.accesses.len(), 1);
    assert!(spec.memory.missing_integration().is_some());
    let (report, _) = object_and_report(
        module,
        trust_cg_codegen::pipeline::OptLevel::O2,
        RelocationModel::Static,
    );
    let body = report.certificate("body").unwrap();
    assert_eq!(body.grade, "Unknown");
    assert!(body.obligations.o4_return.detail.contains("PTR.3b source memory modeled"));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
}

fn object_and_report(
    mut fixture: Module,
    opt: trust_cg_codegen::pipeline::OptLevel,
    model: RelocationModel,
) -> (CerReport, Vec<u8>) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            use trust_cg_codegen::target::TargetSpec;
            use trust_cg_codegen::{
                CodegenLicensePolicy, Compiler, CompilerConfig, UnlicensedBodyPolicy,
            };
            // This hand-built byte fixture declares its native ABI. Source code must
            // earn that classification separately through its actual rustc FnAbi.
            let triple = if model == RelocationModel::Pic {
                "aarch64-unknown-linux-gnu"
            } else {
                "aarch64-apple-darwin"
            };
            fixture.target_info.as_mut().unwrap().triple = triple.into();
            fixture.target_info.as_mut().unwrap().struct_passing =
                trust_ir::StructPassingPolicy::NativeC;
            let module = Arc::new(fixture);
            let config = CompilerConfig {
                opt_level: opt,
                parallel: false,
                emit_proofs: false,
                never_inline: BTreeSet::from(["body".into()]),
                relocation_model: match model {
                    RelocationModel::Static => trust_cg_lower::RelocationModel::Static,
                    RelocationModel::Pic => trust_cg_lower::RelocationModel::Pic,
                    RelocationModel::Pie => trust_cg_lower::RelocationModel::Pie,
                },
                ..CompilerConfig::default()
            };
            // The standard CER fixture licence permits hand-built claim-less bodies;
            // this is byte-proof evidence and grants no source compilation licence.
            let compiler =
                Compiler::new_for_target_spec(config, TargetSpec::parse(triple).unwrap())
                    .with_codegen_license(
                        CodegenLicensePolicy::default()
                            .with_unlicensed(UnlicensedBodyPolicy::Permit),
                    );
            let result = compiler.compile(&module).unwrap();
            let producers = [ProducerModule::named_by_symbols(Arc::clone(&module))];
            let bodies = module
                .functions
                .iter()
                .filter(|f| !f.is_declaration())
                .map(|function| {
                    (function.name.clone(), ProducerBody { producer: 0, func: function.id })
                })
                .collect();
            let placements = module
                .functions
                .iter()
                .map(|function| (function.name.clone(), place(vec![scalar(0, 64)])))
                .collect();
            let report = verify_compiled_module(&CerInput {
                m_cg: &module,
                producers: &producers,
                bodies: &bodies,
                placements: &placements,
                object: &result.object_code,
                relocation_model: model,
            })
            .unwrap();
            (report, result.object_code)
        })
        .unwrap()
        .join()
        .unwrap()
}

fn object_report(
    module: Module,
    opt: trust_cg_codegen::pipeline::OptLevel,
    model: RelocationModel,
) -> CerReport {
    object_and_report(module, opt, model).0
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn actual_full_compiler_object_keeps_pointer_protocol_and_its_independent_gate() {
    use trust_cg_codegen::pipeline::OptLevel;
    for opt in [OptLevel::O0, OptLevel::O2] {
        let report = object_report(pointer_module(), opt, RelocationModel::Static);
        assert_eq!(report.certificates.len(), 3);
        for certificate in &report.certificates {
            println!(
                "{opt:?}: {} {} O3={:?} O4={:?} O5={:?}",
                certificate.symbol,
                certificate.grade,
                certificate.obligations.o3_events,
                certificate.obligations.o4_return,
                certificate.obligations.o5_frame
            );
            assert!(
                !matches!(certificate.verdict, OutputVerdict::Refuted { .. }),
                "{:?}",
                certificate
            );
        }
        println!(
            "{opt:?}: closed_kernel={:?}, strict_ships={}",
            report.closure.closed_kernel,
            report.ships(EmitPolicy::StrictProvenOnly).is_ok()
        );
        let body = report.certificates.iter().find(|c| c.symbol == "body").unwrap();
        assert!(body.is_kernel_proved());
        if opt == OptLevel::O0 {
            assert_eq!(report.closure.closed_kernel, vec!["body"]);
            for symbol in ["caller", "adapter"] {
                let certificate = report.certificates.iter().find(|c| c.symbol == symbol).unwrap();
                assert_eq!(certificate.obligations.o3_events.grade, Grade::Proven);
                assert_eq!(certificate.obligations.o4_return.grade, Grade::Proven);
                assert_eq!(certificate.obligations.o5_frame.grade, Grade::Unknown);
                assert!(certificate.obligations.o5_frame.detail.contains("frame escapes"));
            }
            assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        } else {
            assert!(report.certificates.iter().all(FunctionCertificate::is_kernel_proved));
            assert_eq!(report.closure.closed_kernel, vec!["adapter", "body", "caller"]);
            assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        }
    }
}

#[test]
fn external_and_preemptible_closure_argument_edges_remain_unknown() {
    use trust_cg_codegen::pipeline::OptLevel;
    let mut external = pointer_module();
    external.functions[1].blocks.clear();
    let preemptible = pointer_module();
    for (module, relocation) in
        [(external, RelocationModel::Static), (preemptible, RelocationModel::Pic)]
    {
        let report = object_report(module, OptLevel::O0, relocation);
        let caller = report.certificates.iter().find(|c| c.symbol == "caller").unwrap();
        assert_eq!(caller.obligations.o3_events.grade, Grade::Unknown);
        assert!(
            caller.obligations.o3_events.detail.contains("closure code identity"),
            "{:?}",
            caller
        );
        assert!(!caller.is_kernel_proved());
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    }
}

#[test]
fn equal_nominal_numbers_from_distinct_producers_cannot_bind_a_closure_call() {
    let mut caller_module = pointer_module();
    for signature in &mut caller_module.func_types {
        signature.returns = vec![Ty::U64];
    }
    caller_module.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::ExtractField { ty: Ty::Ptr, aggregate: v(0), field: 0 })
            .with_result(v(1)),
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }).with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![v(2)] }),
    ];
    let mut other = caller_module.clone();
    other.closure_types[0].captures = vec![Ty::U64];
    for signature in &mut other.func_types {
        for ty in &mut signature.params {
            if *ty == Ty::Ptr {
                *ty = Ty::U64;
            }
        }
    }
    for function in &mut other.functions {
        for block in &mut function.blocks {
            for (_, ty) in &mut block.params {
                if *ty == Ty::Ptr {
                    *ty = Ty::U64;
                }
            }
        }
    }
    other.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::ExtractField { ty: Ty::U64, aggregate: v(0), field: 0 })
            .with_result(v(1)),
        InstrNode::new(Inst::Return { values: vec![v(1)] }),
    ];
    // Equal numeric signatures do not make nominal types from two producers identical.
    assert_eq!(
        signature_of(&caller_module, caller_module.functions[1].ty).unwrap(),
        signature_of(&other, other.functions[1].ty).unwrap()
    );
    assert_ne!(caller_module.closure_types[0].captures, other.closure_types[0].captures);
    let caller = Arc::new(caller_module);
    let producers = [
        ProducerModule::named_by_symbols(Arc::clone(&caller)),
        ProducerModule::named_by_symbols(Arc::new(other)),
    ];
    let bodies = BTreeMap::from([("body".into(), ProducerBody { producer: 1, func: f(1) })]);
    let placements = BTreeMap::new();
    let input = CerInput {
        m_cg: &caller,
        producers: &producers,
        bodies: &bodies,
        placements: &placements,
        object: &[],
        relocation_model: RelocationModel::Static,
    };
    assert!(
        direct_call_boundary(&input, ProducerBody { producer: 0, func: f(0) }, f(1), "body", true)
            .is_err()
    );
    let same_module = BTreeMap::from([("body".into(), ProducerBody { producer: 0, func: f(1) })]);
    let input = CerInput { bodies: &same_module, ..input };
    assert!(
        direct_call_boundary(&input, ProducerBody { producer: 0, func: f(0) }, f(1), "body", true)
            .is_ok()
    );
    assert!(
        direct_call_boundary(&input, ProducerBody { producer: 0, func: f(0) }, f(2), "body", true)
            .is_err()
    );
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn actual_pointer_object_executes_c_identity_driver_at_o0_and_o2() {
    use std::process::Command;

    use trust_cg_codegen::pipeline::OptLevel;
    let temporary = tempfile::tempdir().unwrap();
    let directory = std::env::var_os("TRUST_CER_CLOSURE_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| temporary.path().to_path_buf());
    std::fs::create_dir_all(&directory).unwrap();
    let driver = directory.join("identity.c");
    std::fs::write(
        &driver,
        r#"#include <stdint.h>
#include <stddef.h>
extern void *caller(void *);
int main(void) {
    uintptr_t values[16];
    for (unsigned i = 0; i < 16; ++i) values[i] = 0x9e37u + i;
    for (unsigned i = 0; i < 16; ++i) {
        if (caller(&values[i]) != &values[i]) return 10 + i;
        if (values[i] != 0x9e37u + i) return 40 + i;
    }
    if (caller(NULL) != NULL) return 80;
    return 0;
}

"#,
    )
    .unwrap();
    for (name, opt) in [("o0", OptLevel::O0), ("o2", OptLevel::O2)] {
        let (report, object) = object_and_report(pointer_module(), opt, RelocationModel::Static);
        let path = directory.join(format!("pointer-{name}.o"));
        let executable = directory.join(format!("pointer-{name}"));
        std::fs::write(&path, &object).unwrap();
        let summary = format!(
            "object_sha256={}\nclosed_kernel={:?}\nstrict_ships={}\n",
            report.object_sha256,
            report.closure.closed_kernel,
            report.ships(EmitPolicy::StrictProvenOnly).is_ok()
        );
        std::fs::write(directory.join(format!("pointer-{name}.report.txt")), &summary).unwrap();
        let linked = Command::new("/usr/bin/cc")
            .args(["-std=c11", "-Wall", "-Werror"])
            .arg(&driver)
            .arg(&path)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            linked.status.success(),
            "{name}: cc failed: {}",
            String::from_utf8_lossy(&linked.stderr)
        );
        let executed = Command::new(&executable).output().unwrap();
        println!("native {name}: status={} {summary}", executed.status);
        if !executed.status.success() {
            let retained = temporary.keep();
            panic!(
                "{name}: C pointer identity/store-preservation driver failed: {:?}, stderr={}; retained {}",
                executed.status,
                String::from_utf8_lossy(&executed.stderr),
                retained.display()
            );
        }
    }
}

#[cfg(feature = "kernel-recheck")] // asserts kernel grades, which exist only with the kernel
#[test]
fn classified_object_is_checked_against_unchanged_unclassified_producer() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            use trust_cg_codegen::pipeline::OptLevel;
            use trust_cg_codegen::target::TargetSpec;
            use trust_cg_codegen::{
                CodegenLicensePolicy, CompileError, Compiler, CompilerConfig, UnlicensedBodyPolicy,
            };
            let original = Arc::new(pointer_module());
            assert_eq!(
                original.target_info.as_ref().unwrap().struct_passing,
                trust_ir::StructPassingPolicy::Unclassified
            );
            let (native_report, object) =
                object_and_report((*original).clone(), OptLevel::O2, RelocationModel::Static);
            let mut m_cg = (*original).clone();
            m_cg.target_info.as_mut().unwrap().struct_passing =
                trust_ir::StructPassingPolicy::NativeC;
            let producers = [ProducerModule::named_by_symbols(Arc::clone(&original))];
            let bodies = original
                .functions
                .iter()
                .map(|function| {
                    (function.name.clone(), ProducerBody { producer: 0, func: function.id })
                })
                .collect();
            let placements = original
                .functions
                .iter()
                .map(|function| (function.name.clone(), place(vec![scalar(0, 64)])))
                .collect();
            let checked = verify_compiled_module(&CerInput {
                m_cg: &m_cg,
                producers: &producers,
                bodies: &bodies,
                placements: &placements,
                object: &object,
                relocation_model: RelocationModel::Static,
            })
            .unwrap();
            assert_eq!(checked.object_sha256, native_report.object_sha256);
            assert_eq!(checked.closure.closed_kernel, vec!["adapter", "body", "caller"]);
            assert!(checked.ships(EmitPolicy::StrictProvenOnly).is_ok());
            // An original unclassified module remains refused by the raw native
            // compiler. The source frontend must separately earn the classification
            // via actual rustc FnAbi witnesses; this hand-built P does not do that.
            let compiler = Compiler::new_for_target_spec(
                CompilerConfig::default(),
                TargetSpec::parse("aarch64-apple-darwin").unwrap(),
            )
            .with_codegen_license(
                CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
            );
            assert!(matches!(
                compiler.compile(&original),
                Err(CompileError::Adapter(
                    trust_cg_lower::AdapterError::TargetStructPassingUnclassified { .. }
                ))
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}
