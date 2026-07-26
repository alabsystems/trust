use super::*;

#[test]
fn backend_name() {
    let backend = TrustCgCodegenBackend;
    assert_eq!(CodegenBackend::name(&backend), "trust-cg");
}

#[test]
fn backend_thin_lto_not_supported() {
    let backend = TrustCgCodegenBackend;
    assert!(!backend.thin_lto_supported());
}

#[test]
fn backend_new_returns_boxed() {
    let backend = TrustCgCodegenBackend::new();
    assert_eq!(CodegenBackend::name(&*backend), "trust-cg");
}

#[test]
fn backend_no_zstd() {
    let backend = TrustCgCodegenBackend;
    assert!(!backend.has_zstd());
}

#[test]
fn backend_no_replaced_intrinsics() {
    let backend = TrustCgCodegenBackend;
    assert!(backend.replaced_intrinsics().is_empty());
}

#[test]
fn explicit_split_debuginfo_is_only_inert_without_debuginfo() {
    assert!(explicit_split_debuginfo_is_inert(DebugInfo::None));
    for requested in [
        DebugInfo::LineDirectivesOnly,
        DebugInfo::LineTablesOnly,
        DebugInfo::Limited,
        DebugInfo::Full,
    ] {
        assert!(!explicit_split_debuginfo_is_inert(requested));
    }
}

#[test]
fn wasm_target_config_does_not_enter_the_native_bridge() {
    let config = TrustCgCodegenBackend::wasm_target_config();
    assert!(config.target_features.is_empty());
    assert!(config.unstable_target_features.is_empty());
    assert!(!config.has_reliable_f16);
    assert!(!config.has_reliable_f16_math);
    assert!(!config.has_reliable_f128);
    assert!(!config.has_reliable_f128_math);
}

#[test]
fn output_capabilities_reject_mislabeled_artifacts() {
    for output in [OutputType::Metadata, OutputType::DepInfo, OutputType::Mir] {
        assert!(TrustCgCodegenBackend::output_type_supported("wasm32", output));
    }
    for output in [
        OutputType::Exe,
        OutputType::Object,
        OutputType::Assembly,
        OutputType::LlvmAssembly,
        OutputType::Bitcode,
        OutputType::ThinLinkBitcode,
    ] {
        assert!(
            !TrustCgCodegenBackend::output_type_supported("wasm32", output),
            "wasm must reject unsupported --emit={}",
            output.shorthand(),
        );
    }

    assert!(!TrustCgCodegenBackend::output_type_supported("aarch64", OutputType::Object));
    assert!(TrustCgCodegenBackend::output_type_supported("x86_64", OutputType::Exe));
    assert!(!TrustCgCodegenBackend::output_type_supported("aarch64", OutputType::Assembly));
    assert!(!TrustCgCodegenBackend::output_type_supported("x86_64", OutputType::Bitcode));

    assert_eq!(supported_crate_types_for_outputs(true), vec![CrateType::Rlib]);
    let analysis = supported_crate_types_for_outputs(false);
    assert!(analysis.contains(&CrateType::Cdylib));
    assert!(analysis.contains(&CrateType::Executable));
}

#[test]
fn target_capability_matrix_is_exact_and_fail_closed() {
    for triple in
        ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "aarch64-unknown-linux-musl"]
    {
        assert_eq!(target_capability(triple), Some(TrustCgTargetCapability::Aarch64Native));
    }
    for triple in [
        "x86_64-apple-darwin",
        "x86_64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
        "x86_64-pc-windows-msvc",
        "x86_64-pc-windows-gnu",
    ] {
        assert_eq!(target_capability(triple), Some(TrustCgTargetCapability::X86_64Native));
    }
    assert_eq!(
        target_capability("wasm32-unknown-unknown"),
        Some(TrustCgTargetCapability::Wasm32AnalysisOnly)
    );
    for unsupported in [
        "aarch64_be-unknown-linux-gnu",
        "aarch64-unknown-none-softfloat",
        "x86_64-unknown-freebsd",
        "wasm32-wasip1",
        "wasm64-unknown-unknown",
        "",
    ] {
        assert_eq!(target_capability(unsupported), None, "{unsupported}");
    }
    assert!(!TrustCgTargetCapability::Wasm32AnalysisOnly.supports_linked_output());
}

#[test]
fn frame_pointer_policy_ratchets_target_and_cli_requirements() {
    use BridgeFramePointerPolicy::{Always, MayOmit, NonLeaf};

    assert_eq!(
        effective_frame_pointer_policy(FramePointer::MayOmit, FramePointer::MayOmit),
        MayOmit
    );
    assert_eq!(
        effective_frame_pointer_policy(FramePointer::NonLeaf, FramePointer::MayOmit),
        NonLeaf
    );
    assert_eq!(
        effective_frame_pointer_policy(FramePointer::MayOmit, FramePointer::NonLeaf),
        NonLeaf
    );
    assert_eq!(effective_frame_pointer_policy(FramePointer::Always, FramePointer::MayOmit), Always);
    assert_eq!(effective_frame_pointer_policy(FramePointer::MayOmit, FramePointer::Always), Always);
    assert_eq!(effective_frame_pointer_policy(FramePointer::NonLeaf, FramePointer::Always), Always);
}

#[test]
fn linked_artifact_claim_is_exactly_rlib() {
    assert_eq!(supported_link_crate_types(), vec![CrateType::Rlib]);
    let analysis_only = supported_crate_types_for_outputs(false);
    assert!(analysis_only.contains(&CrateType::Executable));
    assert!(analysis_only.contains(&CrateType::Cdylib));
    for unsupported in [
        CrateType::Executable,
        CrateType::Dylib,
        CrateType::StaticLib,
        CrateType::Cdylib,
        CrateType::ProcMacro,
        CrateType::Sdylib,
    ] {
        assert!(!supported_link_crate_types().contains(&unsupported), "{unsupported:?}");
    }
}

#[test]
fn ordinary_print_requests_stop_before_codegen() {
    assert!(print_requests_stop_before_codegen([PrintKind::DeploymentTarget]));
    assert!(print_requests_stop_before_codegen([PrintKind::SupportedCrateTypes]));
    assert!(print_requests_stop_before_codegen([
        PrintKind::NativeStaticLibs,
        PrintKind::SupportedCrateTypes,
    ]));

    assert!(!print_requests_stop_before_codegen([]));
    assert!(!print_requests_stop_before_codegen([PrintKind::NativeStaticLibs]));
    assert!(!print_requests_stop_before_codegen([PrintKind::LinkArgs]));
    assert!(!print_requests_stop_before_codegen([
        PrintKind::NativeStaticLibs,
        PrintKind::LinkArgs,
    ]));
}

#[test]
fn abi_convention_policy_rejects_hidden_or_unwinding_conventions() {
    assert_eq!(supported_canonical_abi(ExternAbi::Rust), Some(CanonAbi::Rust));
    assert_eq!(supported_canonical_abi(ExternAbi::C { unwind: false }), Some(CanonAbi::C));
    for unsupported in [
        ExternAbi::C { unwind: true },
        ExternAbi::RustCall,
        ExternAbi::RustCold,
        ExternAbi::System { unwind: false },
        ExternAbi::SysV64 { unwind: false },
        ExternAbi::Win64 { unwind: false },
    ] {
        assert_eq!(supported_canonical_abi(unsupported), None, "{unsupported}");
    }
}

#[test]
fn scalar_register_argument_limits_are_target_abi_exact() {
    for triple in [
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
        "aarch64-unknown-linux-musl",
    ] {
        assert_eq!(scalar_register_argument_limit(triple), Some(8), "{triple}");
    }
    for triple in [
        "x86_64-apple-darwin",
        "x86_64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
    ] {
        assert_eq!(scalar_register_argument_limit(triple), Some(6), "{triple}");
    }
    for triple in ["x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu"] {
        assert_eq!(scalar_register_argument_limit(triple), Some(4), "{triple}");
    }
    assert_eq!(scalar_register_argument_limit("wasm32-unknown-unknown"), None);
    assert_eq!(scalar_register_argument_limit("aarch64-unknown-freebsd"), None);
}

#[test]
fn abi_attribute_policy_rejects_implicit_entry_contracts() {
    let mut attrs = CodegenFnAttrs::new();
    assert_eq!(codegen_attrs_issue(&attrs), None);

    attrs.flags.insert(CodegenFnAttrFlags::TRACK_CALLER);
    assert!(codegen_attrs_issue(&attrs).unwrap().contains("TRACK_CALLER"));

    let mut attrs = CodegenFnAttrs::new();
    attrs.flags.insert(CodegenFnAttrFlags::NAKED);
    assert!(codegen_attrs_issue(&attrs).unwrap().contains("NAKED"));

    let mut attrs = CodegenFnAttrs::new();
    attrs.instrument_fn = InstrumentFnAttr::On;
    assert!(codegen_attrs_issue(&attrs).unwrap().contains("instrumentation"));
}

#[test]
fn output_gate_modes_follow_the_tracked_closed_domain() {
    assert!(matches!(
        output_gate_mode_from_name("allow-unknown"),
        Ok(OutputGateMode::AllowUnknown)
    ));
    assert!(matches!(output_gate_mode_from_name("strict"), Ok(OutputGateMode::Strict)));
    assert!(matches!(output_gate_mode_from_name("off"), Ok(OutputGateMode::Off)));
    assert!(output_gate_mode_from_name("typo").is_err());
}

#[test]
fn batteries_on_strict_verification_forces_output_preservation() {
    assert!(matches!(
        output_gate_mode_for_verification(true, "allow-unknown"),
        Ok(OutputGateMode::Strict)
    ));
    assert!(matches!(
        output_gate_mode_for_verification(true, "strict"),
        Ok(OutputGateMode::Strict)
    ));
    let Err(error) = output_gate_mode_for_verification(true, "off") else {
        panic!("full verification must reject a disabled output gate");
    };
    assert!(error.contains("incompatible"));
    assert!(output_gate_mode_for_verification(true, "typo").is_err());
    assert!(matches!(
        output_gate_mode_for_verification(false, "allow-unknown"),
        Ok(OutputGateMode::AllowUnknown)
    ));
}

#[test]
fn cross_target_and_allocator_paths_fail_closed_under_strict() {
    assert!(!output_gate_allows_unreconciled_target(OutputGateMode::Strict, false));
    assert!(output_gate_allows_unreconciled_target(OutputGateMode::Strict, true));
    assert!(output_gate_allows_unreconciled_target(OutputGateMode::AllowUnknown, false));
    assert!(!output_gate_allows_unverified_artifact(OutputGateMode::Strict));
}

#[test]
fn production_linkage_policy_never_strengthens_weak_definitions() {
    assert!(production_function_symbol_contract_supported(
        Linkage::External,
        Visibility::Default
    ));
    assert!(!production_function_symbol_contract_supported(
        Linkage::External,
        Visibility::Hidden
    ));
    assert!(!production_function_symbol_contract_supported(
        Linkage::External,
        Visibility::Protected
    ));
    for linkage in [
        Linkage::Internal,
        Linkage::AvailableExternally,
        Linkage::Common,
        Linkage::ExternalWeak,
        Linkage::LinkOnceAny,
        Linkage::LinkOnceODR,
        Linkage::WeakAny,
        Linkage::WeakODR,
    ] {
        assert!(
            !production_function_symbol_contract_supported(linkage, Visibility::Default),
            "{linkage:?}"
        );
    }
}

#[test]
fn allocator_module_spec_from_names_builds_known_wrappers() {
    rustc_span::create_default_session_globals_then(|| {
        let spec = allocator_module_spec_from_names_with_mangler(
            "krate",
            [sym::alloc, sym::alloc_error_handler],
            |item_name| format!("mangled::{item_name}"),
        )
        .expect("known allocator method names should build a spec");

        assert_eq!(spec.module_name, "krate.allocator");
        assert_eq!(
            spec.no_alloc_shim_is_unstable_symbol_name.as_deref(),
            Some("mangled::__rust_no_alloc_shim_is_unstable_v2")
        );
        assert_eq!(spec.functions.len(), 2);
        assert_eq!(spec.functions[0].name, "alloc");
        assert_eq!(spec.functions[0].wrapper_symbol_name, "mangled::__rust_alloc");
        assert_eq!(spec.functions[0].callee_symbol_name, "mangled::__rdl_alloc");
        assert_eq!(spec.functions[0].kind, bridge_backend::AllocatorFunctionKind::Alloc);
        assert_eq!(spec.functions[0].inputs, vec![bridge_backend::AllocatorArgKind::Layout]);
        assert_eq!(spec.functions[0].output, bridge_backend::AllocatorResultKind::ResultPtr);
        assert_eq!(
            spec.functions[1].kind,
            bridge_backend::AllocatorFunctionKind::AllocErrorHandler
        );
        assert_eq!(spec.functions[1].output, bridge_backend::AllocatorResultKind::Never);
    });
}

#[test]
fn allocator_module_spec_from_names_allows_empty_function_set() {
    rustc_span::create_default_session_globals_then(|| {
        let spec =
            allocator_module_spec_from_names_with_mangler("krate", std::iter::empty(), |item| {
                format!("mangled::{item}")
            })
            .expect("empty allocator shim method set should still produce a module spec");

        assert_eq!(spec.module_name, "krate.allocator");
        assert!(spec.functions.is_empty());
        assert_eq!(
            spec.no_alloc_shim_is_unstable_symbol_name.as_deref(),
            Some("mangled::__rust_no_alloc_shim_is_unstable_v2")
        );
    });
}

#[test]
fn allocator_module_spec_from_names_rejects_unknown_methods() {
    rustc_span::create_default_session_globals_then(|| {
        let err = allocator_module_spec_from_names_with_mangler(
            "krate",
            [sym::mystery_alloc],
            |item_name| format!("mangled::{item_name}"),
        )
        .expect_err("unexpected allocator method names should be rejected");

        assert!(err.contains("mystery_alloc"));
    });
}

#[test]
fn apply_direct_call_name_overrides_rewrites_call_terminators() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, VerifiableBody,
    };

    let mut func = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "krate::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "krate::helper".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(trust_types::ConstValue::Bool(true)),
                        expected: true,
                        msg: trust_types::AssertMessage::Custom("ok".to_string()),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::process::exit".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    apply_direct_call_name_overrides(
        &mut func,
        &[
            Some("helper".to_string()),
            Some("should_be_ignored".to_string()),
            Some("_RNvCsynth4core3ptr13drop_in_place".to_string()),
        ],
    )
    .unwrap();

    match &func.body.blocks[0].terminator {
        Terminator::Call { func, .. } => assert_eq!(func, "helper"),
        other => panic!("expected call terminator, got {other:?}"),
    }
    assert!(matches!(func.body.blocks[1].terminator, Terminator::Assert { .. }));
    match &func.body.blocks[2].terminator {
        Terminator::Call { func, .. } => {
            assert_eq!(func, "_RNvCsynth4core3ptr13drop_in_place")
        }
        other => panic!("expected call terminator, got {other:?}"),
    }

    let err = apply_direct_call_name_overrides(&mut func, &[None])
        .expect_err("block-count drift must fail closed");
    assert!(err.contains("block-count drift"));
}
