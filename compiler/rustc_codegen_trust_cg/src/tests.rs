use super::*;

// Trust: v41 object metadata must survive the builtin backend's static adapter.
#[test]
fn production_static_preserves_object_retention_and_linkage() {
    for retained in [false, true] {
        for is_external in [false, true] {
            let global = ProductionStatic {
                symbol: "metadata_fixture".into(),
                bytes: vec![1, 2, 3, 4],
                mutable: true,
                is_external,
                retained,
                align: 4,
            }
            .into_object_global();
            assert_eq!(global.retained, retained);
            assert_eq!(global.is_external, is_external);
            assert_eq!(global.visibility, trust_ir::Visibility::Default);
            assert_eq!(global.data, [1, 2, 3, 4]);
            assert_eq!(global.align, 4);
            assert_eq!(global.section, None);
            assert!(!global.comdat);
            assert!(global.mutable);
            assert!(!global.is_weak && !global.is_import && !global.is_thread_local);
        }
    }
}

#[test]
fn backend_name() {
    let backend = TrustCgCodegenBackend::default();
    assert_eq!(CodegenBackend::name(&backend), "trust-cg");
}

#[test]
fn backend_thin_lto_not_supported() {
    assert!(!TrustCgCodegenBackend::backend_init().thin_lto_supported);
}

#[test]
fn backend_new_returns_boxed() {
    let backend = TrustCgCodegenBackend::new();
    assert_eq!(CodegenBackend::name(&*backend), "trust-cg");
}

#[test]
fn backend_no_zstd() {
    let backend = TrustCgCodegenBackend::default();
    assert!(!backend.has_zstd());
}

#[test]
fn backend_no_replaced_intrinsics() {
    assert!(TrustCgCodegenBackend::backend_init().replaced_intrinsics.is_empty());
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
    assert!(config.internal_target_features.is_empty());
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

    for arch in ["aarch64", "x86_64"] {
        assert!(TrustCgCodegenBackend::output_type_supported(arch, OutputType::Object));
        assert!(TrustCgCodegenBackend::output_type_supported(arch, OutputType::Exe));
    }
    assert!(!TrustCgCodegenBackend::output_type_supported("aarch64", OutputType::Assembly));
    assert!(!TrustCgCodegenBackend::output_type_supported("x86_64", OutputType::Bitcode));

    assert_eq!(supported_crate_types_for_outputs(true), vec![CrateType::Rlib]);
    let analysis = supported_crate_types_for_outputs(false);
    assert!(analysis.contains(&CrateType::Cdylib));
    assert!(analysis.contains(&CrateType::Executable));
}

#[test]
fn object_and_archive_outputs_share_native_safety_and_crate_type_policy() {
    use rustc_session::config::OutputTypes;

    for output in [OutputType::Object, OutputType::Exe] {
        let outputs = OutputTypes::new(&[(output, None)]);
        assert!(native_machine_output_requested(&outputs));
        assert_eq!(
            supported_crate_types_for_outputs(native_machine_output_requested(&outputs)),
            vec![CrateType::Rlib]
        );
        let mixed = OutputTypes::new(&[
            (OutputType::Mir, None),
            (OutputType::Metadata, None),
            (OutputType::DepInfo, None),
            (output, None),
        ]);
        assert!(native_machine_output_requested(&mixed));
    }
    for output in [
        OutputType::Mir,
        OutputType::Metadata,
        OutputType::DepInfo,
        OutputType::TrustIr,
        OutputType::Assembly,
        OutputType::LlvmAssembly,
        OutputType::Bitcode,
        OutputType::ThinLinkBitcode,
    ] {
        let outputs = OutputTypes::new(&[(output, None)]);
        assert!(!native_machine_output_requested(&outputs));
    }
    assert!(!native_machine_output_requested(&OutputTypes::new(&[])));
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

/// WS7.10 / F-114: a dropped crate type is fatal exactly for a session that
/// requests native output and will run codegen.
#[test]
fn unsupported_crate_type_is_fatal_only_for_native_codegen_sessions() {
    // Positive: a real native compilation (default `--emit=link`, or obj) with
    // no print request, or with only link-dependent prints that let codegen run.
    assert!(unsupported_crate_type_is_fatal_for(true, false, []));
    assert!(unsupported_crate_type_is_fatal_for(true, false, [PrintKind::NativeStaticLibs]));
    assert!(unsupported_crate_type_is_fatal_for(true, false, [PrintKind::LinkArgs]));

    // Cargo's capability probe: `--print=file-names` (plus sysroot, cfg, …)
    // stops before codegen, so the probe keeps rustc's warn-and-omit contract.
    assert!(!unsupported_crate_type_is_fatal_for(
        true,
        false,
        [
            PrintKind::FileNames,
            PrintKind::Sysroot,
            PrintKind::SplitDebuginfo,
            PrintKind::CrateName,
            PrintKind::Cfg,
        ],
    ));
    assert!(!unsupported_crate_type_is_fatal_for(
        true,
        false,
        [PrintKind::NativeStaticLibs, PrintKind::FileNames],
    ));

    // Frontend-only output never reaches trust-cg's native lane.
    assert!(!unsupported_crate_type_is_fatal_for(false, false, []));
    assert!(!unsupported_crate_type_is_fatal_for(false, false, [PrintKind::FileNames]));
}

/// WS7.10 review: `-Zunpretty=<mode>` and `-Zno-analysis` build the global
/// context (so the hook runs) but exit before codegen and link, emitting no
/// artifact; a dropped crate type there must stay a warning, even with native
/// output nominally requested and a link-dependent print alongside.
#[test]
fn unsupported_crate_type_is_not_fatal_for_sessions_that_exit_before_codegen() {
    assert!(!unsupported_crate_type_is_fatal_for(true, true, []));
    assert!(!unsupported_crate_type_is_fatal_for(true, true, [PrintKind::NativeStaticLibs]));
    // Mutation control: the same session without the early exit IS fatal, so
    // the flag, not the other arguments, is what exempts it.
    assert!(unsupported_crate_type_is_fatal_for(true, false, [PrintKind::NativeStaticLibs]));
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
    for triple in
        ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "aarch64-unknown-linux-musl"]
    {
        assert_eq!(scalar_register_argument_limit(triple), Some(8), "{triple}");
    }
    for triple in ["x86_64-apple-darwin", "x86_64-unknown-linux-gnu", "x86_64-unknown-linux-musl"] {
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
    attrs.instrument_fn = Some(InstrumentFnAttr::On);
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

// Trust (owner ruling D17): the frozen instance assembler decides "is the gate
// strict?" from the session itself (`strict_gate_from`) rather than from a bool
// this file passes in. It must agree with the emission path's own resolution on
// every (verification, flag) pair, including the refused ones.
#[test]
fn the_instance_lane_reads_the_same_strictness_the_emission_path_uses() {
    for strict_verification in [false, true] {
        for configured in ["strict", "allow-unknown", "off", "typo", ""] {
            let emission = matches!(
                output_gate_mode_for_verification(strict_verification, configured),
                Ok(OutputGateMode::Strict)
            );
            assert_eq!(
                trust_ir_frontend::instance_assembly::strict_gate_from(
                    strict_verification,
                    configured
                ),
                emission,
                "strict_verification={strict_verification}, -Ztrust-cg-output-gate={configured}"
            );
        }
    }
}

// Trust (F1): the frontend selector is a CLOSED domain like the gate mode, and
// its default has to be the shipped MIR path. Both facts are load-bearing: the
// default is what makes "the default path is unchanged" true by construction,
// and a typo that fell through to `mir` would silently compile the MIR path
// while the caller believed they had measured F1.
#[test]
fn trust_cg_frontend_domain_is_closed_and_defaults_to_mir() {
    assert_eq!(trust_cg_frontend_from_name("mir"), Ok(TrustCgFrontend::Mir));
    assert_eq!(trust_cg_frontend_from_name("trust-ir"), Ok(TrustCgFrontend::TrustIr));
    assert!(trust_cg_frontend_from_name("trust_ir").is_err());
    assert!(trust_cg_frontend_from_name("").is_err());
    assert!(trust_cg_frontend_from_name("typo").is_err());
    // The option table's declared default, read back through the same resolver
    // the backend uses.
    assert_eq!(
        trust_cg_frontend_from_name(
            &rustc_session::config::UnstableOptions::default().trust_cg_frontend
        ),
        Ok(TrustCgFrontend::Mir),
    );
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
    // The two STRONG definitions the object emitters can express. `Internal` is
    // admitted because the function-symbol path now carries a per-function
    // binding (Mach-O local / ELF `STB_LOCAL`) AND the codegen unit is emitted
    // as ONE object, so a local callee stays reachable from its callers.
    assert!(production_function_symbol_contract_supported(Linkage::External, Visibility::Default));
    assert!(production_function_symbol_contract_supported(Linkage::Internal, Visibility::Default));

    // VISIBILITY. `Hidden` is admitted on an `External` DEFINITION only: the
    // Mach-O writer emits it as a private extern (`N_EXT | N_PEXT`, 7c2557901d),
    // the quadrant rustc assigns a `pub(crate)` definition promoted across
    // CGUs, and `bridge_function_linkage` maps it to `FunctionLinkage::Hidden`.
    // `Hidden` on a local is redundant and rustc never emits it; `Protected`
    // has dynamic-link semantics no writer models. Both stay refused.
    assert!(production_function_symbol_contract_supported(Linkage::External, Visibility::Hidden));
    assert!(!production_function_symbol_contract_supported(Linkage::Internal, Visibility::Hidden));
    for linkage in [Linkage::External, Linkage::Internal] {
        assert!(
            !production_function_symbol_contract_supported(linkage, Visibility::Protected),
            "{linkage:?} / Protected"
        );
    }

    // Everything that is NOT a strong definition stays refused: weak, link-once,
    // common, and available-externally all have coalescing/interposition
    // semantics the emitters do not implement.
    for linkage in [
        Linkage::AvailableExternally,
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
fn admitted_linkages_map_onto_the_three_emittable_bindings() {
    use rustc_middle::mono::Visibility;
    assert_eq!(
        bridge_function_linkage(Linkage::External, Visibility::Default),
        Ok(bridge_backend::FunctionLinkage::External)
    );
    assert_eq!(
        bridge_function_linkage(Linkage::Internal, Visibility::Default),
        Ok(bridge_backend::FunctionLinkage::Internal)
    );
    // External + Hidden = the pub(crate)-promoted-for-cross-CGU quadrant: a
    // private extern (N_EXT | N_PEXT) on the Mach-O path.
    assert_eq!(
        bridge_function_linkage(Linkage::External, Visibility::Hidden),
        Ok(bridge_backend::FunctionLinkage::Hidden)
    );
    // A linkage the gate never admits must fail closed here rather than be
    // silently exported as a strong definition — and so must a
    // visibility/linkage pair outside the admitted quadrants.
    assert!(bridge_function_linkage(Linkage::WeakODR, Visibility::Default).is_err());
    assert!(bridge_function_linkage(Linkage::Internal, Visibility::Hidden).is_err());
    assert!(bridge_function_linkage(Linkage::External, Visibility::Protected).is_err());
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
                        callee_identity: None,
                        callee_key: None,
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
                        callee_identity: None,
                        callee_key: None,
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
            // Trust (R0 carrier): back-fill of the new `VerifiableBody::datatype_defs`
            // table. An empty table is exactly the pre-carrier meaning, so this is a
            // no-op restatement of what this body already asserted.
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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

/// Rust source with every comment and every string, byte-string, raw-string and char literal
/// blanked, for the source scans below: a literal keeps its delimiters and loses its contents
/// (`"…"` and `r#"…"#` become `""`, `'x'` becomes `' '`), and a comment becomes nothing; line
/// breaks are kept. A needle in prose or in a literal (a `retired_by` text that NAMES a call)
/// then never reads as code, and brace matching sees only code braces. An unterminated literal
/// or comment panics, so a mis-lex cannot silently swallow the rest of a file.
fn code_only(src: &str) -> String {
    fn ident(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }
    fn newlines(out: &mut Vec<u8>, span: &[u8]) {
        out.extend(span.iter().filter(|&&c| c == b'\n'));
    }
    let b = src.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        let next = b.get(i + 1).copied();
        if c == b'/' && next == Some(b'/') {
            i = b[i..].iter().position(|&c| c == b'\n').map_or(b.len(), |p| i + p);
            continue;
        }
        if c == b'/' && next == Some(b'*') {
            let (mut depth, mut j) = (0usize, i);
            loop {
                assert!(j + 1 < b.len(), "unterminated block comment at byte {i}");
                match (b[j], b[j + 1]) {
                    (b'/', b'*') => (depth, j) = (depth + 1, j + 2),
                    (b'*', b'/') => {
                        (depth, j) = (depth - 1, j + 2);
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => j += 1,
                }
            }
            newlines(&mut out, &b[i..j]);
            i = j;
            continue;
        }
        // A raw string, `r"…"`, `r#"…"#`, `br"…"` or `cr"…"`, whose prefix does not continue an
        // identifier (`r#ident` is a raw identifier: no `"` follows its `#`s).
        let after_ident = i > 0 && ident(b[i - 1]);
        if !after_ident && (c == b'r' || ((c == b'b' || c == b'c') && next == Some(b'r'))) {
            let open = if c == b'r' { i + 1 } else { i + 2 };
            let hashes = b[open..].iter().take_while(|&&h| h == b'#').count();
            if b.get(open + hashes) == Some(&b'"') {
                let close: Vec<u8> = std::iter::once(b'"').chain(vec![b'#'; hashes]).collect();
                let body = open + hashes + 1;
                let end = b[body..]
                    .windows(close.len())
                    .position(|w| w == close.as_slice())
                    .map(|p| body + p + close.len())
                    .unwrap_or_else(|| panic!("unterminated raw string at byte {i}"));
                out.extend_from_slice(b"\"\"");
                newlines(&mut out, &b[i..end]);
                i = end;
                continue;
            }
        }
        if c == b'"' {
            let mut j = i + 1;
            loop {
                assert!(j < b.len(), "unterminated string at byte {i}");
                match b[j] {
                    // An escape, a line continuation included, skips the byte it escapes.
                    b'\\' => j += 2,
                    b'"' => break,
                    _ => j += 1,
                }
            }
            out.extend_from_slice(b"\"\"");
            newlines(&mut out, &b[i..j]);
            i = j + 1;
            continue;
        }
        if c == b'\'' {
            // A char literal (`'x'`, `'"'`, `'\''`, `'\u{7b}'`), not a lifetime or a label.
            let end = if next == Some(b'\\') {
                b.get(i + 3..)
                    .and_then(|rest| rest.iter().position(|&c| c == b'\''))
                    .map(|p| i + 3 + p + 1)
            } else {
                src[i + 1..].chars().next().and_then(|ch| {
                    let close = i + 1 + ch.len_utf8();
                    (b.get(close) == Some(&b'\'')).then_some(close + 1)
                })
            };
            if let Some(end) = end {
                out.extend_from_slice(b"' '");
                i = end;
                continue;
            }
        }
        out.push(c);
        i += 1;
    }
    String::from_utf8(out).expect("blanking cuts only at ASCII bytes")
}

/// Every fn item of blanked source `code` ([`code_only`]): its name and the byte range of its
/// body, `{` to `}`. The body opens at the first `{` outside parentheses and brackets after the
/// name; a `;` there first is a bodyless declaration (`[u8; 4]` in a signature is not).
fn fn_bodies(code: &str) -> Vec<(String, std::ops::Range<usize>)> {
    let b = code.as_bytes();
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(rel) = code[from..].find("fn ") {
        let at = from + rel;
        from = at + 3;
        if at > 0 && (b[at - 1].is_ascii_alphanumeric() || b[at - 1] == b'_') {
            continue;
        }
        let name: String =
            code[at + 3..].chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        if name.is_empty() {
            continue;
        }
        let mut depth = 0i32;
        let mut open = None;
        for (k, &c) in b.iter().enumerate().skip(at) {
            match c {
                b'(' | b'[' => depth += 1,
                b')' | b']' => depth -= 1,
                b';' if depth == 0 => break,
                b'{' if depth == 0 => {
                    open = Some(k);
                    break;
                }
                _ => {}
            }
        }
        let Some(open) = open else { continue };
        let mut braces = 0usize;
        let close = b[open..]
            .iter()
            .enumerate()
            .find_map(|(k, &c)| {
                match c {
                    b'{' => braces += 1,
                    b'}' => {
                        braces -= 1;
                        if braces == 0 {
                            return Some(open + k);
                        }
                    }
                    _ => {}
                }
                None
            })
            .unwrap_or_else(|| panic!("fn `{name}` has an unbalanced body"));
        out.push((name, open..close + 1));
    }
    out
}

/// The body of the one fn named `name` in blanked source `code`.
fn fn_text<'a>(code: &'a str, name: &str) -> &'a str {
    let found: Vec<_> = fn_bodies(code).into_iter().filter(|(n, _)| n == name).collect();
    assert_eq!(found.len(), 1, "exactly one fn `{name}`");
    &code[found[0].1.clone()]
}

/// Byte offsets of `ident` as a whole identifier in `code`.
fn ident_offsets(code: &str, ident: &str) -> Vec<usize> {
    let b = code.as_bytes();
    let is_ident = |c: Option<u8>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_');
    code.match_indices(ident)
        .map(|(at, _)| at)
        .filter(|&at| {
            let before = at.checked_sub(1).map(|k| b[k]);
            !is_ident(before) && !is_ident(b.get(at + ident.len()).copied())
        })
        .collect()
}

/// Blanked source `code` ([`code_only`]) without its `#[cfg(test)]` items: each such attribute,
/// any attributes after it, and the item it marks (to its `;`, or to the end of its first
/// brace-balanced block outside parentheses and brackets) become nothing, line breaks kept.
/// Everything else stays, code AFTER a `#[cfg(test)] mod tests;` included: production that
/// follows a test item is still production.
fn without_cfg_test_items(code: &str) -> String {
    const ATTR: &str = "#[cfg(test)]";
    let b = code.as_bytes();
    let mut out = String::with_capacity(code.len());
    let mut from = 0;
    while let Some(rel) = code[from..].find(ATTR) {
        let at = from + rel;
        out.push_str(&code[from..at]);
        let (mut depth, mut k, mut end) = (0i32, at + ATTR.len(), None);
        while k < b.len() {
            match b[k] {
                b'(' | b'[' => depth += 1,
                b')' | b']' => depth -= 1,
                b';' if depth == 0 => {
                    end = Some(k + 1);
                    break;
                }
                b'{' if depth == 0 => {
                    let mut braces = 0usize;
                    end = b[k..].iter().enumerate().find_map(|(j, &c)| {
                        match c {
                            b'{' => braces += 1,
                            b'}' => {
                                braces -= 1;
                                if braces == 0 {
                                    return Some(k + j + 1);
                                }
                            }
                            _ => {}
                        }
                        None
                    });
                    break;
                }
                _ => {}
            }
            k += 1;
        }
        let end = end.unwrap_or_else(|| panic!("the `#[cfg(test)]` item at byte {at} has no end"));
        out.extend(code[at..end].chars().filter(|&c| c == '\n'));
        from = end;
    }
    out.push_str(&code[from..]);
    out
}

/// This crate's production sources with string literals blanked too: every `.rs` file under
/// `dir` except test files, as `(path relative to src/, code)`, comments and literals blanked
/// ([`code_only`]) and every `#[cfg(test)]` item removed ([`without_cfg_test_items`]). Unlike
/// the routing test's filter, nothing after a file's first `#[cfg(test)]` is cut: a production
/// fn placed after `#[cfg(test)] mod tests;` is read.
fn production_sources_of(src: &std::path::Path, dir: &std::path::Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).expect("the crate's src directory") {
        let path = entry.expect("a directory entry").path();
        if path.is_dir() {
            out.extend(production_sources_of(src, &path));
            continue;
        }
        let name = path.strip_prefix(src).expect("under src/").to_string_lossy().into_owned();
        let test_file = name.rsplit('/').next() == Some("tests.rs")
            || name.split('/').any(|segment| segment == "tests");
        if !name.ends_with(".rs") || test_file {
            continue;
        }
        let code = code_only(&std::fs::read_to_string(&path).expect("a source file"));
        out.push((name, without_cfg_test_items(&code)));
    }
    out
}

/// The entry lines of `manifest`'s non-dev dependency tables (`[dependencies]`,
/// `[build-dependencies]`, `[target.<cfg>.dependencies]`, and `[dependencies.<name>]` headers).
fn dependency_lines(manifest: &str) -> Vec<String> {
    let mut lines = Vec::new();
    let mut in_table = false;
    for line in manifest.lines().map(str::trim) {
        if let Some(header) = line.strip_prefix('[') {
            let header = header.trim_end_matches(']');
            in_table =
                matches!(header.rsplit('.').next(), Some("dependencies" | "build-dependencies"));
            if !header.contains("dev-dependencies") && header.contains("dependencies.") {
                lines.push(header.to_string());
            }
            continue;
        }
        if in_table && line.contains('=') && !line.starts_with('#') {
            lines.push(line.to_string());
        }
    }
    lines
}

#[test]
fn the_source_scan_lexer_blanks_literals_and_comments() {
    let src = concat!(
        "fn a() { let s = \"x\\\"instance_mir(\\\\\"; }\n",
        "fn b() { let t = \"line \\\n  instance_mir( continued\"; }\n",
        "fn c() { let r = r#\"raw \"instance_mir(\" }\"#; let q = br\"{\"; }\n",
        "fn d<'a>(x: &'a u8) -> char { let _ = b'{'; let _ = '\\''; '\"' }\n",
        "fn e() { /* outer /* instance_mir( */ { */ g(); } // instance_mir(\n",
        "fn f(x: [u8; 4]) -> u8 { let r#type = 1; instance_mir(x) }\n",
    );
    let code = code_only(src);
    assert_eq!(code.lines().count(), src.lines().count(), "line breaks are kept: {code}");
    assert_eq!(ident_offsets(&code, "instance_mir").len(), 1, "only `f` calls it: {code}");
    let bodies = fn_bodies(&code);
    let names: Vec<&str> = bodies.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["a", "b", "c", "d", "e", "f"], "{code}");
    let at = ident_offsets(&code, "instance_mir")[0];
    assert_eq!(bodies.iter().find(|(_, r)| r.contains(&at)).map(|(n, _)| n.as_str()), Some("f"));
    assert!(fn_text(&code, "e").contains("g();"), "a block comment's braces are not code");
    assert!(fn_text(&code, "d").ends_with("' ' }"), "a char literal `'\"'` opens no string");
    let stripped = without_cfg_test_items(concat!(
        "fn a() {}\n",
        "#[cfg(test)]\n",
        "mod tests;\n",
        "fn b() { instance_mir() }\n",
        "#[cfg(test)]\n",
        "#[allow(dead_code)]\n",
        "mod m { fn c() { instance_mir() } }\n",
        "fn d(x: [u8; 2]) {}\n",
    ));
    assert_eq!(stripped.lines().count(), 8, "line breaks are kept: {stripped}");
    let names: Vec<String> = fn_bodies(&stripped).into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["a", "b", "d"], "code after a test item is kept: {stripped}");
    assert_eq!(ident_offsets(&stripped, "instance_mir").len(), 1, "{stripped}");
    let lines = dependency_lines(
        "[package]\nname = \"x\"\n[dependencies]\na = { workspace = true }\n# c = 1\n\
         [dev-dependencies]\nb = \"1\"\n[target.'cfg(unix)'.dependencies]\nd = \"1\"\n\
         [dependencies.e]\nversion = \"1\"\n",
    );
    assert_eq!(lines, ["a = { workspace = true }", "d = \"1\"", "dependencies.e"]);
}

/// Trust (step 2 increment 4d, sub-step 4d.0a; docs/design/2026-09-29-step2-inc4-drops.md §5
/// and §7.4, docs/design/2026-10-08-step2-inc4d-shims-plan.md §1(b)): NO F1 PATH TAKES THE MIR
/// ROUTE FOR A SHIM. A `Shim(..)` instance is refused `[synthesized-instance]` on F1 until the
/// frozen shim lane (4d.3) synthesizes it as trust-ir; rustc's shim MIR (`mir_shims`, read
/// through `instance_mir`) is never an F1 input. Scoped to F1: trust-cg's MIR frontend
/// (`-Ztrust-cg-frontend=mir`, `build_production_mono_functions`) compiles every inventory item
/// from rustc's MIR, shims included, by construction (an R-2 residual that leaves with that
/// frontend; docs/KNOWN_HAZARDS.md, "shims are refused on F1"), and this test pins only that its
/// extraction is reached from nowhere else.
///
/// Read over the crate's production sources with string literals blanked too and only
/// `#[cfg(test)]` items removed ([`production_sources_of`]), so a `retired_by` text that names a
/// call is not read as one and a production fn after `#[cfg(test)] mod tests;` is. The routing
/// test above is not edited (5.4.2 extends it).
///
/// WHAT (1) SEES, and what it does not (2026-10-13 review): a use of one of the names in
/// `mir_route_names` — rustc's MIR body queries, the entries of trust-mir-extract and
/// trust-thir-lower that read an instance's MIR or turn a MIR body into a `VerifiableFunction`,
/// and the trust-ir-bridge and trust-cg-bridge entries that compile a `VerifiableFunction` into
/// trust-ir or machine code — anywhere outside its pinned (file, enclosing fn) sites, aliases and
/// glob imports included (a `use` names the item). It does not see a dependency entry under a
/// name not on the list: a new MIR reader added to a dependency crate, or a new wrapper of a
/// listed one. trust-thir-lower's own `shim_route_tests` pin that crate's MIR reads and
/// MIR-to-trust-ir lowerings crate-wide; trust-mir-extract builds no trust-ir, so a body it
/// returns reaches code only through a listed bridge entry.
#[test]
fn no_f1_path_takes_the_mir_route_for_a_shim() {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let sources = production_sources_of(&src, &src);
    fn file<'a>(sources: &'a [(String, String)], rel: &str) -> &'a str {
        &sources.iter().find(|(name, _)| name == rel).unwrap_or_else(|| panic!("no `{rel}`")).1
    }
    // Where an identifier is used, its definition excluded, as sorted (file, enclosing fn).
    let uses = |ident: &str| -> Vec<(String, String)> {
        let mut found = Vec::new();
        for (name, code) in &sources {
            let bodies = fn_bodies(code);
            for at in ident_offsets(code, ident) {
                if code[..at].ends_with("fn ") {
                    continue;
                }
                let enclosing = bodies
                    .iter()
                    .filter(|(_, range)| range.contains(&at))
                    .min_by_key(|(_, range)| range.len())
                    .map_or("<item level>", |(fn_name, _)| fn_name.as_str());
                found.push((name.clone(), enclosing.to_string()));
            }
        }
        found.sort();
        found
    };
    let pairs = |list: &[(&str, &str)]| -> Vec<(String, String)> {
        list.iter().map(|(file, func)| (file.to_string(), func.to_string())).collect()
    };

    // (1) Every name through which this crate could read a MIR body, or compile one, is used
    // where it is today and nowhere else. rustc's MIR of an instance is read only by the
    // retained MIR frontend's extraction and the Clean-origin inventory hook (plan step
    // 3.5, `clean_inventory::neighbours`, which demands a local Clean-origin item's MIR for the
    // collector's walk and discards it); that hook returns before reading it for every
    // non-`Item`. No file asks for `mir_shims` or another MIR query, and no file names a
    // dependency's instance-MIR reader. A MIR body becomes a `VerifiableFunction` only in that
    // extraction, and a `VerifiableFunction` becomes trust-ir only in the feature-gated
    // emission adapter (`trust_ir_emission.rs`, the MIR frontend's inventory), and
    // machine code only in the MIR frontend's output gate.
    let mir_route_names: &[&str] = &[
        // rustc's MIR body queries (a shim's body is `mir_shims`, read through `instance_mir`;
        // the others answer for a `DefId`, so asked for a shim's `def_id()` they give another
        // body)
        "instance_mir",
        "mir_shims",
        "optimized_mir",
        "mir_built",
        "mir_promoted",
        "mir_for_ctfe",
        "promoted_mir",
        "mir_drops_elaborated_and_const_checked",
        // trust-mir-extract: a MIR body to a `VerifiableFunction`, and the modules whose entries
        // read an instance's MIR, a shim's included (`instance_body`, `atomic_callsite`,
        // `concurrency_effects`)
        "extract_function",
        "extract_function_faithful",
        "extract_function_for_codegen",
        "extract_function_for_trust_ir_upstream",
        "extract_function_with_contract_bundle",
        "extract_function_with_contract_bundle_and_elem_sizes",
        "extract_faithful_body_with_function_allocations",
        "extract_instance_faithful",
        "instance_body",
        "atomic_callsite",
        "concurrency_effects",
        // trust-thir-lower: the modules that read a shim's MIR (the drop-glue oracle's
        // `shim_events`, the probe's channel C)
        "drop_glue_oracle",
        "shim_events",
        "instance_probe",
        // trust-ir-bridge: a `VerifiableFunction` to trust-ir
        "lower_to_trust_ir",
        "lower_mir_compat_to_trust_ir",
        "lower_mir_compat_functions_to_trust_ir",
        // trust-cg-bridge: a `VerifiableFunction` to LIR or to an object
        "lower_to_lir",
        "lower_to_lir_with_options",
        "lower_body_to_lir",
        "lower_body_to_lir_with_options",
        "lower_body_to_lir_with_options_and_consumptions",
        "emit_objects_verified",
        "emit_objects_verified_with_backend",
        "emit_objects_verified_reported",
        "emit_objects_verified_reported_with_backend",
        "emit_module_object_verified_reported_with_backend",
        "emit_object_verified",
        "emit_object_verified_with_backend",
    ];
    let pinned: &[(&str, &[(&str, &str)])] = &[
        (
            "instance_mir",
            &[
                ("lib.rs", "extract_mono_verifiable_function_with_abi"),
                ("trust_ir_frontend/clean_inventory.rs", "neighbours"),
                // Trust (PKG-CP): a refuse-only ORACLE, not a route. It reads the `Assert`
                // terminators of the instance's MIR and refuses a panic site that matches none
                // (lang item and rustc's `Location` record); nothing from the MIR body reaches
                // trust-ir or machine code (DECISION_QUEUE PKG-CP-CONSUMER-SITING-1).
                ("trust_ir_frontend/panic_sites/rustc_half.rs", "matches_rustc_mir"),
            ],
        ),
        (
            "extract_function_for_codegen",
            &[("lib.rs", "extract_mono_verifiable_function_with_abi")],
        ),
        ("extract_function_for_trust_ir_upstream", &[]),
        ("lower_mir_compat_to_trust_ir", &[]),
        (
            "lower_mir_compat_functions_to_trust_ir",
            &[
                ("trust_ir_emission.rs", "emit_trust_ir_module"),
                ("trust_ir_emission.rs", "validate_emitted_module"),
            ],
        ),
        (
            // The `use` inside the gate, and the call.
            "emit_module_object_verified_reported_with_backend",
            &[
                ("lib.rs", "run_module_output_preservation_gate"),
                ("lib.rs", "run_module_output_preservation_gate"),
            ],
        ),
    ];
    for (name, _) in pinned {
        assert!(mir_route_names.contains(name), "`{name}` is pinned but not scanned");
    }
    for name in mir_route_names {
        let sites = pinned.iter().find(|(n, _)| n == name).map_or(&[][..], |(_, sites)| *sites);
        assert_eq!(
            uses(*name),
            pairs(sites),
            "`{name}` is used outside its pinned sites: a new MIR read, or a new route from a MIR \
             body to trust-ir or machine code (a shim's MIR is `mir_shims`, read through \
             `instance_mir`)"
        );
    }

    // (2) That extraction is reached only from the retained MIR frontend's inventory.
    assert_eq!(
        uses("extract_mono_verifiable_function_with_abi"),
        pairs(&[("lib.rs", "extract_mono_verifiable_function")])
    );
    assert_eq!(
        uses("extract_mono_verifiable_function"),
        pairs(&[("lib.rs", "build_production_mono_functions")]),
        "the MIR frontend's own extraction is reached only from its inventory"
    );
    assert!(
        uses("lower_upstream_instance").is_empty(),
        "the old upstream MIR-to-IR producer is retired"
    );
    assert!(
        uses("routes_to_upstream_mir_lane").is_empty(),
        "no MIR codegen diversion outranks the metadata plan"
    );
    let flat = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        uses("upstream_mir_lane_refusal").is_empty(),
        "Clean metadata is checked without the retired MIR bridge"
    );
    // The Clean-origin inventory hook (plan step 3.5) likewise: it returns for a non-`Item`
    // before its one MIR read, and that read is of its own (`Item`) instance, its body discarded
    // (the collector walks it; nothing here lowers it).
    let clean_inventory = file(&sources, "trust_ir_frontend/clean_inventory.rs");
    let hook = flat(fn_text(clean_inventory, "neighbours"));
    let item_only = hook
        .find("let ty::InstanceKind::Item(def_id) = instance.def else { return None };")
        .expect("the Clean-origin inventory hook returns for a non-`Item`");
    let read = hook
        .find("let _ = tcx.instance_mir(instance.def);")
        .expect("its one MIR read, of its own instance, discarded");
    assert_eq!(hook.matches("instance_mir").count(), 1, "one MIR read: {hook}");
    assert!(item_only < read, "it returns for a non-`Item` before it reads MIR: {hook}");

    // (4) The class's retirement names the shim lane, never rustc's shim MIR or the MIR path.
    let retired = trust_ir_frontend::RefusalClass::SynthesizedInstance.retired_by();
    assert!(retired.contains("shim lane"), "{retired}");
    for stale in ["mir_shims", "MIR path"] {
        assert!(!retired.contains(stale), "`{stale}` in: {retired}");
    }

    // (5) The bridge (the compiler lane's consumer) depends on no MIR producer, so a source
    // needle for one there would be vacuous.
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../crates/trust-cg-bridge/Cargo.toml");
    let manifest = std::fs::read_to_string(&manifest).expect("the bridge's manifest");
    let deps = dependency_lines(&manifest);
    assert!(deps.iter().any(|line| line.starts_with("trust-ir ")), "the table was read: {deps:?}");
    for producer in ["trust-thir-lower", "trust-mir-extract", "trust-ir-bridge"] {
        assert!(
            !deps.iter().any(|line| line.contains(producer)),
            "trust-cg-bridge depends on `{producer}`: {deps:?}"
        );
    }
}

/// Every production source file of this crate under `dir`, as `(path, text)`: test files
/// (`tests.rs`, `tests/`), the `#[cfg(test)]` tail and comment lines excluded, so a doc comment
/// that NAMES a function is not read as a call to it, and a new file is covered too.
fn production_sources(dir: &std::path::Path, out: &mut Vec<(String, String)>) {
    for entry in std::fs::read_dir(dir).expect("the crate's src directory") {
        let path = entry.expect("a directory entry").path();
        if path.is_dir() {
            production_sources(&path, out);
            continue;
        }
        let name = path.to_string_lossy().into_owned();
        if !name.ends_with(".rs") || name.ends_with("/tests.rs") || name.contains("/tests/") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("a source file");
        // Production code only: the `#[cfg(test)]` tail cut, and comment lines dropped so a
        // doc comment that NAMES the producer is not read as a call to it.
        let production = text
            .split("#[cfg(test)]")
            .next()
            .unwrap_or("")
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        out.push((name, production));
    }
}

/// Trust (owner ruling D17): the CONSUMER ROUTING the frozen instance assembler relies on, a
/// residual of its freeze (`scripts/frozen-files.txt`). D17's strict condition, the splice
/// preconditions and the coverage input hold only if every non-upstream item's IR comes from
/// `instance_assembly::Plan::source`: nothing else on this crate's codegen path may call the
/// instance-keyed producer, and the one lowering entry takes the plan's source for the instance
/// it names. Read over every production source file of the crate (test files, `#[cfg(test)]`
/// tails and comment lines excluded), so a new file is covered too.
///
/// Trust (step 2 increment 4c, owner ruling D18 OD-2): the ONE other source is the frozen
/// drop-glue lane, for a drop-glue item only (`drop_glue_lane::GlueLane::glue_item` answers
/// `None` for every other instance, and for every instance when the lane is inactive), decided
/// before the plan; the lane also resolves the drops of whatever the item lowers from, inside
/// the one `lower_from_module` call, which takes it.
#[test]
fn every_planned_item_takes_its_ir_from_the_plan_and_nothing_else_calls_the_producer() {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    production_sources(&src, &mut sources);
    assert!(sources.iter().any(|(name, _)| name.ends_with("/instance_assembly.rs")));
    for (name, text) in &sources {
        if !name.ends_with("/instance_assembly.rs") {
            assert!(
                !text.contains("trust_ir_of_instance_body("),
                "{name} calls the instance-keyed producer outside the frozen assembler"
            );
        }
        for forbidden in ["trust_ir_of_instance(", "trust_ir_of_instance_explained("] {
            assert!(!text.contains(forbidden), "{name} lowers an instance module directly");
        }
    }
    let frontend = &sources
        .iter()
        .find(|(name, _)| name.ends_with("/src/trust_ir_frontend.rs"))
        .expect("the trust-ir frontend")
        .1;
    let lower_instance = &frontend[frontend.find("fn lower_instance<").expect("lower_instance")..];
    let lower_instance = &lower_instance[..lower_instance.find("\n}\n").expect("its end")];
    let flat = lower_instance.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        !flat.contains("routes_to_upstream_mir_lane("),
        "the retired MIR diversion cannot outrank the plan"
    );
    let at_custom =
        flat.find("refuse_custom_mir(tcx, def_id, &symbol)?;").expect("custom-MIR refusal");
    let at_glue = flat
        .find("match glue.glue_item(tcx, instance, &symbol) {")
        .expect("the drop-glue lane's route");
    let at_glue_identity = flat
        .find("glue_function_is_this_instance(&symbol, &module, func_id)?;")
        .expect("the glue item's identity check");
    let at_plan = flat.find("plan.source(index, instance, &symbol)?;").expect("the plan's source");
    let at_identity =
        flat.find("selected_function_is_this_instance(tcx, instance, &symbol, module, func_id)?;");
    let at_lower = flat
        .rfind(
            "lower_from_module(tcx, instance, &symbol, module, func_id, &validate_abi, Some(glue))",
        )
        .expect("the one lowering, which resolves drops through the lane");
    assert!(at_custom < at_glue, "custom-MIR is refused before any source selection");
    assert!(at_glue < at_glue_identity && at_glue_identity < at_plan, "then a glue item's source");
    assert!(at_identity.is_some_and(|at| at_plan < at && at < at_lower));
    assert_eq!(flat.matches("lower_from_module(").count(), 1, "one lowering");
    // The glue lane's `None` arm is the plan: no other route.
    assert_eq!(flat.matches("plan.source(").count(), 1);
    assert_eq!(flat.matches("glue.glue_item(").count(), 1);
    let lib = &sources.iter().find(|(name, _)| name.ends_with("/src/lib.rs")).expect("lib.rs").1;
    let flat_lib = lib.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat_lib.contains("trust_ir_frontend::instance_assembly::plan(tcx, &instances);"));
    assert!(
        flat_lib.contains("trust_ir_frontend::drop_glue_lane::GlueLane::new(tcx, &instances);")
    );
    assert!(flat_lib.contains(
        "match trust_ir_frontend::lower_instance( tcx, instance, &mut plan, &mut glue, index,"
    ));
    // Nothing outside the frozen lane synthesizes glue or rewrites drops into calls.
    for (name, text) in &sources {
        if !name.ends_with("/drop_glue_lane.rs") {
            for forbidden in ["synthesize_glue(", "rewrite_drops(", "glue_plan("] {
                assert!(!text.contains(forbidden), "{name} calls `{forbidden}` outside the lane");
            }
        }
    }

    // Trust (step 2 increment 5, sub-step 5.4.2): the COMPILER LANE's selection takes the same
    // route as `lower_instance`, in the same order, with ONE `plan.source(` and ONE
    // `glue.glue_item(`, and it lowers nothing: neither it nor the pure codegen module calls
    // `lower_from_module(` or the module-to-LIR converter.
    let select = &frontend
        [frontend.find("fn select_for_codegen_module<").expect("the compiler lane's route")..];
    let select = &select[..select.find("\n}\n").expect("its end")];
    let flat_select = select.split_whitespace().collect::<Vec<_>>().join(" ");
    let order = [
        "refuse_custom_mir(tcx, def_id, &symbol)?;",
        "if glue.glue_item(tcx, instance, &symbol).is_some() {",
        "plan.source(index, instance, &symbol)?;",
        "selected_function_is_this_instance(tcx, instance, &symbol, module, func_id)?;",
    ];
    let at: Vec<usize> = order
        .iter()
        .map(|step| flat_select.find(step).unwrap_or_else(|| panic!("no `{step}`")))
        .collect();
    assert!(at.windows(2).all(|w| w[0] < w[1]), "the compiler lane's route is out of order");
    assert_eq!(flat_select.matches("plan.source(").count(), 1);
    assert_eq!(flat_select.matches("glue.glue_item(").count(), 1);
    let codegen_module = &sources
        .iter()
        .find(|(name, _)| name.ends_with("/trust_ir_frontend/codegen_module.rs"))
        .expect("the codegen module")
        .1;
    for (name, text) in
        [("select_for_codegen_module", &flat_select), ("codegen_module.rs", codegen_module)]
    {
        for forbidden in ["lower_from_module(", "lower_module_to_lir"] {
            assert!(!text.contains(forbidden), "{name} lowers through `{forbidden}`");
        }
    }
    let dense_lib: String = lib.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(dense_lib.contains(
        "trust_ir_frontend::select_for_codegen_module(tcx,*instance,&mutplan,&mutglue,index"
    ));
    // Trust (PKG-CP): the compiler lane does not refuse a runtime check at selection; its
    // checks are folded or sited once M_cg is built, after the native classification and
    // before M_cg is taken apart for the compile, and only over a module with no refusal.
    assert!(!flat_select.contains("refuse_unfaithful_panic("), "selection refuses checks again");
    let classify = dense_lib.find("source_abi::classify_native_module(").expect("classification");
    let site = dense_lib
        .find("trust_ir_frontend::panic_sites::rustc_half::site_codegen_module(tcx,&mutout.m_cg")
        .expect("the panic-site pass runs on the compiler lane");
    let taken = dense_lib.find("letcodegen_module::CodegenModuleOutput{").expect("the split");
    assert!(classify < site && site < taken, "the panic-site pass runs out of order");
    assert!(dense_lib[..site].ends_with("ifout.refusals.is_empty(){letsited="));
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the D31 license the bridge's compiler-lane
/// consumer enforces names EXACTLY the authorities the two producers stamp, by value.
#[test]
fn f1_authorities_match_the_producers() {
    assert_eq!(
        trust_cg_bridge::f1_compile::TRUST_DIRECT_LANE_AUTHORITY,
        trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY
    );
    assert_eq!(
        trust_cg_bridge::f1_compile::TRUST_INSTANCE_LANE_AUTHORITY,
        trust_ir_frontend::instance_assembly::TRUST_INSTANCE_LANE_AUTHORITY
    );
}

/// Production text of a source file: comment lines dropped.
fn production_text(source: &str) -> String {
    source
        .split("#[cfg(test)]")
        .next()
        .unwrap_or("")
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane ships ONLY through the
/// bridge's consumer, whose one shipping decision is `CerReport::ships`. The lane never reads a
/// per-function grade, never asks whether a certificate is kernel-proved, and never runs the
/// gate itself.
#[test]
fn compiler_lane_ships_only_through_cer_ships() {
    let lib = production_text(include_str!("lib.rs"));
    let lane = &lib[lib.find("fn codegen_crate_via_compiler_lane<").expect("the lane")..];
    let lane = &lane[..lane.find("\n    }\n").expect("its end")];
    assert!(
        lane.contains("compile_and_verify_trust_ir_module_with_clean("),
        "the lane ships through the consumer"
    );
    assert!(
        lane.contains("clean_admission::with_admissions("),
        "the consumer is scoped to live Session admissions"
    );
    // The join takes the unit out of the ongoing codegen (5db55304711) rather than borrowing it.
    let join = "if let Some(unit) = ongoing.compiler_lane.take() {";
    let join = &lib[lib.find(join).expect("the join")..];
    let join = &join[..join.find("\n        }\n").expect("its end")];
    let pure = production_text(include_str!("trust_ir_frontend/codegen_module.rs"));
    let shape = production_text(include_str!("trust_ir_frontend/abi_shape.rs"));
    for (name, text) in [
        ("the lane", lane),
        ("its join", join),
        ("codegen_module.rs", &pure),
        ("abi_shape.rs", &shape),
    ] {
        for forbidden in [".grade", "is_kernel_proved(", "verify_compiled_module("] {
            assert!(!text.contains(forbidden), "{name} decides shipping through `{forbidden}`");
        }
    }
    // The gate itself is reached ONLY through the bridge's two 16 MiB entries
    // (`census_trust_ir_module`, `compile_and_verify_trust_ir_module`; INC5.4-STACK): no
    // production file of this crate calls it directly, so `RUST_MIN_STACK` cannot shrink the
    // stack it runs on in trustc. Every file, so a new one is covered too.
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    production_sources(&src, &mut sources);
    assert!(sources.len() > 5, "scanned only {} files: wrong root?", sources.len());
    assert!(sources.iter().any(|(name, _)| name.ends_with("/trust_ir_frontend/codegen_module.rs")));
    for (name, text) in &sources {
        assert!(
            !text.contains("verify_compiled_module("),
            "{name} runs the call-event gate outside the bridge's 16 MiB entries"
        );
    }
}

/// Trust (step 2 increment 5, sub-step 5.4.2): `f1_emit_policy` (the compiler lane's) agrees
/// with the two module-to-LIR gate sites, which keep their own literals.
#[test]
fn f1_emit_policy_agrees_with_both_old_sites() {
    use trust_cg_bridge::verify_output::EmitPolicy;
    assert!(matches!(f1_emit_policy(OutputGateMode::Strict), EmitPolicy::StrictProvenOnly));
    assert!(matches!(f1_emit_policy(OutputGateMode::AllowUnknown), EmitPolicy::AllowUnknown));
    // `off` is refused before the lane asks; were it ever asked, it would be strict.
    assert!(matches!(f1_emit_policy(OutputGateMode::Off), EmitPolicy::StrictProvenOnly));
    let lib = production_text(include_str!("lib.rs"));
    let flat = lib.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        flat.matches("OutputGateMode::Strict => EmitPolicy::StrictProvenOnly,").count(),
        3,
        "the two old sites and `f1_emit_policy` each spell the strict arm"
    );
    assert_eq!(
        flat.matches(
            "OutputGateMode::Strict => EmitPolicy::StrictProvenOnly, _ => EmitPolicy::AllowUnknown,"
        )
        .count(),
        2,
        "both old sites map every other mode to allow-unknown, after returning on `off`"
    );
    // The ABI preconditions are extracted, not copied: the old validator calls them first.
    let validate = &lib[lib.find("fn validate_codegen_instance_abi_with<").expect("validator")..];
    let validate = &validate[..validate.find("\n}\n").expect("its end")];
    assert!(validate.contains("let fn_abi = fn_abi_preconditions(tcx, instance, mir_arg_count)?;"));
    assert_eq!(
        lib.matches("fn_abi_of_instance(").count(),
        1,
        "one FnAbi query, in the preconditions"
    );
}
