use super::*;

fn scalar_module() -> trust_ir::Module {
    let mut module = trust_ir::Module::new("coverage-control");
    module.func_types.push(trust_ir::ty::FuncTy::unrecorded(vec![], vec![], false));
    let mut function = trust_ir::Function::new(
        trust_ir::FuncId::new(0), "control", trust_ir::FuncTyId::new(0), trust_ir::BlockId::new(0),
    );
    function.calling_conv = trust_ir::CallingConv::Rust;
    module.functions.push(function);
    module
}

#[test]
fn stopped_hir_walk_unwinds_before_visiting_remaining_siblings() {
    let siblings: Vec<_> = (0..4096).map(|_| rustc_hir::Expr {
        hir_id: rustc_hir::HirId::INVALID,
        kind: rustc_hir::ExprKind::Tup(&[]),
        span: DUMMY_SP,
    }).collect();
    let root = rustc_hir::Expr {
        hir_id: rustc_hir::HirId::INVALID,
        kind: rustc_hir::ExprKind::Tup(&siblings),
        span: DUMMY_SP,
    };
    let mut visited = 0;
    let mut scan = SourceAssemblyScan { checkpoint: || {
        visited += 1;
        if visited == 3 {
            Err(Miss::Stopped(trust_types::determinism::StopCause::Steps))
        } else {
            Ok(())
        }
    }};
    assert_eq!(rustc_hir::intravisit::Visitor::visit_expr(&mut scan, &root),
        ControlFlow::Break(Miss::Stopped(trust_types::determinism::StopCause::Steps)));
    assert_eq!(visited, 3, "parent walk must not poll or walk the remaining siblings");
    let mut complete = 0;
    let mut scan = SourceAssemblyScan { checkpoint: || { complete += 1; Ok(()) }};
    assert_eq!(rustc_hir::intravisit::Visitor::visit_expr(&mut scan, &root), ControlFlow::Continue(()));
    assert_eq!(complete, 8194, "paired unstopped HIR traversal retains every expression and ID");
}

#[test]
fn scalar_defaults_and_presentation_hints_pass_only_the_coverage_fence() {
    let mut module = scalar_module();
    assert_eq!(check_module(&module), Ok(()));
    module.functions[0].attrs.inlinehint = true;
    module.functions[0].attrs.cold = true;
    module.files.push("diagnostic-only.rs".into());
    assert_eq!(check_module(&module), Ok(()));
    // This intentionally invalid empty-body fixture is model DATA,
    // never a source-produced artifact or a VF5/kernel positive.
}

#[test]
fn captured_final_artifact_keeps_exact_reciprocal_identity_and_bytes() {
    let module = scalar_module();
    let id = trust_ir::FuncId::new(0);
    let display = BTreeMap::from([("source::control".into(), id)]);
    let symbols = BTreeMap::from([("control".into(), id)]);
    let captured = FinalArtifact::capture(&module, &display, &symbols).unwrap();
    let claim = captured.claim("source::control").unwrap();
    assert_eq!(claim.fid, 0);
    assert_eq!(claim.symbol, b"control");
    assert_eq!(claim.artifact, trust_ir::binary::serialize_module(&module).unwrap());
    assert!(captured.claim("source::other").is_none());
    let wrong_symbols = BTreeMap::from([("control".into(), trust_ir::FuncId::new(1))]);
    let unbound = FinalArtifact::capture(&module, &display, &wrong_symbols).unwrap();
    assert!(unbound.claim("source::control").is_none(), "display text is not identity authority");
    let mut duplicate = module.clone();
    duplicate.functions.push(module.functions[0].clone());
    assert!(FinalArtifact::capture(&duplicate, &display, &symbols).is_none());
    // Maintained binary writer + model DATA only: no source-produced
    // positive, checked mathematical token, grade or kernel claim.
}

#[test]
fn ignored_assembly_abi_and_optimizer_assumptions_refuse() {
    let mut module = scalar_module();
    module.global_asm.push("unmodelled assembly".into());
    assert_eq!(check_module(&module), Err(Miss::ModuleAssembly));
    module.global_asm.clear();
    module.func_types[0].is_vararg = true;
    assert_eq!(check_module(&module), Err(Miss::SignatureAbi));
    module.func_types[0].is_vararg = false;
    module.functions[0].attrs.readnone = true;
    assert_eq!(check_module(&module), Err(Miss::FunctionSemantics));
    module.functions[0].attrs.readnone = false;
    module.functions[0].linkage = trust_ir::Linkage::Weak;
    assert_eq!(check_module(&module), Err(Miss::FunctionSemantics));
}

#[test]
fn final_module_coverage_observes_the_existing_stop_before_scanning() {
    let module = scalar_module();
    assert_eq!(check_module(&module), Ok(()));
    let _stopped = trust_types::verify_budget::VerifyBudgetGuard::install(None, 0);
    assert_eq!(check_module(&module),
        Err(Miss::Stopped(trust_types::determinism::StopCause::Steps)));
}

#[test]
fn source_flags_are_checked_independently_of_empty_ir_fields() {
    let mut attrs = CodegenFnAttrs::new();
    assert!(source_attributes_admitted(&attrs));
    attrs.flags.insert(CodegenFnAttrFlags::COLD | CodegenFnAttrFlags::NO_MANGLE);
    assert!(source_attributes_admitted(&attrs));
    attrs.flags.insert(CodegenFnAttrFlags::TRACK_CALLER);
    assert!(!source_attributes_admitted(&attrs));
    attrs.flags.remove(CodegenFnAttrFlags::TRACK_CALLER);
    attrs.link_section = Some(sym::test);
    assert!(!source_attributes_admitted(&attrs));
}
