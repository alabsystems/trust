//! Admission for semantic inputs projected out of the pinned VF5 model.
//!
//! An artifact digest binds bytes; it does not give ignored assembly, ABI,
//! optimizer assumptions or linker actions mathematical semantics. This
//! fence grants no proof authority. A miss preserves ordinary policy and
//! every original row/debt, including existing link-level diagnostics.

use super::*;
use std::ops::ControlFlow;
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Miss {
    Stopped(trust_types::determinism::StopCause),
    SourceAssembly,
    SourceAbi,
    SourceAttributes,
    ModuleAssembly,
    SignatureAbi,
    FunctionSemantics,
    GlobalSemantics,
}

/// Session-owned source observation. There is no serialized constructor or
/// favorable label that can substitute for the actual current HIR census.
pub(super) struct SourceCoverage(());

/// One final published artifact and its reciprocal compiler-owned identity
/// index. It is built once at the crate's finalization barrier, never from a
/// saved report, and cannot cache or replace any row's kernel replay.
pub(super) struct FinalArtifact {
    bytes: Vec<u8>,
    bindings: BTreeMap<String, (u64, Vec<u8>)>,
}

impl FinalArtifact {
    pub(super) fn claim(&self, def_path: &str) -> Option<trust_certify::calculus_row::CalculusRowClaim> {
        let (fid, symbol) = self.bindings.get(def_path)?;
        Some(trust_certify::calculus_row::CalculusRowClaim {
            artifact: self.bytes.clone(), fid: *fid, symbol: symbol.clone(),
        })
    }
    fn capture(
        module: &trust_ir::Module,
        display_paths: &BTreeMap<String, trust_ir::FuncId>,
        symbols: &BTreeMap<String, trust_ir::FuncId>,
    ) -> Option<Self> {
        check_module(module)
            .map_err(|error| debug!("VF5 final module outside pinned model; ordinary policy remains: {error:?}"))
            .ok()?;
        let mut by_id = BTreeMap::new();
        for function in &module.functions {
            checkpoint().ok()?;
            if by_id.insert(function.id, function.name.as_str()).is_some() {
                return None;
            }
        }
        let mut bindings = BTreeMap::new();
        for (path, id) in display_paths {
            checkpoint().ok()?;
            let Some(name) = by_id.get(id) else { continue };
            if !name.is_empty() && symbols.get(*name) == Some(id) {
                bindings.insert(path.clone(), (u64::from(id.index()), name.as_bytes().to_vec()));
            }
        }
        checkpoint().ok()?;
        // Same maintained binary image as the actual module publisher.
        // Admission is rechecked after this existing serialization call;
        // no expired capture can become a successful row selector.
        let bytes = trust_ir::binary::serialize_module(module).ok()?;
        checkpoint().ok()?;
        Some(FinalArtifact { bytes, bindings })
    }
}

impl SourceCoverage {
    pub(super) fn capture(tcx: TyCtxt<'_>) -> Result<Self, Miss> {
        checkpoint()?;
        for local in tcx.hir_crate_items(()).definitions() {
            checkpoint()?;
            match tcx.def_kind(local) {
                DefKind::GlobalAsm if !tcx.trust_def_is_clean_island(local.to_def_id()) => {
                    return Err(Miss::SourceAssembly);
                }
                DefKind::Fn | DefKind::AssocFn => {
                    let sig = tcx.fn_sig(local).instantiate_identity().skip_binder();
                    if sig.abi() != rustc_abi::ExternAbi::Rust || sig.c_variadic() {
                        return Err(Miss::SourceAbi);
                    }
                    checkpoint()?;
                    if !source_attributes_admitted(tcx.codegen_fn_attrs(local)) {
                        return Err(Miss::SourceAttributes);
                    }
                }
                DefKind::Static { .. } => {
                    if !source_attributes_admitted(tcx.codegen_fn_attrs(local)) {
                        return Err(Miss::SourceAttributes);
                    }
                }
                _ => {}
            }
        }
        // Read HIR, independently of both the native lowering outcome and
        // fields the producer may omit. No MIR query or production feature
        // is introduced. Each separately owned closure body is visited too.
        for local in tcx.hir_body_owners() {
            checkpoint()?;
            if tcx.trust_def_is_clean_island(local.to_def_id()) {
                continue;
            }
            // definitions() excludes nested closure/coroutine owners.
            // Their codegen attributes are just as semantic, but fn_sig is
            // deliberately NOT a valid query for those closure-like defs.
            if tcx.def_kind(local).has_codegen_attrs()
                && !source_attributes_admitted(tcx.codegen_fn_attrs(local))
            {
                return Err(Miss::SourceAttributes);
            }
            checkpoint()?;
            if let Some(body) = tcx.hir_maybe_body_owned_by(local) {
                let mut scan = SourceAssemblyScan { checkpoint };
                if let ControlFlow::Break(miss) =
                    rustc_hir::intravisit::Visitor::visit_body(&mut scan, body)
                {
                    return Err(miss);
                }
            }
        }
        checkpoint()?;
        Ok(Self(()))
    }

    pub(super) fn capture_final(&self, tcx: TyCtxt<'_>) -> Option<FinalArtifact> {
        trust_thir_lower::crate_module::with_published_crate_module(tcx.sess, |published| {
            let published = published.ok()?;
            let module = published.module();
            FinalArtifact::capture(module, published.display_paths(), published.symbols())
        })
    }
}

/// ControlFlow propagates a stopped scan through every parent walk_list;
/// skipping just the current node would still traverse all later siblings.
struct SourceAssemblyScan<F> {
    checkpoint: F,
}

impl<F: FnMut() -> Result<(), Miss>> SourceAssemblyScan<F> {
    fn poll(&mut self) -> ControlFlow<Miss> {
        match (self.checkpoint)() {
            Ok(()) => ControlFlow::Continue(()),
            Err(miss) => ControlFlow::Break(miss),
        }
    }
}

impl<'tcx, F: FnMut() -> Result<(), Miss>> rustc_hir::intravisit::Visitor<'tcx>
    for SourceAssemblyScan<F>
{
    type Result = ControlFlow<Miss>;

    fn visit_id(&mut self, _id: rustc_hir::HirId) -> Self::Result {
        self.poll()
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
        self.poll()?;
        if matches!(expr.kind, rustc_hir::ExprKind::InlineAsm(_)) {
            return ControlFlow::Break(Miss::SourceAssembly);
        }
        rustc_hir::intravisit::walk_expr(self, expr)
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) -> Self::Result {
        self.poll()?;
        rustc_hir::intravisit::walk_pat(self, pat)
    }

    fn visit_ty(&mut self, ty: &'tcx rustc_hir::Ty<'tcx, rustc_hir::AmbigArg>) -> Self::Result {
        self.poll()?;
        rustc_hir::intravisit::walk_ty(self, ty)
    }

    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) -> Self::Result {
        self.poll()?;
        rustc_hir::intravisit::walk_stmt(self, stmt)
    }
}

fn checkpoint() -> Result<(), Miss> {
    match trust_certify::calculus_row::base::preparation_stop() {
        Some(stop) => Err(Miss::Stopped(stop)),
        None => Ok(()),
    }
}

fn source_attributes_admitted(attrs: &CodegenFnAttrs) -> bool {
    // Cold/inline/optimization hints do not strengthen program behavior.
    // NO_MANGLE and symbol_name remain subject to the actual final module's
    // reciprocal unique source/symbol binding. Unknown future flags refuse.
    let hints = CodegenFnAttrFlags::COLD | CodegenFnAttrFlags::NO_MANGLE;
    attrs.flags.difference(hints).is_empty()
        && attrs.foreign_item_symbol_aliases.is_empty()
        && attrs.link_ordinal.is_none()
        && attrs.target_features.is_empty()
        && !attrs.safe_target_features
        && attrs.linkage.is_none()
        && attrs.import_linkage.is_none()
        && attrs.link_section.is_none()
        && attrs.instruction_set.is_none()
        && attrs.alignment.is_none()
        && attrs.patchable_function_entry.is_none()
        && attrs.objc_class.is_none()
        && attrs.objc_selector.is_none()
        && attrs.instrument_fn.is_none()
        && attrs.sanitizers.disabled.is_empty()
        && attrs.sanitizers.rtsan_setting == Default::default()
}

fn strong(linkage: trust_ir::Linkage) -> bool {
    matches!(linkage, trust_ir::Linkage::External | trust_ir::Linkage::Internal | trust_ir::Linkage::Private)
}

fn check_module(module: &trust_ir::Module) -> Result<(), Miss> {
    checkpoint()?;
    if !module.global_asm.is_empty() {
        return Err(Miss::ModuleAssembly);
    }
    for ty in &module.func_types {
        checkpoint()?;
        if ty.is_vararg || ty.abi.is_some() {
            return Err(Miss::SignatureAbi);
        }
    }
    for function in &module.functions {
        checkpoint()?;
        let attrs = &function.attrs;
        if function.calling_conv != trust_ir::CallingConv::Rust
            || !strong(function.linkage)
            || function.section.is_some()
            || function.visibility != trust_ir::Visibility::Default
            || function.retained
            || attrs.readonly || attrs.readnone || attrs.naked
            || !attrs.target_features.is_empty()
            || !attrs.ret.is_empty()
        {
            return Err(Miss::FunctionSemantics);
        }
        for param in &attrs.params {
            checkpoint()?;
            if !param.is_empty() {
                return Err(Miss::FunctionSemantics);
            }
        }
    }
    for global in &module.globals {
        checkpoint()?;
        if !strong(global.linkage) || global.tls.is_some() || global.align.is_some()
            || global.section.is_some() || global.retained
            || global.visibility != trust_ir::Visibility::Default
        {
            return Err(Miss::GlobalSemantics);
        }
    }
    // No debug/source name, unsited scalar assert, benign proof marker or
    // public obligation label is treated as either authority or a new ban.
    // Unsupported instructions (including GEP) still need the genuine fixed
    // VF5 check; admitting these ignored fields alone proves nothing.
    checkpoint()
}

#[cfg(test)]
mod tests {
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
}
