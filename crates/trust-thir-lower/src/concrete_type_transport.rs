//! Concrete type/table images from the source producer's own converter.
//!
//! This is data construction for the level-S host. It lowers no source body,
//! rederives no effect census and creates no admission or proof token. In
//! particular, a faithful type image says nothing about destructor availability.

use rustc_hir::def::DefKind;
use rustc_middle::thir::{BodyTy, Thir};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_ir::{Module, Ty};

/// A closed type-table image. Every returned root is indexed in this image;
/// transporting it to another module still requires the canonical table remap.
/// No mutable accessor can detach roots from the rows against which they were
/// checked. The image contains neither functions nor proof obligations.
#[derive(PartialEq)]
pub struct ConcreteTypes<'tcx> {
    module: Module,
    roots: Vec<Ty>,
    sources: Vec<ty::Ty<'tcx>>,
}

impl<'tcx> ConcreteTypes<'tcx> {
    pub fn module(&self) -> &Module {
        &self.module
    }
    pub fn roots(&self) -> &[Ty] {
        &self.roots
    }
    pub fn sources(&self) -> &[ty::Ty<'tcx>] {
        &self.sources
    }

    /// Determine metadata from the retained substituted Rust source, independently
    /// of the converter's historical unknown-to-Ptr fallback. This is a shape
    /// observation only; no source refinement, provenance or memory right follows.
    pub fn root_is_thin_pointer(&self, tcx: TyCtxt<'tcx>, index: usize) -> bool {
        let Some(source) = self.sources.get(index) else {
            return false;
        };
        let pointee = match source.kind() {
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => *pointee,
            _ => return false,
        };
        self.roots.get(index) == Some(&Ty::Ptr)
            && crate::source_pointee_meta_and_tail(tcx, pointee).0 == crate::PointeeMeta::Thin
    }
}

fn checked_instance<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<(), String> {
    crate::instance_admission::refuse_inside_producer_lowering()
        .map_err(|_| "concrete type transport is unavailable during source lowering")?;
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || !matches!(tcx.def_kind(instance.def_id()), DefKind::Fn | DefKind::AssocFn)
        || instance.args.len() != tcx.generics_of(instance.def_id()).count()
        || instance.args.has_non_region_param()
        || instance.args.has_non_region_infer()
        || instance.args.has_escaping_bound_vars()
    {
        return Err("concrete type transport requires a concrete actual Rust Item".into());
    }
    crate::template_key::rustc::checked_call_key(
        tcx,
        instance.def_id(),
        instance.args,
        instance.def_id(),
    )
    .map_err(|e| e.to_string())?;
    Ok(())
}

/// Resolve a schema-1 Type key through the same independently checked Rust
/// definition/positional map and return its concrete producer table image.
/// This is an unlicensed image: the data-only template host places it through
/// the canonical table merger and declared contract checks. Runtime level-S
/// admission, source refinement and proof authority remain closed.
pub fn from_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    key: &trust_ir::template::HostKey,
) -> Result<ConcreteTypes<'tcx>, String> {
    checked_instance(tcx, instance)?;
    let key = crate::template_key::decode(key).map_err(|e| e.to_string())?;
    let crate::template_key::HoleKey::Type(key) = key else {
        return Err("concrete type transport received a different hole-key kind".into());
    };
    let source = crate::template_key::rustc::ty_of_key(tcx, &key, instance.def_id())
        .map_err(|e| e.to_string())?;
    lower(tcx, instance, &[source])
}

/// Lower original-owner type terms under one actual concrete Item instance.
///
/// This calls `LowerCx::map_ty`, including its real nominal registration,
/// source-order fields, array interning and Rustc tuple/layout queries. There is
/// no second type converter. Its historical opaque/placeholder lanes cannot
/// escape: the producer's complete-layout walk must check every by-value
/// component, in addition to its normal refusal and confinement ledgers.
pub fn lower<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    source_types: &[ty::Ty<'tcx>],
) -> Result<ConcreteTypes<'tcx>, String> {
    checked_instance(tcx, instance)?;
    if source_types.len() > 65536 {
        return Err("concrete type transport root budget".into());
    }
    // The legacy converter shares storage with the body lowering context. Only
    // its type methods run here: the empty THIR container carries the actual
    // source signature and is never presented as a lowered program or census.
    let signature = tcx.fn_sig(instance.def_id()).instantiate(tcx, instance.args);
    let signature =
        crate::producer_try_normalize(tcx, ty::TypingEnv::fully_monomorphized(), signature)
            .map_err(|_| "concrete type transport signature normalization")?
            .skip_normalization();
    if signature.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
        return Err("concrete type transport nonregion signature binder".into());
    }
    let signature = tcx.instantiate_bound_regions_with_erased(signature);
    let storage = Thir::new(BodyTy::Fn(signature));
    let mut cx =
        crate::LowerCx::new(tcx, &storage, instance.def_id(), false, Some(instance.args), None);
    let mut roots = Vec::with_capacity(source_types.len());
    let mut sources = Vec::with_capacity(source_types.len());
    for &source in source_types {
        // Check owner-relative parameter positions and full nominal identities
        // before substitution. This also bounds expanded Rustc type DAGs before
        // the converter allocates their corresponding table image.
        crate::template_key::rustc::checked_type_key(tcx, source, instance.def_id())
            .map_err(|e| e.to_string())?;
        let source = cx.monomorphize(source);
        if source.has_non_region_param()
            || source.has_non_region_infer()
            || source.has_escaping_bound_vars()
        {
            return Err("concrete type transport leaves a symbolic source type".into());
        }
        roots.push(cx.map_ty(source));
        sources.push(source);
    }
    if !cx.unsupported.is_empty()
        || cx.mono_residual
        || cx.param_opaque
        || cx.opaque_collapse
        || cx.union_value_lane
        || !cx.union_lanes.is_empty()
        || !cx.enum_param_lanes.is_empty()
        || !cx.rmw_degraded_structs.is_empty()
        || !cx.layout_withheld_structs.is_empty()
    {
        return Err("concrete type transport producer refused or confined a type".into());
    }
    // Types may refer to callable signatures and physical closure frames;
    // neither requires a callable body, adapter, global or destructor here.
    if !cx.pending_globals.is_empty() || !cx.pending_adapters.is_empty() {
        return Err("concrete type transport requires executable/global transport".into());
    }
    let mut module = Module::new("concrete_source_types");
    module.target_info = Some(crate::crate_module::source_target_info(tcx));
    module.types = cx.pending_tys.clone();
    module.structs = cx.pending_structs.clone();
    module.enums = cx.pending_enums.clone();
    module.tuple_layouts = cx.pending_tuple_layouts.clone();
    if !cx.pending_func_tys.is_empty() {
        // The original converter numbers pended signatures from one. Fill its
        // reserved zero with this ordinary root carrier, exactly as canonical
        // placement already does. It describes types and has no function body
        // or source/native ABI claim. Do not renumber the converter's tables.
        module.func_types.push(trust_ir::FuncTy {
            params: roots.clone(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        });
        module.func_types.extend(cx.pending_func_tys.iter().cloned());
    }
    module.closure_types = cx.pending_closure_tys.clone();
    module.closure_layouts = cx.pending_closure_layouts.clone();
    let errors = trust_ir_build::validate::validate_module(&module);
    if !errors.is_empty() {
        return Err(format!("concrete type transport invalid producer tables: {errors:?}"));
    }
    // Reuse the same physical/component check as complete source replacement;
    // matching total size alone would miss erased fat-reference siblings.
    let layouts = module.layout_table();
    let mut checked = std::collections::HashSet::new();
    for (&source, root) in sources.iter().zip(&roots) {
        if !cx.replacement_layout_component(&layouts, source, root, &mut Vec::new(), &mut checked) {
            return Err("concrete type transport lacks a complete source layout".into());
        }
    }
    Ok(ConcreteTypes { module, roots, sources })
}
