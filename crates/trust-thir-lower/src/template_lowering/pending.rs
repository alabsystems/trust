//! Pending level-S source data, kept separate from the frozen entry/evidence codec.
//!
//! This module constructs no entry blob, conservation verdict, admission token,
//! body adapter or proof. The metadata writer calls the shared source builder
//! only after its own ordered gates, including actual template conservation.
//! Host keys still need authenticated owner/parameter framing before transport.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::thir::{ExprId, Thir};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use trust_ir::template::Template;
use trust_ir::value::GlobalId;
use trust_ir::{BlockId, FuncId, Function, Inst, Linkage, Module};

use crate::rmeta_entry::{
    self, CalleeNameRefusal, CaptureRefusal, EntryNames, EntryRefusal, TemplateCandidate,
};

/// An inspectable source capture, never an encoded or admitted entry.
#[derive(Clone, Debug)]
pub struct PendingRecord {
    pub body_kind: crate::BodyKind,
    pub capture: Result<TemplateCandidate, CaptureRefusal>,
}

/// A source template with diagnostic validation only. There is deliberately no
/// conversion into a metadata entry, conservation verdict or codegen capability.
pub struct PendingTemplate {
    template: Template,
}

impl PendingTemplate {
    pub fn template(&self) -> &Template {
        &self.template
    }
}

/// Lower actual retained THIR through the same source stage metadata captures.
/// Reuse the frozen predicates rather than replacing their gate semantics.
pub fn lower_record<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &Thir<'tcx>,
    root: ExprId,
) -> Result<Option<PendingRecord>, EntryRefusal> {
    let Some(source) = super::lower_capture(tcx, def, thir, root) else {
        return Ok(None);
    };
    let capture = match source.lowered {
        Err(reason) => Err(reason),
        Ok((lowered, lane)) => {
            let labels = lane.refusal_labels();
            let reasons = rmeta_entry::not_lowered_reasons(&lowered);
            let unsited = lowered
                .module
                .functions
                .first()
                .map(rmeta_entry::unsited_checks)
                .unwrap_or_default();
            if !labels.is_empty() {
                Err(CaptureRefusal::Lane(labels))
            } else if !reasons.is_empty() {
                Err(CaptureRefusal::NotLowered(reasons))
            } else if !unsited.is_empty() {
                Err(CaptureRefusal::UnsitedPanic(unsited))
            } else {
                // Retain the existing stored capture's canonical binary boundary.
                match trust_ir::binary::serialize_module(&lowered.module) {
                    Err(refusal) => Err(CaptureRefusal::NotLowered(vec![format!(
                        "the per-body module has no wire image: {refusal}"
                    )])),
                    Ok(bytes) => {
                        let module = trust_ir::binary::deserialize_module(&bytes).map_err(|e| {
                            EntryRefusal::Invalid(format!(
                                "the sentinel module does not decode: {e:?}"
                            ))
                        })?;
                        Ok(TemplateCandidate {
                            module,
                            callees: lowered.callees,
                            global_origins: lowered.global_origins,
                            facts: lane.facts(),
                        })
                    }
                }
            }
        }
    };
    Ok(Some(PendingRecord { body_kind: source.body_kind, capture }))
}

/// Construct and inspect the source-only typed-hole template. No D28 verdict is
/// accepted or minted here. Metadata still uses its separate frozen builder.
pub fn assemble(
    candidate: &TemplateCandidate,
    names: &dyn EntryNames,
    identity: String,
) -> Result<PendingTemplate, EntryRefusal> {
    source_template(candidate, names, identity).map(|template| PendingTemplate { template })
}

/// Shared source construction for pending inspection and the gated S writer.
/// This accepts no conservation verdict and returns only unlicensed IR data.
pub(crate) fn source_template(
    candidate: &TemplateCandidate,
    names: &dyn EntryNames,
    identity: String,
) -> Result<Template, EntryRefusal> {
    let (template, static_declarations) = assemble_source_template(candidate, names, identity)?;
    let violations = trust_ir_build::template::validate_template(&template);
    if !violations.is_empty() {
        return Err(super::template_refusal(&template, &violations));
    }
    let skolem = trust_ir_build::template::skolem_instance(&template)
        .map_err(|e| EntryRefusal::Invalid(format!("the template has no skolem instance: {e}")))?;
    rmeta_entry::entry_is_self_contained(&skolem, candidate.callees.len(), &static_declarations)
        .map_err(|why| EntryRefusal::Invalid(format!("the skolem instance: {why}")))?;
    extraction_on(candidate, &template, &skolem)?;
    Ok(template)
}

/// A diagnostic equality of the complete effect census/shape after skolem
/// substitution. This is not source refinement or authoritative conservation.
pub fn check_extraction(
    candidate: &TemplateCandidate,
    pending: &PendingTemplate,
) -> Result<(), EntryRefusal> {
    let skolem = trust_ir_build::template::skolem_instance(&pending.template)
        .map_err(|e| EntryRefusal::ExtractionNotConserved(format!("pending template: {e}")))?;
    extraction_on(candidate, &pending.template, &skolem)
}

// Read-only call-site census used only to request the unchanged declaration
// signature predicate. It cannot admit a body or supply a link symbol.
fn body_calls(module: &Module, callee: FuncId) -> bool {
    module.function_by_id(FuncId::new(0)).is_some_and(|body| {
        body.blocks.iter().flat_map(|b| b.body.iter()).any(|node| {
            matches!(&node.inst, Inst::Call { callee: c, .. } | Inst::Invoke { callee: c, .. } if *c == callee)
        })
    })
}

fn assemble_source_template(
    c: &TemplateCandidate,
    names: &dyn EntryNames,
    identity: String,
) -> Result<(trust_ir::template::Template, BTreeSet<GlobalId>), EntryRefusal> {
    if !names.body_abi().is_plain_rust() {
        return Err(EntryRefusal::Invalid("template source calling convention requires an adapter".into()));
    }
    let mut module = c.module.clone();
    if module.functions.len() != 1 || module.functions[0].id != FuncId::new(0) {
        return Err(EntryRefusal::Invalid(format!(
            "the sentinel module holds {} function(s); exactly the body at FuncId(0) was expected",
            module.functions.len()
        )));
    }
    for (index, file) in module.files.iter_mut().enumerate() {
        *file = names.file_name(file).map_err(|why| {
            EntryRefusal::Invalid(format!("source file {index} has no metadata spelling: {why}"))
        })?;
    }
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for (position, callee) in c.callees.iter().enumerate() {
        let k = position + 1;
        if callee.func_id != FuncId::new(k as u32) {
            return Err(EntryRefusal::Invalid(format!(
                "the callee ledger is not dense: position {k} holds FuncId({})",
                callee.func_id.index()
            )));
        }
        let hole = c.facts.callee_holes.iter().find(|h| h.decl == callee.func_id);
        // A hole's neutral level-S row is not an ABI adapter. The current callable
        // instantiator supports only actual plain-Rust headers; source rust-call (or any
        // other protocol) must not disappear behind the reserved hole name/default C.
        if hole.is_some() && !callee.abi.is_plain_rust() {
            return Err(EntryRefusal::Invalid("callee hole source calling convention requires an adapter".into()));
        }
        let (name, func_ty) = if let Some(hole) = hole {
            (
                trust_ir::template::hole_row_name(hole.id),
                hole.signature.clone(),
            )
        } else {
            let name = names.callee_symbol(k, callee).map_err(|why| match why {
                CalleeNameRefusal::Unnamed(why) => {
                    EntryRefusal::UnnamedCallee(format!("FuncId({k}) `{}`: {why}", callee.def_path))
                }
                CalleeNameRefusal::CallerLocation => EntryRefusal::CallerLocation(format!(
                    "callee FuncId({k}) `{}` is #[track_caller]: its symbol takes a hidden \
                     &'static Location argument the trust-ir call does not pass",
                    callee.def_path
                )),
            })?;
            if name.starts_with('!') || !declared.insert(name.clone()) {
                return Err(EntryRefusal::UnnamedCallee(format!(
                    "FuncId({k}) `{}`: `{name}` is reserved or already declared",
                    callee.def_path
                )));
            }
            let func_ty = crate::instance_admission::declaration_func_ty(
                &callee.params,
                callee.ret_ty.clone(),
                callee.ret_ty_conflict,
                body_calls(&module, callee.func_id),
            )
            .map_err(|why| {
                EntryRefusal::UnnamedCallee(format!(
                    "FuncId({k}) `{}`: its declaration cannot be signed: {why}",
                    callee.def_path
                ))
            })?;
            (name, func_ty)
        };
        if hole.is_some() && !declared.insert(name.clone()) {
            return Err(EntryRefusal::Invalid(format!("duplicate callee hole row `{name}`")));
        }
        // Trust (trust-ir D1b): a refused table door refuses the template, never panics
        // (`assemble_entry`'s rule).
        let ty = module.intern_func_type(func_ty).map_err(|refusal| {
            EntryRefusal::Invalid(format!("FuncId({k}) `{}`: {refusal}", callee.def_path))
        })?;
        let mut declaration = Function::new(callee.func_id, name, ty, BlockId::new(0))
            .with_producer(trust_ir::Producer::TRust);
        if hole.is_none() {
            declaration.linkage = Linkage::External;
            declaration.calling_conv = callee.abi.calling_conv()
                .map_err(|why| EntryRefusal::Invalid(why.to_string()))?;
        }
        module
            .try_add_function(declaration)
            .map_err(|refusal| EntryRefusal::Invalid(refusal.to_string()))?;
    }
    let static_declarations = rmeta_entry::rewrite_globals(&mut module, &c.global_origins, names)?;
    module.target_info = Some(names.target_info());
    let template = crate::template_lowering::abstract_template(&module, &c.facts, identity)?;
    Ok((template, static_declarations))
}

fn extraction_on(
    c: &TemplateCandidate,
    t: &trust_ir::template::Template,
    skolem: &Module,
) -> Result<(), EntryRefusal> {
    use crate::effect_conservation::{census_ledger, ir_census, ir_shape};
    let refused = |why: String| EntryRefusal::ExtractionNotConserved(format!("template: {why}"));
    let judged_body = c
        .module
        .functions
        .first()
        .ok_or_else(|| refused("the judged module has no body".into()))?;
    let (ledger, callee_returns) = census_ledger(&c.callees);
    let degraded: BTreeSet<trust_ir::StructId> =
        c.facts.degraded_structs.iter().map(|i| trust_ir::StructId::new(*i)).collect();
    let judged =
        ir_census(&c.module, judged_body, &ledger, &callee_returns, &degraded, c.facts.lanes);
    let skolem_body = skolem
        .functions
        .first()
        .ok_or_else(|| refused("the skolem instance has no body".into()))?;
    // Ground callee rows by symbol: template FuncId -> skolem FuncId.
    let mut by_symbol: BTreeMap<&str, FuncId> = BTreeMap::new();
    for f in skolem.functions.iter().skip(1) {
        by_symbol.insert(f.name.as_str(), f.id);
    }
    let mut remap: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    for f in t.module.functions.iter().skip(1) {
        let hole = t.header.holes.iter().enumerate().find(|(_, hole)| {
            matches!(hole.kind, trust_ir::template::HoleKind::Callee { decl } if decl == f.id)
        });
        let skolem_name = hole.map(|(h, _)| format!("__skolem_hole_{h}"));
        let name = skolem_name.as_deref().unwrap_or(f.name.as_str());
        let Some(id) = by_symbol.get(name) else {
            return Err(refused(format!(
                "callee row `{}` is not declared in the skolem instance",
                f.name
            )));
        };
        remap.insert(f.id, *id);
    }
    let remapped = |id: &FuncId| remap.get(id).copied().unwrap_or(*id);
    let skolem_ledger =
        ledger.iter().map(|(id, row)| (remapped(id), row.clone())).collect::<BTreeMap<_, _>>();
    let skolem_returns = callee_returns
        .iter()
        .map(|(id, ty)| (remapped(id), ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let instance =
        ir_census(&skolem, skolem_body, &skolem_ledger, &skolem_returns, &degraded, c.facts.lanes);
    if instance != judged {
        return Err(refused(format!(
            "the skolem instance's effect census differs from the judged census (shapes {:?} \
             and {:?})",
            instance.shape, judged.shape
        )));
    }
    let (judged_shape, instance_shape) =
        (ir_shape(&c.module, judged_body), ir_shape(&skolem, skolem_body));
    if judged_shape != instance_shape {
        return Err(refused(format!(
            "the skolem instance's effect shape {instance_shape:?} differs from the judged \
             body's {judged_shape:?}"
        )));
    }
    Ok(())
}
