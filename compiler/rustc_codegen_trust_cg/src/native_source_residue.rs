//! Recover source instances reached through the authoritative Trust-IR module.
//!
//! Rust's optimized mono inventory can omit a source closure that remains a
//! real dependency of the source module. Recover its actual typechecked HIR
//! arguments; never fabricate the closure's three synthetic arguments or ask
//! MIR to re-lower the body. Recovery supplies identity only. The caller must
//! still run exact source selection, ABI agreement and the usual output gate.

use rustc_hir::def::DefKind;
use rustc_hir::{ExprKind, Node};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefIndex, LocalDefId};
use trust_ir::{FuncId, Module, Producer};

pub(crate) fn recover_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    module: &Module,
    func: FuncId,
    def_index: u32,
) -> Result<ty::Instance<'tcx>, String> {
    let function = module.function_by_id(func).ok_or("source residue function is missing")?;
    if function.is_declaration() || function.producer != Some(Producer::TRust) {
        return Err("source residue is not a defined Rust source body".into());
    }
    let local = LocalDefId { local_def_index: DefIndex::from_u32(def_index) };
    let selected =
        tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| {
                if handoff.indexed_def_index(func) != Some(def_index)
                    || !handoff.codegen_body_ids().contains(&(def_index, func))
                {
                    return Err("source residue has no exact session FuncId-to-DefIndex mapping"
                        .to_string());
                }
                handoff
                    .exact_body(tcx, local)
                    .map_err(|e| format!("source residue handoff refused: {e:?}"))
            },
        )?;
    if selected.func_id != func || selected.module.as_ref() != module {
        return Err("source residue differs from its exact conservation-filtered handoff".into());
    }
    let def = local.to_def_id();
    let instance = match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn => {
            if tcx.generics_of(def).requires_monomorphization(tcx) {
                return Err("generic source residue has no identity-keyed concrete instance".into());
            }
            ty::Instance::mono(tcx, def)
        }
        DefKind::Closure => {
            if tcx.is_coroutine(def) {
                return Err("coroutine source residue is not a concrete FnOnce closure".into());
            }
            let Node::Expr(expression) = tcx.hir_node_by_def_id(local) else {
                return Err("source closure definition has no HIR expression".into());
            };
            let ExprKind::Closure(closure) = expression.kind else {
                return Err("source closure definition is not a HIR closure expression".into());
            };
            if closure.def_id != local || closure.kind != rustc_hir::ClosureKind::Closure {
                return Err("source closure HIR identity/kind differs from the definition".into());
            }
            let root = tcx.typeck_root_def_id_local(local);
            if !tcx.has_typeck_results(root) {
                return Err("source closure has no typechecking root body".into());
            }
            let typeck = tcx.typeck(root);
            if typeck.tainted_by_errors.is_some() {
                return Err("source closure typechecking contains errors".into());
            }
            let actual = typeck
                .node_type_opt(expression.hir_id)
                .ok_or("source closure has no actual typechecked HIR node type")?;
            let ty::Closure(actual_def, actual_args) = actual.kind() else {
                return Err("source HIR node type is not a concrete closure".into());
            };
            if *actual_def != def {
                return Err("typechecked source closure names another definition".into());
            }
            let args = tcx.erase_and_anonymize_regions(*actual_args);
            if args.has_infer() || args.has_non_region_param() || args.has_escaping_bound_vars() {
                return Err("source closure arguments are not fully concrete and closed".into());
            }
            let closure = args.as_closure();
            // Only PARENT arguments decide whether source identity is enough.
            // The closure's kind/signature/upvar synthetic arguments are real
            // typechecked values and are not generic parent instantiations.
            if !closure.parent_args().iter().all(|arg| arg.as_region().is_some()) {
                return Err("source closure has a type/const-instantiated generic parent".into());
            }
            if closure.kind() != ty::ClosureKind::FnOnce || closure.upvar_tys().is_empty() {
                return Err("source residue requires a capturing FnOnce environment".into());
            }
            ty::Instance::new_raw(def, args)
        }
        other => {
            return Err(format!("source residue definition kind {other:?} has no recovery lane"));
        }
    };
    if tcx.symbol_name(instance).name != function.name {
        return Err("recovered source instance symbol differs from the exact producer body".into());
    }
    Ok(instance)
}
