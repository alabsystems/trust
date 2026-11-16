//! Trust: the first Rust inventory fragment read from the exact conserved IR
//! handoff. The source guard excludes required constants, address materialization
//! and implicit runtime services that the explicit IR dependency census omits.
//! Existing monomorphization checks still run; their current MIR dependence is
//! not retired by this inventory increment. No body or proof is licensed here.

use std::sync::Arc;

use rustc_hir::def::DefKind;
use rustc_middle::thir::{ExprKind, PatKind};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
// The exact pure reader is also exercised as an ordinary Trust Rust component;
// this does not substitute for the normal source compiler check of this caller.
mod ir;
#[derive(Default)]
struct CachedInventory {
    // Retaining the immutable Arc prevents allocation reuse while cached.
    module: Option<Arc<trust_ir::Module>>,
    inventory: ir::ModuleInventory,
}

pub(super) fn neighbours<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    local: LocalDefId,
) -> Option<&'tcx [DefId]> {
    if !plain_local_function(tcx, local.to_def_id()) {
        return None;
    }
    // Every lookup first requires the exact source identity and existing D28
    // conservation judgement. No cached pure inventory result licenses a body.
    let exact = tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.exact_body(tcx, local),
        )
        .ok()?;
    if !source_fragment(tcx, local) {
        return None;
    }
    let admitted = tcx.sess.with_trust_compiler_state::<CachedInventory, _>(|cache| {
        if !cache.module.as_ref().is_some_and(|module| Arc::ptr_eq(module, &exact.module)) {
            cache.inventory = ir::ModuleInventory::new(&exact.module);
            cache.module = Some(Arc::clone(&exact.module));
        }
        cache.inventory.call_free(exact.func_id)
    });
    if !admitted {
        return None;
    }
    // Preserve the checks previously performed by items_of_instance. They
    // remain MIR-based today; an IR inventory answer must not bypass them.
    tcx.ensure_ok().check_mono_item(instance);
    tracing::info!(?local, "F1 inventory read from exact conserved Rust IR");
    Some(&[])
}

fn plain_local_function(tcx: TyCtxt<'_>, def: DefId) -> bool {
    def.is_local()
        && matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx.generics_of(def).count() == 0
        && tcx.intrinsic(def).is_none()
        && !rustc_attr_ir::find_attr!(tcx, def, CustomMir(..))
        && tcx.fn_sig(def).skip_binder().skip_binder().abi() == rustc_abi::ExternAbi::Rust
}

fn source_scalar(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Char | ty::Never) || ty.is_unit()
}

/// This examines every stored THIR expression, including unused expressions.
/// Named/inline constants, function values, locals with patterns, assembly,
/// drops, allocations, unchecked arithmetic and hidden runtime helpers are
/// outside the fragment. Unknown source shapes retain the existing walk.
// F1 retains THIR rather than stealing it. This defensive availability check
// only withholds the inventory optimization if that invariant was violated;
// it supplies no positive evidence or persisted source/body authority.
#[allow(rustc::untracked_query_information)]
fn source_fragment(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    if tcx.hir_maybe_body_owned_by(def).is_none() {
        return false;
    }
    let Ok((body, _)) = tcx.thir_body(def) else { return false };
    if body.is_stolen() {
        return false;
    }
    let body = body.borrow();
    if !body.stmts.is_empty()
        || body.params.iter().any(|p| {
            !source_scalar(p.ty)
                || p.pat.as_ref().is_some_and(|p| {
                    !matches!(p.kind, PatKind::Wild | PatKind::Binding { subpattern: None, .. })
                })
        })
    {
        return false;
    }
    body.exprs.iter().all(|expr| {
        if !source_scalar(expr.ty) {
            return false;
        }
        match &expr.kind {
            ExprKind::Scope { .. }
            | ExprKind::If { .. }
            | ExprKind::LogicalOp { .. }
            | ExprKind::Block { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::Cast { .. }
            | ExprKind::ValueExpr { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::Return { .. } => true,
            ExprKind::ZstLiteral { .. } => expr.ty.is_unit(),
            ExprKind::Binary { op, .. } => matches!(
                op,
                rustc_middle::mir::BinOp::BitAnd
                    | rustc_middle::mir::BinOp::BitOr
                    | rustc_middle::mir::BinOp::BitXor
                    | rustc_middle::mir::BinOp::Eq
                    | rustc_middle::mir::BinOp::Ne
                    | rustc_middle::mir::BinOp::Lt
                    | rustc_middle::mir::BinOp::Le
                    | rustc_middle::mir::BinOp::Gt
                    | rustc_middle::mir::BinOp::Ge
            ),
            ExprKind::Unary { op: rustc_middle::mir::UnOp::Not, .. } => true,
            _ => false,
        }
    })
}
