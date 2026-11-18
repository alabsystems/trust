//! Trust: the first Rust inventory fragment read from the exact conserved IR
//! handoff. Scalar local cells and the existing exact-source thin-pointer
//! comparison model have no implicit runtime services. Required constants,
//! function addresses, destructors and unknown calls retain the ordinary walk.
//! Existing monomorphization checks still run; their current MIR dependence is
//! not retired by this inventory increment. No body or proof is licensed here.

use std::sync::Arc;

use rustc_hir::def::DefKind;
use rustc_middle::thir::{ExprKind, PatKind, StmtKind};
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

fn scalar_or_pointer(ty: Ty<'_>) -> bool {
    source_scalar(ty)
        || matches!(ty.kind(), ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _)
            if source_scalar(*pointee) && !pointee.is_unit() && !pointee.is_never())
}

fn comparison_input<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::FnDef(definition, arguments) = *ty.kind() else { return None };
    trust_thir_lower::core_thin_ptr_eq_input_v1(tcx, definition, arguments.skip_binder())
}

/// This examines every stored THIR expression, including unused expressions.
/// Only plain scalar/pointer bindings and the already authenticated comparison
/// model join the expression fragment. The original IR independently excludes
/// checks and runtime operations, including checked arithmetic's panic path.
/// Raw dereferences retain the ordinary walk: MIR's later pointer-check passes
/// may introduce panic dependencies after D28's mir_built conservation check.
/// Reference dereferences include the compiler's implicit `&T` to `*const T`
/// reborrow. The pointer-check visitor only instruments raw-pointer places.
/// Unknown source shapes retain the existing walk.
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
    if body.stmts.iter().any(|statement| match &statement.kind {
        StmtKind::Expr { .. } => false,
        StmtKind::Let { pattern, else_block, .. } => {
            else_block.is_some()
                || !scalar_or_pointer(pattern.ty)
                || !matches!(
                    pattern.kind,
                    PatKind::Wild | PatKind::Binding { subpattern: None, .. }
                )
        }
    }) || body.params.iter().any(|p| {
        !scalar_or_pointer(p.ty)
            || p.pat.as_ref().is_some_and(|p| {
                !matches!(p.kind, PatKind::Wild | PatKind::Binding { subpattern: None, .. })
            })
    }) {
        return false;
    }
    body.exprs.iter().all(|expr| {
        if !scalar_or_pointer(expr.ty) && comparison_input(tcx, expr.ty).is_none() {
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
            | ExprKind::Borrow { .. }
            | ExprKind::RawBorrow { .. }
            | ExprKind::Assign { .. }
            | ExprKind::ValueExpr { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::Return { .. } => true,
            ExprKind::ZstLiteral { .. } => {
                expr.ty.is_unit() || comparison_input(tcx, expr.ty).is_some()
            }
            ExprKind::Deref { arg } => matches!(body.exprs[*arg].ty.kind(), ty::Ref(..)),
            ExprKind::Call { fun, args, .. } => comparison_input(tcx, body.exprs[*fun].ty)
                .is_some_and(|input| {
                    expr.ty == tcx.types.bool
                        && args.len() == 2
                        && args.iter().all(|id| body.exprs[*id].ty == input)
                }),
            ExprKind::PointerCoercion {
                cast: ty::adjustment::PointerCoercion::MutToConstPointer,
                ..
            } => true,
            ExprKind::Binary { op, .. } => matches!(
                op,
                rustc_middle::mir::BinOp::Add
                    | rustc_middle::mir::BinOp::Sub
                    | rustc_middle::mir::BinOp::Mul
                    | rustc_middle::mir::BinOp::BitAnd
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
