use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{ExprKind, StmtKind, UnOp};
use rustc_middle::mir::{Const, ConstValue};
use rustc_middle::ty::{AnonConstKind, LitToConstInput, Ty, TyCtxt, TypeVisitableExt};

/// Trust: fast pure-HIR syntactic shape filter before querying `clauses_of`
/// (`has_impossible_clauses`), `opaque_types_defined_by`, or `typeck`.
/// Any non-trivial const expression (calls, binary ops, structs, arrays, blocks
/// with non-item statements, etc.) returns `false` immediately without touching
/// query tables or allocating an `InferCtxt`.
#[inline]
fn is_syntactically_trivial_hir(mut expr: &rustc_hir::Expr<'_>) -> bool {
    loop {
        match expr.kind {
            ExprKind::Lit(_) | ExprKind::Path(_) => return true,
            ExprKind::Unary(UnOp::Neg, inner) => return matches!(inner.kind, ExprKind::Lit(_)),
            ExprKind::Cast(source_expr, _cast_ty) => expr = source_expr,
            ExprKind::Block(block, _label) => {
                if block.targeted_by_break {
                    return false;
                }
                if matches!(
                    block.rules,
                    rustc_hir::BlockCheckMode::UnsafeBlock(rustc_hir::UnsafeSource::UserProvided)
                ) {
                    return false;
                }
                if block.stmts.iter().any(|stmt| !matches!(stmt.kind, StmtKind::Item(..))) {
                    return false;
                }
                let Some(block_expr) = block.expr else {
                    return true;
                };
                expr = block_expr;
            }
            _ => return false,
        }
    }
}

/// If the given def is a trivial const, returns the value and type the const evaluates to.
///
/// A "trivial const" is a const which can be easily proven to evaluate successfully, and the value
/// that it evaluates to can be easily found from HIR without building THIR or MIR or going through
/// the usual MIR phases for a const.
///
/// Currently, we support two forms of trivial const:
///
/// 1. Literal (optionally negated, or unit `{}` block, or wrapped in no-op coercion casts / blocks
///    containing only item declarations):
/// ```
/// const A: usize = 0;
/// ```
/// 2. Path referencing another trivial const:
/// ```
/// const A: usize = 0;
/// const B: usize = A;
/// ```
///
/// Being conservative is essential:
/// - False negatives are fine: the ordinary path builds and analyzes THIR/MIR as normal.
/// - False positives are unsound: they would skip borrowck, unsafety checking, and const qualif.
pub(crate) fn trivial_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> Option<(ConstValue, Ty<'tcx>)> {
    match tcx.def_kind(def) {
        DefKind::AssocConst | DefKind::Const => (),
        DefKind::AnonConst if tcx.anon_const_kind(def) != AnonConstKind::NonTypeSystemInline => (),
        _ => return None,
    }

    let body = tcx.hir_maybe_body_owned_by(def)?;

    // Bail if there are arg patterns.
    if !body.params.is_empty() {
        return None;
    }

    // Trust: cheap syntactic HIR shape check runs FIRST so non-trivial consts
    // (calls, arithmetic, aggregates, etc.) bail out in O(1) without querying
    // `has_impossible_clauses`, `opaque_types_defined_by`, or `typeck`.
    if !is_syntactically_trivial_hir(body.value) {
        return None;
    }

    // If there are impossible clauses then MIR passes will replace the body with
    // `unreachable` causing const eval errors when trying to evaluate the body. For
    // now we avoid using trivial consts for such bodies so that the behaviour doesn't
    // change.
    if crate::impossible_clauses::has_impossible_clauses(tcx, def.into()) {
        return None;
    }

    if !tcx.opaque_types_defined_by(def).is_empty() {
        return None;
    }

    // Bail if there are any type errors, to let MIR build produce an error body.
    let typeck_results = tcx.typeck(def);
    if typeck_results.tainted_by_errors.is_some() {
        return None;
    }

    let mut expr = body.value;
    let (lit, neg) = loop {
        // Don't allow adjustments, e.g. coercions, derefs.
        if !typeck_results.expr_adjustments(expr).is_empty() {
            return None;
        }

        match expr.kind {
            ExprKind::Lit(lit) => break (lit, false),
            ExprKind::Unary(UnOp::Neg, inner) => match inner.kind {
                ExprKind::Lit(lit) if !typeck_results.is_method_call(expr) => {
                    break (lit, true);
                }
                _ => return None,
            },
            ExprKind::Cast(source_expr, cast_ty) => {
                // Coercion casts are effectively no-ops.
                if !typeck_results.is_coercion_cast(source_expr.hir_id) {
                    return None;
                }
                if typeck_results.user_provided_types().get(cast_ty.hir_id).is_some() {
                    // Gets wrapped in `thir::ExprKind::ValueTypeAscription`.
                    return None;
                }
                expr = source_expr;
            }
            ExprKind::Path(qpath) => {
                let res = typeck_results.qpath_res(&qpath, expr.hir_id);
                let Res::Def(DefKind::Const | DefKind::AssocConst, def_id) = res else {
                    return None;
                };
                if !typeck_results.node_args(expr.hir_id).is_empty() {
                    return None;
                }
                if tcx.is_direct_const(def_id) {
                    return None;
                }
                return tcx.trivial_const(def_id);
            }
            ExprKind::Block(block, _label) => {
                if block.targeted_by_break {
                    return None;
                }
                if matches!(
                    block.rules,
                    rustc_hir::BlockCheckMode::UnsafeBlock(rustc_hir::UnsafeSource::UserProvided)
                ) {
                    return None;
                }
                for stmt in block.stmts {
                    // Allow items; THIR discards them.
                    let StmtKind::Item(..) = stmt.kind else {
                        return None;
                    };
                }
                if let Some(block_expr) = block.expr {
                    expr = block_expr;
                } else {
                    let ty = typeck_results.expr_ty(expr);
                    return if ty.is_unit() { Some((ConstValue::ZeroSized, ty)) } else { None };
                }
            }
            _ => return None,
        }
    };

    let ty = typeck_results.expr_ty(expr);
    if ty.references_error() {
        return None;
    }

    if ty.has_opaque_types() || tcx.type_of(def).instantiate_identity().has_opaque_types() {
        return None;
    }

    let input = LitToConstInput { lit: lit.node, ty: Some(ty), neg };
    let const_ = rustc_mir_build::lit_to_mir_constant(tcx, input);
    match const_ {
        Const::Ty(..) => None,
        Const::Val(v, ty) => Some((v, ty)),
        Const::Unevaluated(..) => unreachable!(),
    }
}
