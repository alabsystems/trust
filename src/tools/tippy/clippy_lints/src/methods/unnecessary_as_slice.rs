use super::UNNECESSARY_AS_SLICE;
use clippy_utils::diagnostics::span_lint_and_sugg;
// Trust: keep const suggestions within the receiver's stable inherent API.
use clippy_utils::msrvs::Msrv;
use clippy_utils::ty::get_adt_inherent_method;
use clippy_utils::{get_parent_expr, is_in_const_context, sym};
use rustc_errors::Applicability;
use rustc_hir::{Expr, ExprKind, PathSegment};
use rustc_lint::LateContext;
use rustc_span::Symbol;

// Trust: const-stability must respect the linted crate's MSRV.
pub(super) fn check(cx: &LateContext<'_>, expr: &Expr<'_>, recv: &Expr<'_>, name: Symbol, msrv: Msrv) {
    if !expr.span.from_expansion()
        && let Some(parent_expr) = get_parent_expr(cx, expr)
        // the parent is also a method call
        && let ExprKind::MethodCall(PathSegment { ident: parent_method_ident, .. }, parent_recv, ..) = parent_expr.kind
        // Excluding `as_ptr` and `as_mut_ptr` because they are commonly used to get raw pointers for FFI or unsafe code, and removing them might change the semantics of the code.
        && !(parent_method_ident.name == sym::as_ptr || parent_method_ident.name == sym::as_mut_ptr)
        // the parent's recv is the same as the current expr
        && parent_recv.hir_id == expr.hir_id
        // the parent is not a trait method
        && let opt_fn_id = cx.typeck_results().type_dependent_def_id(parent_expr.hir_id)
        && opt_fn_id.is_none_or(|fn_id| cx.tcx.trait_of_assoc(fn_id).is_none())
        // checking whether the recv is a `Vec`
        && let recv_ty = cx.typeck_results().expr_ty(recv).peel_refs()
        && recv_ty
            .ty_adt_def()
            .is_some_and(|adt| cx.tcx.is_diagnostic_item(sym::Vec, adt.did()))
        // Trust: a const slice method reached through Vec::as_slice can be
        // legal even though the corresponding Vec call requires non-const
        // Deref. Only suggest a direct, const-stable Vec method here.
        && (!is_in_const_context(cx)
            || get_adt_inherent_method(cx, recv_ty, parent_method_ident.name)
                .is_some_and(|method| msrv.is_const_stable(cx, method.def_id)))
        && let Some(as_slice_span) = expr.span.trim_start(recv.span)
    {
        let parent_method_name = parent_method_ident.name;
        span_lint_and_sugg(
            cx,
            UNNECESSARY_AS_SLICE,
            as_slice_span,
            format!(
                "this `{name}` is unnecessary because the following method (`{parent_method_name}`) can be called on `Vec` directly"
            ),
            format!("remove `{name}`"),
            String::new(),
            Applicability::MachineApplicable,
        );
    }
}
