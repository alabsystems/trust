use rustc_hir::{Expr, ExprKind};
use rustc_lint_defs::{LintId, declare_lint, declare_lint_pass};
use rustc_middle::ty::layout::LayoutOf;
use rustc_middle::ty::{self, Ty};
use rustc_span::{Symbol, sym};

use crate::diagnostics::HashIterationOrderDiag;
use crate::internal::{ResolvedCall, UnstableIteration};
use crate::{LateContext, LateLintPass, LintContext};

declare_lint! {
    /// The `hash_iteration_order` lint detects iteration of a [`std::collections::HashMap`] or
    /// [`std::collections::HashSet`] whose hasher can order the same entries differently in
    /// another run: a hasher builder that carries state, such as [`RandomState`] with its
    /// per-process keys, or one the lint cannot see, such as a type parameter.
    ///
    /// [`RandomState`]: https://doc.rust-lang.org/std/hash/struct.RandomState.html
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![deny(unknown_lints)]
    /// #![deny(hash_iteration_order)]
    /// use std::collections::HashMap;
    ///
    /// let scores: HashMap<&str, u32> = HashMap::from([("a", 1), ("b", 2)]);
    /// for (name, score) in &scores {
    ///     println!("{name}: {score}");
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// A hash collection visits its entries in hash order, and `RandomState` draws new keys in
    /// every process, so one program on one input can print, serialize or decide in a
    /// different order from one run to the next. Where the order can reach output, iterate an
    /// ordered collection (`BTreeMap`, `BTreeSet`) or sort first. Where it cannot (a count, a
    /// sum, a membership test, a collection into another set), scope
    /// `#[allow(hash_iteration_order)]` to that site and say why.
    ///
    /// A hasher builder with no state, a zero-sized type such as
    /// `BuildHasherDefault<DefaultHasher>`, builds the same hasher in every process and is not
    /// reported. The order then follows the keys' hashes and the order of insertion, so a key
    /// that hashes an address, or a zero-sized builder that seeds from a global, is still the
    /// caller's to rule out. Formatting (`{:?}`) or serializing a map also visits it in hash
    /// order, inside the formatter's or the serializer's own code, which this lint does not
    /// see.
    // Trust: `Allow` by default, for `env_mutation`'s reason. A default-on level of
    // any severity is output, and stderr is what upstream UI tests compare, so a
    // warning would change every upstream test whose subject iterates a `HashMap`;
    // "All valid Rust must compile identically" outranks the stance. The code Trust
    // owns opts in at deny through its workspace lint tables once a seal carries
    // this lint (design 2026-09-29-incremental-deterministic-trust-results.md
    // §3.5 "Maps", the P4 row). The detection is `rustc::potential_query_instability`'s
    // (`internal.rs`, `ResolvedCall::unstable_iteration`), narrowed here to std's
    // hash collections and to the hashers that can change the order.
    pub HASH_ITERATION_ORDER,
    Allow,
    "iterating a hash collection whose hasher can change the order from one run to the next",
    report_in_external_macro
}

declare_lint_pass!(HashIterationOrder => [HASH_ITERATION_ORDER]);

impl<'tcx> LateLintPass<'tcx> for HashIterationOrder {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        // The detector resolves every call it is shown, so a crate that never turns this
        // lint on does not pay for it.
        if !matches!(expr.kind, ExprKind::Call(..) | ExprKind::MethodCall(..))
            || cx.tcx.skippable_lints(()).contains(&LintId::of(HASH_ITERATION_ORDER))
        {
            return;
        }
        let Some(call) = ResolvedCall::of(cx, expr) else { return };
        let Some(UnstableIteration { name, span, owner: Some(owner) }) =
            call.unstable_iteration(cx, expr)
        else {
            return;
        };
        let Some((collection, hasher)) = std_hash_collection(cx, owner) else { return };
        if hasher_is_stateless(cx, hasher) {
            return;
        }
        cx.emit_span_lint(
            HASH_ITERATION_ORDER,
            span,
            HashIterationOrderDiag { method: name, collection, hasher },
        );
    }
}

/// `HashMap` or `HashSet`, with its hasher builder, for a std hash collection or a reference
/// to one.
fn std_hash_collection<'tcx>(cx: &LateContext<'tcx>, ty: Ty<'tcx>) -> Option<(Symbol, Ty<'tcx>)> {
    let ty::Adt(adt, args) = ty.peel_refs().kind() else { return None };
    // `HashMap<K, V, S, A>` and `HashSet<T, S, A>`.
    match cx.tcx.get_diagnostic_name(adt.did())? {
        sym::HashMap => Some((sym::HashMap, args.type_at(2))),
        sym::HashSet => Some((sym::HashSet, args.type_at(1))),
        _ => None,
    }
}

/// Does every value of this hasher builder build the same hasher, in every process?
///
/// Only a builder with no state can promise it: a per-process seed has to live somewhere, and
/// a zero-sized type has nowhere to keep one. A builder whose layout is not known here, such
/// as a type parameter, is not known to be one, and is reported.
fn hasher_is_stateless<'tcx>(cx: &LateContext<'tcx>, hasher: Ty<'tcx>) -> bool {
    cx.layout_of(hasher).is_ok_and(|layout| layout.is_zst())
}
