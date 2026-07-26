use rustc_hir::{Expr, ExprKind, Node};
use rustc_session::{declare_lint, declare_lint_pass};
use rustc_span::{Symbol, sym};

use crate::lints::EnvMutationDiag;
use crate::{LateContext, LateLintPass, LintContext};

declare_lint! {
    /// The `env_mutation` lint detects any call to [`std::env::set_var`] or
    /// [`std::env::remove_var`], including uses of those functions as
    /// first-class values (function pointers).
    ///
    /// [`std::env::set_var`]: https://doc.rust-lang.org/std/env/fn.set_var.html
    /// [`std::env::remove_var`]: https://doc.rust-lang.org/std/env/fn.remove_var.html
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// unsafe { std::env::set_var("KEY", "VALUE") };
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Mutating the environment is a process-global side effect: it races with
    /// every other thread that reads (`std::env::var`, DNS lookups, locale
    /// queries, arbitrary C code calling `getenv`) or writes the environment —
    /// which is undefined behavior on most platforms — and it silently
    /// reconfigures every env-gated reader downstream of the call. Route the
    /// mutation through a single lock-scoped helper that sets, runs, and
    /// restores the variable under a global lock, and scope an exception for
    /// exactly that blessed call site with `#[allow(env_mutation)]`.
    // Trust: `Warn` by default, not `Deny`. This lint is a Trust-specific safety
    // stance (env-mutation races), but a default-`Deny` breaks a CLEAN build of
    // the compiler's own first-party tool fleet from an empty cache — 352 lib/bin
    // call sites across ay, ty, trust-cg, trust-vc, ... legitimately manage env
    // vars (RUSTC_BOOTSTRAP set-restore, solver config) and it was only ever green
    // because cached tool `.rlib`s masked the lint. Emitting at `Warn` keeps the
    // full diagnostic signal (every site is still reported) without gating the
    // toolchain build; crates that want hard enforcement opt in with
    // `#![deny(env_mutation)]` (or the whole-VC verified surface can escalate it).
    pub ENV_MUTATION,
    Warn,
    "mutation of the process-global environment"
}

declare_lint_pass!(EnvMutation => [ENV_MUTATION]);

fn env_mutator_path(name: Symbol) -> Option<&'static str> {
    if name == sym::env_set_var {
        Some("std::env::set_var")
    } else if name == sym::env_remove_var {
        Some("std::env::remove_var")
    } else {
        None
    }
}

/// Is `expr` the callee of a `Call` expression (which is linted as a whole)?
fn is_call_callee(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match cx.tcx.parent_hir_node(expr.hir_id) {
        Node::Expr(parent) => {
            matches!(parent.kind, ExprKind::Call(callee, _) if callee.hir_id == expr.hir_id)
        }
        _ => false,
    }
}

impl<'tcx> LateLintPass<'tcx> for EnvMutation {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        let (path_expr, is_call) = match expr.kind {
            // Direct call: lint the whole call expression once.
            ExprKind::Call(callee, _) => (callee, true),
            // Any other first-class use of the function (e.g. a fn-pointer
            // coercion that could be called later). The callee of a direct
            // call is skipped here because the call itself is linted above.
            ExprKind::Path(_) if !is_call_callee(cx, expr) => (expr, false),
            _ => return,
        };

        if let ExprKind::Path(ref qpath) = path_expr.kind
            && let Some(def_id) = cx.qpath_res(qpath, path_expr.hir_id).opt_def_id()
            && let Some(name) = cx.tcx.get_diagnostic_name(def_id)
            && let Some(fn_path) = env_mutator_path(name)
        {
            cx.emit_span_lint(
                ENV_MUTATION,
                expr.span,
                if is_call {
                    EnvMutationDiag::Call { fn_path }
                } else {
                    EnvMutationDiag::FnValue { fn_path }
                },
            );
        }
    }
}
