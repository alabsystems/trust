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
    /// #![deny(env_mutation)]
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
    // Trust: `Allow` by default. This is a Trust-SPECIFIC safety stance, and a
    // default-on level of ANY severity breaks the release gate that outranks it:
    // "All valid Rust must compile identically" (CLAUDE.md, upstream discipline).
    // A warning is still output — it lands in stderr, which is what upstream UI
    // tests compare — so `Warn` fails every upstream test whose subject legally
    // mutates the environment.
    //
    // Measured 2026-08-23 by `targo trust domination upstream-tests --execute`,
    // the first run of that gate to reach the suite: 8 of its 15 upstream UI
    // failures were THIS LINT and nothing else —
    //   tests/ui/backtrace/{std-backtrace,line-tables-only,dylib-dep}.rs
    //   tests/ui/command/command-exec.rs   tests/ui/issues/issue-45731.rs
    //   tests/ui/process/{process-envs,process-remove-from-env}.rs
    //   tests/ui/rust-2024/unsafe-env-suggestion.rs
    // and the count grows with every upstream test that touches `set_var`.
    // Blessing them would record a Trust opinion as an upstream expectation.
    //
    // The earlier note here reasoned only about `Deny` vs `Warn` for the
    // first-party tool fleet (352 legitimate call sites across ay, ty, trust-cg,
    // trust-vc that manage `RUSTC_BOOTSTRAP` and solver config). That trade-off
    // is real and is unchanged — it is simply not the only constraint. `Allow`
    // satisfies both: the toolchain builds, and upstream code compiles
    // identically.
    //
    // NOTHING IS LOST for the code Trust owns. `crates/Cargo.toml`'s
    // `[workspace.lints.rust]` now carries `env_mutation = "warn"`, which every
    // Trust-owned member inherits through `[lints] workspace = true` — the
    // opt-in that `src/tools/tidy/src/workspace_lints.rs` ratchets at zero, so
    // a member cannot silently drop out of it. Escalate per crate with
    // `#![deny(env_mutation)]` where the stance should be hard.
    pub ENV_MUTATION,
    Allow,
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
