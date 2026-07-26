// Trust: rust-lang#100914 — Detect functions with large estimated stack frames.
// LLVM can miscompile very large stack allocations; this lint warns before that happens.

use rustc_middle::mir;
use rustc_middle::ty::{self, Instance, TyCtxt};
use rustc_session::lint::builtin::LARGE_STACK_FRAME;
use tracing::debug;

use crate::diagnostics::LargeStackFrameLint;

/// Check if a function body's estimated stack frame size exceeds the configured limit.
pub(crate) fn check_stack_frame<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'tcx mir::Body<'tcx>,
) {
    let limit = tcx.stack_frame_limit();
    if limit.0 == 0 {
        return;
    }

    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut total_size = 0u64;
    for local_decl in &body.local_decls {
        let ty = instance.instantiate_mir_and_normalize_erasing_regions(
            tcx,
            typing_env,
            ty::EarlyBinder::bind(tcx, local_decl.ty),
        );
        let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
            continue;
        };
        total_size = total_size.saturating_add(layout.size.bytes());
    }

    debug!(?instance, total_size, limit = limit.0, "stack frame size check");

    if total_size <= limit.0 as u64 {
        return;
    }

    let Some(lint_root) = mir::OUTERMOST_SOURCE_SCOPE.lint_root(&body.source_scopes) else {
        return;
    };

    let span = body.span;
    tcx.emit_node_span_lint(
        LARGE_STACK_FRAME,
        lint_root,
        span,
        LargeStackFrameLint { span, size: total_size, limit: limit.0 as u64 },
    );
}
