use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_mir_dataflow::debuginfo::debuginfo_locals;
use rustc_session::config::MirStripDebugInfo;

use crate::PassPolicy;

/// Conditionally remove some of the VarDebugInfo in MIR.
///
/// In particular, stripping non-parameter debug info for tiny, primitive-like
/// methods in core saves work later, and nobody ever wanted to use it anyway.
pub(super) struct StripDebugInfo;

impl<'tcx> crate::MirPass<'tcx> for StripDebugInfo {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        // Trust: a verifying session keeps every row. Contract and loop-clause
        // names are bound through `var_debug_info`, and a stripped shadow left only
        // the shadowed parameter's row, so `fn f(lim: u8) { let lim: u16 = 300;
        // while .. invariant lim <= 255 .. }` was proved about the parameter
        // (review round 39, 2026-10-02). Stripping changes only debug info.
        PassPolicy::optional(
            ctx.opts.unstable_opts.mir_strip_debuginfo != MirStripDebugInfo::None
                && !ctx.trust_verification_enabled(),
        )
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Trust: see `is_enabled`; the pass is required, so it still runs.
        if tcx.sess.trust_verification_enabled() {
            return;
        }
        match tcx.sess.opts.unstable_opts.mir_strip_debuginfo {
            MirStripDebugInfo::None => return,
            MirStripDebugInfo::AllLocals => {}
            MirStripDebugInfo::LocalsInTinyFunctions
                if let TerminatorKind::Return { .. } =
                    body.basic_blocks[START_BLOCK].terminator().kind => {}
            MirStripDebugInfo::LocalsInTinyFunctions => return,
        }

        if body.var_debug_info.is_empty() {
            return;
        }
        let prev_len = body.var_debug_info.len();
        body.var_debug_info.retain(|vdi| {
            matches!(
                vdi.value,
                VarDebugInfoContents::Place(place)
                    if place.local.as_usize() <= body.arg_count && place.local != RETURN_PLACE,
            )
        });

        if body.var_debug_info.len() != prev_len {
            drop_invalid_debuginfos(body);
        }
    }
}

// Drop invalid debuginfos when strip locals in `var_debug_info`.
pub(super) fn drop_invalid_debuginfos(body: &mut Body<'_>) {
    let debuginfo_locals = debuginfo_locals(body);
    for data in body.basic_blocks.as_mut_preserves_cfg() {
        for stmt in data.statements.iter_mut() {
            stmt.debuginfos.retain_locals(&debuginfo_locals);
        }
        data.after_last_stmt_debuginfos.retain_locals(&debuginfo_locals);
    }
}
