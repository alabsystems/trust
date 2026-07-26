use rustc_hir::def::DefKind;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_session::lint::builtin::UNREACHABLE_CODE;

use crate::diagnostics::UnreachableDueToUninhabited;

/// Lint unreachable code due to uninhabited values from function calls,
/// and remove return edges from those calls.
pub(super) struct LintAndRemoveUninhabited;

impl<'tcx> crate::MirPass<'tcx> for LintAndRemoveUninhabited {
    #[tracing::instrument(level = "debug", skip_all)]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let def_id = body.source.def_id().expect_local();
        tracing::debug!(?def_id);

        // Trust: scan read-only first and only go through `basic_blocks.as_mut()`
        // (which invalidates the CFG caches) when a return edge actually has to
        // be removed — the overwhelmingly common case removes nothing. The
        // parent-module/typing-env lookups are deferred to the first Call
        // terminator, and the return-type inhabitedness check (added for
        // rust-lang#149571) to the first uninhabited destination.
        let mut env = None;
        let mut return_ty_is_inhabited = None;
        let mut edits = vec![];
        let mut lints = vec![];
        for (bb, bbdata) in body.basic_blocks.iter_enumerated() {
            let term = bbdata.terminator();
            let TerminatorKind::Call { target: Some(target_bb), destination, .. } = term.kind
            else {
                continue;
            };

            let (parent_module, typing_env) = *env.get_or_insert_with(|| {
                (tcx.parent_module_from_def_id(def_id).to_def_id(), body.typing_env(tcx))
            });
            let ty = destination.ty(&body.local_decls, tcx).ty;
            let ty_is_inhabited = ty.is_inhabited_from(tcx, parent_module, typing_env);
            if !ty_is_inhabited {
                // Unreachable code warnings are already emitted during type checking.
                // However, during type checking, full type information is being
                // calculated but not yet available, so the check for diverging
                // expressions due to uninhabited result types is pretty crude and
                // only checks whether ty.is_never(). Here, we have full type
                // information available and can issue warnings for less obviously
                // uninhabited types (e.g. empty enums). The check above is used so
                // that we do not emit the same warning twice if the uninhabited type
                // is indeed `!`.
                if !ty.is_never()
                    && *return_ty_is_inhabited.get_or_insert_with(|| {
                        matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
                            && body.local_decls[RETURN_PLACE].ty.is_inhabited_from(
                                tcx,
                                parent_module,
                                typing_env,
                            )
                    })
                {
                    lints.push((target_bb, ty, term.source_info.span));
                }

                // The presence or absence of a return edge affects control-flow sensitive
                // MIR checks and ultimately whether code is accepted or not. We can only
                // omit the return edge if a return type is visibly uninhabited to a module
                // that makes the call.
                edits.push(bb);
            }
        }

        if edits.is_empty() {
            return;
        }
        // Remove the return edges before linting: `find_unreachable_code_from`
        // consults predecessor counts, which must reflect the edited CFG.
        let bbs = body.basic_blocks.as_mut();
        for bb in edits {
            let TerminatorKind::Call { ref mut target, .. } = bbs[bb].terminator_mut().kind else {
                unreachable!("collected block is no longer a Call terminator");
            };
            *target = None;
        }

        for (target_bb, orig_ty, orig_span) in lints {
            if orig_span.in_external_macro(tcx.sess.source_map()) {
                continue;
            }

            let Some((target_loc, descr)) = find_unreachable_code_from(target_bb, body) else {
                continue;
            };
            let lint_root = body.source_scopes[target_loc.scope]
                .local_data
                .as_ref()
                .unwrap_crate_local()
                .lint_root;
            tcx.emit_node_span_lint(
                UNREACHABLE_CODE,
                lint_root,
                target_loc.span,
                UnreachableDueToUninhabited {
                    expr: target_loc.span,
                    orig: orig_span,
                    descr,
                    ty: orig_ty,
                },
            );
        }
    }

    fn is_required(&self) -> bool {
        true
    }
}

/// Starting at a target unreachable block, find some user code to lint as unreachable
#[tracing::instrument(level = "debug", skip(body), ret)]
fn find_unreachable_code_from<'tcx>(
    bb: BasicBlock,
    body: &Body<'tcx>,
) -> Option<(SourceInfo, &'static str)> {
    let bbdata = &body.basic_blocks[bb];
    for stmt in &bbdata.statements {
        match &stmt.kind {
            // Ignore the implicit `()` return place assignment for unit functions/blocks
            StatementKind::Assign((_, Rvalue::Use(Operand::Constant(const_), _)))
                if const_.ty().is_unit() =>
            {
                continue;
            }
            // Ignore return value plumbing. After a call returning a non-`!`
            // uninhabited type, a tail expression can be unreachable while
            // still being needed to satisfy the surrounding return type.
            StatementKind::Assign((place, _)) if place.as_local() == Some(RETURN_PLACE) => {
                continue;
            }
            // Ignore statements inserted by MIR building that do not correspond to user code.
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::BackwardIncompatibleDropHint { .. } => {
                continue;
            }
            StatementKind::FakeRead(..) => return Some((stmt.source_info, "definition")),
            _ => return Some((stmt.source_info, "expression")),
        }
    }

    let term = bbdata.terminator();
    match term.kind {
        // The user does not care for `goto` and compiler-generated drops. If the target block is
        // only reachable through those terminators, continue searching there.
        TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } => {
            if &body.basic_blocks.predecessors()[target][..] == &[bb] {
                find_unreachable_code_from(target, body)
            } else {
                None
            }
        }
        TerminatorKind::Return => None,
        _ => Some((term.source_info, "expression")),
    }
}
