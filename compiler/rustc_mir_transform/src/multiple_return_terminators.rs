//! This pass removes jumps to basic blocks containing only a return, and replaces them with a
//! return instead.

use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

use crate::{PassPolicy, simplify};

pub(super) struct MultipleReturnTerminators;

impl<'tcx> crate::MirPass<'tcx> for MultipleReturnTerminators {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.mir_opt_level() >= 4)
    }

    fn run_pass(&self, _: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // find basic blocks with no statement and a return terminator
        let mut bbs_simple_returns = DenseBitSet::new_empty(body.basic_blocks.len());
        let mut has_simple_return = false;
        for (idx, bb) in body.basic_blocks.iter_enumerated() {
            if bb.statements.is_empty() && bb.terminator().kind == TerminatorKind::Return {
                bbs_simple_returns.insert(idx);
                has_simple_return = true;
            }
        }
        if !has_simple_return {
            return;
        }

        let mut changed = false;
        for idx in body.basic_blocks.indices() {
            if let TerminatorKind::Goto { target, .. } = body.basic_blocks[idx].terminator().kind
                && bbs_simple_returns.contains(target)
            {
                body.basic_blocks_mut()[idx].terminator_mut().kind = TerminatorKind::Return;
                changed = true;
            }
        }

        if changed {
            simplify::remove_dead_blocks(body);
        }
    }
}
