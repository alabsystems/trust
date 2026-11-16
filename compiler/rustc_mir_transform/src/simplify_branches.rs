use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use tracing::trace;

use crate::PassPolicy;
use crate::patch::MirPatch;

pub(super) enum SimplifyConstCondition {
    AfterInstSimplify,
    AfterConstProp,
    Final,
}

/// A pass that replaces a branch with a goto when its condition is known.
impl<'tcx> crate::MirPass<'tcx> for SimplifyConstCondition {
    fn name(&self) -> &'static str {
        match self {
            SimplifyConstCondition::AfterInstSimplify => {
                "SimplifyConstCondition-after-inst-simplify"
            }
            SimplifyConstCondition::AfterConstProp => "SimplifyConstCondition-after-const-prop",
            SimplifyConstCondition::Final => "SimplifyConstCondition-final",
        }
    }

    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(true)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        trace!("Running SimplifyConstCondition on {:?}", body.source);
        let mut typing_env = None;
        let mut patch = MirPatch::new_without_block_cache(body);

        fn try_get_const<'tcx, 'a>(
            operand: &'a Operand<'tcx>,
            prev_stmt: Option<&'a Statement<'tcx>>,
        ) -> Option<&'a ConstOperand<'tcx>> {
            match operand {
                Operand::Constant(const_operand) => Some(const_operand),
                // `prev_stmt` is the immediately preceding statement in the same basic block.
                // Soundness: There is nothing that can modify the place, as there are no statements between the two statements.
                Operand::Copy(place) | Operand::Move(place)
                    if let Some(stmt) = prev_stmt
                        && let StatementKind::Assign(ref assign) = stmt.kind
                        && let (place_const, Rvalue::Use(Operand::Constant(ref const_operand), _)) =
                            **assign
                        && place_const == *place =>
                {
                    Some(const_operand)
                }
                Operand::Copy(_) | Operand::Move(_) | Operand::RuntimeChecks(_) => None,
            }
        }

        'blocks: for (bb, block) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in block.statements.iter().enumerate() {
                // Simplify `assume` of a known value: either a NOP or unreachable.
                if let StatementKind::Intrinsic(ref intrinsic) = stmt.kind
                    && let NonDivergingIntrinsic::Assume(ref discr) = **intrinsic
                    && let prev_stmt = statement_index.checked_sub(1).map(|i| &block.statements[i])
                    && let Some(c) = try_get_const(discr, prev_stmt)
                    && let typing_env = *typing_env.get_or_insert_with(|| body.typing_env(tcx))
                    && let Some(constant) = c.const_.try_eval_bool(tcx, typing_env)
                {
                    if constant {
                        patch.nop_statement(Location { block: bb, statement_index });
                    } else {
                        patch.patch_terminator(bb, TerminatorKind::Unreachable);
                        continue 'blocks;
                    }
                }
            }

            let terminator = block.terminator();
            let terminator = match terminator.kind {
                TerminatorKind::SwitchInt { ref discr, ref targets, .. }
                    if let Some(c) = try_get_const(discr, block.statements.last())
                        && let typing_env = *typing_env.get_or_insert_with(|| body.typing_env(tcx))
                        && let Some(constant) = c.const_.try_eval_bits(tcx, typing_env) =>
                {
                    let target = targets.target_for_value(constant);
                    TerminatorKind::goto(target)
                }
                TerminatorKind::Assert { target, ref cond, expected, .. }
                    if let Some(c) = try_get_const(cond, block.statements.last())
                        && let typing_env = *typing_env.get_or_insert_with(|| body.typing_env(tcx))
                        && let Some(constant) = c.const_.try_eval_bool(tcx, typing_env)
                        && constant == expected =>
                {
                    TerminatorKind::goto(target)
                }
                _ => continue,
            };
            patch.patch_terminator(bb, terminator);
        }
        patch.apply(body);
    }
}
