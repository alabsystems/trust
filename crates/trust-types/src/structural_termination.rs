//! Structural (intra-function) termination evidence — the loop-free half of the
//! E6 `Total` facet.
//!
//! A function whose control-flow graph has NO cycle reachable from its entry
//! terminates on its own: every execution path is bounded by the number of
//! basic blocks. This module computes that fact from the [`VerifiableFunction`]
//! CFG alone — a pure, deterministic analysis with no compiler (`rustc`)
//! dependency, so it lives in the clean IR crate and is unit-testable in
//! isolation.
//!
//! SCOPE. This is the STRUCTURAL half of `Total`. It is sound but incomplete on
//! its own:
//!   * it does NOT account for a non-terminating CALLEE — a caller of a
//!     diverging function is loop-free here yet not `Total`; that composes with
//!     the acyclic-call-graph / all-callees-`Total` lane;
//!   * a function with a genuine LOOP is (correctly) reported not-loop-free
//!     here; establishing its termination needs the E5 measure lane.
//! So `is_control_flow_loop_free == true` is one INPUT to a `Total` facet
//! certificate, never the whole of it. It is deliberately conservative: an
//! empty body, or any reachable cycle, yields `false`.
//!
//! ASSUMPTION on `Terminator::Opaque` (unmodeled control flow). This analysis
//! trusts an `Opaque` terminator's recorded `targets` to be the COMPLETE set of
//! its control-flow successors, and trusts the terminator not to diverge
//! INTERNALLY. That holds for the benign scaffolding `Opaque` stands in for —
//! `FalseEdge` / `FalseUnwind` and switch-lowering artifacts all terminate and
//! carry their true successors — but NOT for a construct that loops inside
//! itself with no MIR back-edge, the clearest case being an `asm!` block
//! containing an internal jump (`2: jmp 2b`): its CFG looks acyclic yet it never
//! returns. Such a function would be reported loop-free here. Distinguishing the
//! two would need the `Opaque` `kind` to reliably tag inline-asm (it does not
//! today), so this is left as a documented boundary rather than a blanket
//! fail-closed — blanket rejection would wrongly deny `Total` to the common,
//! genuinely-terminating `FalseEdge`/`FalseUnwind` cases. (Contrast the `Pure` /
//! `NoPanic` / `Deterministic` analyses, where `Opaque` DOES fail closed: there
//! it is a rare own-effect/panic/nondet source with no legitimate coverage cost,
//! whereas here it is common benign scaffolding.)

use crate::{BasicBlock, BlockId, Terminator, VerifiableFunction};
use std::collections::HashMap;

/// The successor blocks a terminator may branch to (empty for the leaves
/// `Return`, `Unreachable`, `Resume`, and a `Call` with no return target).
#[must_use]
pub fn terminator_successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut s: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
            s.push(*otherwise);
            s
        }
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return | Terminator::Unreachable | Terminator::Resume => Vec::new(),
    }
}

/// Whether the block CFG is loop-free — no block reachable from the entry (the
/// first block) lies on a cycle. Only REACHABLE blocks are explored, so a cycle
/// in dead code does not affect the verdict (dead code cannot execute, so it
/// cannot diverge). An empty block list returns `false` (nothing to certify).
///
/// Implementation: an iterative three-colour DFS (white / grey / black). A grey
/// → grey edge is a back edge, i.e. a cycle.
#[must_use]
pub fn is_loop_free(blocks: &[BasicBlock]) -> bool {
    let Some(entry) = blocks.first().map(|b| b.id) else {
        return false;
    };
    let succ: HashMap<BlockId, Vec<BlockId>> =
        blocks.iter().map(|b| (b.id, terminator_successors(&b.terminator))).collect();

    // 0 = white (unseen), 1 = grey (on the DFS stack), 2 = black (finished).
    let mut colour: HashMap<BlockId, u8> = HashMap::new();
    let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
    colour.insert(entry, 1);
    while let Some(&(node, idx)) = stack.last() {
        let succs: &[BlockId] = succ.get(&node).map_or(&[], Vec::as_slice);
        if idx < succs.len() {
            stack.last_mut().unwrap().1 += 1;
            let next = succs[idx];
            match colour.get(&next).copied().unwrap_or(0) {
                1 => return false, // grey: back edge → cycle
                0 => {
                    colour.insert(next, 1);
                    stack.push((next, 0));
                }
                _ => {} // black: already finished
            }
        } else {
            colour.insert(node, 2);
            stack.pop();
        }
    }
    true
}

/// [`is_loop_free`] over a whole function's body — one sound INPUT to its `Total`
/// facet (see the module docs for what it does NOT establish).
#[must_use]
pub fn is_control_flow_loop_free(func: &VerifiableFunction) -> bool {
    is_loop_free(&func.body.blocks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Terminator;

    fn block(id: usize, t: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: Vec::new(), terminator: t }
    }

    #[test]
    fn straight_line_is_loop_free() {
        // bb0 → bb1 → return.
        let blocks =
            vec![block(0, Terminator::Goto(BlockId(1))), block(1, Terminator::Return)];
        assert!(is_loop_free(&blocks));
    }

    #[test]
    fn acyclic_branch_is_loop_free() {
        // bb0 branches to bb1 / bb2, both return — a diamond with no join loop.
        let blocks = vec![
            block(
                0,
                Terminator::Opaque {
                    kind: "branch".to_string(),
                    targets: vec![BlockId(1), BlockId(2)],
                    span: crate::SourceSpan::default(),
                },
            ),
            block(1, Terminator::Return),
            block(2, Terminator::Return),
        ];
        assert!(is_loop_free(&blocks));
    }

    #[test]
    fn self_loop_is_not_loop_free() {
        // bb0 → bb0.
        assert!(!is_loop_free(&[block(0, Terminator::Goto(BlockId(0)))]));
    }

    #[test]
    fn back_edge_is_not_loop_free() {
        // bb0 → bb1 → bb0 (a two-block loop).
        let blocks =
            vec![block(0, Terminator::Goto(BlockId(1))), block(1, Terminator::Goto(BlockId(0)))];
        assert!(!is_loop_free(&blocks));
    }

    #[test]
    fn cycle_in_dead_code_is_ignored() {
        // bb0 returns immediately; bb1 ↔ bb2 form a loop unreachable from bb0.
        let blocks = vec![
            block(0, Terminator::Return),
            block(1, Terminator::Goto(BlockId(2))),
            block(2, Terminator::Goto(BlockId(1))),
        ];
        assert!(is_loop_free(&blocks), "an unreachable cycle cannot execute");
    }

    #[test]
    fn empty_body_fails_closed() {
        assert!(!is_loop_free(&[]));
    }
}
