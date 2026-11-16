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

use crate::fx::{FxHashMap, FxHashSet};
use crate::{BasicBlock, BlockId, Terminator, VerifiableFunction};

/// Visit each successor block a terminator may branch to in canonical order,
/// without allocating a temporary `Vec<BlockId>`.
pub(crate) fn for_each_terminator_successor(t: &Terminator, mut f: impl FnMut(BlockId)) {
    match t {
        Terminator::Goto(b)
        | Terminator::Assert { target: b, .. }
        | Terminator::Drop { target: b, .. } => f(*b),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for (_, b) in targets {
                f(*b);
            }
            f(*otherwise);
        }
        Terminator::Call { target, .. } => {
            if let Some(b) = target {
                f(*b);
            }
        }
        Terminator::Opaque { targets, .. } => {
            for b in targets {
                f(*b);
            }
        }
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => {}
    }
}

/// Return the `idx`-th successor of `t` in the same order as [`terminator_successors`],
/// without allocating a temporary `Vec<BlockId>`.
#[inline]
pub(crate) fn terminator_successor_at(t: &Terminator, idx: usize) -> Option<BlockId> {
    match t {
        Terminator::Goto(b)
        | Terminator::Assert { target: b, .. }
        | Terminator::Drop { target: b, .. } => (idx == 0).then_some(*b),
        Terminator::Call { target, .. } => (idx == 0).then_some(*target)?,
        Terminator::SwitchInt { targets, otherwise, .. } => {
            if let Some((_, b)) = targets.get(idx) {
                Some(*b)
            } else if idx == targets.len() {
                Some(*otherwise)
            } else {
                None
            }
        }
        Terminator::Opaque { targets, .. } => targets.get(idx).copied(),
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => None,
    }
}

/// Whether `target` is a direct control-flow successor of `t`.
#[inline]
pub(crate) fn terminator_has_successor(t: &Terminator, target: BlockId) -> bool {
    match t {
        Terminator::Goto(b)
        | Terminator::Assert { target: b, .. }
        | Terminator::Drop { target: b, .. } => *b == target,
        Terminator::Call { target: Some(b), .. } => *b == target,
        Terminator::SwitchInt { targets, otherwise, .. } => {
            *otherwise == target || targets.iter().any(|(_, b)| *b == target)
        }
        Terminator::Opaque { targets, .. } => targets.contains(&target),
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => false,
    }
}

/// Whether every block reachable from `blocks.first()` satisfies `predicate`.
/// Returns `false` on an empty block slice (fail closed).
pub(crate) fn all_reachable_blocks(
    blocks: &[BasicBlock],
    mut predicate: impl FnMut(&BasicBlock) -> bool,
) -> bool {
    let Some(entry) = blocks.first().map(|b| b.id) else {
        return false;
    };
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let mut seen = vec![false; blocks.len()];
        seen[0] = true;
        let mut stack = Vec::with_capacity(blocks.len());
        stack.push(0usize);
        while let Some(idx) = stack.pop() {
            let Some(block) = blocks.get(idx) else {
                continue;
            };
            if !predicate(block) {
                return false;
            }
            for_each_terminator_successor(&block.terminator, |s| {
                if let Some(slot) = seen.get_mut(s.0)
                    && !*slot
                {
                    *slot = true;
                    stack.push(s.0);
                }
            });
        }
        return true;
    }

    let by_id: FxHashMap<BlockId, &BasicBlock> = blocks.iter().map(|b| (b.id, b)).collect();
    let mut seen: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(blocks.len(), Default::default());
    seen.insert(entry);
    let mut stack = Vec::with_capacity(blocks.len());
    stack.push(entry);
    while let Some(bid) = stack.pop() {
        let Some(block) = by_id.get(&bid) else {
            continue;
        };
        if !predicate(block) {
            return false;
        }
        for_each_terminator_successor(&block.terminator, |s| {
            if seen.insert(s) {
                stack.push(s);
            }
        });
    }
    true
}

/// The successor blocks a terminator may branch to (empty for the leaves
/// `Return`, `Unreachable`, `Resume`, and a `Call` with no return target).
#[must_use]
pub fn terminator_successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut s: Vec<BlockId> = Vec::with_capacity(targets.len() + 1);
            s.extend(targets.iter().map(|(_, b)| *b));
            s.push(*otherwise);
            s
        }
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => Vec::new(),
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
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        // 0 = white (unseen), 1 = grey (on the DFS stack), 2 = black (finished).
        let mut colour = vec![0u8; blocks.len()];
        let mut stack: Vec<(usize, usize)> = Vec::with_capacity(blocks.len());
        colour[0] = 1;
        stack.push((0, 0));
        while let Some(top) = stack.last_mut() {
            let (node, idx) = *top;
            let Some(block) = blocks.get(node) else {
                stack.pop();
                continue;
            };
            if let Some(next) = terminator_successor_at(&block.terminator, idx) {
                top.1 += 1;
                let Some(next_colour) = colour.get_mut(next.0) else {
                    continue;
                };
                match *next_colour {
                    1 => return false, // grey: back edge → cycle
                    0 => {
                        *next_colour = 1;
                        stack.push((next.0, 0));
                    }
                    _ => {} // black: already finished
                }
            } else {
                colour[node] = 2;
                stack.pop();
            }
        }
        return true;
    }

    let by_id: FxHashMap<BlockId, &BasicBlock> = blocks.iter().map(|b| (b.id, b)).collect();
    // 0 = white (unseen), 1 = grey (on the DFS stack), 2 = black (finished).
    let mut colour: FxHashMap<BlockId, u8> =
        FxHashMap::with_capacity_and_hasher(blocks.len(), Default::default());
    let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
    colour.insert(entry, 1);
    while let Some(top) = stack.last_mut() {
        let (node, idx) = *top;
        let next = by_id
            .get(&node)
            .and_then(|block| terminator_successor_at(&block.terminator, idx));
        if let Some(next) = next {
            top.1 += 1;
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
        let blocks = vec![block(0, Terminator::Goto(BlockId(1))), block(1, Terminator::Return)];
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
