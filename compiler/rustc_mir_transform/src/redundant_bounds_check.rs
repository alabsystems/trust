// Trust: MIR pass to eliminate redundant array bounds checks (#867)
// Trust: rust-lang#127553: "Missed bounds check elimination"
//
// Trust: When code performs a bounds check (e.g., `assert!(i < arr.len())`) and
// Trust: then indexes `arr[i]`, the compiler generates two BoundsCheck asserts.
// Trust: If the first dominates the second and checks the same index against the
// Trust: same length, the second is redundant.
//
// Trust: This pass uses two complementary strategies:
// Trust: 1. Condition-based: If two Assert terminators share the same condition
// Trust:    local and expected value, and the first dominates the second, the
// Trust:    second is redundant.
// Trust: 2. BoundsCheck-specific: If two BoundsCheck asserts reference the same
// Trust:    index and length locals, the dominated one is redundant.
//
// Trust: Strategy 1 benefits from running after GVN, which merges identical
// Trust: computations into the same SSA local.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use smallvec::SmallVec;
use tracing::{debug, trace};

use crate::ssa::SsaLocals;

pub(super) struct RedundantBoundsCheckElim;

impl<'tcx> crate::MirPass<'tcx> for RedundantBoundsCheckElim {
    fn name(&self) -> &'static str {
        "RedundantBoundsCheckElim"
    }

    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 2
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Trust: cheap pre-scan over RAW (un-SSA-filtered) keys — a rewrite
        // needs two asserts sharing a (cond, expected) or (index, len) key,
        // and the SSA filter below only shrinks buckets, so if no raw bucket
        // has >= 2 members nothing can ever be rewritten. This skips the full
        // SsaLocals analysis for assert-free bodies, single-assert bodies (a
        // lone bounds check — the common case in post-GVN release MIR), and
        // multi-assert bodies whose keys are all distinct.
        let mut raw_cond: FxHashMap<(Local, bool), u32> = FxHashMap::default();
        let mut raw_bounds: FxHashMap<(Local, Local), u32> = FxHashMap::default();
        let mut has_candidate = false;
        for block in body.basic_blocks.iter() {
            if let TerminatorKind::Assert { ref cond, expected, ref msg, .. } =
                block.terminator().kind
            {
                if let Some(cond_local) = operand_as_plain_local(cond) {
                    let n = raw_cond.entry((cond_local, expected)).or_default();
                    *n += 1;
                    has_candidate |= *n >= 2;
                }
                if expected {
                    if let AssertKind::BoundsCheck { ref len, ref index } = **msg {
                        if let (Some(idx), Some(ln)) =
                            (operand_as_plain_local(index), operand_as_plain_local(len))
                        {
                            let n = raw_bounds.entry((idx, ln)).or_default();
                            *n += 1;
                            has_candidate |= *n >= 2;
                        }
                    }
                }
            }
        }
        if !has_candidate {
            return;
        }

        // Trust: MIR locals are not SSA by construction — a local may be reassigned
        // between a dominating assert and a dominated one, in which case the second
        // check is *not* redundant. Restrict both strategies to SSA locals (single
        // assignment dominating all uses): for those, no path from the dominating
        // assert to the dominated one can re-execute the assignment, so the compared
        // locals are known to hold the same values at both asserts.
        let ssa = SsaLocals::new(tcx, body, body.typing_env(tcx));
        let dominators = body.basic_blocks.dominators();

        // Trust: Phase 1 — Index all Assert(cond, true, ...) terminators, keyed by
        // (cond_local, expected) for condition-based dedup and (index, len) locals
        // for BoundsCheck-specific dedup. Keyed buckets (not a flat list) keep
        // phase 2 at O(bucket) per assert — a flat list made assert-heavy bodies
        // quadratic. Unreachable blocks are skipped: `dominates` never holds from
        // an unreachable block, and unreachable asserts are not worth rewriting.
        let mut assert_cond_blocks: FxHashMap<(Local, bool), SmallVec<[BasicBlock; 4]>> =
            FxHashMap::default();
        let mut bounds_check_blocks: FxHashMap<(Local, Local), SmallVec<[BasicBlock; 4]>> =
            FxHashMap::default();

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            if !dominators.is_reachable(bb) {
                continue;
            }
            let terminator = block.terminator();
            if let TerminatorKind::Assert { ref cond, expected, ref msg, .. } = terminator.kind {
                if let Some(cond_local) = operand_as_ssa_local(&ssa, cond) {
                    assert_cond_blocks.entry((cond_local, expected)).or_default().push(bb);
                }
                if expected {
                    if let AssertKind::BoundsCheck { ref len, ref index } = **msg {
                        if let (Some(idx), Some(ln)) =
                            (operand_as_ssa_local(&ssa, index), operand_as_ssa_local(&ssa, len))
                        {
                            bounds_check_blocks.entry((idx, ln)).or_default().push(bb);
                        }
                    }
                }
            }
        }

        // Trust: Phase 2 — collect redundant asserts read-only, then rewrite.
        // Splitting the phases keeps the cached dominator tree borrowable
        // instead of cloning it per body.
        let mut rewrites: Vec<(BasicBlock, BasicBlock)> = Vec::new();
        for (bb, block) in body.basic_blocks.iter_enumerated() {
            if !dominators.is_reachable(bb) {
                continue;
            }
            let TerminatorKind::Assert { ref cond, expected, ref msg, target, .. } =
                block.terminator().kind
            else {
                continue;
            };

            let cond_local = match operand_as_ssa_local(&ssa, cond) {
                Some(l) => l,
                None => continue,
            };

            // Trust: Strategy 1 — Same condition local, same expected value,
            // dominating block. Works for any Assert, not just BoundsCheck.
            let redundant_by_cond =
                assert_cond_blocks.get(&(cond_local, expected)).is_some_and(|doms| {
                    doms.iter().any(|&dom_bb| dom_bb != bb && dominators.dominates(dom_bb, bb))
                });

            // Trust: Strategy 2 — BoundsCheck-specific: same index and length locals.
            let redundant_by_bounds = !redundant_by_cond
                && expected
                && if let AssertKind::BoundsCheck { ref len, ref index } = **msg {
                    if let (Some(idx), Some(ln)) =
                        (operand_as_ssa_local(&ssa, index), operand_as_ssa_local(&ssa, len))
                    {
                        bounds_check_blocks.get(&(idx, ln)).is_some_and(|doms| {
                            doms.iter()
                                .any(|&dom_bb| dom_bb != bb && dominators.dominates(dom_bb, bb))
                        })
                    } else {
                        false
                    }
                } else {
                    false
                };

            if redundant_by_cond || redundant_by_bounds {
                let strategy = if redundant_by_cond { "condition" } else { "bounds-check" };
                trace!(
                    "Trust: eliminating redundant assert in {:?} via {} strategy \
                     (cond={:?})",
                    bb, strategy, cond_local
                );
                rewrites.push((bb, target));
            }
        }

        if rewrites.is_empty() {
            return;
        }
        debug!(
            "Trust: RedundantBoundsCheckElim eliminated {} redundant check(s) in {:?}",
            rewrites.len(),
            body.source.def_id()
        );
        let blocks = body.basic_blocks.as_mut();
        for (bb, target) in rewrites {
            blocks[bb].terminator_mut().kind = TerminatorKind::Goto { target };
        }
    }

    fn is_required(&self) -> bool {
        false
    }
}

/// Trust: Extract the Local from an Operand if it's a Copy or Move of a projection-free
/// SSA local (single assignment dominating all uses). Non-SSA locals may be reassigned
/// between two asserts, so they must not participate in redundancy detection.
fn operand_as_ssa_local(ssa: &SsaLocals, op: &Operand<'_>) -> Option<Local> {
    match op {
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() && ssa.is_ssa(place.local) =>
        {
            Some(place.local)
        }
        _ => None,
    }
}

/// Trust: the raw (pre-SSA-analysis) variant, used only by the pre-scan — a
/// superset of `operand_as_ssa_local`, so an empty raw bucket proves an empty
/// SSA-filtered bucket.
fn operand_as_plain_local(op: &Operand<'_>) -> Option<Local> {
    match op {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}
