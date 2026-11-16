//! TINV step 3: the unwind (U) points at which a type invariant is owed
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P1/P4-U, §3 G7, §6 step 3).
//!
//! STRATEGY-INDEPENDENT BY CONSTRUCTION. Whether U is owed at a terminator is decided from
//! the terminator's KIND and the model's normal control flow, never from its `UnwindEdge`.
//! rustc rewrites the edge by panic strategy: under `-Cpanic=abort`, `AbortUnwindingCalls`
//! sets every Rust-ABI Call, Assert and Drop to `Unreachable`, `-Zpanic-in-drop` does the
//! same for Drop, and `RemoveNoopLandingPads` plus `SimplifyCfg` delete the cleanup blocks.
//! An `Unreachable` edge on the wire is therefore not "cannot unwind", and the verdict here
//! is identical under both strategies (TINV-3: no `panic=abort` waiver, D20).
//!
//! Extractor rewrites that change edges (`trust-mir-extract`'s `convert.rs`), recorded so a
//! consumer does not trust a terminator kind further than it goes:
//! * an Opaque terminator (indirect or unsupported Call, unsupported Assert message,
//!   InlineAsm, Yield) carries rustc's `successors()`, which INCLUDE the cleanup block, as
//!   ordinary targets; [`u_point`] refuses every Opaque;
//! * `discharge_provably_safe_pointer_asserts` turns a provably safe alignment or null
//!   Assert into a Goto, deleting its U point with its panic;
//! * a `mem::drop` Call becomes a model `Drop`;
//! * FalseUnwind and FalseEdge become Goto.

use std::collections::{HashSet, VecDeque};

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    BasicBlock, BlockId, Operand, Place, Rvalue, Statement, SysrootItem, Terminator, UnwindEdge,
    VerifiableBody,
};

use super::TinvBodyFacts;

/// Which callees a step-1 exact model states cannot unwind, for every panic strategy.
///
/// The ONLY nounwind exemption in v1 (design B5). It is keyed on the callee's DefId-derived
/// identity, never on display text and never on the call's `UnwindEdge`.
pub trait ExactCallModels {
    /// Whether `call` (a `Terminator::Call`) is modelled exactly and cannot unwind.
    fn is_nounwind(&self, body: &VerifiableBody, call: &Terminator) -> bool;
}

/// No exemption: every call owes U.
pub struct NoExactModels;

impl ExactCallModels for NoExactModels {
    fn is_nounwind(&self, _body: &VerifiableBody, _call: &Terminator) -> bool {
        false
    }
}

/// The exact sysroot models that run no user code and cannot panic for ANY `T`:
/// `core::mem::replace` and `core::mem::swap` are a read and two writes of `T` by value.
/// `mem::take` is NOT here: it calls `T::default()`, which may be user code; admitting it
/// needs the place's type (an integer or a std `Vec`), which is step 1's model row.
pub struct SysrootExactModels;

impl ExactCallModels for SysrootExactModels {
    fn is_nounwind(&self, _body: &VerifiableBody, call: &Terminator) -> bool {
        let Terminator::Call { callee_key: Some(key), .. } = call else { return false };
        key.krate_is_real_sysroot
            && matches!(key.sysroot_item, Some(SysrootItem::MemReplace | SysrootItem::MemSwap))
    }
}

/// When a U point's invariant check must fail for the panic to be taken.
#[derive(Debug, Clone)]
pub enum UFailure {
    /// An `Assert` panics exactly when `cond != expected`.
    AssertFails { cond: Operand, expected: bool },
    /// A call or a drop may panic whenever it runs.
    Always,
}

/// The state the invariant is checked in on the unwind edge.
#[derive(Debug, Clone)]
pub enum UState {
    /// The state before the terminator.
    Pre,
    /// The state before a call, with every place the call may write havocked by the SAME
    /// `callee_write_set` summary its normal successor uses (never a normal-return
    /// postcondition: the callee did not return).
    PreCallHavoc,
    /// The state before a drop, with the dropped place havocked: drop glue ran on it, or
    /// part of it, before the panic.
    PreHavoc(Place),
    /// A drop-and-replace (`p = v` on a place that needs dropping): rustc's unwind path
    /// performs the same assignment before continuing to unwind, so the state is the
    /// pre-state with `place := rvalue`. Recognised structurally on the NORMAL path
    /// ([`replace_assign`]), because the cleanup copy does not exist under `panic=abort`.
    PreAssign { place: Place, rvalue: Rvalue },
}

/// Why a terminator cannot be classified: the certificate is withheld (design G7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum URefusal {
    /// The extractor lost the terminator's meaning and its edges.
    OpaqueTerminator,
    /// A tail call leaves the frame; its expansion writes a synthesised edge.
    TailCall,
    /// A terminator variant added after this classifier was written.
    UnknownTerminator,
}

/// The classification of one block's terminator.
#[derive(Debug, Clone)]
pub enum UPoint {
    /// No invariant is owed on an unwind edge here.
    None,
    /// The invariant is owed on the unwind edge, in `state`, when `failure` holds.
    Owed { failure: UFailure, state: UState },
    /// The certificate is withheld for every candidate type this body touches.
    Refuse(URefusal),
}

/// The model's partition of a body's reachable blocks.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BodyRegions {
    /// Blocks reachable from `bb0` through normal successors.
    pub normal: HashSet<BlockId>,
    /// Blocks reachable only through an unwind (cleanup) edge.
    pub cleanup: HashSet<BlockId>,
}

/// The successors of `term` taken when it does not panic. The cleanup block of a Call,
/// Assert or Drop is never one; an Opaque's targets are all treated as normal, since the
/// extractor cannot say which of them was rustc's cleanup block.
#[must_use]
pub fn normal_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().map(|(_, block)| *block).chain(std::iter::once(*otherwise)).collect()
        }
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => Vec::new(),
        // Unknown variants: no successor is claimed; `u_point` refuses them.
        _ => Vec::new(),
    }
}

fn unwind_edge(term: &Terminator) -> Option<&UnwindEdge> {
    match term {
        Terminator::Call { unwind, .. }
        | Terminator::Assert { unwind, .. }
        | Terminator::Drop { unwind, .. } => Some(unwind),
        _ => None,
    }
}

pub(super) fn for_each_normal_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    match term {
        Terminator::Goto(target)
        | Terminator::Assert { target, .. }
        | Terminator::Drop { target, .. } => f(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for (_, block) in targets {
                f(*block);
            }
            f(*otherwise);
        }
        Terminator::Call { target, .. } => {
            if let Some(target) = target {
                f(*target);
            }
        }
        Terminator::Opaque { targets, .. } => {
            for target in targets {
                f(*target);
            }
        }
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => {}
        _ => {}
    }
}

pub(super) fn for_each_all_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    for_each_normal_successor(term, &mut f);
    if let Some(target) = unwind_edge(term).and_then(UnwindEdge::cleanup_target) {
        f(target);
    }
}

pub(super) enum BlockIndex<'a> {
    Identity(&'a [BasicBlock]),
    Map(FxHashMap<BlockId, &'a BasicBlock>),
}

impl<'a> BlockIndex<'a> {
    #[inline]
    pub(super) fn get(&self, id: &BlockId) -> Option<&'a BasicBlock> {
        match self {
            BlockIndex::Identity(blocks) => blocks.get(id.0),
            BlockIndex::Map(map) => map.get(id).copied(),
        }
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        match self {
            BlockIndex::Identity(blocks) => blocks.len(),
            BlockIndex::Map(map) => map.len(),
        }
    }
}

pub(super) fn block_index(body: &VerifiableBody) -> BlockIndex<'_> {
    // PERF-COMPILER-VCGEN-698: canonical dense `BlockId`s (`b.id.0 == i`) need
    // zero heap allocation and resolve in O(1) by slice index.
    if body.blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        return BlockIndex::Identity(&body.blocks);
    }
    let mut out = FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    for block in &body.blocks {
        out.insert(block.id, block);
    }
    BlockIndex::Map(out)
}

fn reach<S: Default + Extend<BlockId>>(
    index: &BlockIndex<'_>,
    roots: impl IntoIterator<Item = BlockId>,
    mut step: impl FnMut(&Terminator, &mut VecDeque<BlockId>),
) -> S
where
    for<'a> &'a S: IntoIterator<Item = &'a BlockId>,
{
    let mut seen: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(index.len(), Default::default());
    let mut out = S::default();
    let mut queue: VecDeque<BlockId> = roots.into_iter().collect();
    while let Some(id) = queue.pop_front() {
        let Some(block) = index.get(&id) else { continue };
        if seen.insert(id) {
            out.extend(std::iter::once(id));
            step(&block.terminator, &mut queue);
        }
    }
    out
}

/// The cleanup region computed from the MODEL: blocks reachable from `bb0` at all, but not
/// through normal successors alone.
#[must_use]
pub fn body_regions(body: &VerifiableBody) -> BodyRegions {
    let index = block_index(body);
    body_regions_with(&index)
}

pub(super) fn body_regions_with(index: &BlockIndex<'_>) -> BodyRegions {
    let normal: HashSet<BlockId> = reach(index, [BlockId(0)], |term, q| {
        for_each_normal_successor(term, |succ| q.push_back(succ));
    });
    let mut cleanup_roots: Vec<BlockId> = Vec::new();
    for id in &normal {
        if let Some(block) = index.get(id)
            && let Some(target) = unwind_edge(&block.terminator).and_then(UnwindEdge::cleanup_target)
            && !normal.contains(&target)
        {
            cleanup_roots.push(target);
        }
    }
    let cleanup: HashSet<BlockId> = if cleanup_roots.is_empty() {
        HashSet::new()
    } else {
        reach(index, cleanup_roots, |term, q| {
            for_each_all_successor(term, |succ| {
                if !normal.contains(&succ) {
                    q.push_back(succ);
                }
            });
        })
    };
    BodyRegions { normal, cleanup }
}

/// Whether `inner` is `outer` or a place projected from it.
pub(super) fn is_within(inner: &Place, outer: &Place) -> bool {
    inner.local == outer.local && inner.projections.starts_with(&outer.projections)
}

/// The drop-and-replace a `Drop` of `place` begins, if any: rustc's
/// `build_drop_and_replace` makes the Drop's normal target start with `place = value`.
/// `ElaborateDrops` may first split the drop into a ladder of drops of `place`'s
/// projections (and Gotos), so statement-free blocks ending in such a Drop or a Goto are
/// followed, at most `LADDER_LIMIT` of them.
///
/// Every block the walk enters must have exactly ONE predecessor (the block it came
/// from): `build_drop_and_replace` creates its assign block for this drop alone. Without
/// that, a plain scope-end drop whose Goto chain reaches a loop join that some OTHER
/// path enters with `place = v` would be misread as a replace, and its unwind state
/// would claim a value the drop never assigned (adversarial review, 2026-10-05).
#[must_use]
pub fn replace_assign(
    body: &VerifiableBody,
    place: &Place,
    target: BlockId,
) -> Option<(Place, Rvalue)> {
    let index = block_index(body);
    let mut predecessors: FxHashMap<BlockId, usize> =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    for block in &body.blocks {
        for_each_all_successor(&block.terminator, |succ| {
            *predecessors.entry(succ).or_default() += 1;
        });
    }
    // Delegates the single-predecessor Statement::Assign check to replace_assign_with.
    replace_assign_with(&index, &predecessors, place, target)
}

pub(super) fn replace_assign_with(
    index: &BlockIndex<'_>,
    predecessors: &FxHashMap<BlockId, usize>,
    place: &Place,
    target: BlockId,
) -> Option<(Place, Rvalue)> {
    const LADDER_LIMIT: usize = 16;
    let mut at = target;
    for _ in 0..LADDER_LIMIT {
        if at.0 == 0 || predecessors.get(&at).copied() != Some(1) {
            return None;
        }
        let block = index.get(&at)?;
        if let Some(first) = block.stmts.first() {
            return match first {
                Statement::Assign { place: assigned, rvalue, .. } if assigned == place => {
                    Some((assigned.clone(), rvalue.clone()))
                }
                _ => None,
            };
        }
        at = match &block.terminator {
            Terminator::Drop { place: dropped, target, .. } if is_within(dropped, place) => *target,
            Terminator::Goto(next) => *next,
            _ => return None,
        };
    }
    None
}

/// Whether, and in which state, `block`'s terminator owes the invariant on its unwind edge.
#[must_use]
pub fn u_point(
    body: &VerifiableBody,
    block: &BasicBlock,
    regions: &BodyRegions,
    models: &dyn ExactCallModels,
) -> UPoint {
    // A panic inside cleanup aborts (rustc's `UnwindTerminate`); the frame is already
    // unwinding and owes nothing further here. Keyed on region membership from the model,
    // never on the edge value.
    if regions.cleanup.contains(&block.id) {
        return UPoint::None;
    }
    let term = &block.terminator;
    match term {
        Terminator::Goto(_)
        | Terminator::SwitchInt { .. }
        | Terminator::Return
        | Terminator::Unreachable
        | Terminator::Resume => UPoint::None,
        Terminator::Assert { cond, expected, .. } => UPoint::Owed {
            failure: UFailure::AssertFails { cond: cond.clone(), expected: *expected },
            state: UState::Pre,
        },
        Terminator::Call { .. } => {
            if models.is_nounwind(body, term) {
                UPoint::None
            } else {
                UPoint::Owed { failure: UFailure::Always, state: UState::PreCallHavoc }
            }
        }
        Terminator::Drop { place, target, .. } => {
            let state = match replace_assign(body, place, *target) {
                Some((place, rvalue)) => UState::PreAssign { place, rvalue },
                None => UState::PreHavoc(place.clone()),
            };
            UPoint::Owed { failure: UFailure::Always, state }
        }
        Terminator::Opaque { .. } => UPoint::Refuse(URefusal::OpaqueTerminator),
        Terminator::TailCall { .. } => UPoint::Refuse(URefusal::TailCall),
        _ => UPoint::Refuse(URefusal::UnknownTerminator),
    }
}

pub(super) fn u_point_with(
    body: &VerifiableBody,
    index: &BlockIndex<'_>,
    predecessors: &FxHashMap<BlockId, usize>,
    block: &BasicBlock,
    regions: &BodyRegions,
    models: &dyn ExactCallModels,
) -> UPoint {
    if regions.cleanup.contains(&block.id) {
        return UPoint::None;
    }
    let term = &block.terminator;
    match term {
        Terminator::Goto(_)
        | Terminator::SwitchInt { .. }
        | Terminator::Return
        | Terminator::Unreachable
        | Terminator::Resume => UPoint::None,
        Terminator::Assert { cond, expected, .. } => UPoint::Owed {
            failure: UFailure::AssertFails { cond: cond.clone(), expected: *expected },
            state: UState::Pre,
        },
        Terminator::Call { .. } => {
            if models.is_nounwind(body, term) {
                UPoint::None
            } else {
                UPoint::Owed { failure: UFailure::Always, state: UState::PreCallHavoc }
            }
        }
        Terminator::Drop { place, target, .. } => {
            let state = match replace_assign_with(index, predecessors, place, *target) {
                Some((place, rvalue)) => UState::PreAssign { place, rvalue },
                None => UState::PreHavoc(place.clone()),
            };
            UPoint::Owed { failure: UFailure::Always, state }
        }
        Terminator::Opaque { .. } => UPoint::Refuse(URefusal::OpaqueTerminator),
        Terminator::TailCall { .. } => UPoint::Refuse(URefusal::TailCall),
        _ => UPoint::Refuse(URefusal::UnknownTerminator),
    }
}

/// How the rustc-side facts disagree with the model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossCheckMismatch {
    /// The model and rustc count different blocks.
    BlockCount { model: usize, rustc: usize },
    /// The model puts a block in the cleanup region that rustc does not mark `is_cleanup`.
    CleanupNotInRustc(BlockId),
    /// A rustc cleanup block's model terminator carries a `Continue` or `Cleanup` edge,
    /// which rustc's validator forbids (and checks only under `-Zvalidate-mir`).
    CleanupBlockUnwinds(BlockId),
    /// rustc marks a drop-and-replace the structural recogniser does not see.
    ReplaceDropNotRecognised(BlockId),
}

/// Cross-check the model against the rustc facts. Any mismatch withholds the certificate
/// for every candidate type the body touches; a match changes nothing.
///
/// The model's cleanup region may be SMALLER than rustc's (a cleanup block reached through
/// an Opaque's targets, or through an Assert the extractor turned into a Goto, looks
/// normal); that over-approximates the U points and is allowed. It may never be larger.
pub fn cross_check(
    body: &VerifiableBody,
    regions: &BodyRegions,
    facts: &TinvBodyFacts,
) -> Result<(), CrossCheckMismatch> {
    if facts.block_count != body.blocks.len() {
        return Err(CrossCheckMismatch::BlockCount {
            model: body.blocks.len(),
            rustc: facts.block_count,
        });
    }
    let index = block_index(body);
    let mut predecessors: FxHashMap<BlockId, usize> = if facts.replace_drops.is_empty() {
        FxHashMap::default()
    } else {
        let mut preds = FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
        for block in &body.blocks {
            for_each_all_successor(&block.terminator, |succ| {
                *preds.entry(succ).or_default() += 1;
            });
        }
        preds
    };
    cross_check_with(body, &index, &mut Some(&mut predecessors), regions, facts)
}

pub(super) fn cross_check_with(
    body: &VerifiableBody,
    index: &BlockIndex<'_>,
    predecessors: &mut Option<&mut FxHashMap<BlockId, usize>>,
    regions: &BodyRegions,
    facts: &TinvBodyFacts,
) -> Result<(), CrossCheckMismatch> {
    if facts.block_count != body.blocks.len() {
        return Err(CrossCheckMismatch::BlockCount {
            model: body.blocks.len(),
            rustc: facts.block_count,
        });
    }
    if let Some(id) = regions
        .cleanup
        .iter()
        .copied()
        .filter(|id| !facts.cleanup_blocks.contains(id))
        .min_by_key(|id| id.0)
    {
        return Err(CrossCheckMismatch::CleanupNotInRustc(id));
    }
    if let Some(&id) = facts
        .cleanup_blocks
        .iter()
        .filter(|&&id| {
            index
                .get(&id)
                .and_then(|b| unwind_edge(&b.terminator))
                .is_some_and(|edge| matches!(edge, UnwindEdge::Continue | UnwindEdge::Cleanup(_)))
        })
        .min_by_key(|id| id.0)
    {
        return Err(CrossCheckMismatch::CleanupBlockUnwinds(id));
    }
    if !facts.replace_drops.is_empty() {
        let preds = match predecessors.as_deref_mut() {
            Some(preds) => {
                if preds.is_empty() && !body.blocks.is_empty() {
                    preds.reserve(body.blocks.len());
                    for block in &body.blocks {
                        for_each_all_successor(&block.terminator, |succ| {
                            *preds.entry(succ).or_default() += 1;
                        });
                    }
                }
                &*preds
            }
            None => return Ok(()),
        };
        if let Some(&id) = facts
            .replace_drops
            .iter()
            .filter(|&&id| {
                !index.get(&id).is_some_and(|block| match &block.terminator {
                    Terminator::Drop { place, target, .. } => {
                        replace_assign_with(index, preds, place, *target).is_some()
                    }
                    _ => false,
                })
            })
            .min_by_key(|id| id.0)
        {
            return Err(CrossCheckMismatch::ReplaceDropNotRecognised(id));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_types::{
        AssertMessage, CalleeKey, ConstValue, LocalDecl, SourceSpan, Ty, UnwindEdge,
    };

    use super::*;

    fn same(a: &UPoint, b: &UPoint) -> bool {
        format!("{a:?}") == format!("{b:?}")
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn body(blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody {
            locals: (0..4)
                .map(|index| LocalDecl {
                    index,
                    ty: Ty::Int { width: 64, signed: false },
                    name: None,
                })
                .collect(),
            blocks,
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn call(target: Option<usize>, unwind: UnwindEdge, key: Option<CalleeKey>) -> Terminator {
        Terminator::Call {
            func: "f".into(),
            args: vec![],
            dest: Place::local(2),
            target: target.map(BlockId),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind,
            callee_identity: None,
            callee_key: key,
        }
    }

    fn assert_term(target: usize, unwind: UnwindEdge) -> Terminator {
        Terminator::Assert {
            cond: Operand::Copy(Place::local(3)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(target),
            span: SourceSpan::default(),
            unwind,
        }
    }

    fn drop_term(place: Place, target: usize, unwind: UnwindEdge) -> Terminator {
        Terminator::Drop { place, target: BlockId(target), span: SourceSpan::default(), unwind }
    }

    fn assign(place: Place, value: i128) -> Statement {
        Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
            span: SourceSpan::default(),
        }
    }

    /// bb0: call -> bb1, unwind -> bb2 (cleanup); bb1: return; bb2: resume.
    fn call_with_cleanup(unwind: UnwindEdge) -> VerifiableBody {
        body(vec![
            block(0, vec![], call(Some(1), unwind, None)),
            block(1, vec![], Terminator::Return),
            block(2, vec![], Terminator::Resume),
        ])
    }

    fn points(b: &VerifiableBody) -> Vec<UPoint> {
        let regions = body_regions(b);
        b.blocks.iter().map(|blk| u_point(b, blk, &regions, &NoExactModels)).collect()
    }

    #[test]
    fn the_u_points_do_not_depend_on_the_unwind_edge() {
        // `panic=unwind` gives the call a cleanup edge; `panic=abort` rewrites it to
        // `Unreachable` and deletes the cleanup block. The call owes U either way.
        let unwind = call_with_cleanup(UnwindEdge::Cleanup(BlockId(2)));
        let mut abort = call_with_cleanup(UnwindEdge::Unreachable);
        abort.blocks.pop();
        let owed = UPoint::Owed { failure: UFailure::Always, state: UState::PreCallHavoc };
        assert!(same(&points(&unwind)[0], &owed));
        assert!(same(&points(&abort)[0], &owed));
        // The cleanup block itself owes nothing.
        assert!(matches!(points(&unwind)[2], UPoint::None));
        let regions = body_regions(&unwind);
        assert!(regions.cleanup.contains(&BlockId(2)) && !regions.normal.contains(&BlockId(2)));
    }

    #[test]
    fn asserts_owe_u_in_the_pre_state_and_a_diverging_call_owes_it_too() {
        let b = body(vec![
            block(0, vec![], assert_term(1, UnwindEdge::Continue)),
            block(1, vec![], call(None, UnwindEdge::Continue, None)),
        ]);
        let p = points(&b);
        assert!(same(
            &p[0],
            &UPoint::Owed {
                failure: UFailure::AssertFails {
                    cond: Operand::Copy(Place::local(3)),
                    expected: true
                },
                state: UState::Pre,
            }
        ));
        assert!(same(
            &p[1],
            &UPoint::Owed { failure: UFailure::Always, state: UState::PreCallHavoc }
        ));
    }

    #[test]
    fn only_the_exact_nounwind_sysroot_models_are_exempt() {
        let key = |item, real| CalleeKey {
            sysroot_item: Some(item),
            krate_is_real_sysroot: real,
            krate_name_is_ambiguous: false,
            stable_crate_id: 0,
            krate_name: "core".into(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        };
        for (k, exempt) in [
            (key(SysrootItem::MemReplace, true), true),
            (key(SysrootItem::MemSwap, true), true),
            // Another exact model is not a nounwind claim: `vec![x; n]` allocates and
            // clones. (`mem::take`, which runs `T::default()`, stays out the same way.)
            (key(SysrootItem::VecFromElem, true), false),
            // A forged crate is not the sysroot.
            (key(SysrootItem::MemReplace, false), false),
        ] {
            let b = body(vec![
                block(0, vec![], call(Some(1), UnwindEdge::Continue, Some(k))),
                block(1, vec![], Terminator::Return),
            ]);
            let regions = body_regions(&b);
            let got = u_point(&b, &b.blocks[0], &regions, &SysrootExactModels);
            assert_eq!(matches!(got, UPoint::None), exempt, "{got:?}");
            // Without the models nothing is exempt.
            assert!(!matches!(u_point(&b, &b.blocks[0], &regions, &NoExactModels), UPoint::None));
        }
    }

    #[test]
    fn a_drop_and_replace_is_recognised_on_the_normal_path_through_a_ladder() {
        let field = Place::field(1, 0);
        // bb0: drop(_1.0) -> bb1; bb1: drop(_1.0.2) -> bb2 (a ladder step); bb2: _1.0 = 7.
        let mut deeper = field.clone();
        deeper.projections.push(trust_types::Projection::Field(2));
        let b = body(vec![
            block(0, vec![], drop_term(field.clone(), 1, UnwindEdge::Unreachable)),
            block(1, vec![], drop_term(deeper, 2, UnwindEdge::Unreachable)),
            block(2, vec![assign(field.clone(), 7)], Terminator::Return),
        ]);
        let UPoint::Owed { state: UState::PreAssign { place, .. }, .. } = &points(&b)[0] else {
            panic!("expected a drop-and-replace state, got {:?}", points(&b)[0]);
        };
        assert_eq!(place, &field);
        // A plain drop (the next statement assigns a different place) havocs the place.
        let plain = body(vec![
            block(0, vec![], drop_term(field.clone(), 1, UnwindEdge::Unreachable)),
            block(1, vec![assign(Place::local(2), 7)], Terminator::Return),
        ]);
        assert!(same(
            &points(&plain)[0],
            &UPoint::Owed { failure: UFailure::Always, state: UState::PreHavoc(field) }
        ));
    }

    #[test]
    fn a_plain_drop_whose_goto_chain_reaches_a_join_is_not_a_replace() {
        // bb0: drop(_1.0) -> bb1; bb1: goto bb3; bb2: goto bb3 (another path);
        // bb3 (a join): _1.0 = 7. The drop's own chain does not own bb3.
        let field = Place::field(1, 0);
        let b = body(vec![
            block(0, vec![], drop_term(field.clone(), 1, UnwindEdge::Unreachable)),
            block(1, vec![], Terminator::Goto(BlockId(3))),
            block(2, vec![], Terminator::Goto(BlockId(3))),
            block(3, vec![assign(field.clone(), 7)], Terminator::Return),
        ]);
        assert!(replace_assign(&b, &field, BlockId(1)).is_none());
        assert!(same(
            &points(&b)[0],
            &UPoint::Owed { failure: UFailure::Always, state: UState::PreHavoc(field) }
        ));
    }

    #[test]
    fn lost_edges_refuse() {
        let b = body(vec![block(
            0,
            vec![],
            Terminator::Opaque {
                kind: "InlineAsm".into(),
                targets: vec![],
                span: SourceSpan::default(),
            },
        )]);
        assert!(matches!(points(&b)[0], UPoint::Refuse(URefusal::OpaqueTerminator)));
    }

    #[test]
    fn the_cross_check_withholds_on_every_disagreement() {
        let b = call_with_cleanup(UnwindEdge::Cleanup(BlockId(2)));
        let regions = body_regions(&b);
        let good = TinvBodyFacts {
            cleanup_blocks: [BlockId(2)].into_iter().collect(),
            replace_drops: HashSet::new(),
            block_count: 3,
            ..Default::default()
        };
        assert_eq!(cross_check(&b, &regions, &good), Ok(()));
        let mut count = good.clone();
        count.block_count = 4;
        assert!(matches!(
            cross_check(&b, &regions, &count),
            Err(CrossCheckMismatch::BlockCount { .. })
        ));
        let mut missing = good.clone();
        missing.cleanup_blocks.clear();
        assert_eq!(
            cross_check(&b, &regions, &missing),
            Err(CrossCheckMismatch::CleanupNotInRustc(BlockId(2)))
        );
        // A rustc cleanup block whose model terminator unwinds again.
        let mut nested = call_with_cleanup(UnwindEdge::Cleanup(BlockId(2)));
        nested.blocks[2].terminator = call(Some(1), UnwindEdge::Continue, None);
        let regions = body_regions(&nested);
        assert_eq!(
            cross_check(&nested, &regions, &good),
            Err(CrossCheckMismatch::CleanupBlockUnwinds(BlockId(2)))
        );
        // rustc says drop-and-replace; the model's next statement assigns something else.
        let plain = body(vec![
            block(0, vec![], drop_term(Place::field(1, 0), 1, UnwindEdge::Unreachable)),
            block(1, vec![assign(Place::local(2), 7)], Terminator::Return),
        ]);
        let facts = TinvBodyFacts {
            cleanup_blocks: HashSet::new(),
            replace_drops: [BlockId(0)].into_iter().collect(),
            block_count: 2,
            ..Default::default()
        };
        assert_eq!(
            cross_check(&plain, &body_regions(&plain), &facts),
            Err(CrossCheckMismatch::ReplaceDropNotRecognised(BlockId(0)))
        );
    }
}
