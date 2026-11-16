//! The producer's REFUSAL LEDGER and the one rule for rolling it back.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! `LowerCx::unsupported` is the ONLY record that a body was not lowered faithfully:
//! `crate_module::splice_refusal` admits a body exactly when it is empty, and the codegen
//! license, the F1 frontend (`-Ztrust-cg-frontend=trust-ir`) and `--emit=trust-ir` all
//! consume what the splice admits. A tag is therefore not a diagnostic, it is the refusal.
//!
//! The producer has NO node rollback: `push_node` only appends and `seal_with` only moves the
//! open block into `blocks`. A lowering attempt that fails leaves every node it emitted in the
//! function. Many fail-closed arms rely on exactly that: they emit a STUB and push a tag that
//! "keeps the gate red" — `capture_arm` seals an arm with no value `Unreachable`, a block keeps
//! lowering past a statement that failed, a labeled block's valueless tail seals `Unreachable`.
//! The stub is harmless ONLY while its tag survives.
//!
//! THE DEFECT THIS MODULE CLOSES (2026-09-29, adversarial review finding F1). The ledger used
//! to be a bare `Vec`, and 49 sites rolled it back with `truncate(mark)`. The call-argument
//! lane truncated on ANY sealed cursor, on the belief that a sealed cursor means the argument
//! diverged. For `consume(if c { <declined value> } else { return 0 })` the then-arm was a
//! fail-closed `Unreachable` stub and the else-arm a real `return`; the truncate erased the
//! stub's tag, and the body was spliced as `condbr c; then: unreachable; else: ret 0` with
//! `unsupported == []` — rustc computes a value and calls `consume` where the spliced body
//! executes `unreachable`.
//!
//! THE RULE. A tag may be discarded only when NOTHING the attempt that pushed it emitted
//! survives with a meaning. Since nothing is ever un-emitted, that is decided on the IR the
//! attempt actually left behind, by the IR's own definition of "means nothing if unused":
//!
//!   * no block was sealed or started, the cursor never moved, and no fail-closed stub was
//!     sealed ([`IrPos`] is identical in every coordinate except the open block's length); and
//!   * every node the attempt appended to the open block is removable by dead-code elimination
//!     when its result is unused (`!Inst::has_observable_effects()` — the soundness-critical
//!     DCE predicate trust-ir owns: no store, call, assert, terminator, borrow, drop, ...).
//!
//! An attempt that left anything else behind keeps its tags, and the refusal is recorded with
//! [`ROLLBACK_REFUSED`] so every body the rule refuses names the rollback that would have
//! laundered it. The ledger has no `truncate`: [`RefusalLedger::discard_if_inert`] is the only
//! way to remove a tag, and it takes a [`FailedAttempt`] only [`RefusalLedger::close_failed`]
//! can build, from the IR itself.
//!
//! A genuine divergence (`return`, `break`, a `!`-typed call) pushes no tag at all, so a
//! rollback over one never had anything to discard — which is why the call-argument lane's
//! sealed arm no longer rolls back anything.

use std::ops::Range;

use trust_ir::{BlockId, InstrNode};

/// One refusal: where, and the tag.
pub(crate) type Refusal = (String, &'static str);

/// The tag recorded when a rollback is REFUSED because the failed attempt left IR behind.
pub(crate) const ROLLBACK_REFUSED: &str = "Rollback(failed attempt left IR behind)";

/// Where the producer's IR cursor stood. Built only by [`IrPos::observe`] from the live
/// cursor; compared, never interpreted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct IrPos {
    /// `blocks.len()`: a seal moves the open block here, so any seal changes it.
    blocks: usize,
    /// The open block.
    cur_id: BlockId,
    /// `cur.len()`: nodes appended to the open block.
    cur_len: usize,
    /// Whether the open block is sealed.
    sealed: bool,
    /// Every cursor movement (`start_block`, `seal_with`, `snapshot_open`, an arm re-open):
    /// a window that moves the cursor away and back is still a window that emitted.
    cursor_moves: u64,
    /// Fail-closed stub seals (`LowerCx::seal_fail_closed`), counted separately from genuine
    /// terminators so a seal records WHY it sealed.
    fail_closed_seals: u64,
}

impl IrPos {
    pub(crate) fn observe(
        blocks: usize,
        cur_id: BlockId,
        cur_len: usize,
        sealed: bool,
        cursor_moves: u64,
        fail_closed_seals: u64,
    ) -> Self {
        IrPos { blocks, cur_id, cur_len, sealed, cursor_moves, fail_closed_seals }
    }

    pub(crate) fn fail_closed_seals(&self) -> u64 {
        self.fail_closed_seals
    }
}

/// A watermark taken immediately BEFORE a lowering attempt: the ledger length and the cursor.
#[derive(Clone, Copy, Debug)]
pub(crate) struct AttemptMark {
    tags: usize,
    ir: IrPos,
}

impl AttemptMark {
    /// The ledger length at the mark (for the `len() == mark` idioms that decide, without
    /// discarding anything, whether an attempt pushed a tag).
    pub(crate) fn tags(&self) -> usize {
        self.tags
    }

    pub(crate) fn ir(&self) -> IrPos {
        self.ir
    }
}

/// A CLOSED failed attempt: the tags it pushed and whether it left IR that means something.
/// Constructed only by [`RefusalLedger::close_failed`]; consumed by
/// [`RefusalLedger::discard_if_inert`].
#[derive(Debug)]
#[must_use = "a closed failed attempt is either discarded or deliberately kept"]
pub(crate) struct FailedAttempt {
    tags: Range<usize>,
    inert: bool,
}

impl FailedAttempt {
    /// True iff the attempt left nothing but DCE-removable nodes in the open block.
    #[cfg(test)]
    pub(crate) fn is_inert(&self) -> bool {
        self.inert
    }
}

/// The refusal ledger. Deliberately NOT a `Vec`: there is no `truncate`, no `pop`, no `clear`.
#[derive(Debug, Default)]
pub(crate) struct RefusalLedger {
    tags: Vec<Refusal>,
}

impl RefusalLedger {
    pub(crate) fn new(tags: Vec<Refusal>) -> Self {
        RefusalLedger { tags }
    }

    pub(crate) fn push(&mut self, r: Refusal) {
        self.tags.push(r);
    }

    pub(crate) fn len(&self) -> usize {
        self.tags.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.tags.is_empty()
    }

    pub(crate) fn get(&self, i: usize) -> Option<&Refusal> {
        self.tags.get(i)
    }

    pub(crate) fn into_vec(self) -> Vec<Refusal> {
        self.tags
    }

    /// Mark the ledger and the cursor immediately before an attempt.
    pub(crate) fn mark(&self, ir: IrPos) -> AttemptMark {
        AttemptMark { tags: self.tags.len(), ir }
    }

    /// Close an attempt that FAILED (or that a lane is about to abandon): judge, from the IR
    /// it actually left behind, whether its tags may be discarded. `now` is the cursor right
    /// after the attempt and `open_block` the open block's nodes (`LowerCx::cur`).
    pub(crate) fn close_failed(
        &self,
        m: AttemptMark,
        now: IrPos,
        open_block: &[InstrNode],
    ) -> FailedAttempt {
        let same_cursor = now.blocks == m.ir.blocks
            && now.cur_id == m.ir.cur_id
            && now.sealed == m.ir.sealed
            && now.cursor_moves == m.ir.cursor_moves
            && now.fail_closed_seals == m.ir.fail_closed_seals
            && now.cur_len >= m.ir.cur_len
            && now.cur_len == open_block.len();
        let inert = same_cursor
            && open_block[m.ir.cur_len..].iter().all(|n| !n.inst.has_observable_effects());
        // A ledger shorter than the mark cannot happen (nothing removes a tag except
        // `discard_if_inert`, over a range that starts at a LATER mark); if it ever did, the
        // empty range discards nothing and the attempt is judged non-inert.
        let end = self.tags.len();
        let inert = inert && end >= m.tags;
        FailedAttempt { tags: m.tags..end.max(m.tags), inert }
    }

    /// Close a failed attempt WITHOUT discarding anything: the lane has decided its tags stand
    /// (the call-argument lane's sealed arm). If it pushed any, record [`ROLLBACK_REFUSED`] at
    /// `site`, so a body this refuses names the rollback that used to launder it.
    pub(crate) fn keep(&mut self, a: FailedAttempt, site: &str) {
        if !a.tags.is_empty() {
            self.tags.push((site.to_string(), ROLLBACK_REFUSED));
        }
    }

    /// Discard a failed attempt's tags IFF it left nothing that means something. Otherwise
    /// keep them and record [`ROLLBACK_REFUSED`] at `site`, so the refused body names the
    /// rollback that would have laundered it. Returns whether the tags were discarded.
    ///
    /// Tags pushed AFTER the attempt closed (by a lane that then succeeded) are never touched:
    /// only the attempt's own range is removed.
    pub(crate) fn discard_if_inert(&mut self, a: FailedAttempt, site: &str) -> bool {
        if a.inert && a.tags.end <= self.tags.len() {
            self.tags.drain(a.tags);
            true
        } else {
            if !a.tags.is_empty() {
                self.tags.push((site.to_string(), ROLLBACK_REFUSED));
            }
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::{Constant, Inst, Ty, ValueId};

    use super::*;

    fn pos(blocks: usize, cur_len: usize, sealed: bool, moves: u64, fcs: u64) -> IrPos {
        IrPos::observe(blocks, BlockId::new(0), cur_len, sealed, moves, fcs)
    }

    fn konst(v: u32) -> InstrNode {
        InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(1) })
            .with_result(ValueId::new(v))
    }

    fn store() -> InstrNode {
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            volatile: false,
            align: None,
        })
    }

    fn tag(what: &'static str) -> Refusal {
        ("at".to_string(), what)
    }

    #[test]
    fn test_ledger_probe_that_emitted_nothing_discards_its_tags() {
        let mut l = RefusalLedger::new(vec![tag("before")]);
        let m = l.mark(pos(1, 3, false, 5, 0));
        l.push(tag("probe"));
        let a = l.close_failed(m, pos(1, 3, false, 5, 0), &[konst(0), konst(1), konst(2)]);
        assert!(a.is_inert());
        assert!(l.discard_if_inert(a, "probe"));
        assert_eq!(l.into_vec(), vec![tag("before")], "tags before the mark are never touched");
    }

    #[test]
    fn test_ledger_attempt_that_left_only_removable_nodes_discards() {
        let mut l = RefusalLedger::default();
        let open = vec![konst(0), konst(1)];
        let m = l.mark(pos(0, 1, false, 0, 0));
        l.push(tag("attempt"));
        let a = l.close_failed(m, pos(0, 2, false, 0, 0), &open);
        assert!(l.discard_if_inert(a, "site"));
        assert!(l.is_empty());
    }

    #[test]
    fn test_ledger_attempt_that_left_an_effect_keeps_its_tags() {
        let mut l = RefusalLedger::default();
        let open = vec![konst(0), store()];
        let m = l.mark(pos(0, 1, false, 0, 0));
        l.push(tag("attempt"));
        let a = l.close_failed(m, pos(0, 2, false, 0, 0), &open);
        assert!(!a.is_inert());
        assert!(!l.discard_if_inert(a, "site"));
        assert_eq!(l.into_vec(), vec![tag("attempt"), ("site".to_string(), ROLLBACK_REFUSED)]);
    }

    /// F1 itself, at the ledger: an attempt that SEALED (the stub's `Unreachable`, or a real
    /// `return` after a refused statement) left a terminator behind — never discardable.
    #[test]
    fn test_ledger_attempt_that_sealed_keeps_its_tags() {
        let mut l = RefusalLedger::default();
        let m = l.mark(pos(2, 4, false, 7, 0));
        l.push(tag("If(then no value)"));
        let a = l.close_failed(m, pos(4, 0, true, 10, 1), &[]);
        assert!(!a.is_inert());
        assert!(!l.discard_if_inert(a, "call-arg"));
        assert_eq!(l.len(), 2);
    }

    #[test]
    fn test_ledger_cursor_moved_away_and_back_is_not_inert() {
        let mut l = RefusalLedger::default();
        let m = l.mark(pos(0, 0, false, 3, 0));
        l.push(tag("attempt"));
        let a = l.close_failed(m, pos(0, 0, false, 5, 0), &[]);
        assert!(!a.is_inert());
    }

    #[test]
    fn test_ledger_fail_closed_seal_in_window_is_not_inert() {
        let mut l = RefusalLedger::default();
        let m = l.mark(pos(0, 0, false, 0, 2));
        l.push(tag("attempt"));
        let a = l.close_failed(m, pos(0, 0, false, 0, 3), &[]);
        assert!(!a.is_inert());
    }

    /// A lane that closes the failed attempt, then SUCCEEDS with tags of its own, discards
    /// only the failed attempt's range.
    #[test]
    fn test_ledger_discard_removes_only_the_failed_range() {
        let mut l = RefusalLedger::new(vec![tag("before")]);
        let m = l.mark(pos(0, 0, false, 0, 0));
        l.push(tag("failed-1"));
        l.push(tag("failed-2"));
        let a = l.close_failed(m, pos(0, 0, false, 0, 0), &[]);
        l.push(tag("success-lane"));
        assert!(l.discard_if_inert(a, "site"));
        assert_eq!(l.into_vec(), vec![tag("before"), tag("success-lane")]);
    }

    #[test]
    fn test_ledger_keep_never_discards_and_attributes() {
        let mut l = RefusalLedger::default();
        let m = l.mark(pos(0, 0, false, 0, 0));
        l.push(tag("attempt"));
        let a = l.close_failed(m, pos(0, 0, false, 0, 0), &[]);
        assert!(a.is_inert());
        l.keep(a, "site");
        assert_eq!(l.into_vec(), vec![tag("attempt"), ("site".to_string(), ROLLBACK_REFUSED)]);
    }

    #[test]
    fn test_ledger_refusal_with_nothing_to_discard_records_nothing() {
        let mut l = RefusalLedger::default();
        let m = l.mark(pos(0, 0, false, 0, 0));
        let a = l.close_failed(m, pos(1, 0, true, 1, 0), &[]);
        assert!(!l.discard_if_inert(a, "site"));
        assert!(l.is_empty(), "a genuine divergence pushed no tag, so there is nothing to keep");
    }
}
