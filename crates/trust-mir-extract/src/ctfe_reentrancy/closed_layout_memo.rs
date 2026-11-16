// Trust: invocation-local reuse of independently completed layout-safety walks.
// No layout or certificate is cached. Exact closed type facts, raw source
// bindings and fully completed guarded projection reads remain distinct and
// confined to one immutable compiler context/policy epoch.

const MAX_COMPLETED: usize = 256;
const MAX_FRAMES: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ProjectionRhsPolicy {
    LeafConstants,
    WrittenOnly,
}

pub(super) struct ClosedLayoutMemo<K> {
    enabled: bool,
    epoch: Option<(u64, fn() -> Option<u64>)>,
    completed: Vec<K>,
    written_projections: Vec<(K, Option<K>)>,
    projection_reads: Vec<(K, ProjectionRhsPolicy, Option<(K, K)>)>,
    frames: Vec<(usize, bool)>,
}

impl<K: Copy + Eq> ClosedLayoutMemo<K> {
    pub(super) fn new(enabled: bool) -> Self {
        Self {
            enabled,
            epoch: None,
            completed: Vec::new(),
            written_projections: Vec::new(),
            projection_reads: Vec::new(),
            frames: Vec::new(),
        }
    }

    pub(super) fn for_epoch(epoch: Option<u64>, read: fn() -> Option<u64>) -> Self {
        let mut memo = Self::new(epoch.is_some());
        memo.epoch = epoch.map(|epoch| (epoch, read));
        memo
    }

    pub(super) fn policy_valid(&self) -> bool {
        self.epoch.is_none_or(|(epoch, read)| read() == Some(epoch))
    }

    fn valid(&self) -> bool {
        self.enabled && self.policy_valid()
    }

    pub(super) fn contains(&self, key: K) -> bool {
        self.valid() && self.completed.contains(&key)
    }

    pub(super) fn is_empty(&self) -> bool {
        !self.valid()
            || (self.completed.is_empty()
                && self.written_projections.is_empty()
                && self.projection_reads.is_empty())
    }

    fn slot_count(&self) -> usize {
        self.completed.len() + self.written_projections.len() + self.projection_reads.len()
    }

    /// This slot is populated only after the exact reader has completed every
    /// argument/header/candidate/solver/RHS check. It is not a raw-written-RHS
    /// upgrade, a type-layout result, or a bare trait-goal answer.
    fn written_consistent(&self, key: K, written: K) -> bool {
        self.written_projections.iter().all(|(k, prior)| *k != key || *prior == Some(written))
            && self.projection_reads.iter().all(|(k, _, prior)| {
                *k != key || prior.is_some_and(|(_, old_written)| old_written == written)
            })
    }

    fn poison_projection(&mut self, key: K) {
        // A contradiction always has at least one existing slot. Revocation
        // mutates those slots even when the shared allocation cap is full.
        for (k, value) in &mut self.written_projections {
            if *k == key {
                *value = None;
            }
        }
        for (k, _, value) in &mut self.projection_reads {
            if *k == key {
                *value = None;
            }
        }
    }

    pub(super) fn record_completed_projection(
        &mut self,
        key: K,
        policy: ProjectionRhsPolicy,
        value: K,
        written: K,
    ) {
        if !self.valid() {
            return;
        }
        if !self.written_consistent(key, written) {
            self.poison_projection(key);
            return;
        }
        if let Some((_, _, previous)) =
            self.projection_reads.iter().find(|(k, p, _)| *k == key && *p == policy)
        {
            if *previous != Some((value, written)) {
                self.poison_projection(key);
            }
        } else if self.slot_count() < MAX_COMPLETED {
            self.projection_reads.push((key, policy, Some((value, written))));
        }
    }

    pub(super) fn completed_projection(
        &self,
        key: K,
        policy: ProjectionRhsPolicy,
    ) -> Option<(K, K)> {
        if !self.valid()
            || self.projection_reads.iter().any(|(k, _, result)| *k == key && result.is_none())
        {
            return None;
        }
        self.projection_reads
            .iter()
            .find(|(k, p, _)| *k == key && *p == policy)
            .and_then(|(_, _, result)| *result)
    }

    /// Data custody from a successful guarded reader, never a safety/trait answer.
    /// A conflicting key is permanently tombstoned, including in child copies.
    pub(super) fn record_written_projection(&mut self, key: K, written: K) {
        if !self.valid() {
            return;
        }
        if !self.written_consistent(key, written) {
            self.poison_projection(key);
            return;
        }
        if !self.written_projections.iter().any(|(k, _)| *k == key)
            && self.slot_count() < MAX_COMPLETED
        {
            self.written_projections.push((key, Some(written)));
        }
    }

    pub(super) fn written_projection(&self, key: K) -> Option<K> {
        self.valid()
            .then(|| {
                self.written_projections
                    .iter()
                    .find(|(k, _)| *k == key)
                    .and_then(|(_, value)| *value)
            })
            .flatten()
    }

    pub(super) fn has_written_projection_slot(&self, key: K) -> bool {
        self.valid() && self.written_projections.iter().any(|(k, _)| *k == key)
    }

    pub(super) fn argument_scope(&self) -> Self {
        // Projection arguments are independently walked with the original carried
        // depth. Only closed facts may cross into their fresh ancestor stack.
        // Each scope retains the same fixed bounds; argument facts do not escape
        // back into the enclosing walk.
        if !self.valid() {
            return Self::new(false);
        }
        Self {
            enabled: self.enabled,
            epoch: self.epoch,
            completed: self.completed.clone(),
            written_projections: self.written_projections.clone(),
            projection_reads: self.projection_reads.clone(),
            frames: Vec::new(),
        }
    }

    pub(super) fn begin(&mut self, outer_ancestors: usize) -> Option<usize> {
        if !self.valid() || self.frames.len() == MAX_FRAMES {
            return None;
        }
        let frame = self.frames.len();
        self.frames.push((outer_ancestors, false));
        Some(frame)
    }

    pub(super) fn backedge(&mut self, ancestor: usize, exact_type_and_args: bool) {
        for (outer, conditional) in &mut self.frames {
            // A DefId-only recursive shortcut is the old walk's conservative rule,
            // not a closed proof for a different generic instantiation.
            if !exact_type_and_args || ancestor < *outer {
                *conditional = true;
            }
        }
    }

    pub(super) fn finish(&mut self, key: K, frame: Option<usize>, success: bool) {
        let Some(frame) = frame else { return };
        assert_eq!(frame + 1, self.frames.len());
        let (_, conditional) = self.frames.pop().expect("tracked layout frame");
        if success && self.valid() && !conditional && self.slot_count() < MAX_COMPLETED {
            self.completed.push(key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    std::thread_local! {
        static TEST_EPOCH: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(Some(1)) };
    }
    fn epoch() -> Option<u64> {
        TEST_EPOCH.with(std::cell::Cell::get)
    }

    #[test]
    fn policy_transition_revokes_hits_copies_and_active_walk_writes_immediately() {
        TEST_EPOCH.with(|e| e.set(Some(1)));
        let mut memo = ClosedLayoutMemo::for_epoch(Some(1), epoch);
        let closed = memo.begin(0);
        memo.finish(1, closed, true);
        memo.record_written_projection(2, 3);
        let copied = memo.argument_scope();
        let active = memo.begin(0);
        TEST_EPOCH.with(|e| e.set(Some(2)));
        assert!(!memo.policy_valid());
        assert!(!memo.contains(1));
        assert_eq!(memo.written_projection(2), None);
        assert!(!copied.contains(1));
        assert_eq!(copied.written_projection(2), None);
        assert!(memo.argument_scope().is_empty());
        memo.finish(4, active, true);
        assert!(!memo.completed.contains(&4));
        TEST_EPOCH.with(|e| e.set(Some(3)));
        assert!(!memo.contains(1));
        TEST_EPOCH.with(|e| e.set(None));
        let mut overflow = ClosedLayoutMemo::for_epoch(None, epoch);
        let frame = overflow.begin(0);
        overflow.finish(1, frame, true);
        assert!(!overflow.contains(1));
    }

    #[test]
    fn completed_projection_reads_are_policy_scoped_bounded_and_revoked() {
        use ProjectionRhsPolicy::{LeafConstants, WrittenOnly};
        TEST_EPOCH.with(|e| e.set(Some(1)));
        let mut memo = ClosedLayoutMemo::for_epoch(Some(1), epoch);
        memo.record_written_projection(1, 2);
        assert_eq!(memo.completed_projection(1, LeafConstants), None);
        memo.record_completed_projection(1, LeafConstants, 3, 2);
        assert_eq!(memo.completed_projection(1, LeafConstants), Some((3, 2)));
        assert_eq!(memo.completed_projection(1, WrittenOnly), None);
        assert_eq!(memo.completed_projection(4, LeafConstants), None);
        let copy = memo.argument_scope();
        assert!(copy.frames.is_empty());
        assert_eq!(copy.completed_projection(1, LeafConstants), Some((3, 2)));
        memo.record_completed_projection(1, LeafConstants, 4, 2);
        memo.record_completed_projection(1, LeafConstants, 3, 2);
        assert_eq!(memo.completed_projection(1, LeafConstants), None);
        assert_eq!(memo.argument_scope().completed_projection(1, LeafConstants), None);
        TEST_EPOCH.with(|e| e.set(Some(2)));
        assert_eq!(copy.completed_projection(1, LeafConstants), None);
        memo.record_completed_projection(5, LeafConstants, 6, 7);
        assert_eq!(memo.completed_projection(5, LeafConstants), None);

        let mut bounded = ClosedLayoutMemo::new(true);
        for k in 0..MAX_COMPLETED {
            bounded.record_written_projection(k, k);
        }
        bounded.record_completed_projection(MAX_COMPLETED, LeafConstants, 1, 1);
        assert_eq!(bounded.completed_projection(MAX_COMPLETED, LeafConstants), None);
        assert_eq!(bounded.slot_count(), MAX_COMPLETED);
        let mut conflict = ClosedLayoutMemo::new(true);
        conflict.record_completed_projection(1, LeafConstants, 3, 2);
        conflict.record_written_projection(1, 2);
        conflict.record_written_projection(1, 9);
        conflict.record_completed_projection(1, LeafConstants, 3, 2);
        assert_eq!(conflict.completed_projection(1, LeafConstants), None);
    }

    #[test]
    fn conflicting_reader_result_revokes_preexisting_other_policy_and_copies() {
        use ProjectionRhsPolicy::{LeafConstants, WrittenOnly};
        let mut memo = ClosedLayoutMemo::new(true);
        memo.record_completed_projection(1, LeafConstants, 3, 2);
        memo.record_completed_projection(1, WrittenOnly, 2, 2);
        assert_eq!(memo.completed_projection(1, WrittenOnly), Some((2, 2)));
        memo.record_completed_projection(1, LeafConstants, 4, 2);
        assert_eq!(memo.completed_projection(1, LeafConstants), None);
        assert_eq!(memo.completed_projection(1, WrittenOnly), None);
        assert_eq!(memo.argument_scope().completed_projection(1, WrittenOnly), None);
        memo.record_completed_projection(1, WrittenOnly, 2, 2);
        assert_eq!(memo.completed_projection(1, WrittenOnly), None);
    }

    #[test]
    fn first_raw_binding_contradiction_revokes_reader_and_cannot_be_reinserted() {
        use ProjectionRhsPolicy::LeafConstants;
        let mut memo = ClosedLayoutMemo::new(true);
        memo.record_completed_projection(1, LeafConstants, 3, 2);
        memo.record_written_projection(1, 9);
        assert_eq!(memo.completed_projection(1, LeafConstants), None);
        assert_eq!(memo.written_projection(1), None);
        memo.record_completed_projection(1, LeafConstants, 3, 2);
        memo.record_written_projection(1, 2);
        assert_eq!(memo.argument_scope().completed_projection(1, LeafConstants), None);
        assert_eq!(memo.argument_scope().written_projection(1), None);
    }

    #[test]
    fn raw_and_every_policy_reconcile_written_identity_in_both_orders() {
        use ProjectionRhsPolicy::{LeafConstants, WrittenOnly};
        for raw_first in [false, true] {
            let mut memo = ClosedLayoutMemo::new(true);
            if raw_first {
                memo.record_written_projection(1, 2);
            } else {
                memo.record_completed_projection(1, WrittenOnly, 2, 2);
            }
            memo.record_completed_projection(1, LeafConstants, 3, 9);
            assert_eq!(memo.completed_projection(1, LeafConstants), None);
            assert_eq!(memo.completed_projection(1, WrittenOnly), None);
            assert_eq!(memo.written_projection(1), None);
            memo.record_written_projection(1, 2);
            memo.record_completed_projection(1, WrittenOnly, 2, 2);
            assert_eq!(memo.argument_scope().completed_projection(1, WrittenOnly), None);
            assert_eq!(memo.argument_scope().written_projection(1), None);
        }
        let mut full = ClosedLayoutMemo::new(true);
        for key in 0..MAX_COMPLETED {
            full.record_written_projection(key, key);
        }
        full.record_completed_projection(1, LeafConstants, 7, 9);
        assert_eq!(full.written_projection(1), None);
        assert_eq!(full.slot_count(), MAX_COMPLETED);
    }

    #[test]
    fn completed_subgraphs_reuse_but_failed_walks_do_not() {
        let mut memo = ClosedLayoutMemo::new(true);
        let frame = memo.begin(0);
        memo.finish(1, frame, true);
        assert!(memo.contains(1));
        let frame = memo.begin(0);
        memo.finish(2, frame, false);
        assert!(!memo.contains(2));
    }

    #[test]
    fn ancestor_dependent_child_is_not_reusable_but_closed_parent_is() {
        let mut memo = ClosedLayoutMemo::new(true);
        let parent = memo.begin(0);
        let child = memo.begin(1);
        memo.backedge(0, true);
        memo.finish(2, child, true);
        assert!(!memo.contains(2));
        memo.finish(1, parent, true);
        assert!(memo.contains(1));
    }

    #[test]
    fn changed_generic_backedge_cannot_close_any_live_summary() {
        let mut memo = ClosedLayoutMemo::new(true);
        let parent = memo.begin(0);
        let child = memo.begin(1);
        memo.backedge(1, false);
        memo.finish(2, child, true);
        memo.finish(1, parent, true);
        assert!(!memo.contains(1) && !memo.contains(2));
    }

    #[test]
    fn argument_scope_copies_only_closed_facts_and_cannot_mutate_parent() {
        let mut parent = ClosedLayoutMemo::new(true);
        let frame = parent.begin(0);
        parent.finish(1, frame, true);
        let outer = parent.begin(0);
        let dependent = parent.begin(1);
        parent.backedge(0, true);
        let mut argument = parent.argument_scope();
        assert!(argument.contains(1));
        assert_eq!(argument.frames.len(), 0);
        let frame = argument.begin(0);
        argument.backedge(0, true);
        argument.finish(3, frame, true);
        assert!(argument.contains(3));
        assert!(!parent.contains(3));
        parent.finish(2, dependent, true);
        assert!(!parent.contains(2));
        parent.finish(4, outer, true);
        assert!(parent.contains(4));
    }

    #[test]
    fn written_rhs_is_exact_scoped_and_conflicts_cannot_be_reinserted() {
        let mut parent = ClosedLayoutMemo::new(true);
        parent.record_written_projection(10, 20);
        assert_eq!(parent.written_projection(10), Some(20));
        assert_eq!(parent.written_projection(11), None);
        let mut child = parent.argument_scope();
        child.record_written_projection(10, 30);
        child.record_written_projection(10, 20);
        assert_eq!(child.written_projection(10), None);
        assert_eq!(child.argument_scope().written_projection(10), None);
        assert_eq!(parent.written_projection(10), Some(20));
        assert!(!parent.contains(10)); // a source binding is not a closed layout fact
        assert_eq!(ClosedLayoutMemo::<u32>::new(true).written_projection(10), None);
    }

    #[test]
    fn source_binding_and_closed_fact_slots_share_the_same_fixed_cap() {
        let mut memo = ClosedLayoutMemo::new(true);
        memo.record_written_projection(0, 1);
        memo.record_written_projection(0, 2); // tombstone still occupies a slot
        for key in 1..MAX_COMPLETED {
            let frame = memo.begin(0);
            memo.finish(key, frame, true);
        }
        memo.record_written_projection(MAX_COMPLETED, 99);
        assert_eq!(memo.written_projection(MAX_COMPLETED), None);
        assert_eq!(memo.completed.len() + memo.written_projections.len(), MAX_COMPLETED);
        assert_eq!(memo.written_projection(0), None);
    }

    #[test]
    fn tracking_and_completed_storage_are_bounded_and_disabled_mode_is_uncached() {
        let mut memo = ClosedLayoutMemo::new(true);
        for key in 0..MAX_COMPLETED + 1 {
            let frame = memo.begin(0);
            memo.finish(key, frame, true);
        }
        assert_eq!(memo.completed.len(), MAX_COMPLETED);
        assert!(!memo.contains(MAX_COMPLETED));
        let frames: Vec<_> = (0..MAX_FRAMES).map(|_| memo.begin(0)).collect();
        assert_eq!(memo.begin(0), None);
        for frame in frames.into_iter().rev() {
            memo.finish(999, frame, false);
        }
        let mut disabled = ClosedLayoutMemo::new(false);
        let frame = disabled.begin(0);
        disabled.finish(1, frame, true);
        assert!(!disabled.contains(1));
    }
}
