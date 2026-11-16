// trust_vcgen/memory_ordering/atomic_access.rs: AtomicAccessEntry and AtomicAccessLog
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::SourceSpan;
use trust_types::fx::FxHashSet;

use crate::data_race::{AccessKind, MemoryOrdering};

/// An entry in the atomic access log.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomicAccessEntry {
    /// The memory location accessed.
    pub location: String,
    /// The access kind (must be atomic: AtomicRead, AtomicWrite, or Fence).
    pub access_kind: AccessKind,
    /// Thread performing the access.
    pub thread_id: String,
    /// Source span for diagnostics.
    pub span: SourceSpan,
}

/// Records atomic operations with their orderings for analysis.
///
/// Provides methods to query ordering patterns and detect potential issues
/// like using Relaxed ordering where Acquire/Release is needed.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AtomicAccessLog {
    /// All recorded atomic accesses in program order.
    entries: Vec<AtomicAccessEntry>,
}

fn is_legal_log_entry(kind: AccessKind) -> bool {
    match kind {
        AccessKind::Read
        | AccessKind::Write
        | AccessKind::AtomicRead(MemoryOrdering::Release | MemoryOrdering::AcqRel)
        | AccessKind::AtomicWrite(MemoryOrdering::Acquire | MemoryOrdering::AcqRel)
        | AccessKind::Fence(MemoryOrdering::Relaxed) => false,
        AccessKind::AtomicRead(_)
        | AccessKind::AtomicWrite(_)
        | AccessKind::AtomicRmw(..)
        | AccessKind::Fence(_) => true,
    }
}

impl AtomicAccessLog {
    /// Create a new empty log.
    #[must_use]
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Record an atomic access.
    ///
    /// Returns the index of the newly added entry. Panics if the access kind
    /// is non-atomic or has an illegal ordering for its operation kind (use
    /// `try_record` for fallible recording).
    pub fn record(&mut self, entry: AtomicAccessEntry) -> usize {
        assert!(
            !entry.access_kind.is_non_atomic(),
            "AtomicAccessLog::record requires atomic access"
        );
        assert!(
            is_legal_log_entry(entry.access_kind),
            "AtomicAccessLog::record requires legal atomic ordering"
        );
        let idx = self.entries.len();
        self.entries.push(entry);
        idx
    }

    /// Record an atomic access, returning `None` for a non-atomic access or
    /// an ordering that is illegal for the operation kind.
    pub fn try_record(&mut self, entry: AtomicAccessEntry) -> Option<usize> {
        if !is_legal_log_entry(entry.access_kind) {
            return None;
        }
        Some(self.record(entry))
    }

    /// Return all entries in the log.
    #[must_use]
    pub fn entries(&self) -> &[AtomicAccessEntry] {
        &self.entries
    }

    /// Return the number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Return whether the log is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Validate that every log entry has an atomic operation and legal ordering.
    ///
    /// `record` and `try_record` enforce this during normal construction, but
    /// deserialization can still materialize malformed logs. Returning all
    /// offending indices lets callers fail closed before deriving ordering
    /// evidence from any part of the log.
    pub fn validate(&self) -> Result<(), Vec<usize>> {
        let invalid_indices: Vec<_> = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(idx, entry)| (!is_legal_log_entry(entry.access_kind)).then_some(idx))
            .collect();

        if invalid_indices.is_empty() { Ok(()) } else { Err(invalid_indices) }
    }

    /// Find all accesses to a given location.
    #[must_use]
    pub fn accesses_to(&self, location: &str) -> Vec<(usize, &AtomicAccessEntry)> {
        if self.validate().is_err() {
            return Vec::new();
        }

        self.entries.iter().enumerate().filter(|(_, e)| e.location == location).collect()
    }

    /// Find all accesses by a given thread.
    #[must_use]
    pub fn accesses_by_thread(&self, thread_id: &str) -> Vec<(usize, &AtomicAccessEntry)> {
        if self.validate().is_err() {
            return Vec::new();
        }

        self.entries.iter().enumerate().filter(|(_, e)| e.thread_id == thread_id).collect()
    }

    /// Find all accesses using a specific ordering.
    #[must_use]
    pub fn accesses_with_ordering(
        &self,
        ordering: MemoryOrdering,
    ) -> Vec<(usize, &AtomicAccessEntry)> {
        if self.validate().is_err() {
            return Vec::new();
        }

        self.entries
            .iter()
            .enumerate()
            .filter(|(_, e)| e.access_kind.ordering() == Some(ordering))
            .collect()
    }

    /// Return the set of unique locations accessed.
    #[must_use]
    pub fn locations(&self) -> FxHashSet<&str> {
        if self.validate().is_err() {
            return FxHashSet::default();
        }

        self.entries.iter().map(|e| e.location.as_str()).collect()
    }

    /// Return the set of unique thread IDs.
    #[must_use]
    pub fn threads(&self) -> FxHashSet<&str> {
        if self.validate().is_err() {
            return FxHashSet::default();
        }

        self.entries.iter().map(|e| e.thread_id.as_str()).collect()
    }

    /// Return synchronization pairs backed by read-from evidence.
    ///
    /// This log records event shape and order, but not which write an acquire
    /// read or whether that write belongs to a release sequence. Even adjacent
    /// release/acquire events on the same location cannot establish a pair.
    /// Until that evidence is available, callers must not derive HB edges from
    /// this log. The events remain available through `entries` for diagnostics.
    #[must_use]
    pub fn find_release_acquire_pairs(&self) -> Vec<(usize, usize)> {
        if self.validate().is_err() {
            return Vec::new();
        }
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{AtomicRmwOp, SourceSpan, VcKind};

    use super::{AtomicAccessEntry, AtomicAccessLog};
    use crate::data_race::{AccessKind, MemoryOrdering};
    use crate::memory_ordering::{HappensBefore, MemoryModelChecker};

    fn entry(thread_id: &str, access_kind: AccessKind) -> AtomicAccessEntry {
        AtomicAccessEntry {
            location: "flag".to_string(),
            access_kind,
            thread_id: thread_id.to_string(),
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn adjacent_release_acquire_without_read_from_does_not_create_hb() {
        let mut log = AtomicAccessLog::new();
        log.record(entry("producer", AccessKind::AtomicWrite(MemoryOrdering::Release)));
        log.record(entry("consumer", AccessKind::AtomicRead(MemoryOrdering::Acquire)));

        assert_eq!(log.entries().len(), 2);
        assert_eq!(log.accesses_to("flag").len(), 2);
        assert!(log.find_release_acquire_pairs().is_empty());
        let graph = MemoryModelChecker::new(log, HappensBefore::new(2)).build_happens_before(&[]);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn intervening_write_does_not_create_release_acquire_hb() {
        let mut log = AtomicAccessLog::new();
        log.record(entry("producer", AccessKind::AtomicWrite(MemoryOrdering::Release)));
        log.record(entry("other", AccessKind::AtomicWrite(MemoryOrdering::Relaxed)));
        log.record(entry("consumer", AccessKind::AtomicRead(MemoryOrdering::Acquire)));

        assert_eq!(log.entries().len(), 3);
        assert_eq!(log.accesses_to("flag").len(), 3);
        assert!(log.find_release_acquire_pairs().is_empty());
        let graph = MemoryModelChecker::new(log, HappensBefore::new(3)).build_happens_before(&[]);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn seq_cst_ordering_alone_does_not_establish_read_from() {
        let mut log = AtomicAccessLog::new();
        log.record(entry("producer", AccessKind::AtomicWrite(MemoryOrdering::SeqCst)));
        log.record(entry("consumer", AccessKind::AtomicRead(MemoryOrdering::SeqCst)));

        assert!(log.find_release_acquire_pairs().is_empty());
    }

    #[test]
    fn rmw_ordering_alone_does_not_establish_read_from() {
        let mut log = AtomicAccessLog::new();
        log.record(entry(
            "producer",
            AccessKind::AtomicRmw(MemoryOrdering::Release, AtomicRmwOp::Add),
        ));
        log.record(entry(
            "consumer",
            AccessKind::AtomicRmw(MemoryOrdering::Acquire, AtomicRmwOp::Add),
        ));

        assert!(log.find_release_acquire_pairs().is_empty());
        let graph = MemoryModelChecker::new(log, HappensBefore::new(2)).build_happens_before(&[]);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn illegal_atomic_orderings_in_imported_log_emit_coverage_gap_vcs() {
        let illegal = [
            AccessKind::AtomicRead(MemoryOrdering::Release),
            AccessKind::AtomicRead(MemoryOrdering::AcqRel),
            AccessKind::AtomicWrite(MemoryOrdering::Acquire),
            AccessKind::AtomicWrite(MemoryOrdering::AcqRel),
            AccessKind::Fence(MemoryOrdering::Relaxed),
        ];

        for access_kind in illegal {
            let malformed = entry("worker", access_kind);
            let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
                "entries": [malformed]
            }))
            .expect("serialized evidence can bypass record");

            assert_eq!(log.validate(), Err(vec![0]), "{access_kind:?}");
            let checker = MemoryModelChecker::new(log, HappensBefore::new(1));
            assert!(!checker.check().is_sound, "{access_kind:?}");
            let vcs = checker.generate_vcs("illegal_atomic_ordering");
            assert_eq!(vcs.len(), 1, "{access_kind:?}");
            assert!(
                matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == "ConcurrencyOrderingCoverageGap"),
                "{access_kind:?}: {vcs:?}"
            );
        }
    }

    #[test]
    fn legal_atomic_orderings_remain_recordable() {
        let legal = [
            AccessKind::AtomicRead(MemoryOrdering::Acquire),
            AccessKind::AtomicWrite(MemoryOrdering::Release),
            AccessKind::Fence(MemoryOrdering::Acquire),
            AccessKind::Fence(MemoryOrdering::Release),
            AccessKind::Fence(MemoryOrdering::SeqCst),
            AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add),
        ];
        let mut log = AtomicAccessLog::new();
        for access_kind in legal {
            assert!(log.try_record(entry("worker", access_kind)).is_some());
        }
        assert_eq!(log.validate(), Ok(()));
        assert_eq!(log.len(), legal.len());
    }

    #[test]
    fn try_record_refuses_illegal_atomic_ordering_without_mutating_log() {
        let mut log = AtomicAccessLog::new();
        assert_eq!(
            log.try_record(entry("worker", AccessKind::AtomicRead(MemoryOrdering::Release))),
            None
        );
        assert!(log.is_empty());
    }

    #[test]
    #[should_panic(expected = "AtomicAccessLog::record requires legal atomic ordering")]
    fn record_rejects_illegal_atomic_ordering() {
        AtomicAccessLog::new().record(entry("worker", AccessKind::Fence(MemoryOrdering::Relaxed)));
    }
}
