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

impl AtomicAccessLog {
    /// Create a new empty log.
    #[must_use]
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Record an atomic access.
    ///
    /// Returns the index of the newly added entry. Panics if the access kind
    /// is non-atomic (use `try_record` for fallible recording).
    pub fn record(&mut self, entry: AtomicAccessEntry) -> usize {
        assert!(
            !entry.access_kind.is_non_atomic(),
            "AtomicAccessLog::record requires atomic access"
        );
        let idx = self.entries.len();
        self.entries.push(entry);
        idx
    }

    /// Record an atomic access, returning `None` if the access is non-atomic.
    pub fn try_record(&mut self, entry: AtomicAccessEntry) -> Option<usize> {
        if entry.access_kind.is_non_atomic() {
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

    /// Validate that every log entry preserves the atomic-only invariant.
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
            .filter_map(|(idx, entry)| entry.access_kind.is_non_atomic().then_some(idx))
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

    /// Check for release-acquire pairs on the same location across threads.
    ///
    /// Returns pairs `(release_idx, acquire_idx)` where a release store
    /// to location L in thread A is followed by an acquire load from L
    /// in thread B.
    #[must_use]
    pub fn find_release_acquire_pairs(&self) -> Vec<(usize, usize)> {
        if self.validate().is_err() {
            return Vec::new();
        }

        let mut pairs = Vec::new();

        for (i, release) in self.entries.iter().enumerate() {
            let is_release = matches!(
                release.access_kind,
                AccessKind::AtomicWrite(MemoryOrdering::Release)
                    | AccessKind::AtomicWrite(MemoryOrdering::AcqRel)
                    | AccessKind::AtomicWrite(MemoryOrdering::SeqCst)
                    | AccessKind::AtomicRmw(MemoryOrdering::Release, _)
                    | AccessKind::AtomicRmw(MemoryOrdering::AcqRel, _)
                    | AccessKind::AtomicRmw(MemoryOrdering::SeqCst, _)
            );
            if !is_release {
                continue;
            }

            for (j, acquire) in self.entries.iter().enumerate().skip(i + 1) {
                if acquire.location != release.location {
                    continue;
                }
                if acquire.thread_id == release.thread_id {
                    continue;
                }
                let is_acquire = matches!(
                    acquire.access_kind,
                    AccessKind::AtomicRead(MemoryOrdering::Acquire)
                        | AccessKind::AtomicRead(MemoryOrdering::AcqRel)
                        | AccessKind::AtomicRead(MemoryOrdering::SeqCst)
                        | AccessKind::AtomicRmw(MemoryOrdering::Acquire, _)
                        | AccessKind::AtomicRmw(MemoryOrdering::AcqRel, _)
                        | AccessKind::AtomicRmw(MemoryOrdering::SeqCst, _)
                );
                if is_acquire {
                    pairs.push((i, j));
                }
            }
        }

        pairs
    }
}
