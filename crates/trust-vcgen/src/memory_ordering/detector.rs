// trust_vcgen/memory_ordering/detector.rs: DataRaceDetector
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::SourceSpan;

use super::happens_before::HappensBefore;
use super::race_condition::RaceCondition;
use crate::data_race::{AccessKind, SharedAccess};

/// A stateful data race detector that combines access tracking with
/// happens-before analysis.
///
/// Usage:
/// 1. Add accesses via `add_access`.
/// 2. Establish ordering via `add_happens_before` or `add_sync_pair`.
/// 3. Call `detect_races` to find all potential data races.
#[derive(Debug, Clone)]
pub struct DataRaceDetector {
    /// All recorded memory accesses.
    accesses: Vec<SharedAccess>,
    /// The happens-before partial order.
    hb: HappensBefore,
}

impl DataRaceDetector {
    /// Create a new empty detector.
    #[must_use]
    pub fn new() -> Self {
        Self { accesses: Vec::new(), hb: HappensBefore::new(0) }
    }

    /// Add a memory access and return its index.
    pub fn add_access(
        &mut self,
        variable: &str,
        kind: AccessKind,
        thread: &str,
        span: SourceSpan,
    ) -> usize {
        let idx = self.accesses.len();
        self.accesses.push(SharedAccess {
            variable: variable.to_string(),
            access_kind: kind,
            thread_id: thread.to_string(),
            happens_before: Vec::new(),
            span,
        });
        // Grow the HB relation to cover the new event.
        self.hb = HappensBefore::new(self.accesses.len());
        // Re-add all existing edges from the SharedAccess HB lists.
        for (i, access) in self.accesses.iter().enumerate() {
            for &dep in &access.happens_before {
                self.hb.add_edge(dep, i);
            }
        }
        idx
    }

    /// Establish a happens-before edge: `from` -> `to`.
    pub fn add_happens_before(&mut self, from: usize, to: usize) -> bool {
        if to < self.accesses.len() && from < self.accesses.len() {
            self.accesses[to].happens_before.push(from);
            self.hb.add_edge(from, to)
        } else {
            false
        }
    }

    /// Establish a synchronizes-with relationship (release -> acquire).
    ///
    /// This is a convenience method for the common pattern where a release
    /// store synchronizes with an acquire load.
    pub fn add_sync_pair(&mut self, release: usize, acquire: usize) -> bool {
        self.add_happens_before(release, acquire)
    }

    /// Detect all potential data races.
    ///
    /// Two accesses race when:
    /// 1. Same variable.
    /// 2. Different threads.
    /// 3. At least one is a write.
    /// 4. At least one is non-atomic.
    /// 5. No happens-before relationship in either direction.
    #[must_use]
    pub fn detect_races(&self) -> Vec<RaceCondition> {
        let mut races = Vec::new();

        for (i, a) in self.accesses.iter().enumerate() {
            if matches!(a.access_kind, AccessKind::Fence(_)) {
                continue;
            }

            for (j, b) in self.accesses.iter().enumerate().skip(i + 1) {
                if matches!(b.access_kind, AccessKind::Fence(_)) {
                    continue;
                }

                // Same variable
                if a.variable != b.variable {
                    continue;
                }

                // Different threads
                if a.thread_id == b.thread_id {
                    continue;
                }

                // At least one write
                if !a.access_kind.is_write() && !b.access_kind.is_write() {
                    continue;
                }

                // At least one non-atomic
                if !a.access_kind.is_non_atomic() && !b.access_kind.is_non_atomic() {
                    continue;
                }

                // No happens-before in either direction
                if self.hb.are_ordered(i, j) {
                    continue;
                }

                races.push(RaceCondition {
                    first_access: i,
                    second_access: j,
                    location: a.variable.clone(),
                    first_thread: a.thread_id.clone(),
                    second_thread: b.thread_id.clone(),
                    first_kind: a.access_kind,
                    second_kind: b.access_kind,
                    first_span: a.span.clone(),
                    second_span: b.span.clone(),
                });
            }
        }

        races
    }

    /// Return the number of recorded accesses.
    #[must_use]
    pub fn access_count(&self) -> usize {
        self.accesses.len()
    }

    /// Return a reference to the happens-before relation.
    #[must_use]
    pub fn happens_before(&self) -> &HappensBefore {
        &self.hb
    }

    /// Return a reference to the recorded accesses.
    #[must_use]
    pub fn accesses(&self) -> &[SharedAccess] {
        &self.accesses
    }
}

impl Default for DataRaceDetector {
    fn default() -> Self {
        Self::new()
    }
}
