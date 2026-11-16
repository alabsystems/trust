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
/// 2. Record claimed ordering via `add_happens_before` or `add_sync_pair`.
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
    ///
    /// `variable` and `thread` are diagnostic labels only. They establish
    /// neither disjoint locations nor identical runtime threads.
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
        self.hb.add_event();
        idx
    }

    /// Record a claimed happens-before edge: `from` -> `to`.
    ///
    /// This public API does not authenticate runtime events or the edge, so
    /// `detect_races` cannot use it to discard a potential race.
    pub fn add_happens_before(&mut self, from: usize, to: usize) -> bool {
        if to < self.accesses.len() && from < self.accesses.len() {
            if self.hb.add_edge(from, to) {
                self.accesses[to].happens_before.push(from);
                true
            } else {
                false
            }
        } else {
            self.hb.invalidate();
            false
        }
    }

    /// Record a claimed synchronizes-with relationship (release -> acquire).
    ///
    /// This convenience method records a claimed release/acquire pair; it
    /// does not authenticate a read-from witness or establish real sync.
    pub fn add_sync_pair(&mut self, release: usize, acquire: usize) -> bool {
        self.add_happens_before(release, acquire)
    }

    /// Detect all potential data races.
    ///
    /// Two accesses race when:
    /// 1. Their locations may alias (assumed for all current inputs).
    /// 2. The accesses may come from different runtime threads.
    /// 3. At least one is a write.
    /// 4. At least one is non-atomic.
    /// 5. No authenticated happens-before relationship is available here.
    ///
    /// This is a potential-race diagnostic, not proof of race freedom. Display
    /// names never establish disjointness or same-thread identity. Caller-supplied
    /// HB edges cannot establish ordering authority either.
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

                // At least one write
                if !a.access_kind.is_write() && !b.access_kind.is_write() {
                    continue;
                }

                // At least one non-atomic
                if !a.access_kind.is_non_atomic() && !b.access_kind.is_non_atomic() {
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

#[cfg(test)]
mod tests {
    use trust_types::MemoryLocationId;

    use super::*;

    fn races_between(first: &str, second: &str) -> Vec<RaceCondition> {
        let mut detector = DataRaceDetector::new();
        detector.add_access(first, AccessKind::Write, "writer", SourceSpan::default());
        detector.add_access(second, AccessKind::Read, "reader", SourceSpan::default());
        detector.detect_races()
    }

    #[test]
    fn unknown_location_may_alias_other_label_in_either_order() {
        for unknown in ["", "_", "?", "<unknown>", "unknown", "UNKNOWN", "ambiguous"] {
            for (first, second) in [(unknown, "data"), ("data", unknown)] {
                let races = races_between(first, second);
                assert_eq!(races.len(), 1, "{first:?} and {second:?} may alias");
                assert_eq!((races[0].first_access, races[0].second_access), (0, 1));
            }
        }
    }

    #[test]
    fn distinct_names_and_alias_expressions_may_alias() {
        for (first, second) in [
            ("p", "q"),
            ("*p", "*q"),
            ("left.field", "right.field"),
            ("buf[i]", "buf[j]"),
            ("global:module::DATA", "global:module::FLAG"),
        ] {
            assert_eq!(races_between(first, second).len(), 1, "{first:?} and {second:?} may alias");
        }
    }

    #[test]
    fn extern_statics_with_distinct_def_paths_and_one_link_name_may_alias() {
        #[allow(dead_code)]
        unsafe extern "C" {
            #[link_name = "SHARED"]
            static mut LEFT: u8;
            #[link_name = "SHARED"]
            static mut RIGHT: u8;
        }
        let left = MemoryLocationId::Global { def_path: "ffi::LEFT".into() };
        let right = MemoryLocationId::Global { def_path: "ffi::RIGHT".into() };
        assert_ne!(left, right);
        let races = races_between(&left.to_string(), &right.to_string());
        assert_eq!(races.len(), 1);
        assert_eq!((races[0].first_access, races[0].second_access), (0, 1));
    }

    #[test]
    fn same_label_and_fabricated_distinct_global_id_text_still_race() {
        assert_eq!(races_between("shared", "shared").len(), 1);
        let claimed_left = MemoryLocationId::Global { def_path: "fabricated::LEFT".into() };
        let claimed_right = MemoryLocationId::Global { def_path: "fabricated::RIGHT".into() };
        assert_ne!(claimed_left, claimed_right);
        assert_eq!(races_between(&claimed_left.to_string(), &claimed_right.to_string()).len(), 1);
    }

    #[test]
    fn parameter_arc_capture_and_unknown_id_text_may_alias() {
        let parameter_a = MemoryLocationId::Parameter { function: "worker".into(), param_index: 0 };
        let parameter_b = MemoryLocationId::Parameter { function: "worker".into(), param_index: 1 };
        let arc_a = MemoryLocationId::ArcCapture { source_def_path: "left".into() };
        let arc_b = MemoryLocationId::ArcCapture { source_def_path: "right".into() };
        for (a, b) in [
            (parameter_a, parameter_b),
            (arc_a, arc_b),
            (
                MemoryLocationId::Global { def_path: "module::DATA".into() },
                MemoryLocationId::Unknown { description: "opaque".into() },
            ),
        ] {
            assert_eq!(races_between(&a.to_string(), &b.to_string()).len(), 1);
        }
    }
}
