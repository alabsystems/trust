// trust_vcgen/memory_ordering/happens_before.rs: HappensBefore partial order
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};
use trust_types::fx::{FxHashMap, FxHashSet};

/// A partial order representing the happens-before relation between events.
///
/// Each event is identified by a `usize` index. The relation is:
/// - Reflexive: every event happens-before itself.
/// - Transitive: if a HB b and b HB c, then a HB c.
/// - Antisymmetric: if a HB b and b HB a, then a == b.
///
/// Edges are stored explicitly; transitive closure is computed on demand.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HappensBefore {
    /// Adjacency list: for each event, the set of events it directly
    /// happens-before (i.e., edges[a] contains b means a -> b).
    edges: FxHashMap<usize, FxHashSet<usize>>,
    /// Total number of events in the relation.
    event_count: usize,
}

impl HappensBefore {
    /// Create a new empty happens-before relation with `n` events.
    #[must_use]
    pub fn new(event_count: usize) -> Self {
        Self { edges: FxHashMap::default(), event_count }
    }

    /// Add a direct happens-before edge: `from` -> `to`.
    ///
    /// Returns `true` if the edge was newly inserted, `false` if it already existed.
    pub fn add_edge(&mut self, from: usize, to: usize) -> bool {
        if from >= self.event_count || to >= self.event_count {
            return false;
        }
        self.edges.entry(from).or_default().insert(to)
    }

    /// Add a synchronizes-with edge between a release store and an acquire load.
    ///
    /// In the C11 memory model, a release-store to location X synchronizes-with
    /// an acquire-load from X that reads the stored value. This establishes a
    /// happens-before edge.
    pub fn add_synchronizes_with(&mut self, release_event: usize, acquire_event: usize) -> bool {
        self.add_edge(release_event, acquire_event)
    }

    /// Validate that all deserialized edges reference in-range events.
    ///
    /// `add_edge` enforces this during normal construction, but serde can
    /// materialize edge maps with out-of-range sources or targets. Returning all
    /// invalid edge endpoints lets callers reject the whole relation before
    /// deriving partial ordering evidence from it.
    pub fn validate(&self) -> Result<(), Vec<(usize, Option<usize>)>> {
        let mut invalid_edges = Vec::new();

        for (&from, successors) in &self.edges {
            if from >= self.event_count && successors.is_empty() {
                invalid_edges.push((from, None));
            }

            for &to in successors {
                if from >= self.event_count || to >= self.event_count {
                    invalid_edges.push((from, Some(to)));
                }
            }
        }

        if invalid_edges.is_empty() { Ok(()) } else { Err(invalid_edges) }
    }

    /// Check whether `from` happens-before `to` (transitively).
    ///
    /// Uses BFS over the edge graph. Reflexive: `happens_before(a, a)` is true.
    #[must_use]
    pub fn happens_before(&self, from: usize, to: usize) -> bool {
        if self.validate().is_err() {
            return false;
        }
        if from >= self.event_count || to >= self.event_count {
            return false;
        }
        if from == to {
            return true;
        }

        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();

        if let Some(successors) = self.edges.get(&from) {
            for &s in successors {
                if s == to {
                    return true;
                }
                visited.insert(s);
                queue.push_back(s);
            }
        }

        while let Some(current) = queue.pop_front() {
            if let Some(successors) = self.edges.get(&current) {
                for &s in successors {
                    if s == to {
                        return true;
                    }
                    if visited.insert(s) {
                        queue.push_back(s);
                    }
                }
            }
        }

        false
    }

    /// Check whether two events are ordered (either direction).
    #[must_use]
    pub fn are_ordered(&self, a: usize, b: usize) -> bool {
        self.happens_before(a, b) || self.happens_before(b, a)
    }

    /// Return all direct successors of an event.
    #[must_use]
    pub fn successors(&self, event: usize) -> Vec<usize> {
        if self.validate().is_err() || event >= self.event_count {
            return Vec::new();
        }

        self.edges.get(&event).map(|s| s.iter().copied().collect()).unwrap_or_default()
    }

    /// Return the number of events in the relation.
    #[must_use]
    pub fn event_count(&self) -> usize {
        self.event_count
    }

    /// Return the number of direct edges in the relation.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        if self.validate().is_err() {
            return 0;
        }

        self.edges.values().map(|s| s.len()).sum()
    }
}
