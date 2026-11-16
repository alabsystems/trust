// trust_vcgen/memory_ordering/happens_before.rs: HappensBefore partial order
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};
use trust_types::fx::{FxHashMap, FxHashSet};

fn validation_pending_after_deserialize() -> bool {
    true
}

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
    /// A rejected contradictory edge is evidence of an invalid relation, even
    /// though the edge itself is not inserted into the DAG.
    #[serde(default)]
    inconsistent: bool,
    /// Constructed graphs maintain the DAG invariant incrementally. A loaded
    /// graph must earn it once before mutation; this flag is never imported.
    #[serde(skip, default = "validation_pending_after_deserialize")]
    validation_pending: bool,
}

impl HappensBefore {
    /// Create a new empty happens-before relation with `n` events.
    #[must_use]
    pub fn new(event_count: usize) -> Self {
        Self {
            edges: FxHashMap::default(),
            event_count,
            inconsistent: false,
            validation_pending: false,
        }
    }

    /// Extend the event universe without rebuilding or losing prior evidence.
    pub fn add_event(&mut self) {
        if !self.is_acyclic() {
            self.inconsistent = true;
        } else {
            self.validation_pending = false;
        }
        if let Some(next) = self.event_count.checked_add(1) {
            self.event_count = next;
        } else {
            self.inconsistent = true;
        }
    }

    /// Add a direct happens-before edge: `from` -> `to`.
    ///
    /// Returns `true` if the edge was newly inserted. Duplicate, invalid, and
    /// cycle-forming edges are rejected.
    pub fn add_edge(&mut self, from: usize, to: usize) -> bool {
        if from >= self.event_count || to >= self.event_count || from == to {
            self.inconsistent = true;
            return false;
        }
        if self.edges.get(&from).is_some_and(|successors| successors.contains(&to)) {
            return false;
        }
        if !self.is_acyclic() {
            self.inconsistent = true;
            return false;
        }
        self.validation_pending = false;
        if self.reachable_unchecked(to, from) {
            self.inconsistent = true;
            return false;
        }
        self.edges.entry(from).or_default().insert(to)
    }

    /// Record that an edge referring to this relation could not be represented.
    pub fn invalidate(&mut self) {
        self.inconsistent = true;
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

    /// Return whether the relation is a valid directed acyclic graph.
    /// Invalid deserialized endpoints also fail this check.
    #[must_use]
    pub fn is_acyclic(&self) -> bool {
        if self.inconsistent {
            return false;
        }
        if !self.validation_pending {
            return true;
        }
        if self.validate().is_err() {
            return false;
        }

        let mut indegree = FxHashMap::<usize, usize>::default();
        for (&from, successors) in &self.edges {
            indegree.entry(from).or_insert(0);
            for &to in successors {
                *indegree.entry(to).or_insert(0) += 1;
            }
        }

        let mut queue = VecDeque::new();
        for (&event, &degree) in &indegree {
            if degree == 0 {
                queue.push_back(event);
            }
        }

        let mut visited = 0;
        while let Some(event) = queue.pop_front() {
            visited += 1;
            if let Some(successors) = self.edges.get(&event) {
                for successor in successors {
                    // Unreachable by construction: `indegree` above inserts every
                    // `to` of every successor list, and this walks exactly those
                    // keys. Take `is_acyclic`'s own fail-closed exit rather than
                    // abort the verifier — the same `return false` the
                    // `validate()` failure above takes, which propagates to
                    // `happens_before() == false`, i.e. no ordering proven.
                    let Some(degree) = indegree.get_mut(successor) else {
                        return false;
                    };
                    *degree -= 1;
                    if *degree == 0 {
                        queue.push_back(*successor);
                    }
                }
            }
        }
        visited == indegree.len()
    }

    /// Check whether `from` happens-before `to` (transitively).
    ///
    /// Uses BFS over the edge graph. Reflexive: `happens_before(a, a)` is true.
    #[must_use]
    pub fn happens_before(&self, from: usize, to: usize) -> bool {
        if !self.is_acyclic() || from >= self.event_count || to >= self.event_count {
            return false;
        }
        self.reachable_unchecked(from, to)
    }

    fn reachable_unchecked(&self, from: usize, to: usize) -> bool {
        if from == to {
            return true;
        }
        let Some(successors) = self.edges.get(&from) else {
            return false;
        };
        if successors.contains(&to) {
            return true;
        }

        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::with_capacity(successors.len());
        for &s in successors {
            visited.insert(s);
            queue.push_back(s);
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

    /// Check whether there is a direct edge `from -> to` in an acyclic graph
    /// without allocating a temporary `Vec<usize>`.
    #[must_use]
    pub(in crate::memory_ordering) fn has_direct_edge(&self, from: usize, to: usize) -> bool {
        self.is_acyclic()
            && from < self.event_count
            && to < self.event_count
            && self.edges.get(&from).is_some_and(|s| s.contains(&to))
    }

    /// Return all direct successors of an event.
    #[must_use]
    pub fn successors(&self, event: usize) -> Vec<usize> {
        if !self.is_acyclic() || event >= self.event_count {
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
        if !self.is_acyclic() {
            return 0;
        }

        self.edges.values().map(|s| s.len()).sum()
    }
}
