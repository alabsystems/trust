// trust_vcgen/memory_ordering/hb_graph.rs: HappensBeforeGraph and MemoryModelChecker phase 2
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{ConcurrencyPoint, HappensBeforeEdgeKind, VerifiableFunction};

use super::checker::MemoryModelChecker;
use super::happens_before::HappensBefore;

/// A typed happens-before graph with program-point nodes and labeled edges.
///
/// Extends the raw `HappensBefore` (usize-indexed) with semantic information:
/// each node is a `ConcurrencyPoint` (function + block + thread), and each edge
/// carries a `HappensBeforeEdgeKind` explaining why the ordering exists.
///
/// Usage:
/// 1. Add nodes with `add_node()`.
/// 2. Add edges with `add_edge()`.
/// 3. Query with `happens_before()` or `are_ordered()`.
#[derive(Debug, Clone, Default)]
pub struct HappensBeforeGraph {
    /// Map from program point to node index.
    point_to_index: FxHashMap<ConcurrencyPoint, usize>,
    /// Reverse map from node index to program point.
    index_to_point: Vec<ConcurrencyPoint>,
    /// The underlying integer-indexed HB relation.
    hb: HappensBefore,
    /// Edge labels for diagnostics.
    edge_labels: FxHashMap<(usize, usize), HappensBeforeEdgeKind>,
}

impl HappensBeforeGraph {
    /// Create a new empty graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a program point as a node. Returns its index.
    ///
    /// If the point already exists, returns the existing index.
    pub fn add_node(&mut self, point: ConcurrencyPoint) -> usize {
        if let Some(&idx) = self.point_to_index.get(&point) {
            return idx;
        }
        let idx = self.index_to_point.len();
        self.point_to_index.insert(point.clone(), idx);
        self.index_to_point.push(point);
        self.hb.add_event();
        idx
    }

    /// Add a happens-before edge between two program points.
    ///
    /// Both points must have been added via `add_node()` first.
    /// Returns `true` if the edge was newly inserted.
    pub fn add_edge(
        &mut self,
        from: &ConcurrencyPoint,
        to: &ConcurrencyPoint,
        kind: HappensBeforeEdgeKind,
    ) -> bool {
        let from_idx = match self.point_to_index.get(from) {
            Some(&idx) => idx,
            None => {
                self.hb.invalidate();
                return false;
            }
        };
        let to_idx = match self.point_to_index.get(to) {
            Some(&idx) => idx,
            None => {
                self.hb.invalidate();
                return false;
            }
        };
        self.add_edge_indices(from_idx, to_idx, kind)
    }

    /// Add a happens-before edge between two already-registered node indices.
    pub(crate) fn add_edge_indices(
        &mut self,
        from_idx: usize,
        to_idx: usize,
        kind: HappensBeforeEdgeKind,
    ) -> bool {
        if self.hb.add_edge(from_idx, to_idx) {
            self.edge_labels.insert((from_idx, to_idx), kind);
            true
        } else {
            false
        }
    }

    /// Check whether point `from` happens-before point `to` (transitively).
    #[must_use]
    pub fn happens_before(&self, from: &ConcurrencyPoint, to: &ConcurrencyPoint) -> bool {
        let from_idx = match self.point_to_index.get(from) {
            Some(&idx) => idx,
            None => return false,
        };
        let to_idx = match self.point_to_index.get(to) {
            Some(&idx) => idx,
            None => return false,
        };
        self.hb.happens_before(from_idx, to_idx)
    }

    /// Check whether two program points are ordered (either direction).
    #[must_use]
    pub fn are_ordered(&self, a: &ConcurrencyPoint, b: &ConcurrencyPoint) -> bool {
        self.happens_before(a, b) || self.happens_before(b, a)
    }

    /// Return the number of nodes in the graph.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.index_to_point.len()
    }

    /// Return the number of edges in the graph.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.edge_labels.len()
    }

    /// Return the edge kind between two program points, if an edge exists.
    #[must_use]
    pub fn edge_kind(
        &self,
        from: &ConcurrencyPoint,
        to: &ConcurrencyPoint,
    ) -> Option<HappensBeforeEdgeKind> {
        let from_idx = self.point_to_index.get(from)?;
        let to_idx = self.point_to_index.get(to)?;
        self.edge_labels.get(&(*from_idx, *to_idx)).copied()
    }

    /// Return a reference to the underlying `HappensBefore` relation.
    #[must_use]
    pub fn raw_hb(&self) -> &HappensBefore {
        &self.hb
    }

    /// Lookup a program point by its node index.
    #[must_use]
    pub fn point_at(&self, index: usize) -> Option<&ConcurrencyPoint> {
        self.index_to_point.get(index)
    }

    /// Return all program points in the graph.
    #[must_use]
    pub fn points(&self) -> &[ConcurrencyPoint] {
        &self.index_to_point
    }
}

impl MemoryModelChecker {
    /// Build a happens-before graph from a set of verifiable functions.
    ///
    /// Function blocks and spawn/join sites are static program points, not
    /// execution events. They cannot supply program-order or thread-lifecycle
    /// edges without invocation and child-event identities, so this builder
    /// leaves them out of the event graph. Synchronization pairs may be added
    /// only when the atomic access log supplies them with sufficient evidence.
    ///
    /// This is Phase 2 of the memory ordering verification pipeline.
    #[must_use]
    pub fn build_happens_before(&self, _functions: &[&VerifiableFunction]) -> HappensBeforeGraph {
        let mut graph = HappensBeforeGraph::new();

        // Only evidence-backed release-acquire pairs may create sync edges.
        let pairs = self.log.find_release_acquire_pairs();
        for (release_idx, acquire_idx) in pairs {
            if let (Some(release), Some(acquire)) =
                (self.log.entries().get(release_idx), self.log.entries().get(acquire_idx))
            {
                // Create program points for the release and acquire entries.
                // Thread ID comes from the entry itself.
                let release_point = ConcurrencyPoint::new(
                    &release.location,
                    trust_types::BlockId(release_idx),
                    &release.thread_id,
                );
                let acquire_point = ConcurrencyPoint::new(
                    &acquire.location,
                    trust_types::BlockId(acquire_idx),
                    &acquire.thread_id,
                );

                let release_node = graph.add_node(release_point);
                let acquire_node = graph.add_node(acquire_point);
                graph.add_edge_indices(
                    release_node,
                    acquire_node,
                    HappensBeforeEdgeKind::SyncWith,
                );
            }
        }

        graph
    }
}
