// trust_vcgen/memory_ordering/hb_graph.rs: HappensBeforeGraph and MemoryModelChecker phase 2
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{
    ConcurrencyPoint, HappensBeforeEdgeKind, VerifiableFunction, detect_thread_joins,
    detect_thread_spawns,
};

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
        // Rebuild the HB relation with the new event count.
        self.hb = HappensBefore::new(self.index_to_point.len());
        // Re-add all existing edges.
        for &(from, to) in self.edge_labels.keys() {
            self.hb.add_edge(from, to);
        }
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
            None => return false,
        };
        let to_idx = match self.point_to_index.get(to) {
            Some(&idx) => idx,
            None => return false,
        };
        self.edge_labels.insert((from_idx, to_idx), kind);
        self.hb.add_edge(from_idx, to_idx)
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
    /// Detects thread spawn/join sites and establishes:
    /// - Program-order edges within each function (sequential blocks).
    /// - Spawn edges from the spawn call to the child thread's entry.
    /// - Join edges from the child thread's exit to the join return.
    /// - Release-acquire sync edges from the atomic access log.
    ///
    /// This is Phase 2 of the memory ordering verification pipeline.
    #[must_use]
    pub fn build_happens_before(&self, functions: &[&VerifiableFunction]) -> HappensBeforeGraph {
        let mut graph = HappensBeforeGraph::new();

        // Phase 1: Add program-order edges within each function.
        for func in functions {
            let thread_id = "main"; // Initial: all in main thread
            for (i, block) in func.body.blocks.iter().enumerate() {
                let point = ConcurrencyPoint::new(&func.def_path, block.id, thread_id);
                graph.add_node(point.clone());

                // Program-order edge from previous block to this block.
                if i > 0 {
                    let prev = ConcurrencyPoint::new(
                        &func.def_path,
                        func.body.blocks[i - 1].id,
                        thread_id,
                    );
                    graph.add_edge(&prev, &point, HappensBeforeEdgeKind::ProgramOrder);
                }
            }
        }

        // Phase 2: Detect spawn/join sites and add spawn/join edges.
        for func in functions {
            let spawns = detect_thread_spawns(func);
            let joins = detect_thread_joins(func);

            for spawn in &spawns {
                let spawn_point =
                    ConcurrencyPoint::new(&spawn.caller_function, spawn.block, "main");

                // Create a synthetic entry point for the spawned thread.
                let child_thread_id = format!("spawned_at_bb{}", spawn.block.0);
                let child_entry =
                    ConcurrencyPoint::new(&spawn.caller_function, spawn.block, &child_thread_id);

                graph.add_node(spawn_point.clone());
                graph.add_node(child_entry.clone());
                graph.add_edge(&spawn_point, &child_entry, HappensBeforeEdgeKind::Spawn);
            }

            for join in &joins {
                let join_point = ConcurrencyPoint::new(&join.caller_function, join.block, "main");

                // Create a synthetic exit point for the joined thread.
                // We match by handle_local back to the spawn site.
                let child_thread_id = spawns
                    .iter()
                    .find(|s| s.join_handle_local == Some(join.handle_local))
                    .map(|s| format!("spawned_at_bb{}", s.block.0))
                    .unwrap_or_else(|| format!("joined_at_bb{}", join.block.0));

                let child_exit =
                    ConcurrencyPoint::new(&join.caller_function, join.block, &child_thread_id);

                graph.add_node(child_exit.clone());
                graph.add_node(join_point.clone());
                graph.add_edge(&child_exit, &join_point, HappensBeforeEdgeKind::Join);
            }
        }

        // Phase 3: Add release-acquire sync edges from the atomic access log.
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

                graph.add_node(release_point.clone());
                graph.add_node(acquire_point.clone());
                graph.add_edge(&release_point, &acquire_point, HappensBeforeEdgeKind::SyncWith);
            }
        }

        graph
    }
}
