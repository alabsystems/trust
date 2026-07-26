// Call graph construction from MIR for interprocedural analysis.
//
// Pure data structure — no rustc dependencies. Supports direct, indirect,
// virtual, and closure call edges with graph algorithms (SCC, topological
// sort, reachability).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// this compiler-internal analysis scaffold is compiled and
// unit-tested before the extraction pipeline wires it into production use.
#![allow(dead_code)]
// The hash-backed traversals either sort externally visible results or feed
// local graph worklists; no rustc query key/result depends on raw iteration.
#![allow(rustc::potential_query_instability)]

use std::collections::VecDeque;

use trust_types::fx::{FxHashMap, FxHashSet};

/// The kind of call observed at a call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[trust::skip]
#[non_exhaustive]
pub(crate) enum CallKind {
    /// Static dispatch to a known function.
    Direct,
    /// Call through a function pointer or opaque operand.
    Indirect,
    /// Virtual dispatch through a trait vtable.
    Virtual,
    /// Call to a closure or async block.
    Closure,
}

/// A single call site observed in MIR.
#[derive(Debug, Clone, PartialEq, Eq)]
#[trust::skip]
pub(crate) struct CallSite {
    /// Fully-qualified name of the calling function.
    pub caller: String,
    /// Fully-qualified name of the callee.
    pub callee: String,
    /// How the call is dispatched.
    pub kind: CallKind,
    /// Human-readable source location (e.g. "src/lib.rs:42:5").
    pub location: String,
}

/// A summarized edge in the call graph (may aggregate multiple call sites).
#[derive(Debug, Clone, PartialEq, Eq)]
#[trust::skip]
pub(crate) struct CallEdge {
    /// Source function.
    pub from: String,
    /// Target function.
    pub to: String,
    /// Dominant call kind for this edge.
    pub kind: CallKind,
    /// Number of call sites from `from` to `to`.
    pub call_count: usize,
}

/// Summary statistics for a call graph.
#[derive(Debug, Clone, PartialEq, Eq)]
#[trust::skip]
pub(crate) struct CallGraphStats {
    pub total_nodes: usize,
    pub total_edges: usize,
    pub max_depth: usize,
    pub num_recursive: usize,
}

/// An interprocedural call graph built from MIR analysis.
///
/// Nodes are function names (strings). Edges carry call-site metadata.
#[derive(Debug, Clone)]
pub(crate) struct CallGraph {
    /// Set of all known function names.
    functions: FxHashSet<String>,
    /// Forward edges: caller -> [(callee, kind, count)].
    forward: FxHashMap<String, Vec<EdgeInfo>>,
    /// Reverse edges: callee -> [caller].
    reverse: FxHashMap<String, FxHashSet<String>>,
}

/// Internal compact edge representation.
#[derive(Debug, Clone)]
struct EdgeInfo {
    target: String,
    kind: CallKind,
    count: usize,
}

impl CallGraph {
    /// Create an empty call graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            functions: FxHashSet::default(),
            forward: FxHashMap::default(),
            reverse: FxHashMap::default(),
        }
    }

    /// Register a function node (even if it has no calls).
    pub(crate) fn add_function(&mut self, name: &str) {
        self.functions.insert(name.to_string());
    }

    /// Add a call site to the graph. Both caller and callee are auto-registered.
    pub(crate) fn add_call(&mut self, site: CallSite) {
        self.functions.insert(site.caller.clone());
        self.functions.insert(site.callee.clone());

        // Update or insert forward edge.
        let edges = self.forward.entry(site.caller.clone()).or_default();
        if let Some(existing) = edges.iter_mut().find(|e| e.target == site.callee) {
            existing.count += 1;
        } else {
            edges.push(EdgeInfo { target: site.callee.clone(), kind: site.kind, count: 1 });
        }

        // Update reverse edge.
        self.reverse.entry(site.callee).or_default().insert(site.caller);
    }

    /// Return all functions that call `function`.
    #[must_use]
    pub(crate) fn callers_of<'a>(&'a self, function: &str) -> Vec<&'a str> {
        self.reverse
            .get(function)
            .map(|set| set.iter().map(|s| s.as_str()).collect())
            .unwrap_or_default()
    }

    /// Return all functions called by `function`.
    #[must_use]
    pub(crate) fn callees_of<'a>(&'a self, function: &str) -> Vec<&'a str> {
        self.forward
            .get(function)
            .map(|edges| edges.iter().map(|e| e.target.as_str()).collect())
            .unwrap_or_default()
    }

    /// Return all functions transitively reachable from `function` (excluding itself
    /// unless it is in a cycle).
    #[must_use]
    pub(crate) fn reachable_from(&self, function: &str) -> Vec<String> {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();

        // Seed with direct callees.
        if let Some(edges) = self.forward.get(function) {
            for edge in edges {
                if visited.insert(edge.target.clone()) {
                    queue.push_back(edge.target.clone());
                }
            }
        }

        while let Some(current) = queue.pop_front() {
            if let Some(edges) = self.forward.get(&current) {
                for edge in edges {
                    if visited.insert(edge.target.clone()) {
                        queue.push_back(edge.target.clone());
                    }
                }
            }
        }

        let mut result: Vec<String> = visited.into_iter().collect();
        result.sort();
        result
    }

    /// Check whether `function` is (directly or transitively) recursive.
    #[must_use]
    pub(crate) fn is_recursive(&self, function: &str) -> bool {
        // Direct self-recursion check.
        if let Some(edges) = self.forward.get(function) {
            if edges.iter().any(|e| e.target == function) {
                return true;
            }
        }
        // Mutual recursion: check if `function` is in an SCC of size > 1.
        for scc in self.strongly_connected_components() {
            if scc.iter().any(|member| member == function) {
                return scc.len() > 1;
            }
        }
        false
    }

    /// Compute strongly connected components using Tarjan's algorithm.
    ///
    /// Returns SCCs in reverse topological order (leaves first).
    #[must_use]
    pub(crate) fn strongly_connected_components(&self) -> Vec<Vec<String>> {
        let mut index_counter: usize = 0;
        let mut stack: Vec<String> = Vec::new();
        let mut on_stack: FxHashSet<String> = FxHashSet::default();
        let mut indices: FxHashMap<String, usize> = FxHashMap::default();
        let mut lowlinks: FxHashMap<String, usize> = FxHashMap::default();
        let mut result: Vec<Vec<String>> = Vec::new();

        // Collect all nodes in sorted order for determinism.
        let mut nodes: Vec<&String> = self.functions.iter().collect();
        nodes.sort();

        for node in &nodes {
            if !indices.contains_key(*node) {
                self.tarjan_strongconnect(
                    node,
                    &mut index_counter,
                    &mut stack,
                    &mut on_stack,
                    &mut indices,
                    &mut lowlinks,
                    &mut result,
                );
            }
        }

        // Sort each SCC internally for determinism.
        for scc in &mut result {
            scc.sort();
        }
        result
    }

    /// Tarjan's DFS helper (iterative to avoid stack overflow on deep graphs).
    fn tarjan_strongconnect(
        &self,
        start: &str,
        index_counter: &mut usize,
        stack: &mut Vec<String>,
        on_stack: &mut FxHashSet<String>,
        indices: &mut FxHashMap<String, usize>,
        lowlinks: &mut FxHashMap<String, usize>,
        result: &mut Vec<Vec<String>>,
    ) {
        // Use an explicit work stack to avoid recursion limits.
        struct Frame {
            node: String,
            edge_idx: usize,
        }

        let mut work: Vec<Frame> = Vec::new();

        // Initialize start node.
        indices.insert(start.to_string(), *index_counter);
        lowlinks.insert(start.to_string(), *index_counter);
        *index_counter += 1;
        stack.push(start.to_string());
        on_stack.insert(start.to_string());
        work.push(Frame { node: start.to_string(), edge_idx: 0 });

        while let Some(frame) = work.last_mut() {
            let successors: Vec<String> = self
                .forward
                .get(&frame.node)
                .map(|edges| edges.iter().map(|e| e.target.clone()).collect())
                .unwrap_or_default();

            if frame.edge_idx < successors.len() {
                let successor = &successors[frame.edge_idx];
                frame.edge_idx += 1;

                if !indices.contains_key(successor) {
                    // Tree edge: recurse.
                    indices.insert(successor.clone(), *index_counter);
                    lowlinks.insert(successor.clone(), *index_counter);
                    *index_counter += 1;
                    stack.push(successor.clone());
                    on_stack.insert(successor.clone());
                    work.push(Frame { node: successor.clone(), edge_idx: 0 });
                } else if on_stack.contains(successor) {
                    // Back edge: update lowlink.
                    let current_node = frame.node.clone();
                    let current_low = lowlinks[&current_node];
                    let successor_idx = indices[successor];
                    if successor_idx < current_low {
                        lowlinks.insert(current_node, successor_idx);
                    }
                }
            } else {
                // All successors processed. Check if this is an SCC root.
                let current_node = frame.node.clone();
                let current_low = lowlinks[&current_node];
                let current_idx = indices[&current_node];

                if current_low == current_idx {
                    // Pop SCC from stack.
                    let mut scc = Vec::new();
                    while let Some(top) = stack.pop() {
                        on_stack.remove(&top);
                        let is_root = top == current_node;
                        scc.push(top);
                        if is_root {
                            break;
                        }
                    }
                    result.push(scc);
                }

                work.pop();

                // Propagate lowlink to parent.
                if let Some(parent) = work.last() {
                    let parent_node = parent.node.clone();
                    let parent_low = lowlinks[&parent_node];
                    if current_low < parent_low {
                        lowlinks.insert(parent_node, current_low);
                    }
                }
            }
        }
    }

    /// Return a topological ordering of the call graph, or `None` if cycles exist.
    #[must_use]
    pub(crate) fn topological_order(&self) -> Option<Vec<String>> {
        // Kahn's algorithm.
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for func in &self.functions {
            in_degree.entry(func.as_str()).or_insert(0);
        }
        for edges in self.forward.values() {
            for edge in edges {
                *in_degree.entry(edge.target.as_str()).or_insert(0) += 1;
            }
        }

        // Seed with zero in-degree nodes (sorted for determinism).
        let mut queue: VecDeque<String> = {
            let mut zeros: Vec<String> = in_degree
                .iter()
                .filter(|(_, deg)| **deg == 0)
                .map(|(name, _)| name.to_string())
                .collect();
            zeros.sort();
            zeros.into_iter().collect()
        };

        let mut order = Vec::with_capacity(self.functions.len());

        while let Some(node) = queue.pop_front() {
            order.push(node.clone());
            if let Some(edges) = self.forward.get(&node) {
                // Process successors in sorted order for determinism.
                let mut targets: Vec<&str> = edges.iter().map(|e| e.target.as_str()).collect();
                targets.sort();
                for target in targets {
                    if let Some(deg) = in_degree.get_mut(target) {
                        *deg -= 1;
                        if *deg == 0 {
                            queue.push_back(target.to_string());
                        }
                    }
                }
            }
        }

        if order.len() == self.functions.len() {
            Some(order)
        } else {
            None // Cycle detected.
        }
    }

    /// Compute summary statistics.
    #[must_use]
    pub(crate) fn stats(&self) -> CallGraphStats {
        let total_edges = self.forward.values().map(|v| v.len()).sum();

        // Count recursive functions.
        let num_recursive = self.functions.iter().filter(|f| self.is_recursive(f)).count();

        // Compute max depth via BFS from each root (node with in-degree 0).
        let roots: Vec<&str> = self
            .functions
            .iter()
            .filter(|f| !self.reverse.get(f.as_str()).map_or(false, |callers| !callers.is_empty()))
            .map(|s| s.as_str())
            .collect();

        let mut max_depth = 0;
        for root in &roots {
            let depth = self.bfs_depth(root);
            if depth > max_depth {
                max_depth = depth;
            }
        }

        // If all nodes are in cycles (no roots), try from every node.
        if roots.is_empty() {
            for func in &self.functions {
                let depth = self.bfs_depth(func);
                if depth > max_depth {
                    max_depth = depth;
                }
            }
        }

        CallGraphStats { total_nodes: self.functions.len(), total_edges, max_depth, num_recursive }
    }

    /// Number of registered function nodes.
    #[must_use]
    pub(crate) fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Return all edges as `CallEdge` summaries.
    #[must_use]
    pub(crate) fn edges(&self) -> Vec<CallEdge> {
        let mut result = Vec::new();
        for (from, edges) in &self.forward {
            for edge in edges {
                result.push(CallEdge {
                    from: from.clone(),
                    to: edge.target.clone(),
                    kind: edge.kind,
                    call_count: edge.count,
                });
            }
        }
        result.sort_by(|a, b| (&a.from, &a.to).cmp(&(&b.from, &b.to)));
        result
    }

    /// Number of unique directed edges.
    #[must_use]
    pub(crate) fn edge_count(&self) -> usize {
        self.forward.values().map(|v| v.len()).sum()
    }

    /// BFS depth from a start node (longest shortest path to any reachable node).
    fn bfs_depth(&self, start: &str) -> usize {
        let mut visited = FxHashSet::default();
        visited.insert(start.to_string());
        let mut queue = VecDeque::new();
        queue.push_back((start.to_string(), 0usize));
        let mut max_d = 0;

        while let Some((node, depth)) = queue.pop_front() {
            if depth > max_d {
                max_d = depth;
            }
            if let Some(edges) = self.forward.get(&node) {
                for edge in edges {
                    if visited.insert(edge.target.clone()) {
                        queue.push_back((edge.target.clone(), depth + 1));
                    }
                }
            }
        }

        max_d
    }
}

impl Default for CallGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to build a CallSite quickly.
    fn site(caller: &str, callee: &str, kind: CallKind) -> CallSite {
        CallSite {
            caller: caller.to_string(),
            callee: callee.to_string(),
            kind,
            location: format!("{}->{}", caller, callee),
        }
    }

    #[test]
    fn test_call_graph_new_is_empty() {
        let cg = CallGraph::new();
        assert_eq!(cg.function_count(), 0);
        assert_eq!(cg.edge_count(), 0);
    }

    #[test]
    fn test_call_graph_add_function_increments_count() {
        let mut cg = CallGraph::new();
        cg.add_function("foo");
        cg.add_function("bar");
        assert_eq!(cg.function_count(), 2);
        // Adding duplicate is idempotent.
        cg.add_function("foo");
        assert_eq!(cg.function_count(), 2);
    }

    #[test]
    fn test_call_graph_add_call_registers_both_endpoints() {
        let mut cg = CallGraph::new();
        cg.add_call(site("main", "helper", CallKind::Direct));
        assert_eq!(cg.function_count(), 2);
        assert_eq!(cg.edge_count(), 1);
    }

    #[test]
    fn test_call_graph_callees_of() {
        let mut cg = CallGraph::new();
        cg.add_call(site("main", "foo", CallKind::Direct));
        cg.add_call(site("main", "bar", CallKind::Direct));
        let mut callees = cg.callees_of("main");
        callees.sort();
        assert_eq!(callees, vec!["bar", "foo"]);
        assert!(cg.callees_of("foo").is_empty());
    }

    #[test]
    fn test_call_graph_callers_of() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "c", CallKind::Direct));
        cg.add_call(site("b", "c", CallKind::Direct));
        let mut callers = cg.callers_of("c");
        callers.sort();
        assert_eq!(callers, vec!["a", "b"]);
        assert!(cg.callers_of("a").is_empty());
    }

    #[test]
    fn test_call_graph_callers_callees_unknown_function() {
        let cg = CallGraph::new();
        assert!(cg.callers_of("nonexistent").is_empty());
        assert!(cg.callees_of("nonexistent").is_empty());
    }

    #[test]
    fn test_call_graph_reachable_from_linear_chain() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("b", "c", CallKind::Direct));
        cg.add_call(site("c", "d", CallKind::Direct));
        let reachable = cg.reachable_from("a");
        assert_eq!(reachable, vec!["b", "c", "d"]);
    }

    #[test]
    fn test_call_graph_reachable_from_excludes_self_unless_cycle() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        let reachable = cg.reachable_from("a");
        assert!(!reachable.contains(&"a".to_string()));
    }

    #[test]
    fn test_call_graph_reachable_from_includes_self_on_cycle() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("b", "a", CallKind::Direct));
        let reachable = cg.reachable_from("a");
        assert!(reachable.contains(&"a".to_string()));
        assert!(reachable.contains(&"b".to_string()));
    }

    #[test]
    fn test_call_graph_is_recursive_direct() {
        let mut cg = CallGraph::new();
        cg.add_call(site("fib", "fib", CallKind::Direct));
        assert!(cg.is_recursive("fib"));
    }

    #[test]
    fn test_call_graph_is_recursive_mutual() {
        let mut cg = CallGraph::new();
        cg.add_call(site("even", "odd", CallKind::Direct));
        cg.add_call(site("odd", "even", CallKind::Direct));
        assert!(cg.is_recursive("even"));
        assert!(cg.is_recursive("odd"));
    }

    #[test]
    fn test_call_graph_is_recursive_false_for_non_recursive() {
        let mut cg = CallGraph::new();
        cg.add_call(site("main", "helper", CallKind::Direct));
        assert!(!cg.is_recursive("main"));
        assert!(!cg.is_recursive("helper"));
    }

    #[test]
    fn test_call_graph_scc_no_cycles() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("b", "c", CallKind::Direct));
        let sccs = cg.strongly_connected_components();
        // Each node is its own SCC.
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.len(), 1);
        }
    }

    #[test]
    fn test_call_graph_scc_with_cycle() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("b", "c", CallKind::Direct));
        cg.add_call(site("c", "a", CallKind::Direct));
        cg.add_function("d");
        let sccs = cg.strongly_connected_components();
        // One 3-node SCC + one singleton.
        let big: Vec<&Vec<String>> = sccs.iter().filter(|s| s.len() > 1).collect();
        assert_eq!(big.len(), 1);
        assert_eq!(big[0].len(), 3);
    }

    #[test]
    fn test_call_graph_topological_order_acyclic() {
        let mut cg = CallGraph::new();
        cg.add_call(site("main", "foo", CallKind::Direct));
        cg.add_call(site("main", "bar", CallKind::Direct));
        cg.add_call(site("foo", "baz", CallKind::Direct));
        let order = cg.topological_order().expect("acyclic graph should have topo order");
        // main must come before foo and bar; foo must come before baz.
        let pos = |name: &str| order.iter().position(|n| n == name).unwrap();
        assert!(pos("main") < pos("foo"));
        assert!(pos("main") < pos("bar"));
        assert!(pos("foo") < pos("baz"));
    }

    #[test]
    fn test_call_graph_topological_order_returns_none_on_cycle() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("b", "a", CallKind::Direct));
        assert!(cg.topological_order().is_none());
    }

    #[test]
    fn test_call_graph_stats_basic() {
        let mut cg = CallGraph::new();
        cg.add_call(site("main", "foo", CallKind::Direct));
        cg.add_call(site("foo", "bar", CallKind::Direct));
        cg.add_call(site("bar", "bar", CallKind::Direct)); // self-recursive
        let stats = cg.stats();
        assert_eq!(stats.total_nodes, 3);
        assert_eq!(stats.total_edges, 3);
        assert_eq!(stats.num_recursive, 1);
        assert!(stats.max_depth >= 2);
    }

    #[test]
    fn test_call_graph_multiple_calls_same_edge_increment_count() {
        let mut cg = CallGraph::new();
        cg.add_call(site("a", "b", CallKind::Direct));
        cg.add_call(site("a", "b", CallKind::Direct));
        // Still one edge, but count should be 2.
        assert_eq!(cg.edge_count(), 1);
        let callees = cg.callees_of("a");
        assert_eq!(callees, vec!["b"]);
    }

    #[test]
    fn test_call_graph_different_call_kinds() {
        let mut cg = CallGraph::new();
        cg.add_call(site("dispatch", "target", CallKind::Virtual));
        cg.add_call(site("dispatch", "closure", CallKind::Closure));
        cg.add_call(site("dispatch", "unknown", CallKind::Indirect));
        assert_eq!(cg.edge_count(), 3);
        let mut callees = cg.callees_of("dispatch");
        callees.sort();
        assert_eq!(callees, vec!["closure", "target", "unknown"]);
    }

    #[test]
    fn test_call_graph_default_is_empty() {
        let cg = CallGraph::default();
        assert_eq!(cg.function_count(), 0);
        assert_eq!(cg.edge_count(), 0);
    }
}
