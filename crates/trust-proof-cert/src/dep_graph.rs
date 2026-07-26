// trust-proof-cert dependency graph
//
// Directed graph of public certificate-record dependencies between functions.
// Supports topological sorting for inspection order and
// Tarjan's algorithm for strongly connected component (SCC) detection
// to identify mutual recursion.
//
// Record presence is structural metadata, not proof authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::CertError;

/// A node in the certificate-record dependency graph, representing a function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DepNode {
    /// Fully qualified function name.
    pub function: String,
    /// Functions this function calls (outgoing edges).
    pub callees: Vec<String>,
    /// Whether a public certificate record exists for this function.
    ///
    /// This flag says nothing about record integrity or proof authority.
    pub has_record: bool,
}

/// A strongly connected component: a set of mutually recursive functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StronglyConnectedComponent {
    /// Function names in this SCC.
    pub functions: Vec<String>,
}

impl StronglyConnectedComponent {
    /// Returns true if this SCC represents mutual recursion (more than one function).
    pub fn is_recursive(&self) -> bool {
        self.functions.len() > 1
    }
}

/// Result of analyzing the dependency graph.
#[derive(Debug, Clone, PartialEq)]
pub struct DepGraphAnalysis {
    /// Functions in topological order (callees before callers).
    /// Empty if the graph has cycles.
    pub topological_order: Vec<String>,
    /// Strongly connected components (groups of mutually recursive functions).
    pub sccs: Vec<StronglyConnectedComponent>,
    /// Registered functions with no public certificate record.
    pub without_record: Vec<String>,
    /// Record-bearing functions whose transitive registered dependencies are
    /// also structurally covered.
    ///
    /// This is graph metadata only, not semantic proof discharge.
    pub structurally_covered: Vec<String>,
    /// Fraction of registered functions with public records (0.0 - 1.0).
    pub record_coverage: f64,
}

/// Directed graph of public certificate-record dependencies between functions.
///
/// Each node represents a function. Edges go from caller to callee
/// (function A depends on function B means A calls B). Structural inspection
/// proceeds with registered callees before callers. Neither the graph nor its
/// analysis establishes that any record is valid or authoritative.
#[derive(Debug, Clone)]
pub struct DepGraph {
    // Trust: BTreeMap for deterministic certificate output
    /// Nodes indexed by function name.
    nodes: BTreeMap<String, DepNode>,
}

impl DepGraph {
    /// Create a new empty dependency graph.
    pub fn new() -> Self {
        DepGraph { nodes: BTreeMap::new() }
    }

    /// Add a function node with its callees.
    pub fn add_function(&mut self, function: &str, callees: Vec<String>, has_record: bool) {
        self.nodes.insert(
            function.to_string(),
            DepNode { function: function.into(), callees, has_record },
        );
    }

    /// Get a node by function name.
    pub fn get_node(&self, function: &str) -> Option<&DepNode> {
        self.nodes.get(function)
    }

    /// Return all function names in the graph.
    pub fn functions(&self) -> Vec<String> {
        self.nodes.keys().cloned().collect()
    }

    /// Return the number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return true if the graph has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Compute topological order using Kahn's algorithm.
    ///
    /// Returns functions in dependency order: callees before callers.
    /// Returns `Err` if the graph contains cycles.
    pub fn topological_sort(&self) -> Result<Vec<String>, CertError> {
        // Count each caller's distinct registered dependencies and build the
        // reverse index once. The legacy implementation first built an unused
        // in-degree map, then rescanned every node after every pop (O(V*E)).
        let mut remaining_dependencies: BTreeMap<&str, usize> = BTreeMap::new();
        let mut callers_by_callee: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for name in self.nodes.keys() {
            remaining_dependencies.insert(name.as_str(), 0);
        }
        for node in self.nodes.values() {
            let registered_callees: BTreeSet<&str> = node
                .callees
                .iter()
                .map(String::as_str)
                .filter(|callee| self.nodes.contains_key(*callee))
                .collect();
            remaining_dependencies.insert(node.function.as_str(), registered_callees.len());
            for callee in registered_callees {
                callers_by_callee.entry(callee).or_default().insert(node.function.as_str());
            }
        }

        let mut ready: BTreeSet<&str> = remaining_dependencies
            .iter()
            .filter_map(|(&name, &count)| (count == 0).then_some(name))
            .collect();

        let mut result = Vec::new();
        while let Some(function) = ready.pop_first() {
            result.push(function.to_string());
            if let Some(callers) = callers_by_callee.get(function) {
                for caller in callers {
                    if let Some(count) = remaining_dependencies.get_mut(caller) {
                        debug_assert!(*count > 0, "each registered dependency is removed once");
                        *count -= 1;
                        if *count == 0 {
                            ready.insert(caller);
                        }
                    }
                }
            }
        }

        if result.len() != self.nodes.len() {
            return Err(CertError::VerificationFailed {
                reason: "dependency graph contains cycles; topological sort incomplete".to_string(),
            });
        }

        Ok(result)
    }

    /// Detect strongly connected components using Tarjan's algorithm.
    ///
    /// Returns SCCs in reverse topological order. SCCs with more than
    /// one function represent mutual recursion.
    pub fn find_sccs(&self) -> Vec<StronglyConnectedComponent> {
        let mut state = TarjanState::new();

        for name in self.nodes.keys() {
            if !state.visited.contains(name.as_str()) {
                self.tarjan_visit(name, &mut state);
            }
        }

        state.sccs
    }

    /// Tarjan's DFS visit.
    fn tarjan_visit<'a>(&'a self, node_name: &'a str, state: &mut TarjanState<'a>) {
        let index = state.next_index;
        state.next_index += 1;
        state.index.insert(node_name, index);
        state.lowlink.insert(node_name, index);
        state.visited.insert(node_name);
        state.stack.push(node_name);
        state.on_stack.insert(node_name);

        if let Some(node) = self.nodes.get(node_name) {
            for callee in &node.callees {
                let callee_str = callee.as_str();
                if !self.nodes.contains_key(callee_str) {
                    continue; // external dependency, skip
                }
                if !state.visited.contains(callee_str) {
                    self.tarjan_visit(callee_str, state);
                    let callee_low = state.lowlink[callee_str];
                    let node_low = state.lowlink[node_name];
                    if callee_low < node_low {
                        state.lowlink.insert(node_name, callee_low);
                    }
                } else if state.on_stack.contains(callee_str) {
                    let callee_idx = state.index[callee_str];
                    let node_low = state.lowlink[node_name];
                    if callee_idx < node_low {
                        state.lowlink.insert(node_name, callee_idx);
                    }
                }
            }
        }

        // If this node is a root of an SCC
        if state.lowlink[node_name] == state.index[node_name] {
            let mut scc_functions = Vec::new();
            loop {
                // SAFETY: Tarjan's algorithm guarantees the stack contains this node.
                // Invariant: Tarjan's algorithm guarantees the stack contains this node.
                let w = state
                    .stack
                    .pop()
                    .expect("invariant: Tarjan stack must contain current SCC root");
                state.on_stack.remove(w);
                scc_functions.push(w.to_string());
                if w == node_name {
                    break;
                }
            }
            scc_functions.sort(); // deterministic ordering
            state.sccs.push(StronglyConnectedComponent { functions: scc_functions });
        }
    }

    /// Analyze graph shape and public-record presence.
    ///
    /// `structurally_covered` is computed transitively over registered nodes.
    /// Unregistered callees are outside this graph's declared boundary. Callers
    /// that need them included must register them as nodes, even without a
    /// record. No result from this method grants proof authority.
    pub fn analyze(&self) -> DepGraphAnalysis {
        let sccs = self.find_sccs();

        let topological_order = self.topological_sort().unwrap_or_default();

        let without_record: Vec<String> = self
            .nodes
            .values()
            .filter(|node| !node.has_record)
            .map(|node| node.function.clone())
            .collect();

        // A one-hop presence check incorrectly covered A in A -> B -> C when
        // A and B had records but C did not. Grow coverage from record-bearing
        // leaves so every registered transitive dependency must be covered.
        let mut covered = BTreeSet::new();
        loop {
            let before = covered.len();
            for node in self.nodes.values().filter(|node| node.has_record) {
                let registered_callees_covered = node
                    .callees
                    .iter()
                    .filter(|callee| self.nodes.contains_key(callee.as_str()))
                    .all(|callee| covered.contains(callee));
                if registered_callees_covered {
                    covered.insert(node.function.clone());
                }
            }
            if covered.len() == before {
                break;
            }
        }
        let structurally_covered = covered.into_iter().collect();

        let total = self.nodes.len();
        let record_count = total - without_record.len();
        let record_coverage = if total == 0 { 0.0 } else { record_count as f64 / total as f64 };

        DepGraphAnalysis {
            topological_order,
            sccs,
            without_record,
            structurally_covered,
            record_coverage,
        }
    }
}

impl Default for DepGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Internal state for Tarjan's SCC algorithm.
struct TarjanState<'a> {
    next_index: usize,
    index: BTreeMap<&'a str, usize>,
    lowlink: BTreeMap<&'a str, usize>,
    visited: BTreeSet<&'a str>,
    stack: Vec<&'a str>,
    on_stack: BTreeSet<&'a str>,
    sccs: Vec<StronglyConnectedComponent>,
}

impl<'a> TarjanState<'a> {
    fn new() -> Self {
        TarjanState {
            next_index: 0,
            index: BTreeMap::new(),
            lowlink: BTreeMap::new(),
            visited: BTreeSet::new(),
            stack: Vec::new(),
            on_stack: BTreeSet::new(),
            sccs: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_graph_empty() {
        let graph = DepGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.len(), 0);
        assert!(graph.functions().is_empty());
    }

    #[test]
    fn test_dep_graph_add_function() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], true);

        assert_eq!(graph.len(), 2);
        assert!(!graph.is_empty());

        let foo = graph.get_node("foo").expect("foo should exist");
        assert_eq!(foo.callees, vec!["bar"]);
        assert!(foo.has_record);

        let bar = graph.get_node("bar").expect("bar should exist");
        assert!(bar.callees.is_empty());
    }

    #[test]
    fn test_dep_node_serialization_uses_record_language_only() {
        let node = DepNode { function: "foo".to_string(), callees: vec![], has_record: true };

        let json = serde_json::to_string(&node).unwrap();
        assert!(json.contains("\"has_record\":true"));
        assert!(!json.contains("has_proof"));
        assert!(
            serde_json::from_str::<DepNode>(r#"{"function":"foo","callees":[],"has_proof":true}"#)
                .is_err(),
            "the authority-shaped legacy field must not remain a deserialization alias"
        );
    }

    #[test]
    fn test_topological_sort_linear() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec![], true);

        let order = graph.topological_sort().expect("should succeed for acyclic graph");
        let pos_a = order.iter().position(|x| x == "a").expect("a in order");
        let pos_b = order.iter().position(|x| x == "b").expect("b in order");
        let pos_c = order.iter().position(|x| x == "c").expect("c in order");

        assert!(pos_c < pos_b, "c should come before b (callee first)");
        assert!(pos_b < pos_a, "b should come before a (callee first)");
    }

    #[test]
    fn test_topological_sort_diamond() {
        let mut graph = DepGraph::new();
        graph.add_function("main", vec!["left".to_string(), "right".to_string()], true);
        graph.add_function("left", vec!["shared".to_string()], true);
        graph.add_function("right", vec!["shared".to_string()], true);
        graph.add_function("shared", vec![], true);

        let order = graph.topological_sort().expect("should succeed");
        let pos_main = order.iter().position(|x| x == "main").expect("main");
        let pos_left = order.iter().position(|x| x == "left").expect("left");
        let pos_right = order.iter().position(|x| x == "right").expect("right");
        let pos_shared = order.iter().position(|x| x == "shared").expect("shared");

        assert!(pos_shared < pos_left, "shared before left");
        assert!(pos_shared < pos_right, "shared before right");
        assert!(pos_left < pos_main, "left before main");
        assert!(pos_right < pos_main, "right before main");
    }

    #[test]
    fn test_topological_sort_cycle_fails() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);

        let result = graph.topological_sort();
        assert!(result.is_err(), "cycle should cause topological sort to fail");
    }

    #[test]
    fn test_find_sccs_no_cycles() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec![], true);

        let sccs = graph.find_sccs();
        // Each function is its own SCC (no mutual recursion)
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.functions.len(), 1);
            assert!(!scc.is_recursive());
        }
    }

    #[test]
    fn test_find_sccs_mutual_recursion() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);
        graph.add_function("c", vec![], true);

        let sccs = graph.find_sccs();

        // Should have 2 SCCs: {a, b} and {c}
        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1, "should find one recursive SCC");
        let scc = &recursive_sccs[0];
        assert!(scc.functions.contains(&"a".to_string()));
        assert!(scc.functions.contains(&"b".to_string()));
    }

    #[test]
    fn test_find_sccs_three_way_cycle() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec!["a".to_string()], true);

        let sccs = graph.find_sccs();

        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
        assert_eq!(recursive_sccs[0].functions.len(), 3);
    }

    #[test]
    fn test_analyze_full_record_coverage() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], true);

        let analysis = graph.analyze();
        assert_eq!(analysis.topological_order.len(), 2);
        assert!(analysis.without_record.is_empty());
        assert_eq!(analysis.structurally_covered.len(), 2);
        assert!((analysis.record_coverage - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_partial_record_coverage() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], false);

        let analysis = graph.analyze();
        assert_eq!(analysis.without_record, vec!["bar"]);
        // foo has a record but its registered callee bar does not, so foo is
        // not structurally covered.
        assert!(
            !analysis.structurally_covered.contains(&"foo".to_string()),
            "foo should not be structurally covered when bar has no record"
        );
        assert!((analysis.record_coverage - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_empty_graph() {
        let graph = DepGraph::new();
        let analysis = graph.analyze();
        assert!(analysis.topological_order.is_empty());
        assert!(analysis.sccs.is_empty());
        assert!(analysis.without_record.is_empty());
        assert!(analysis.structurally_covered.is_empty());
        assert!((analysis.record_coverage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_with_cycles() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);

        let analysis = graph.analyze();
        // Topological order should be empty due to cycle
        assert!(analysis.topological_order.is_empty());
        // Should detect the SCC
        let recursive_sccs: Vec<_> = analysis.sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
    }

    #[test]
    fn test_dep_graph_external_callee() {
        // If a callee is not in the graph, it's an external dependency
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["external::bar".to_string()], true);

        let order = graph.topological_sort().expect("should succeed");
        assert_eq!(order, vec!["foo"]);

        let analysis = graph.analyze();
        // The graph explicitly treats unregistered callees as outside its
        // boundary, so foo is structurally covered within this graph.
        assert!(analysis.structurally_covered.contains(&"foo".to_string()));
    }

    #[test]
    fn test_analyze_transitive_missing_record_blocks_all_callers() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec![], false);

        let analysis = graph.analyze();
        assert_eq!(analysis.without_record, vec!["c"]);
        assert!(analysis.structurally_covered.is_empty());
        assert!((analysis.record_coverage - (2.0 / 3.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn test_topological_sort_deduplicates_edges() {
        let mut graph = DepGraph::new();
        graph.add_function("caller", vec!["callee".to_string(), "callee".to_string()], true);
        graph.add_function("callee", vec![], true);

        assert_eq!(graph.topological_sort().unwrap(), vec!["callee", "caller"]);
    }

    #[test]
    fn test_dep_graph_default() {
        let graph = DepGraph::default();
        assert!(graph.is_empty());
    }
}
