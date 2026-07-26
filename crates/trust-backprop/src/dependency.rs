//! Call graph analysis for dependency-aware cross-module rewriting.
//!
//! Builds a call graph from `VerifiableFunction` data by inspecting
//! `Terminator::Call` in each function's MIR blocks. Provides topological
//! ordering (callee-first) so rewrites propagate correctly.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::call_graph::{CalleeResolver, resolve_unique_def_path};
use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{Terminator, VerifiableFunction};

/// A call graph mapping function def-paths to the functions they call.
#[derive(Debug, Clone)]
pub struct CallGraph {
    /// For each function def-path, the set of resolved callee def-paths.
    /// External or ambiguous call spellings remain unresolved strings.
    edges: FxHashMap<String, FxHashSet<String>>,
    /// All known function def-paths (including those with no outgoing calls).
    nodes: FxHashSet<String>,
    /// Declared short name for each function def-path.
    names: FxHashMap<String, String>,
}

impl CallGraph {
    /// Return the set of callees for a given function, or `None` if unknown.
    /// Exact def-paths and unambiguous shorthand are accepted.
    #[must_use]
    pub fn callees(&self, function: &str) -> Option<&FxHashSet<String>> {
        self.resolve_function(function).and_then(|def_path| self.edges.get(def_path))
    }

    /// Return the set of callees for a given function, or empty set if unknown.
    #[must_use]
    pub fn callees_or_empty(&self, function: &str) -> FxHashSet<String> {
        self.callees(function).cloned().unwrap_or_default()
    }

    /// Return all known function def-paths in the graph.
    #[must_use]
    pub fn functions(&self) -> &FxHashSet<String> {
        &self.nodes
    }

    /// Return the set of callers (reverse edges) for a given function.
    #[must_use]
    pub fn callers(&self, function: &str) -> FxHashSet<String> {
        let Some(function) = self.resolve_function(function) else { return FxHashSet::default() };
        self.edges
            .iter()
            .filter(|(_, callees)| callees.contains(function))
            .map(|(caller, _)| caller.clone())
            .collect()
    }

    /// Resolve an exact def-path or globally unique shorthand to a node.
    #[must_use]
    pub fn resolve_function(&self, function: &str) -> Option<&str> {
        resolve_unique_def_path(
            function,
            self.names.iter().map(|(def_path, name)| (def_path.as_str(), name.as_str())),
        )
    }

    /// Return the declared short name for an exact function def-path.
    #[must_use]
    pub fn function_name(&self, def_path: &str) -> Option<&str> {
        self.names.get(def_path).map(String::as_str)
    }

    /// Return the number of functions (nodes) in the graph.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the graph is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// Build a call graph from a slice of `VerifiableFunction`s.
///
/// Inspects `Terminator::Call { func, .. }` in each function's MIR blocks
/// to discover caller-callee relationships. Only functions present in the
/// input slice are included as def-path-keyed nodes. External and ambiguous
/// callees remain unresolved edges and cannot affect internal rewrite order.
#[must_use]
pub fn build_call_graph(functions: &[VerifiableFunction]) -> CallGraph {
    let mut edges: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut nodes: FxHashSet<String> = FxHashSet::default();
    let mut names: FxHashMap<String, String> = FxHashMap::default();
    let resolver = CalleeResolver::new(
        functions.iter().map(|func| (func.def_path.as_str(), func.name.as_str())),
    );

    for func in functions {
        nodes.insert(func.def_path.clone());
        names.insert(func.def_path.clone(), func.name.clone());
        let callees = edges.entry(func.def_path.clone()).or_default();

        for block in &func.body.blocks {
            if let Terminator::Call { func: callee, .. } = &block.terminator {
                callees.insert(resolver.resolve(callee).unwrap_or(callee).to_owned());
            }
        }
    }

    CallGraph { edges, nodes, names }
}

/// Produce a topological ordering of functions: callees before callers.
///
/// This ensures that when we apply rewrites, a callee's new precondition
/// is established before we generate the corresponding caller-site checks.
///
/// If the graph contains cycles, functions in cycles are appended at the end
/// in deterministic def-path order (cycles in call graphs are valid -- mutual recursion).
#[must_use]
pub fn topological_order(graph: &CallGraph) -> Vec<String> {
    // Kahn's algorithm with reversed edges (we want callees first).
    // In-degree here means "number of functions I call that are in the graph."
    // Actually, we want callees first, so we use standard topological sort
    // where edges go caller -> callee, and we output sinks (no outgoing
    // in-graph edges) first.

    // Emit nodes with no outgoing in-graph edges first, then their callers.
    let mut out_degree: FxHashMap<&str, usize> = FxHashMap::default();
    for node in &graph.nodes {
        let count = graph
            .edges
            .get(node.as_str())
            .map(|callees| callees.iter().filter(|c| graph.nodes.contains(c.as_str())).count())
            .unwrap_or(0);
        out_degree.insert(node.as_str(), count);
    }

    // Reverse edges: callee -> set of callers (within graph nodes)
    let mut reverse: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for node in &graph.nodes {
        reverse.entry(node.as_str()).or_default();
    }
    for (caller, callees) in &graph.edges {
        if !graph.nodes.contains(caller.as_str()) {
            continue;
        }
        for callee in callees {
            if graph.nodes.contains(callee.as_str()) {
                reverse.entry(callee.as_str()).or_default().push(caller.as_str());
            }
        }
    }

    let mut queue: VecDeque<&str> = VecDeque::new();
    for (node, &deg) in &out_degree {
        if deg == 0 {
            queue.push_back(node);
        }
    }

    // Sort the initial queue for deterministic output.
    let mut sorted_queue: Vec<&str> = queue.drain(..).collect();
    sorted_queue.sort();
    queue.extend(sorted_queue);

    let mut result = Vec::with_capacity(graph.nodes.len());

    while let Some(node) = queue.pop_front() {
        result.push(node.to_owned());
        // For each caller of this node, decrement their out-degree.
        if let Some(callers) = reverse.get(node) {
            let mut callers_sorted: Vec<&str> = callers.clone();
            callers_sorted.sort();
            for caller in callers_sorted {
                if let Some(deg) = out_degree.get_mut(caller) {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        queue.push_back(caller);
                    }
                }
            }
        }
    }

    // Append any remaining nodes (part of cycles) in sorted order.
    let in_result: FxHashSet<&str> = result.iter().map(String::as_str).collect();
    let mut remaining: Vec<String> =
        graph.nodes.iter().filter(|n| !in_result.contains(n.as_str())).cloned().collect();
    remaining.sort();
    result.extend(remaining);

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Helper to make a minimal VerifiableFunction with specified callees.
    fn make_function(name: &str, callees: &[&str]) -> VerifiableFunction {
        make_function_at(name, &format!("crate::{name}"), callees)
    }

    fn make_function_at(name: &str, def_path: &str, callees: &[&str]) -> VerifiableFunction {
        let mut blocks = Vec::new();

        // Create a block for each callee with a Call terminator.
        for (i, callee) in callees.iter().enumerate() {
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(i + 1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            });
        }

        // Final block with Return terminator.
        blocks.push(BasicBlock {
            id: BlockId(callees.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals: vec![], blocks, arg_count: 0, return_ty: Ty::Unit },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_build_call_graph_empty() {
        let graph = build_call_graph(&[]);
        assert!(graph.is_empty());
        assert_eq!(graph.len(), 0);
    }

    #[test]
    fn test_build_call_graph_single_no_calls() {
        let funcs = vec![make_function("main", &[])];
        let graph = build_call_graph(&funcs);
        assert_eq!(graph.len(), 1);
        assert!(graph.functions().contains("crate::main"));
        assert!(graph.callees_or_empty("main").is_empty());
    }

    #[test]
    fn test_build_call_graph_simple_call() {
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        assert_eq!(graph.len(), 2);
        assert!(graph.callees_or_empty("caller").contains("crate::callee"));
        assert!(graph.callees_or_empty("callee").is_empty());
    }

    #[test]
    fn test_build_call_graph_qualified_name() {
        let funcs = vec![
            make_function("main", &["crate::module::helper"]),
            make_function_at("helper", "crate::module::helper", &[]),
        ];
        let graph = build_call_graph(&funcs);
        assert!(graph.callees_or_empty("main").contains("crate::module::helper"));
    }

    #[test]
    fn test_build_call_graph_chain() {
        // a -> b -> c
        let funcs =
            vec![make_function("a", &["b"]), make_function("b", &["c"]), make_function("c", &[])];
        let graph = build_call_graph(&funcs);
        assert!(graph.callees_or_empty("a").contains("crate::b"));
        assert!(graph.callees_or_empty("b").contains("crate::c"));
        assert!(graph.callees_or_empty("c").is_empty());
    }

    #[test]
    fn test_build_call_graph_multiple_callees() {
        let funcs = vec![
            make_function("main", &["foo", "bar", "baz"]),
            make_function("foo", &[]),
            make_function("bar", &[]),
            make_function("baz", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let callees = graph.callees_or_empty("main");
        assert_eq!(callees.len(), 3);
        assert!(callees.contains("crate::foo"));
        assert!(callees.contains("crate::bar"));
        assert!(callees.contains("crate::baz"));
    }

    #[test]
    fn test_callers() {
        let funcs =
            vec![make_function("a", &["c"]), make_function("b", &["c"]), make_function("c", &[])];
        let graph = build_call_graph(&funcs);
        let callers = graph.callers("c");
        assert_eq!(callers.len(), 2);
        assert!(callers.contains("crate::a"));
        assert!(callers.contains("crate::b"));
    }

    #[test]
    fn test_callers_unknown_function() {
        let funcs = vec![make_function("a", &[])];
        let graph = build_call_graph(&funcs);
        assert!(graph.callers("nonexistent").is_empty());
    }

    #[test]
    fn test_topological_order_empty() {
        let graph = build_call_graph(&[]);
        let order = topological_order(&graph);
        assert!(order.is_empty());
    }

    #[test]
    fn test_topological_order_single() {
        let funcs = vec![make_function("main", &[])];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        assert_eq!(order, vec!["crate::main"]);
    }

    #[test]
    fn test_topological_order_callee_before_caller() {
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        let caller_pos = order.iter().position(|n| n == "crate::caller").unwrap();
        let callee_pos = order.iter().position(|n| n == "crate::callee").unwrap();
        assert!(callee_pos < caller_pos, "callee should come before caller: {order:?}");
    }

    #[test]
    fn test_topological_order_chain() {
        // a -> b -> c: order should be c, b, a
        let funcs =
            vec![make_function("a", &["b"]), make_function("b", &["c"]), make_function("c", &[])];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        assert_eq!(order, vec!["crate::c", "crate::b", "crate::a"]);
    }

    #[test]
    fn test_topological_order_diamond() {
        //   a
        //  / \
        // b   c
        //  \ /
        //   d
        let funcs = vec![
            make_function("a", &["b", "c"]),
            make_function("b", &["d"]),
            make_function("c", &["d"]),
            make_function("d", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);

        let pos = |name: &str| order.iter().position(|n| n == name).unwrap();
        assert!(pos("crate::d") < pos("crate::b"), "d before b: {order:?}");
        assert!(pos("crate::d") < pos("crate::c"), "d before c: {order:?}");
        assert!(pos("crate::b") < pos("crate::a"), "b before a: {order:?}");
        assert!(pos("crate::c") < pos("crate::a"), "c before a: {order:?}");
    }

    #[test]
    fn test_topological_order_cycle() {
        // a -> b -> a (mutual recursion): both should appear
        let funcs = vec![make_function("a", &["b"]), make_function("b", &["a"])];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        assert_eq!(order.len(), 2);
        assert!(order.contains(&"crate::a".to_string()));
        assert!(order.contains(&"crate::b".to_string()));
    }

    #[test]
    fn test_topological_order_external_callee_ignored() {
        // "main" calls "external_fn" which is not in the graph.
        // Only "main" should appear in the ordering.
        let funcs = vec![make_function("main", &["external_fn"])];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        assert_eq!(order, vec!["crate::main"]);
    }

    #[test]
    fn test_topological_order_independent_functions() {
        let funcs = vec![
            make_function("alpha", &[]),
            make_function("beta", &[]),
            make_function("gamma", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let order = topological_order(&graph);
        // Independent functions sorted alphabetically for determinism.
        assert_eq!(order, vec!["crate::alpha", "crate::beta", "crate::gamma"]);
    }

    #[test]
    fn test_duplicate_short_names_keep_distinct_nodes_and_ambiguous_edge_unresolved() {
        let funcs = vec![
            make_function("caller", &["helper"]),
            make_function_at("helper", "crate::left::helper", &[]),
            make_function_at("helper", "crate::right::helper", &[]),
        ];
        let graph = build_call_graph(&funcs);

        assert_eq!(graph.len(), 3);
        assert!(graph.functions().contains("crate::left::helper"));
        assert!(graph.functions().contains("crate::right::helper"));
        assert!(graph.resolve_function("helper").is_none());
        assert!(graph.callers("helper").is_empty());

        let callees = graph.callees_or_empty("crate::caller");
        assert!(callees.contains("helper"), "ambiguous spelling remains unresolved");
        assert!(!callees.contains("crate::left::helper"));
        assert!(!callees.contains("crate::right::helper"));

        let order = topological_order(&graph);
        let caller = order.iter().position(|path| path == "crate::caller").unwrap();
        let left = order.iter().position(|path| path == "crate::left::helper").unwrap();
        let right = order.iter().position(|path| path == "crate::right::helper").unwrap();
        assert!(caller < left && caller < right, "ambiguous edge must not impose a dependency");
    }
}
