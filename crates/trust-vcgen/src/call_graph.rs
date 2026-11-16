// trust_vcgen/call_graph.rs: Call graph construction and cycle detection
//
// Builds a CallGraph from a set of VerifiableFunction definitions by
// scanning ordinary and tail-call edges. Provides cycle detection (Tarjan's SCC)
// for identifying recursive functions that need special summary handling.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::call_graph::{CallGraph, CallGraphEdge, CallGraphNode, CalleeResolver};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Terminator, VerifiableFunction};

/// Build a call graph from a slice of verifiable functions.
///
/// Scans each function's basic blocks for ordinary and tail-call edges and
/// constructs a directed graph of caller -> callee relationships.
/// The first function in the slice is treated as the entry point.
#[must_use]
pub fn build_call_graph(functions: &[VerifiableFunction]) -> CallGraph {
    let mut graph = CallGraph::new();
    graph.nodes.reserve(functions.len());

    // Add nodes for all functions
    for (i, func) in functions.iter().enumerate() {
        graph.add_node(CallGraphNode {
            def_path: func.def_path.clone(),
            name: func.name.clone(),
            is_public: true,
            is_entry_point: i == 0,
            span: func.span.clone(),
        });
    }

    let resolver = CalleeResolver::new(
        functions.iter().map(|func| (func.def_path.as_str(), func.name.as_str())),
    );

    // Scan for call edges
    for func in functions {
        for block in &func.body.blocks {
            let (callee_name, args, span) = match &block.terminator {
                Terminator::Call { func, args, span, .. }
                | Terminator::TailCall { func, args, span, .. } => (func, args, span),
                _ => continue,
            };
            // Preserve ambiguous or external spellings as unresolved
            // edges. Proof-producing consumers must never guess which of
            // several same-named functions was called.
            let callee_path = resolver.resolve(callee_name).unwrap_or(callee_name).to_string();

            graph.add_edge(CallGraphEdge {
                caller: func.def_path.clone(),
                callee: callee_path,
                call_site: span.clone(),
            });

            // Trust: W6 closure-composition ordering — a Fn-trait
            // `call_once`/`call_mut`/`call` dispatch names its closure by the
            // SPAN-shaped receiver string (`<{closure@…} as FnOnce<…>>::…`), which
            // carries NO def_path_hash, so the edge above resolves to that span text,
            // NOT the closure BODY. Add the REAL caller→closure edge recovered from
            // the first actual's `Ty::Closure.name` so the closure LEAF certifies
            // BEFORE this caller in `compute_verification_order` (callees-first).
            // Additive + sound: it only pulls a genuine callee earlier; a cycle still
            // fails closed (Tarjan/DFS visited-set), and the closure def-path is a
            // real corpus node when present.
            if let Some(closure_def) = fn_trait_closure_callee(callee_name, args, &func.body) {
                graph.add_edge(CallGraphEdge {
                    caller: func.def_path.clone(),
                    callee: closure_def,
                    call_site: span.clone(),
                });
            }
        }
    }

    graph
}

/// Resolve the CLOSURE def-path a Fn-trait method call dispatches to, from the ENV
/// RECEIVER (the first actual). `Some(name)` ONLY when `callee_name` is a
/// `call_once`/`call_mut`/`call` Fn-trait dispatch AND the first actual is a
/// projectionless (possibly `&`-wrapped) `Ty::Closure { name, .. }`. The span-shaped
/// Fn-trait `func` string carries no def_path_hash, so this recovers the closure body
/// identity the SAME way the W6 closure-composition recognizer does (the env operand's
/// closure type) — for verification ORDERING only, never a proof claim. Fail-closed
/// (`None`) on anything else, so a non-closure call can never gain a spurious edge.
fn fn_trait_closure_callee(
    callee_name: &str,
    args: &[trust_types::Operand],
    body: &trust_types::VerifiableBody,
) -> Option<String> {
    use trust_types::{Operand, Ty};
    if !callee_name.contains("call") {
        return None;
    }
    let (Operand::Move(p) | Operand::Copy(p)) = args.first()? else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let closure_name = match &body.locals.get(p.local)?.ty {
        Ty::Closure { name, .. } => name,
        Ty::Ref { inner, .. } => match &**inner {
            Ty::Closure { name, .. } => name,
            _ => return None,
        },
        _ => return None,
    };
    let is_fn_trait = callee_name.contains("call_once")
        || callee_name.contains("call_mut")
        || (callee_name.ends_with("::call")
            && callee_name.contains(" as ")
            && callee_name.contains("Fn"));
    is_fn_trait.then(|| closure_name.clone())
}

/// A strongly connected component (set of mutually recursive functions).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scc {
    /// Function def_paths in this SCC.
    pub members: Vec<String>,
}

impl Scc {
    /// Returns true if this SCC contains a cycle (more than one member,
    /// or a single member that calls itself).
    #[must_use]
    pub fn is_recursive(&self) -> bool {
        self.members.len() > 1
    }
}

/// Detect strongly connected components (cycles) in a call graph.
///
/// Uses Tarjan's algorithm. Returns SCCs in reverse topological order
/// (leaf SCCs first). An SCC with >1 member indicates mutual recursion.
/// Self-recursive functions appear as single-member SCCs but can be
/// detected by checking if their def_path appears in their own call edges.
#[must_use]
pub fn detect_cycles(graph: &CallGraph) -> Vec<Scc> {
    let n_nodes = graph.nodes.len();
    if n_nodes == 0 {
        return Vec::new();
    }
    let mut sorted_nodes: Vec<&str> = Vec::with_capacity(n_nodes);
    if graph.edges.is_empty() {
        for n in &graph.nodes {
            sorted_nodes.push(n.def_path.as_str());
        }
        sorted_nodes.sort_unstable();
        return sorted_nodes.into_iter().map(|s| Scc { members: vec![s.to_string()] }).collect();
    }
    let mut node_set: FxHashSet<&str> =
        FxHashSet::with_capacity_and_hasher(n_nodes, Default::default());
    for n in &graph.nodes {
        let s = n.def_path.as_str();
        sorted_nodes.push(s);
        node_set.insert(s);
    }

    // Build adjacency list (only for callers with in-graph outgoing edges)
    let mut adj: FxHashMap<&str, Vec<&str>> =
        FxHashMap::with_capacity_and_hasher(n_nodes, Default::default());
    for edge in &graph.edges {
        if node_set.contains(edge.callee.as_str()) {
            adj.entry(edge.caller.as_str()).or_default().push(&edge.callee);
        }
    }

    // Tarjan's SCC algorithm
    let mut index_counter: usize = 0;
    let mut stack: Vec<&str> = Vec::with_capacity(n_nodes);
    let mut on_stack: FxHashSet<&str> =
        FxHashSet::with_capacity_and_hasher(n_nodes, Default::default());
    let mut indices: FxHashMap<&str, usize> =
        FxHashMap::with_capacity_and_hasher(n_nodes, Default::default());
    let mut lowlinks: FxHashMap<&str, usize> =
        FxHashMap::with_capacity_and_hasher(n_nodes, Default::default());
    let mut sccs: Vec<Scc> = Vec::with_capacity(n_nodes);

    #[allow(clippy::too_many_arguments)]
    fn strongconnect<'a>(
        v: &'a str,
        adj: &FxHashMap<&str, Vec<&'a str>>,
        index_counter: &mut usize,
        stack: &mut Vec<&'a str>,
        on_stack: &mut FxHashSet<&'a str>,
        indices: &mut FxHashMap<&'a str, usize>,
        lowlinks: &mut FxHashMap<&'a str, usize>,
        sccs: &mut Vec<Scc>,
    ) {
        let v_idx = *index_counter;
        indices.insert(v, v_idx);
        lowlinks.insert(v, v_idx);
        *index_counter += 1;
        stack.push(v);
        on_stack.insert(v);

        if let Some(successors) = adj.get(v) {
            for &w in successors {
                if let Some(&w_idx) = indices.get(w) {
                    if on_stack.contains(w)
                        && let Some(v_low) = lowlinks.get_mut(v)
                    {
                        *v_low = (*v_low).min(w_idx);
                    }
                } else {
                    strongconnect(w, adj, index_counter, stack, on_stack, indices, lowlinks, sccs);
                    let w_low = lowlinks[w];
                    if let Some(v_low) = lowlinks.get_mut(v) {
                        *v_low = (*v_low).min(w_low);
                    }
                }
            }
        }

        if lowlinks[v] == v_idx {
            let mut scc_members = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack.remove(w);
                scc_members.push(w.to_string());
                if w == v {
                    break;
                }
            }
            if scc_members.len() > 1 {
                scc_members.sort_unstable(); // deterministic order
            }
            sccs.push(Scc { members: scc_members });
        }
    }

    // Sort nodes for deterministic output
    sorted_nodes.sort_unstable();

    for &node in &sorted_nodes {
        if !indices.contains_key(node) {
            strongconnect(
                node,
                &adj,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut sccs,
            );
        }
    }

    sccs
}

/// Check if a specific function is self-recursive (calls itself directly).
#[must_use]
pub fn is_self_recursive(graph: &CallGraph, def_path: &str) -> bool {
    graph.edges.iter().any(|e| e.caller == def_path && e.callee == def_path)
}

/// Return the set of functions involved in any cycle (recursive functions).
#[must_use]
pub fn recursive_functions(graph: &CallGraph) -> FxHashSet<String> {
    if graph.edges.is_empty() || graph.nodes.is_empty() {
        return FxHashSet::default();
    }
    if graph.nodes.len() == 1 {
        let mut result = FxHashSet::default();
        let def_path = &graph.nodes[0].def_path;
        if is_self_recursive(graph, def_path) {
            result.insert(def_path.clone());
        }
        return result;
    }
    let sccs = detect_cycles(graph);
    let mut result = FxHashSet::default();

    for scc in sccs {
        if scc.is_recursive() {
            result.extend(scc.members);
        }
    }

    // Check self-recursion in O(V + E) instead of O(V * E).
    let mut node_set =
        FxHashSet::with_capacity_and_hasher(graph.nodes.len(), Default::default());
    for n in &graph.nodes {
        node_set.insert(n.def_path.as_str());
    }
    for edge in &graph.edges {
        if edge.caller == edge.callee
            && !result.contains(edge.caller.as_str())
            && node_set.contains(edge.caller.as_str())
        {
            result.insert(edge.caller.clone());
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Helper: build a minimal function with optional call terminators.
    fn make_func(name: &str, def_path: &str, calls: &[&str]) -> VerifiableFunction {
        let mut blocks = Vec::new();

        for (i, callee) in calls.iter().enumerate() {
            let target =
                if i + 1 < calls.len() { Some(BlockId(i + 1)) } else { Some(BlockId(calls.len())) };
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target,
                    span: span(),
                    atomic: None,
                },
            });
        }

        // Final return block
        blocks.push(BasicBlock {
            id: BlockId(calls.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks,
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn make_tail_func(name: &str, def_path: &str, callee: &str) -> VerifiableFunction {
        let mut func = make_func(name, def_path, &[callee]);
        let Terminator::Call {
            func: callee, args, span, atomic, callee_identity, callee_key, ..
        } = func.body.blocks[0].terminator.clone()
        else {
            unreachable!();
        };
        func.body.blocks[0].terminator = Terminator::TailCall {
            func: callee,
            args,
            span,
            atomic,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity,
            callee_key,
        };
        func.body.blocks.truncate(1);
        func
    }

    #[test]
    fn test_build_call_graph_linear_chain() {
        // A -> B -> C
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c"]),
            make_func("c", "crate::c", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.edges.len(), 2);
        assert!(graph.edges.iter().any(|e| e.caller == "crate::a" && e.callee == "crate::b"));
        assert!(graph.edges.iter().any(|e| e.caller == "crate::b" && e.callee == "crate::c"));
    }

    #[test]
    fn test_build_call_graph_diamond() {
        // A -> B, A -> C, B -> D, C -> D
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b", "crate::c"]),
            make_func("b", "crate::b", &["crate::d"]),
            make_func("c", "crate::c", &["crate::d"]),
            make_func("d", "crate::d", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 4);
        assert_eq!(graph.edges.len(), 4);
    }

    #[test]
    fn test_build_call_graph_name_resolution() {
        // Caller references callee by short name
        let funcs = vec![
            make_func("caller", "crate::caller", &["helper"]),
            make_func("helper", "crate::util::helper", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.edges.len(), 1);
        // Edge should resolve to full def_path
        assert_eq!(graph.edges[0].callee, "crate::util::helper");
    }

    #[test]
    fn test_build_call_graph_preserves_ambiguous_short_name_as_unresolved() {
        let funcs = vec![
            make_func("caller", "crate::caller", &["helper", "crate::right::helper"]),
            make_func("helper", "crate::left::helper", &[]),
            make_func("helper", "crate::right::helper", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.edges[0].callee, "helper");
        assert_eq!(
            graph.edges[1].callee, "crate::right::helper",
            "an exact path remains resolvable even when its short name is ambiguous"
        );
    }

    #[test]
    fn test_detect_cycles_no_cycles() {
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c"]),
            make_func("c", "crate::c", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let sccs = detect_cycles(&graph);

        // All SCCs should be single-member (no mutual recursion)
        for scc in &sccs {
            assert_eq!(scc.members.len(), 1, "no cycles expected");
            assert!(!scc.is_recursive());
        }
    }

    #[test]
    fn test_detect_cycles_mutual_recursion() {
        // A -> B, B -> A (mutual recursion)
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::a"]),
        ];
        let graph = build_call_graph(&funcs);
        let sccs = detect_cycles(&graph);

        // Should find one SCC with both members
        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
        assert_eq!(recursive_sccs[0].members.len(), 2);
        assert!(recursive_sccs[0].members.contains(&"crate::a".to_string()));
        assert!(recursive_sccs[0].members.contains(&"crate::b".to_string()));
    }

    #[test]
    fn tail_calls_participate_in_mutual_recursion_sccs() {
        let funcs = vec![
            make_tail_func("a", "crate::a", "crate::b"),
            make_tail_func("b", "crate::b", "crate::a"),
        ];
        let graph = build_call_graph(&funcs);
        assert_eq!(graph.edges.len(), 2);
        let recursive = recursive_functions(&graph);
        assert_eq!(recursive.len(), 2);
        assert!(recursive.contains("crate::a"));
        assert!(recursive.contains("crate::b"));
    }

    #[test]
    fn test_detect_cycles_self_recursion() {
        // factorial calls itself
        let funcs = vec![make_func("factorial", "crate::factorial", &["crate::factorial"])];
        let graph = build_call_graph(&funcs);

        assert!(is_self_recursive(&graph, "crate::factorial"));

        let rec = recursive_functions(&graph);
        assert!(rec.contains("crate::factorial"));
    }

    #[test]
    fn test_recursive_functions_mixed() {
        // A -> B -> C, B -> B (self-recursive), D -> E -> D (mutual)
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c", "crate::b"]),
            make_func("c", "crate::c", &[]),
            make_func("d", "crate::d", &["crate::e"]),
            make_func("e", "crate::e", &["crate::d"]),
        ];
        let graph = build_call_graph(&funcs);
        let rec = recursive_functions(&graph);

        assert!(rec.contains("crate::b"), "b is self-recursive");
        assert!(rec.contains("crate::d"), "d is in mutual recursion with e");
        assert!(rec.contains("crate::e"), "e is in mutual recursion with d");
        assert!(!rec.contains("crate::a"), "a is not recursive");
        assert!(!rec.contains("crate::c"), "c is not recursive");
    }

    #[test]
    fn test_build_call_graph_empty() {
        let graph = build_call_graph(&[]);
        assert!(graph.nodes.is_empty());
        assert!(graph.edges.is_empty());
    }

    #[test]
    fn test_build_call_graph_single_no_calls() {
        let funcs = vec![make_func("leaf", "crate::leaf", &[])];
        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.edges.is_empty());
        assert!(graph.nodes[0].is_entry_point);
    }
}
