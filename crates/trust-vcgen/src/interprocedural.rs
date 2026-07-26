// trust_vcgen/interprocedural.rs: Interprocedural analysis for verification ordering
//
// Computes verification order from call graphs (topological sort, callees first)
// and builds function summaries that capture preconditions, postconditions,
// side effects, and purity. Summaries from verified callees are applied to
// strengthen caller VCs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::call_graph::CallGraph;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;

use crate::call_graph::{build_call_graph, recursive_functions};
use crate::modular::FunctionSummary;
use crate::summaries::{self, SummaryStore};

/// Side effects that a function may have.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SideEffects {
    /// Places that may be written (mutated).
    pub writes: Vec<String>,
    /// Whether the function may panic.
    pub may_panic: bool,
    /// Whether the function performs I/O or calls external functions.
    pub may_diverge: bool,
}

/// Extended function summary for interprocedural analysis.
///
/// Extends the base `FunctionSummary` with side effect and purity information
/// derived from the function body analysis.
#[derive(Debug, Clone)]
pub struct InterproceduralSummary {
    /// Base summary (pre/postconditions, proved status).
    pub base: FunctionSummary,
    /// Side effects discovered from the function body.
    pub side_effects: SideEffects,
    /// Whether the function is pure (no side effects, no panics, no divergence).
    pub is_pure: bool,
}

impl InterproceduralSummary {
    /// Create a new summary for a function with no conditions and unknown purity.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            base: FunctionSummary::new(name),
            side_effects: SideEffects::default(),
            is_pure: true,
        }
    }
}

/// Analyzer that computes verification ordering and function summaries
/// from a call graph and set of verifiable functions.
#[derive(Debug)]
pub struct InterproceduralAnalyzer {
    /// Computed verification order (callees before callers).
    order: Vec<String>,
    /// Summaries indexed by function def_path.
    summaries: FxHashMap<String, InterproceduralSummary>,
}

impl InterproceduralAnalyzer {
    /// Create a new analyzer from a call graph.
    ///
    /// Computes topological verification order (callees first). Functions
    /// in cycles are grouped together and ordered arbitrarily within the cycle.
    #[must_use]
    pub fn new(graph: &CallGraph) -> Self {
        let order = compute_verification_order(graph);
        Self { order, summaries: FxHashMap::default() }
    }

    /// Returns the computed verification order.
    #[must_use]
    pub fn verification_order(&self) -> &[String] {
        &self.order
    }

    /// Store a computed summary for a function.
    pub fn insert_summary(&mut self, summary: InterproceduralSummary) {
        self.summaries.insert(summary.base.name.clone(), summary);
    }

    /// Retrieve a summary by function name.
    #[must_use]
    pub fn get_summary(&self, name: &str) -> Option<&InterproceduralSummary> {
        self.summaries.get(name)
    }

    /// Number of stored summaries.
    #[must_use]
    pub fn summary_count(&self) -> usize {
        self.summaries.len()
    }
}

/// Result of interprocedural analysis over a set of functions.
#[derive(Debug)]
pub struct AnalysisResult {
    /// Summaries computed for all analyzed functions.
    pub summaries: SummaryStore,
    /// Verification order used (callees first).
    pub verification_order: Vec<String>,
    /// Functions identified as recursive.
    pub recursive: FxHashSet<String>,
    /// VCs generated for all functions. Callee summaries are recorded, but their
    /// postconditions are not used as global caller assumptions.
    pub all_vcs: Vec<VerificationCondition>,
}

/// Run full bottom-up interprocedural analysis on a set of functions.
///
/// This is the main entry point for interprocedural VC generation:
/// 1. Build the call graph from the function set
/// 2. Detect cycles to identify recursive functions
/// 3. Compute verification order (topological sort, callees first)
/// 4. For each function in order:
///    - Compute summary using available callee summaries
///    - For recursive functions, use Unknown summary (no postconditions)
///    - Generate VCs, recording callee summaries without treating their
///      postconditions as global premises
/// 5. Return all VCs and computed summaries
#[must_use]
pub fn analyze_functions(functions: &[VerifiableFunction]) -> AnalysisResult {
    if functions.is_empty() {
        return AnalysisResult {
            summaries: SummaryStore::new(),
            verification_order: Vec::new(),
            recursive: FxHashSet::default(),
            all_vcs: Vec::new(),
        };
    }

    // Build call graph and detect cycles
    let graph = build_call_graph(functions);
    let rec_funcs = recursive_functions(&graph);
    let order = compute_verification_order(&graph);
    let resolver = graph.callee_resolver();

    // Build a lookup from def_path to function
    let func_map: FxHashMap<&str, &VerifiableFunction> =
        functions.iter().map(|f| (f.def_path.as_str(), f)).collect();

    let mut store = SummaryStore::new();
    let mut all_vcs = Vec::new();

    // Bottom-up: process functions in verification order (callees first)
    for def_path in &order {
        let Some(func) = func_map.get(def_path.as_str()) else {
            continue;
        };

        let is_recursive = rec_funcs.contains(def_path);

        // Compute summary using available callee summaries. The older
        // recursive_verify path was removed with the trust_wp migration.
        let summary = summaries::compute_summary(func, &store, &resolver, is_recursive);

        // Generate VCs for this function
        let mut func_vcs = crate::generate_vcs(func);

        // Record call-site summaries without injecting callee postconditions as
        // global assumptions. `substitute_callee_summary` remains conservative
        // until it has precise call-site substitution and dominance semantics.
        for block in &func.body.blocks {
            if let Terminator::Call { func: callee_name, .. } = &block.terminator
                && let Some(callee_path) = resolver.resolve(callee_name)
                && let Some(callee_summary) = store.get(callee_path)
                && callee_summary.has_postconditions()
            {
                func_vcs = func_vcs
                    .into_iter()
                    .map(|vc| summaries::substitute_callee_summary(vc, callee_summary))
                    .collect();
            }
        }

        all_vcs.extend(func_vcs);
        store.insert(summary);
    }

    AnalysisResult { summaries: store, verification_order: order, recursive: rec_funcs, all_vcs }
}

/// Compute a topological verification order from a call graph.
///
/// Returns function def_paths in an order such that callees appear before
/// callers. This ensures that when verifying a caller, all callee summaries
/// are already available.
///
/// Functions in strongly-connected components (mutual recursion) are grouped
/// together. Within an SCC, order is deterministic but arbitrary.
#[must_use]
pub fn compute_verification_order(graph: &CallGraph) -> Vec<String> {
    // Build adjacency list: caller -> [callee def_paths]
    let resolver = graph.callee_resolver();
    let mut adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for node in &graph.nodes {
        adj.entry(node.def_path.as_str()).or_default();
    }
    for edge in &graph.edges {
        if let Some(callee) = resolver.resolve(&edge.callee) {
            adj.entry(edge.caller.as_str()).or_default().push(callee);
        }
    }

    // Kahn's algorithm for topological sort (reverse: callees first).
    // Compute in-degree for each node.
    let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
    for node in &graph.nodes {
        in_degree.entry(node.def_path.as_str()).or_insert(0);
    }
    for edges in adj.values() {
        for &callee in edges {
            *in_degree.entry(callee).or_insert(0) += 1;
        }
    }

    // Start with nodes that have no incoming edges (leaf functions / no callers).
    // We want callees first, so we reverse the graph: start from functions
    // nobody calls (leaves), then add their callers.

    // Reverse adjacency: callee -> [callers]
    let mut rev_adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for node in &graph.nodes {
        rev_adj.entry(node.def_path.as_str()).or_default();
    }
    for (caller, callees) in &adj {
        for &callee in callees {
            rev_adj.entry(callee).or_default().push(caller);
        }
    }

    // out-degree in the original graph = in-degree in reversed graph
    // We want callees first, so use the original graph's out-degree
    // Actually, let's use a simpler post-order DFS approach.

    let mut visited: FxHashSet<&str> = FxHashSet::default();
    let mut result: Vec<String> = Vec::new();

    // Post-order DFS: visit callees before callers
    fn dfs<'a>(
        node: &'a str,
        adj: &FxHashMap<&str, Vec<&'a str>>,
        visited: &mut FxHashSet<&'a str>,
        result: &mut Vec<String>,
    ) {
        if !visited.insert(node) {
            return;
        }
        if let Some(callees) = adj.get(node) {
            for &callee in callees {
                dfs(callee, adj, visited, result);
            }
        }
        result.push(node.to_string());
    }

    // Sort nodes for deterministic output
    let mut sorted_nodes: Vec<&str> = graph.nodes.iter().map(|n| n.def_path.as_str()).collect();
    sorted_nodes.sort();

    for &node in &sorted_nodes {
        dfs(node, &adj, &mut visited, &mut result);
    }

    result
}

/// Compute a summary for a verifiable function.
///
/// Analyzes the function body to determine:
/// - Preconditions (from explicit `#[requires]` contracts)
/// - Postconditions (from explicit `#[ensures]` contracts)
/// - Side effects (writes, panics, divergence)
/// - Purity (no side effects)
#[must_use]
pub fn compute_summary(func: &VerifiableFunction) -> InterproceduralSummary {
    let mut summary = InterproceduralSummary::new(&func.name);

    // Extract preconditions from contracts
    for pre in &func.preconditions {
        summary.base.preconditions.push(pre.clone());
    }

    // Extract postconditions from contracts
    for post in &func.postconditions {
        summary.base.postconditions.push(post.clone());
    }

    // Note: Contract structs carry string bodies, not parsed formulas.
    // The parsed formulas are in func.preconditions and func.postconditions.

    // Analyze side effects from the function body
    let mut writes = Vec::new();
    let mut may_panic = false;
    let mut has_calls = false;

    for block in &func.body.blocks {
        // Check for writes in statements
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt {
                // Arguments (locals beyond arg_count) being written indicate mutation
                if place.local < func.body.arg_count && !place.projections.is_empty() {
                    let name = func
                        .body
                        .locals
                        .get(place.local)
                        .and_then(|d| d.name.as_deref())
                        .unwrap_or("unknown")
                        .to_string();
                    writes.push(name);
                }
            }
        }

        // Check terminator for panics and calls
        match &block.terminator {
            Terminator::Call { .. } => {
                has_calls = true;
            }
            Terminator::Assert { .. } => {
                may_panic = true;
            }
            Terminator::Unreachable => {
                may_panic = true;
            }
            _ => {}
        }
    }

    writes.sort();
    writes.dedup();

    summary.side_effects = SideEffects { writes, may_panic, may_diverge: has_calls };

    // A function is pure if it has no side effects
    summary.is_pure = summary.side_effects.writes.is_empty()
        && !summary.side_effects.may_panic
        && !summary.side_effects.may_diverge;

    summary
}

/// Record that a callee summary is available for a caller VC.
///
/// This function intentionally does not turn callee postconditions into
/// caller-side assumptions. A proved callee summary is evidence about the
/// callee, not a sound global premise for every VC in the caller. Precise
/// call-site substitution can be added later once return values, arguments, and
/// dominance are modeled explicitly.
#[must_use]
pub fn apply_callee_summary(
    caller_vc: VerificationCondition,
    _callee_summary: &InterproceduralSummary,
) -> VerificationCondition {
    caller_vc
}

#[cfg(test)]
mod tests {
    use trust_types::call_graph::{CallGraphEdge, CallGraphNode};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Build a simple chain: main -> a -> b -> c (no cycles).
    fn chain_graph() -> CallGraph {
        let mut g = CallGraph::new();
        for (path, name, is_entry) in [
            ("crate::main", "main", true),
            ("crate::a", "a", false),
            ("crate::b", "b", false),
            ("crate::c", "c", false),
        ] {
            g.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: true,
                is_entry_point: is_entry,
                span: span(),
            });
        }
        for (caller, callee) in
            [("crate::main", "crate::a"), ("crate::a", "crate::b"), ("crate::b", "crate::c")]
        {
            g.add_edge(CallGraphEdge {
                caller: caller.to_string(),
                callee: callee.to_string(),
                call_site: span(),
            });
        }
        g
    }

    #[test]
    fn test_verification_order_chain_callees_first() {
        let g = chain_graph();
        let order = compute_verification_order(&g);

        assert_eq!(order.len(), 4);

        // c must come before b, b before a, a before main
        let pos = |name: &str| order.iter().position(|s| s == name).unwrap();
        assert!(pos("crate::c") < pos("crate::b"), "c should be verified before b");
        assert!(pos("crate::b") < pos("crate::a"), "b should be verified before a");
        assert!(pos("crate::a") < pos("crate::main"), "a should be verified before main");
    }

    #[test]
    fn test_verification_order_empty_graph() {
        let g = CallGraph::new();
        let order = compute_verification_order(&g);
        assert!(order.is_empty());
    }

    #[test]
    fn test_verification_order_single_node() {
        let mut g = CallGraph::new();
        g.add_node(CallGraphNode {
            def_path: "crate::leaf".to_string(),
            name: "leaf".to_string(),
            is_public: true,
            is_entry_point: true,
            span: span(),
        });
        let order = compute_verification_order(&g);
        assert_eq!(order, vec!["crate::leaf"]);
    }

    #[test]
    fn test_verification_order_diamond() {
        // main -> a, main -> b, a -> c, b -> c
        let mut g = CallGraph::new();
        for (path, name, is_entry) in [
            ("crate::main", "main", true),
            ("crate::a", "a", false),
            ("crate::b", "b", false),
            ("crate::c", "c", false),
        ] {
            g.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: true,
                is_entry_point: is_entry,
                span: span(),
            });
        }
        for (caller, callee) in [
            ("crate::main", "crate::a"),
            ("crate::main", "crate::b"),
            ("crate::a", "crate::c"),
            ("crate::b", "crate::c"),
        ] {
            g.add_edge(CallGraphEdge {
                caller: caller.to_string(),
                callee: callee.to_string(),
                call_site: span(),
            });
        }

        let order = compute_verification_order(&g);
        assert_eq!(order.len(), 4);

        let pos = |name: &str| order.iter().position(|s| s == name).unwrap();
        assert!(pos("crate::c") < pos("crate::a"));
        assert!(pos("crate::c") < pos("crate::b"));
        assert!(pos("crate::a") < pos("crate::main"));
        assert!(pos("crate::b") < pos("crate::main"));
    }

    #[test]
    fn test_verification_order_cycle_no_panic() {
        // a -> b -> a (mutual recursion)
        let mut g = CallGraph::new();
        for (path, name) in [("crate::a", "a"), ("crate::b", "b")] {
            g.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: true,
                is_entry_point: false,
                span: span(),
            });
        }
        g.add_edge(CallGraphEdge {
            caller: "crate::a".to_string(),
            callee: "crate::b".to_string(),
            call_site: span(),
        });
        g.add_edge(CallGraphEdge {
            caller: "crate::b".to_string(),
            callee: "crate::a".to_string(),
            call_site: span(),
        });

        let order = compute_verification_order(&g);
        // Both nodes should appear exactly once
        assert_eq!(order.len(), 2);
        assert!(order.contains(&"crate::a".to_string()));
        assert!(order.contains(&"crate::b".to_string()));
    }

    #[test]
    fn test_compute_summary_pure_function() {
        // A simple function with no calls, no panics
        let func = VerifiableFunction {
            name: "add_one".to_string(),
            def_path: "test::add_one".to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let summary = compute_summary(&func);
        assert_eq!(summary.base.name, "add_one");
        assert!(summary.is_pure, "function with no calls/panics should be pure");
        assert!(summary.side_effects.writes.is_empty());
        assert!(!summary.side_effects.may_panic);
        assert!(!summary.side_effects.may_diverge);
    }

    #[test]
    fn test_compute_summary_with_contracts() {
        let pre =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let post = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );

        let func = VerifiableFunction {
            name: "checked_add".to_string(),
            def_path: "test::checked_add".to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![pre.clone()],
            postconditions: vec![post.clone()],
            spec: Default::default(),
        };

        let summary = compute_summary(&func);
        assert_eq!(summary.base.preconditions.len(), 1);
        assert_eq!(summary.base.preconditions[0], pre);
        assert_eq!(summary.base.postconditions.len(), 1);
        assert_eq!(summary.base.postconditions[0], post);
    }

    #[test]
    fn test_compute_summary_impure_function_with_call() {
        let func = VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "callee".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: None,
                        span: span(),
                        atomic: None,
                    },
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let summary = compute_summary(&func);
        assert!(!summary.is_pure, "function with calls should not be pure");
        assert!(summary.side_effects.may_diverge);
    }

    #[test]
    fn test_apply_callee_summary_proved_with_postconditions_is_conservative() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };

        let postcond =
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)));

        let mut summary = InterproceduralSummary::new("callee");
        summary.base.postconditions.push(postcond.clone());
        summary.base.proved = true;

        let result = apply_callee_summary(vc, &summary);
        assert_eq!(
            result.formula,
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0))),
            "proved callee postconditions are recorded, not injected as caller assumptions"
        );
    }

    #[test]
    fn test_apply_callee_summary_unproved_unchanged() {
        let original_formula = Formula::Bool(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: original_formula.clone(),
            contract_metadata: None,
        };

        let mut summary = InterproceduralSummary::new("callee");
        summary.base.postconditions.push(Formula::Bool(false));
        // NOT proved

        let result = apply_callee_summary(vc, &summary);
        assert_eq!(result.formula, original_formula, "unproved summary should not change VC");
    }

    #[test]
    fn test_apply_callee_summary_no_postconditions_unchanged() {
        let original_formula = Formula::Bool(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: original_formula.clone(),
            contract_metadata: None,
        };

        let mut summary = InterproceduralSummary::new("callee");
        summary.base.proved = true;
        // No postconditions

        let result = apply_callee_summary(vc, &summary);
        assert_eq!(result.formula, original_formula, "empty postconditions should not change VC");
    }

    #[test]
    fn test_apply_callee_summary_multiple_postconditions_is_conservative() {
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "caller".into(),
            location: span(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let post1 =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let post2 =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        let mut summary = InterproceduralSummary::new("callee");
        summary.base.postconditions.push(post1.clone());
        summary.base.postconditions.push(post2.clone());
        summary.base.proved = true;

        let result = apply_callee_summary(vc, &summary);
        assert_eq!(
            result.formula,
            Formula::Bool(true),
            "multiple callee postconditions are not injected as a global premise"
        );
    }

    #[test]
    fn test_interprocedural_analyzer_workflow() {
        let g = chain_graph();
        let mut analyzer = InterproceduralAnalyzer::new(&g);

        assert_eq!(analyzer.verification_order().len(), 4);
        assert_eq!(analyzer.summary_count(), 0);

        // Simulate verifying c first
        let mut c_summary = InterproceduralSummary::new("c");
        c_summary.base.postconditions.push(Formula::Bool(true));
        c_summary.base.proved = true;
        c_summary.is_pure = true;
        analyzer.insert_summary(c_summary);

        assert_eq!(analyzer.summary_count(), 1);
        let retrieved = analyzer.get_summary("c").unwrap();
        assert!(retrieved.base.proved);
        assert!(retrieved.is_pure);
    }

    #[test]
    fn test_verification_order_suffix_matching() {
        let mut g = CallGraph::new();
        g.add_node(CallGraphNode {
            def_path: "crate::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: span(),
        });
        g.add_node(CallGraphNode {
            def_path: "crate::util::helper".to_string(),
            name: "helper".to_string(),
            is_public: false,
            is_entry_point: false,
            span: span(),
        });
        // Edge uses short name
        g.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "helper".to_string(),
            call_site: span(),
        });

        let order = compute_verification_order(&g);
        assert_eq!(order.len(), 2);

        let pos = |name: &str| order.iter().position(|s| s == name).unwrap();
        assert!(
            pos("crate::util::helper") < pos("crate::main"),
            "helper should be verified before main via suffix matching"
        );
    }

    #[test]
    fn test_verification_order_ignores_ambiguous_short_name() {
        let mut g = CallGraph::new();
        for (path, name) in [
            ("crate::0_caller", "caller"),
            ("crate::left::helper", "helper"),
            ("crate::right::helper", "helper"),
        ] {
            g.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: false,
                is_entry_point: false,
                span: span(),
            });
        }
        g.add_edge(CallGraphEdge {
            caller: "crate::0_caller".to_string(),
            callee: "helper".to_string(),
            call_site: span(),
        });

        let order = compute_verification_order(&g);
        let pos = |name: &str| order.iter().position(|path| path == name).unwrap();

        assert!(pos("crate::0_caller") < pos("crate::left::helper"));
        assert!(pos("crate::0_caller") < pos("crate::right::helper"));
    }

    // -----------------------------------------------------------------------
    // Interprocedural analysis integration tests
    // -----------------------------------------------------------------------

    /// Helper: build a function with optional call edges and a division
    /// (to produce a DivisionByZero VC for testing summary strengthening).
    fn make_func_with_div(
        name: &str,
        def_path: &str,
        calls: &[&str],
        pre: Vec<Formula>,
        post: Vec<Formula>,
    ) -> VerifiableFunction {
        let mut blocks = Vec::new();
        let mut next_id = 0;

        // Call blocks
        for callee in calls {
            blocks.push(BasicBlock {
                id: BlockId(next_id),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(next_id + 1)),
                    span: span(),
                    atomic: None,
                },
            });
            next_id += 1;
        }

        // Block with a division (generates DivisionByZero VC)
        blocks.push(BasicBlock {
            id: BlockId(next_id),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                ],
                blocks,
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: pre,
            postconditions: post,
            spec: Default::default(),
        }
    }

    /// Test: Linear call chain A -> B -> C
    ///
    /// C has postcondition y >= 1. The summary is recorded, but not injected as
    /// a caller-wide assumption.
    #[test]
    fn test_analyze_linear_chain_a_b_c() {
        let post_c =
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)));

        let funcs = vec![
            make_func_with_div("a", "crate::a", &["crate::b"], vec![], vec![]),
            make_func_with_div("b", "crate::b", &["crate::c"], vec![], vec![]),
            make_func_with_div("c", "crate::c", &[], vec![], vec![post_c.clone()]),
        ];

        let result = analyze_functions(&funcs);

        // Verification order: C first, then B, then A
        let pos = |name: &str| result.verification_order.iter().position(|s| s == name).unwrap();
        assert!(pos("crate::c") < pos("crate::b"), "C before B");
        assert!(pos("crate::b") < pos("crate::a"), "B before A");

        // All three functions should have summaries
        assert_eq!(result.summaries.len(), 3);

        // C's summary should have the postcondition
        let c_sum = result.summaries.get("crate::c").unwrap();
        assert_eq!(c_sum.postconditions, vec![post_c.clone()]);
        assert!(c_sum.is_complete);

        // No recursive functions in a linear chain
        assert!(result.recursive.is_empty());

        // DivisionByZero checks are now handled by trust-mc-lib.
        // The division in make_func_with_div no longer produces VCs from
        // trust_vcgen's generate_vcs. VCs may still be empty or contain only
        // non-division VCs from other checkers (contracts, specs, etc.).
        // The interprocedural analysis structure is still validated above.
    }

    /// Test: Diamond call pattern A -> B, A -> C, B -> D, C -> D
    ///
    /// D has postcondition. Both B and C record D's summary, but do not use it
    /// as a caller-wide assumption.
    /// A calls both B and C.
    #[test]
    fn test_analyze_diamond_pattern() {
        let post_d =
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)));

        let funcs = vec![
            make_func_with_div("a", "crate::a", &["crate::b", "crate::c"], vec![], vec![]),
            make_func_with_div("b", "crate::b", &["crate::d"], vec![], vec![]),
            make_func_with_div("c", "crate::c", &["crate::d"], vec![], vec![]),
            make_func_with_div("d", "crate::d", &[], vec![], vec![post_d.clone()]),
        ];

        let result = analyze_functions(&funcs);

        // D must come before B and C, both before A
        let pos = |name: &str| result.verification_order.iter().position(|s| s == name).unwrap();
        assert!(pos("crate::d") < pos("crate::b"));
        assert!(pos("crate::d") < pos("crate::c"));
        assert!(pos("crate::b") < pos("crate::a"));
        assert!(pos("crate::c") < pos("crate::a"));

        assert_eq!(result.summaries.len(), 4);
        assert!(result.recursive.is_empty());

        // D's summary
        let d_sum = result.summaries.get("crate::d").unwrap();
        assert_eq!(d_sum.postconditions, vec![post_d.clone()]);

        // B's VCs should not be globally strengthened with D's postcondition.
        let b_vcs: Vec<_> = result.all_vcs.iter().filter(|vc| vc.function == "b").collect();
        for vc in &b_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "B's VCs should not have callee summary assumptions"
            );
        }

        // C's VCs should not be globally strengthened with D's postcondition.
        let c_vcs: Vec<_> = result.all_vcs.iter().filter(|vc| vc.function == "c").collect();
        for vc in &c_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "C's VCs should not have callee summary assumptions"
            );
        }
    }

    #[test]
    fn test_analyze_ambiguous_short_name_never_consumes_a_summary() {
        let left_pre = Formula::Eq(
            Box::new(Formula::Var("left".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        let right_pre = Formula::Eq(
            Box::new(Formula::Var("right".into(), Sort::Int)),
            Box::new(Formula::Int(2)),
        );
        let funcs = vec![
            make_func_with_div("helper", "crate::a::helper", &[], vec![left_pre.clone()], vec![]),
            make_func_with_div("helper", "crate::b::helper", &[], vec![right_pre.clone()], vec![]),
            make_func_with_div("caller", "crate::z_caller", &["helper"], vec![], vec![]),
        ];

        let result = analyze_functions(&funcs);
        let caller = result.summaries.get("crate::z_caller").unwrap();

        assert!(!caller.is_complete, "ambiguous callees must be treated as unresolved");
        assert!(!caller.preconditions.contains(&left_pre));
        assert!(!caller.preconditions.contains(&right_pre));
    }

    /// Test: Simple recursion (factorial with base case)
    ///
    /// Recursive functions should get Unknown summary (no postconditions).
    /// Their VCs should NOT be strengthened with their own summary.
    #[test]
    fn test_analyze_simple_recursion_factorial() {
        // factorial calls itself
        let funcs = vec![make_func_with_div(
            "factorial",
            "crate::factorial",
            &["crate::factorial"],
            vec![Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )],
            vec![], // No postconditions (would need user-provided invariant)
        )];

        let result = analyze_functions(&funcs);

        // factorial should be identified as recursive
        assert!(
            result.recursive.contains("crate::factorial"),
            "factorial should be detected as recursive"
        );

        // Summary should be Unknown (incomplete, no postconditions)
        let f_sum = result.summaries.get("crate::factorial").unwrap();
        assert!(f_sum.is_recursive);
        assert!(!f_sum.is_complete);
        assert!(
            f_sum.postconditions.is_empty(),
            "recursive function without invariant should have no postconditions"
        );

        // VCs should NOT be wrapped in Implies (no callee postconditions)
        let f_vcs: Vec<_> = result.all_vcs.iter().filter(|vc| vc.function == "factorial").collect();
        assert!(!f_vcs.is_empty(), "factorial should produce VCs");
        for vc in &f_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "recursive function VCs should not be strengthened (Unknown summary)"
            );
        }
    }

    /// Test: Empty function set produces empty results.
    #[test]
    fn test_analyze_empty_functions() {
        let result = analyze_functions(&[]);

        assert!(result.summaries.is_empty());
        assert!(result.verification_order.is_empty());
        assert!(result.recursive.is_empty());
        assert!(result.all_vcs.is_empty());
    }

    /// Test: Mutual recursion (A calls B, B calls A) both get Unknown.
    #[test]
    fn test_analyze_mutual_recursion() {
        let funcs = vec![
            make_func_with_div("a", "crate::a", &["crate::b"], vec![], vec![]),
            make_func_with_div("b", "crate::b", &["crate::a"], vec![], vec![]),
        ];

        let result = analyze_functions(&funcs);

        assert!(result.recursive.contains("crate::a"));
        assert!(result.recursive.contains("crate::b"));

        // Both summaries should be Unknown
        for path in &["crate::a", "crate::b"] {
            let s = result.summaries.get(path).unwrap();
            assert!(s.is_recursive);
            assert!(!s.is_complete);
        }
    }
}
