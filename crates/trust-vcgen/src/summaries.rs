// trust_vcgen/summaries.rs: Function summary computation and storage
//
// Provides `SummaryStore` for caching computed function summaries and
// `compute_summary` that builds a summary from a function body and its
// callee summaries. Callee postconditions are retained as evidence; they are
// not injected into callers without precise call-site modeling.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::call_graph::{CalleeResolver, resolve_unique_def_path};
use trust_types::fx::FxHashMap;
use trust_types::*;

/// A function summary mapping preconditions to postconditions.
///
/// Captures what a function requires from its callers and what it
/// guarantees to them. Used during interprocedural analysis to avoid
/// re-analyzing callees.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSummary {
    /// Function name.
    pub name: String,
    /// Function def_path.
    pub def_path: String,
    /// Preconditions the caller must establish.
    pub preconditions: Vec<Formula>,
    /// Postconditions the callee guarantees.
    pub postconditions: Vec<Formula>,
    /// Whether this summary is complete (all callees resolved) or
    /// approximate (recursive / unknown callees).
    pub is_complete: bool,
    /// Whether this function is recursive (directly or mutually).
    pub is_recursive: bool,
    /// F6 (float interval summaries): verifier-derived signed interval
    /// containing every possible f64 return value under the function's own
    /// gated preconditions (`generate::derive_float_result_range`); `None` for
    /// non-f64 returns, recursive functions, and anything the tracer cannot
    /// bound (fail-closed). See `modular::FunctionSummary::result_range` for
    /// the consumption-side authority discipline.
    pub result_range: Option<(f64, f64)>,
}

impl FunctionSummary {
    /// Create a new empty summary for a function.
    #[must_use]
    pub fn new(name: impl Into<String>, def_path: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            def_path: def_path.into(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            is_complete: true,
            is_recursive: false,
            result_range: None,
        }
    }

    /// Create an unknown/top summary for recursive functions.
    ///
    /// An unknown summary makes no guarantees: no postconditions and
    /// no preconditions. This is the safe default for functions whose
    /// behavior cannot be fully summarized (e.g., recursive functions
    /// without user-provided invariants).
    #[must_use]
    pub fn unknown(name: impl Into<String>, def_path: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            def_path: def_path.into(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            is_complete: false,
            is_recursive: true,
            result_range: None,
        }
    }

    /// Returns true if the summary carries proved postcondition evidence.
    #[must_use]
    pub fn has_postconditions(&self) -> bool {
        !self.postconditions.is_empty()
    }
}

/// Cache of computed function summaries, keyed by def_path.
#[derive(Debug, Clone, Default)]
pub struct SummaryStore {
    summaries: FxHashMap<String, FunctionSummary>,
}

impl SummaryStore {
    /// Create an empty summary store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace a function summary.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.def_path.clone(), summary);
    }

    /// Look up a summary by function def_path.
    #[must_use]
    pub fn get(&self, def_path: &str) -> Option<&FunctionSummary> {
        self.summaries.get(def_path)
    }

    /// Look up a summary by an exact def-path or unique function shorthand.
    ///
    /// This scans all stored entries and fails closed when a shorthand matches
    /// more than one function. Interprocedural analysis should resolve against
    /// its complete call graph instead: a partially populated store can make a
    /// globally ambiguous shorthand appear temporarily unique.
    #[must_use]
    pub fn get_by_name(&self, name: &str) -> Option<&FunctionSummary> {
        let def_path = resolve_unique_def_path(
            name,
            self.summaries
                .values()
                .map(|summary| (summary.def_path.as_str(), summary.name.as_str())),
        )?;
        self.get(def_path)
    }

    /// Number of stored summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Returns true if no summaries are stored.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// Iterate over all stored summaries.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &FunctionSummary)> {
        self.summaries.iter()
    }
}

/// Compute a function summary from its body and available callee summaries.
///
/// This performs a lightweight analysis:
/// 1. Collects explicit preconditions and postconditions from the function spec
/// 2. Propagates callee preconditions as caller requirements
/// 3. If a callee has no summary (external or unresolved), marks the summary
///    incomplete
///
/// For recursive functions, pass `is_recursive = true` to produce an
/// incomplete summary that does not claim completeness.
#[must_use]
pub(crate) fn compute_summary(
    func: &VerifiableFunction,
    callee_summaries: &SummaryStore,
    callee_resolver: &CalleeResolver<'_>,
    is_recursive: bool,
) -> FunctionSummary {
    let mut summary = FunctionSummary::new(&func.name, &func.def_path);
    summary.is_recursive = is_recursive;
    summary.is_complete = !is_recursive;

    // Collect explicit preconditions
    summary.preconditions = func.preconditions.clone();

    // Collect explicit postconditions
    summary.postconditions = func.postconditions.clone();

    // F6: derive the f64 result interval for NON-recursive functions (the
    // tracer already assumes the function's own gated preconditions, which is
    // exactly this summary's assume-guarantee premise; a recursive body's
    // return defs feed on themselves — no closed form, fail-closed to None).
    if !is_recursive {
        summary.result_range = crate::generate::derive_float_result_range(func);
    }

    // Walk call sites and collect callee requirements
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, .. } = &block.terminator {
            // Resolve against the complete function universe, not the
            // bottom-up cache. A duplicate short name must remain ambiguous
            // even if only one of its summaries happens to be cached so far.
            let callee_summary = callee_resolver
                .resolve(callee_name)
                .and_then(|def_path| callee_summaries.get(def_path));

            if let Some(cs) = callee_summary {
                // If callee has preconditions, propagate them as requirements
                // the caller must establish before the call
                for pre in &cs.preconditions {
                    // Propagate callee preconditions as caller obligations
                    // (they become part of what the caller needs to verify)
                    if !summary.preconditions.contains(pre) {
                        summary.preconditions.push(pre.clone());
                    }
                }

                // Callee postconditions can strengthen our own analysis
                // but we don't automatically promote them to our postconditions
                // (that would be unsound — we only guarantee what we explicitly ensure)
            } else {
                // Unknown callee: summary is incomplete
                summary.is_complete = false;
            }
        }
    }

    summary
}

/// Substitute a callee summary at a call site in a verification condition.
///
/// Historically this wrapped the VC as
/// `(callee_post_1 AND ... AND callee_post_n) => original_vc`. That is the WRONG
/// POLARITY for Trust's "SAT iff violation" VC convention (`A => V` adds the `¬A`
/// disjunct, so the VC is SAT — a false-FAIL — whenever the assumption is false),
/// and it ignored return-value binding and dominance.
///
/// Sound call-site postcondition assumption is now IMPLEMENTED — but at the layer
/// that has the information this single-VC function lacks: the establish-point
/// versioning lane in `generate::build_semantic_guard_map_with_summaries`, reached
/// via [`crate::modular::modular_vcgen`] /
/// `generate::generate_vcs_with_discharge_and_summaries`. There a proved callee's
/// postcondition is rebound to the call site (formals→args, result→dest),
/// version-pinned to the dest's post-call token `s{b}_t`, scoped to the dominated
/// successors, and CONJOINED (never implied) into the body VCs. See
/// `designs/2026-06-25-trust-ir-composition-design.md` §4.
///
/// This entry point operates on a single, opaque [`VerificationCondition`] with no
/// call site, parameter names, dominance, or version context, so it CANNOT perform
/// that sound substitution here; it stays a conservative no-op by design (returning
/// the VC unchanged can only weaken a PROVE to a FAIL, never the reverse) and
/// delegates the real work to the establish-point lane above.
#[must_use]
pub fn substitute_callee_summary(
    vc: VerificationCondition,
    _callee_summary: &FunctionSummary,
) -> VerificationCondition {
    vc
}

#[cfg(test)]
mod tests {
    use trust_types::call_graph::{CallGraph, CallGraphNode};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Helper: build a function with optional calls and contracts.
    fn make_func_with_spec(
        name: &str,
        def_path: &str,
        calls: &[&str],
        pre: Vec<Formula>,
        post: Vec<Formula>,
    ) -> VerifiableFunction {
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
            },
            contracts: vec![],
            preconditions: pre,
            postconditions: post,
            spec: Default::default(),
        }
    }

    fn graph_with_nodes(nodes: &[(&str, &str)]) -> CallGraph {
        CallGraph {
            nodes: nodes
                .iter()
                .map(|(def_path, name)| CallGraphNode {
                    def_path: (*def_path).to_string(),
                    name: (*name).to_string(),
                    is_public: false,
                    is_entry_point: false,
                    span: span(),
                })
                .collect(),
            edges: vec![],
        }
    }

    #[test]
    fn test_summary_store_basic_operations() {
        let mut store = SummaryStore::new();
        assert!(store.is_empty());

        let summary = FunctionSummary::new("add", "crate::add");
        store.insert(summary);

        assert_eq!(store.len(), 1);
        assert!(store.get("crate::add").is_some());
        assert!(store.get_by_name("add").is_some());
        assert!(store.get("nonexistent").is_none());
    }

    #[test]
    fn test_summary_store_ambiguous_name_fails_closed() {
        let mut store = SummaryStore::new();
        store.insert(FunctionSummary::new("helper", "crate::left::helper"));
        store.insert(FunctionSummary::new("helper", "crate::right::helper"));

        assert!(store.get_by_name("helper").is_none());
        assert!(store.get_by_name("crate::left::helper").is_some());
    }

    #[test]
    fn test_compute_summary_leaf_function() {
        let post = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let func = make_func_with_spec("leaf", "crate::leaf", &[], vec![], vec![post.clone()]);

        let store = SummaryStore::new();
        let graph = graph_with_nodes(&[("crate::leaf", "leaf")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), false);

        assert_eq!(summary.name, "leaf");
        assert!(summary.is_complete);
        assert!(!summary.is_recursive);
        assert_eq!(summary.postconditions, vec![post]);
    }

    #[test]
    fn test_compute_summary_with_callee() {
        // Callee has precondition x >= 0
        let callee_pre =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let callee_post = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );

        let mut store = SummaryStore::new();
        let mut callee_summary = FunctionSummary::new("helper", "crate::helper");
        callee_summary.preconditions.push(callee_pre.clone());
        callee_summary.postconditions.push(callee_post);
        store.insert(callee_summary);

        let func =
            make_func_with_spec("caller", "crate::caller", &["crate::helper"], vec![], vec![]);

        let graph = graph_with_nodes(&[("crate::caller", "caller"), ("crate::helper", "helper")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), false);

        // Callee's precondition should propagate to caller
        assert!(summary.preconditions.contains(&callee_pre));
        assert!(summary.is_complete);
    }

    #[test]
    fn test_compute_summary_unknown_callee() {
        let func =
            make_func_with_spec("caller", "crate::caller", &["external::unknown"], vec![], vec![]);

        let store = SummaryStore::new();
        let graph = graph_with_nodes(&[("crate::caller", "caller")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), false);

        // Unknown callee makes summary incomplete
        assert!(!summary.is_complete);
    }

    #[test]
    fn test_compute_summary_recursive() {
        let func = make_func_with_spec(
            "factorial",
            "crate::factorial",
            &["crate::factorial"],
            vec![],
            vec![],
        );

        let store = SummaryStore::new();
        let graph = graph_with_nodes(&[("crate::factorial", "factorial")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), true);

        assert!(summary.is_recursive);
        assert!(!summary.is_complete);
    }

    #[test]
    fn test_compute_summary_does_not_borrow_ambiguous_callee_precondition() {
        let left_pre = Formula::Eq(
            Box::new(Formula::Var("left".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        let right_pre = Formula::Eq(
            Box::new(Formula::Var("right".into(), Sort::Int)),
            Box::new(Formula::Int(2)),
        );

        let mut store = SummaryStore::new();
        let mut left = FunctionSummary::new("helper", "crate::left::helper");
        left.preconditions.push(left_pre.clone());
        store.insert(left);
        let mut right = FunctionSummary::new("helper", "crate::right::helper");
        right.preconditions.push(right_pre.clone());
        store.insert(right);

        let caller = make_func_with_spec("caller", "crate::caller", &["helper"], vec![], vec![]);
        let graph = graph_with_nodes(&[
            ("crate::caller", "caller"),
            ("crate::left::helper", "helper"),
            ("crate::right::helper", "helper"),
        ]);

        let summary = compute_summary(&caller, &store, &graph.callee_resolver(), false);

        assert!(!summary.is_complete);
        assert!(!summary.preconditions.contains(&left_pre));
        assert!(!summary.preconditions.contains(&right_pre));
    }

    #[test]
    fn test_unknown_summary() {
        let summary = FunctionSummary::unknown("rec", "crate::rec");

        assert!(summary.is_recursive);
        assert!(!summary.is_complete);
        assert!(!summary.has_postconditions());
        assert_eq!(summary.result_range, None);
    }

    /// F6: an f64-returning constant leaf. `_0 = 1.5`.
    fn f64_leaf(name: &str, def_path: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::f64_ty(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(1.5))),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::f64_ty(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_compute_summary_derives_f64_result_range() {
        let func = f64_leaf("leaf", "crate::leaf");
        let store = SummaryStore::new();
        let graph = graph_with_nodes(&[("crate::leaf", "leaf")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), false);
        assert_eq!(summary.result_range, Some((1.5, 1.5)));
    }

    #[test]
    fn test_compute_summary_recursive_has_no_result_range() {
        // SOUNDNESS twin: a recursive body's return defs feed on themselves —
        // no closed-form interval may be claimed, even for this const-only
        // body (the flag, not the trace, is the gate).
        let func = f64_leaf("rec", "crate::rec");
        let store = SummaryStore::new();
        let graph = graph_with_nodes(&[("crate::rec", "rec")]);
        let summary = compute_summary(&func, &store, &graph.callee_resolver(), true);
        assert_eq!(summary.result_range, None);
    }

    #[test]
    fn test_substitute_callee_summary_with_postconditions_is_conservative_noop() {
        let original =
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: original.clone(),
            contract_metadata: None,
        };

        let post =
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)));

        let mut summary = FunctionSummary::new("callee", "crate::callee");
        summary.postconditions.push(post.clone());

        let result = substitute_callee_summary(vc, &summary);

        assert_eq!(result.formula, original);
        assert!(!matches!(result.formula, Formula::Implies(..)));
    }

    #[test]
    fn test_substitute_callee_summary_no_postconditions() {
        let original = Formula::Bool(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: original.clone(),
            contract_metadata: None,
        };

        let summary = FunctionSummary::new("callee", "crate::callee");
        let result = substitute_callee_summary(vc, &summary);

        assert_eq!(result.formula, original, "no postconditions -> unchanged");
    }

    #[test]
    fn test_substitute_callee_summary_multiple_postconditions_is_conservative_noop() {
        let original = Formula::Bool(true);
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "caller".into(),
            location: span(),
            formula: original.clone(),
            contract_metadata: None,
        };

        let post1 =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let post2 =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        let mut summary = FunctionSummary::new("callee", "crate::callee");
        summary.postconditions.push(post1.clone());
        summary.postconditions.push(post2.clone());

        let result = substitute_callee_summary(vc, &summary);

        assert_eq!(result.formula, original);
        assert!(!matches!(result.formula, Formula::Implies(..)));
    }

    #[test]
    fn test_summary_store_iteration() {
        let mut store = SummaryStore::new();
        store.insert(FunctionSummary::new("a", "crate::a"));
        store.insert(FunctionSummary::new("b", "crate::b"));

        let names: Vec<&str> = store.iter().map(|(_, s)| s.name.as_str()).collect();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"a"));
        assert!(names.contains(&"b"));
    }
}
