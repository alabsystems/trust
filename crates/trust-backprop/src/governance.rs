//! Governance rules for source rewriting.
//!
//! Controls what rewrites are allowed. Key invariants:
//! - Public function signatures are immutable (changing them breaks callers)
//! - Test functions are immutable (rewrites must not modify test code)
//! - Protected functions can be explicitly listed
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};
use trust_strengthen::{Proposal, ProposalKind};

use crate::dependency::CallGraph;

/// Policy governing which rewrites are allowed.
///
/// This policy decides *what may be proposed against a function*. It
/// deliberately carries no switch for the compile and re-verification gates
/// that judge a rewrite after it reaches disk: those run unconditionally in the
/// rewrite loop. A deserializable off switch for the only safety gate on a tool
/// that edits the user's source is a footgun that reads like a guarantee, and
/// the toolchain — not a config file — decides whether an unjudged edit may
/// survive.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GovernancePolicy {
    /// If true, public function signatures cannot be modified.
    /// Native contract clauses are additive and allowed; executable signature changes are not.
    pub immutable_pub_signatures: bool,
    /// If true, test functions (`#[test]`, `#[cfg(test)]`) are immutable.
    pub immutable_tests: bool,
    /// If true, governance violations cause hard errors instead of skips.
    pub strict: bool,
    /// Explicitly protected function names that cannot be rewritten.
    pub protected_functions: Vec<String>,

    // --- Safety invariant fields (Part of #459) ---
    /// Allow adding native `requires`/`ensures`/`invariant` clauses
    /// to protected functions. Specs do not change runtime behavior.
    /// Default: `true`.
    #[serde(default = "default_true")]
    pub allow_spec_only_on_protected: bool,

    /// Maximum cumulative rewrites per function across all iterations.
    /// Once reached, further rewrites to this function are blocked.
    /// Default: 5.
    #[serde(default = "default_max_rewrites")]
    pub max_rewrites_per_function: usize,
}

fn default_true() -> bool {
    true
}

fn default_max_rewrites() -> usize {
    5
}

impl Default for GovernancePolicy {
    fn default() -> Self {
        Self {
            immutable_pub_signatures: true,
            immutable_tests: true,
            strict: false,
            protected_functions: Vec::new(),
            allow_spec_only_on_protected: true,
            max_rewrites_per_function: 5,
        }
    }
}

/// A governance violation describing why a rewrite was rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GovernanceViolation {
    /// The function is in the protected list.
    ProtectedFunction { function: String },
    /// The function appears to be a test function.
    TestFunction { function: String },
    /// A pub function's spec changed but not all callers were updated.
    PubApiChangedWithoutCallerUpdate { function: String, missing_callers: Vec<String> },
    /// The function has been rewritten too many times (Part of #459).
    RewriteLimitExceeded { function: String, count: usize, limit: usize },
}

impl GovernancePolicy {
    /// Check a proposal against governance rules.
    ///
    /// Returns an empty vec if the proposal is allowed, or a list of violations.
    #[must_use]
    pub fn check(&self, proposal: &Proposal) -> Vec<GovernanceViolation> {
        let mut violations = Vec::new();

        // Check protected functions list using path-aware matching.
        // A protected entry like "json::parse" matches against function_path,
        // while a simple name like "parse" matches against function_name.
        // Qualified entries (containing "::") match as a suffix of function_path.
        if self.protected_functions.iter().any(|f| {
            if f.contains("::") {
                // Qualified path: match as suffix of function_path
                proposal.function_path == *f || proposal.function_path.ends_with(&format!("::{f}"))
            } else {
                // Simple name: match against function_name (backwards compatible)
                f == &proposal.function_name
            }
        }) {
            // Part of #459: Skip protection if this is a spec-only change
            // and the exemption is enabled. Spec attributes do not change
            // runtime behavior.
            let is_spec_only = matches!(
                &proposal.kind,
                ProposalKind::AddPrecondition { .. }
                    | ProposalKind::AddPostcondition { .. }
                    | ProposalKind::AddInvariant { .. }
            );

            if !(self.allow_spec_only_on_protected && is_spec_only) {
                violations.push(GovernanceViolation::ProtectedFunction {
                    function: proposal.function_name.clone(),
                });
            }
        }

        // Check test function names
        if self.immutable_tests && is_test_function(&proposal.function_name) {
            violations.push(GovernanceViolation::TestFunction {
                function: proposal.function_name.clone(),
            });
        }

        violations
    }
}

/// Heuristic: detect if a function name looks like a test.
fn is_test_function(name: &str) -> bool {
    name.starts_with("test_") || name.contains("::test_") || name.contains("::tests::")
}

/// Tracks cumulative rewrites per function across loop iterations (Part of #459).
///
/// Used to enforce `GovernancePolicy::max_rewrites_per_function`. Once a function
/// has been rewritten `max_rewrites_per_function` times, further rewrites are
/// blocked with `GovernanceViolation::RewriteLimitExceeded`.
#[derive(Debug, Clone, Default)]
pub struct RewriteTracker {
    /// Map from function name to cumulative rewrite count.
    counts: FxHashMap<String, usize>,
}

impl RewriteTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that a rewrite was applied to a function.
    pub fn record(&mut self, function_name: &str) {
        *self.counts.entry(function_name.to_string()).or_insert(0) += 1;
    }

    /// Check whether a function has exceeded the rewrite limit.
    #[must_use]
    pub fn exceeds_limit(&self, function_name: &str, limit: usize) -> bool {
        self.counts.get(function_name).copied().unwrap_or(0) >= limit
    }

    /// Get the current count for a function.
    #[must_use]
    pub fn count(&self, function_name: &str) -> usize {
        self.counts.get(function_name).copied().unwrap_or(0)
    }

    /// Reset all counts.
    pub fn reset(&mut self) {
        self.counts.clear();
    }

    /// Number of functions tracked.
    #[must_use]
    pub fn tracked_count(&self) -> usize {
        self.counts.len()
    }
}

/// Check cross-module invariants: if a pub function gets a new precondition,
/// all its callers must have corresponding checks in the rewrite plan.
///
/// Returns violations for any pub function whose spec changed but whose callers
/// are not all present in the rewrite targets.
///
/// # Arguments
///
/// * `proposals` - The proposals being applied.
/// * `call_graph` - The call graph for the functions under verification.
/// * `rewrite_targets` - Set of function def-paths (or unambiguous legacy short
///   names) that have rewrites in the plan.
/// * `pub_functions` - Set of function names known to be `pub`.
#[must_use]
pub fn check_cross_module_invariants(
    proposals: &[Proposal],
    call_graph: &CallGraph,
    rewrite_targets: &FxHashSet<String>,
    pub_functions: &FxHashSet<String>,
) -> Vec<GovernanceViolation> {
    let mut violations = Vec::new();

    for proposal in proposals {
        // Only precondition changes on pub functions require caller updates.
        let is_precondition = matches!(&proposal.kind, ProposalKind::AddPrecondition { .. });
        if !is_precondition {
            continue;
        }
        let Some(function_path) = call_graph
            .resolve_function(&proposal.function_path)
            .or_else(|| call_graph.resolve_function(&proposal.function_name))
        else {
            continue;
        };
        let short_name_identifies_target =
            call_graph.resolve_function(&proposal.function_name) == Some(function_path);
        if !pub_functions.contains(function_path)
            && !(short_name_identifies_target && pub_functions.contains(&proposal.function_name))
        {
            continue;
        }

        // Find callers that are NOT in the rewrite targets.
        let callers = call_graph.callers(function_path);
        let missing: Vec<String> = callers
            .into_iter()
            .filter(|caller| {
                !rewrite_targets.contains(caller)
                    && !call_graph.function_name(caller).is_some_and(|name| {
                        call_graph.resolve_function(name) == Some(caller.as_str())
                            && rewrite_targets.contains(name)
                    })
            })
            .map(|caller| match call_graph.function_name(&caller) {
                Some(name) if call_graph.resolve_function(name) == Some(caller.as_str()) => {
                    name.to_string()
                }
                _ => caller,
            })
            .collect();

        if !missing.is_empty() {
            let mut sorted_missing = missing;
            sorted_missing.sort();
            violations.push(GovernanceViolation::PubApiChangedWithoutCallerUpdate {
                function: proposal.function_name.clone(),
                missing_callers: sorted_missing,
            });
        }
    }

    violations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dependency::build_call_graph;
    use trust_strengthen::{Proposal, ProposalKind};
    use trust_types::*;

    fn make_proposal(func_name: &str) -> Proposal {
        Proposal {
            function_path: format!("crate::{func_name}"),
            function_name: func_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "test".into(),
        }
    }

    #[test]
    fn test_default_policy_allows_normal_functions() {
        let policy = GovernancePolicy::default();
        let proposal = make_proposal("get_midpoint");
        let violations = policy.check(&proposal);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_protected_function_spec_only_allowed_by_default() {
        // Part of #459: spec-only proposals are allowed on protected functions
        // when allow_spec_only_on_protected is true (the default).
        let policy = GovernancePolicy {
            protected_functions: vec!["critical_fn".into()],
            ..Default::default()
        };
        let proposal = make_proposal("critical_fn"); // AddPrecondition = spec-only
        let violations = policy.check(&proposal);
        assert!(
            violations.is_empty(),
            "spec-only proposals should be allowed on protected functions by default"
        );
    }

    #[test]
    fn test_protected_function_blocked_when_spec_exemption_disabled() {
        let policy = GovernancePolicy {
            protected_functions: vec!["critical_fn".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposal = make_proposal("critical_fn");
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            GovernanceViolation::ProtectedFunction { function } if function == "critical_fn"
        ));
    }

    #[test]
    fn test_protected_function_code_transform_always_blocked() {
        // Even with spec exemption on, code transforms on protected functions are blocked.
        let policy = GovernancePolicy {
            protected_functions: vec!["critical_fn".into()],
            allow_spec_only_on_protected: true,
            ..Default::default()
        };
        let proposal = Proposal {
            function_path: "crate::critical_fn".into(),
            function_name: "critical_fn".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1);
        assert!(matches!(&violations[0], GovernanceViolation::ProtectedFunction { .. }));
    }

    #[test]
    fn test_test_function_blocked() {
        let policy = GovernancePolicy { immutable_tests: true, ..Default::default() };
        let proposal = make_proposal("test_overflow_detection");
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1);
        assert!(matches!(&violations[0], GovernanceViolation::TestFunction { .. }));
    }

    #[test]
    fn test_test_function_allowed_when_disabled() {
        let policy = GovernancePolicy { immutable_tests: false, ..Default::default() };
        let proposal = make_proposal("test_overflow_detection");
        let violations = policy.check(&proposal);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_nested_test_function_blocked() {
        let policy = GovernancePolicy::default();
        let proposal = make_proposal("module::tests::helper");
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1);
        assert!(matches!(&violations[0], GovernanceViolation::TestFunction { .. }));
    }

    #[test]
    fn test_multiple_violations_with_spec_exemption_disabled() {
        let policy = GovernancePolicy {
            immutable_tests: true,
            protected_functions: vec!["test_critical".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposal = make_proposal("test_critical");
        let violations = policy.check(&proposal);
        // Both protected AND test name match when spec exemption is off
        assert_eq!(violations.len(), 2);
    }

    #[test]
    fn test_multiple_violations_spec_exemption_on() {
        // With spec exemption (default), protected check is skipped for spec-only,
        // but test function check still fires.
        let policy = GovernancePolicy {
            immutable_tests: true,
            protected_functions: vec!["test_critical".into()],
            ..Default::default()
        };
        let proposal = make_proposal("test_critical");
        let violations = policy.check(&proposal);
        // Only TestFunction violation since spec-only exempts from ProtectedFunction
        assert_eq!(violations.len(), 1);
        assert!(matches!(&violations[0], GovernanceViolation::TestFunction { .. }));
    }

    #[test]
    fn test_non_test_prefix_allowed() {
        let policy = GovernancePolicy::default();
        let proposal = make_proposal("testing_helper");
        // "testing_helper" does not start with "test_"
        let violations = policy.check(&proposal);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_is_test_function_heuristic() {
        assert!(is_test_function("test_overflow"));
        assert!(is_test_function("module::test_something"));
        assert!(is_test_function("crate::tests::helper"));
        assert!(!is_test_function("get_midpoint"));
        assert!(!is_test_function("testing_util"));
        assert!(!is_test_function("contest_winner"));
    }

    #[test]
    fn test_empty_protected_list() {
        let policy = GovernancePolicy {
            protected_functions: vec![],
            immutable_tests: false,
            ..Default::default()
        };
        let proposal = make_proposal("any_function");
        let violations = policy.check(&proposal);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_governance_serialization_roundtrip() {
        let policy = GovernancePolicy {
            immutable_pub_signatures: true,
            immutable_tests: false,
            strict: true,
            protected_functions: vec!["main".into(), "init".into()],
            ..Default::default()
        };
        let json = serde_json::to_string(&policy).unwrap();
        let deserialized: GovernancePolicy = serde_json::from_str(&json).unwrap();
        assert!(deserialized.strict);
        assert_eq!(deserialized.protected_functions.len(), 2);
    }

    #[test]
    fn test_violation_serialization_roundtrip() {
        let violation = GovernanceViolation::ProtectedFunction { function: "foo".into() };
        let json = serde_json::to_string(&violation).unwrap();
        let deserialized: GovernanceViolation = serde_json::from_str(&json).unwrap();
        assert_eq!(violation, deserialized);
    }

    // --- Cross-module invariant tests ---

    /// Helper: make a VerifiableFunction with specified callees.
    fn make_vfunc(name: &str, callees: &[&str]) -> VerifiableFunction {
        make_vfunc_at(name, &format!("crate::{name}"), callees)
    }

    fn make_vfunc_at(name: &str, def_path: &str, callees: &[&str]) -> VerifiableFunction {
        let mut blocks = Vec::new();
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
    fn test_cross_module_no_violations_when_all_callers_updated() {
        let funcs = vec![make_vfunc("caller", &["callee"]), make_vfunc("callee", &[])];
        let graph = build_call_graph(&funcs);

        let proposals = vec![make_proposal("callee")];
        let rewrite_targets: FxHashSet<String> =
            ["callee", "caller"].iter().map(|s| s.to_string()).collect();
        let pub_fns: FxHashSet<String> = ["callee"].iter().map(|s| s.to_string()).collect();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_cross_module_violation_when_caller_missing() {
        let funcs = vec![make_vfunc("caller", &["callee"]), make_vfunc("callee", &[])];
        let graph = build_call_graph(&funcs);

        let proposals = vec![make_proposal("callee")];
        // Only callee is in rewrite targets, not caller.
        let rewrite_targets: FxHashSet<String> = ["callee"].iter().map(|s| s.to_string()).collect();
        let pub_fns: FxHashSet<String> = ["callee"].iter().map(|s| s.to_string()).collect();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            GovernanceViolation::PubApiChangedWithoutCallerUpdate {
                function,
                missing_callers,
            } if function == "callee" && missing_callers == &["caller".to_string()]
        ));
    }

    #[test]
    fn test_cross_module_no_violation_for_private_function() {
        let funcs =
            vec![make_vfunc("caller", &["private_helper"]), make_vfunc("private_helper", &[])];
        let graph = build_call_graph(&funcs);

        let proposals = vec![make_proposal("private_helper")];
        let rewrite_targets: FxHashSet<String> =
            ["private_helper"].iter().map(|s| s.to_string()).collect();
        // private_helper is NOT in pub_functions.
        let pub_fns: FxHashSet<String> = FxHashSet::default();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_cross_module_no_violation_for_non_precondition() {
        let funcs = vec![make_vfunc("caller", &["callee"]), make_vfunc("callee", &[])];
        let graph = build_call_graph(&funcs);

        // SafeArithmetic proposal, not AddPrecondition.
        let proposals = vec![Proposal {
            function_path: "crate::callee".into(),
            function_name: "callee".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "safe".into(),
        }];
        let rewrite_targets: FxHashSet<String> = ["callee"].iter().map(|s| s.to_string()).collect();
        let pub_fns: FxHashSet<String> = ["callee"].iter().map(|s| s.to_string()).collect();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_cross_module_exact_path_checks_only_matching_duplicate_name_callers() {
        let funcs = vec![
            make_vfunc_at("caller", "crate::left::caller", &["crate::left::helper"]),
            make_vfunc_at("caller", "crate::right::caller", &["crate::right::helper"]),
            make_vfunc_at("helper", "crate::left::helper", &[]),
            make_vfunc_at("helper", "crate::right::helper", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let proposals = vec![Proposal {
            function_path: "crate::left::helper".into(),
            function_name: "helper".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "test".into(),
        }];
        let rewrite_targets: FxHashSet<String> =
            ["crate::left::helper", "caller"].into_iter().map(str::to_string).collect();
        let pub_fns: FxHashSet<String> =
            ["crate::left::helper"].into_iter().map(str::to_string).collect();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);

        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            GovernanceViolation::PubApiChangedWithoutCallerUpdate { missing_callers, .. }
                if missing_callers == &["crate::left::caller".to_string()]
        ));
    }

    // --- Path-aware protected function matching tests (Part of #419) ---

    #[test]
    fn test_qualified_protected_blocks_matching_path() {
        // Disable spec exemption so protected function check fires for preconditions.
        let policy = GovernancePolicy {
            protected_functions: vec!["json::parse".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        // Proposal with function_path "crate::json::parse" should be blocked
        let proposal = Proposal {
            function_path: "crate::json::parse".into(),
            function_name: "parse".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "test".into(),
        };
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1, "qualified path should match as suffix");
    }

    #[test]
    fn test_qualified_protected_does_not_block_different_module() {
        let policy = GovernancePolicy {
            protected_functions: vec!["json::parse".into()],
            ..Default::default()
        };
        // Proposal for csv::parse should NOT be blocked by "json::parse"
        let proposal = Proposal {
            function_path: "crate::csv::parse".into(),
            function_name: "parse".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "test".into(),
        };
        let violations = policy.check(&proposal);
        assert!(
            violations.is_empty(),
            "csv::parse should not be blocked by json::parse protection"
        );
    }

    #[test]
    fn test_simple_name_protected_still_works() {
        // Backwards compatibility: simple names match against function_name
        let policy = GovernancePolicy {
            protected_functions: vec!["parse".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposal = make_proposal("parse");
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1, "simple name match should still work");
    }

    #[test]
    fn test_exact_path_match() {
        let policy = GovernancePolicy {
            protected_functions: vec!["crate::json::parse".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposal = Proposal {
            function_path: "crate::json::parse".into(),
            function_name: "parse".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "test".into(),
        };
        let violations = policy.check(&proposal);
        assert_eq!(violations.len(), 1, "exact path match should work");
    }

    #[test]
    fn test_cross_module_multiple_missing_callers() {
        let funcs = vec![
            make_vfunc("a", &["target"]),
            make_vfunc("b", &["target"]),
            make_vfunc("c", &["target"]),
            make_vfunc("target", &[]),
        ];
        let graph = build_call_graph(&funcs);

        let proposals = vec![make_proposal("target")];
        // Only "target" and "a" updated; "b" and "c" missing.
        let rewrite_targets: FxHashSet<String> =
            ["target", "a"].iter().map(|s| s.to_string()).collect();
        let pub_fns: FxHashSet<String> = ["target"].iter().map(|s| s.to_string()).collect();

        let violations =
            check_cross_module_invariants(&proposals, &graph, &rewrite_targets, &pub_fns);
        assert_eq!(violations.len(), 1);
        match &violations[0] {
            GovernanceViolation::PubApiChangedWithoutCallerUpdate { missing_callers, .. } => {
                assert_eq!(missing_callers.len(), 2);
                assert!(missing_callers.contains(&"b".to_string()));
                assert!(missing_callers.contains(&"c".to_string()));
            }
            other => panic!("unexpected violation: {other:?}"),
        }
    }
}
