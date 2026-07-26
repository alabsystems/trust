//! Approval workflows for safety-critical source rewrites.
//!
//! Classifies proposed rewrites into policy tiers: Auto (apply immediately),
//! Review (queue for human/AI review), or Block (never auto-apply). Uses
//! pattern-matching rules on function paths and rewrite kinds.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::frontend_firewall::ClaimProvenance;

use crate::{RewriteKind, SourceRewrite};

/// Policy tier for a proposed rewrite.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ApprovalPolicy {
    /// Apply the rewrite immediately without review.
    Auto,
    /// Queue the rewrite for review before applying.
    Review,
    /// Never auto-apply; block outright.
    Block,
}

/// A rule that maps a (function path pattern, rewrite kind) to an approval policy.
///
/// Patterns use simple substring matching on function paths. If `kind_filter` is
/// `None`, the rule matches all rewrite kinds for functions matching the pattern.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyRule {
    /// Substring pattern to match against the function name or file path.
    pub path_pattern: String,
    /// Optional filter on the rewrite kind. `None` matches all kinds.
    pub kind_filter: Option<RewriteKindFilter>,
    /// The policy to apply when this rule matches.
    pub policy: ApprovalPolicy,
}

/// Filter for matching rewrite kinds in policy rules.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RewriteKindFilter {
    /// Match `InsertAttribute` rewrites.
    InsertAttribute,
    /// Match first-class signature-clause insertions.
    InsertContractClause,
    /// Match `ReplaceExpression` rewrites.
    ReplaceExpression,
    /// Match `InsertAssertion` rewrites.
    InsertAssertion,
}

impl RewriteKindFilter {
    /// Check whether a `RewriteKind` matches this filter.
    #[must_use]
    pub fn matches(&self, kind: &RewriteKind) -> bool {
        matches!(
            (self, kind),
            (Self::InsertAttribute, RewriteKind::InsertAttribute { .. })
                | (Self::InsertContractClause, RewriteKind::InsertContractClause { .. })
                | (Self::ReplaceExpression, RewriteKind::ReplaceExpression { .. })
                | (Self::InsertAssertion, RewriteKind::InsertAssertion { .. })
        )
    }
}

/// A rewrite pending review in the approval queue.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PendingRewrite {
    /// The rewrite awaiting approval.
    pub rewrite: SourceRewrite,
    /// The policy that caused it to be queued.
    pub policy: ApprovalPolicy,
    /// Optional reviewer notes (set during review).
    pub reviewer_notes: Option<String>,
}

/// Queue of rewrites awaiting review before application.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ApprovalQueue {
    /// Pending rewrites awaiting review.
    pub pending: Vec<PendingRewrite>,
}

impl ApprovalQueue {
    /// Create a new empty approval queue.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a rewrite to the pending queue.
    pub fn enqueue(&mut self, rewrite: SourceRewrite, policy: ApprovalPolicy) {
        self.pending.push(PendingRewrite { rewrite, policy, reviewer_notes: None });
    }

    /// Number of pending rewrites.
    #[must_use]
    pub fn len(&self) -> usize {
        self.pending.len()
    }

    /// Whether the queue is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// Approve a pending rewrite by index, returning it for application.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn approve(&mut self, index: usize) -> Option<SourceRewrite> {
        if index < self.pending.len() { Some(self.pending.remove(index).rewrite) } else { None }
    }

    /// Reject a pending rewrite by index, removing it from the queue.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn reject(&mut self, index: usize) -> Option<PendingRewrite> {
        if index < self.pending.len() { Some(self.pending.remove(index)) } else { None }
    }

    /// Approve all pending rewrites, draining the queue.
    pub fn approve_all(&mut self) -> Vec<SourceRewrite> {
        self.pending.drain(..).map(|pr| pr.rewrite).collect()
    }

    /// Drain all pending rewrites, returning them for external processing.
    pub fn drain_all(&mut self) -> Vec<PendingRewrite> {
        self.pending.drain(..).collect()
    }
}

/// Classify a rewrite according to the given policy rules.
///
/// Rules are evaluated in order; the first matching rule wins. If no rule
/// matches, the default policy is `Auto` for internal functions and `Review`
/// for pub API / unsafe functions (see `default_rules()`).
///
/// One classification is decided before the rules are consulted at all: a
/// rewrite proposed by an untrusted frontend is never `Auto`. See
/// [`frontend_ceiling`] for why that is not something a rule may override.
#[must_use]
pub fn classify_rewrite(rewrite: &SourceRewrite, rules: &[PolicyRule]) -> ApprovalPolicy {
    let classified = classify_by_rules(rewrite, rules);
    frontend_ceiling(rewrite.provenance, classified)
}

/// Cap a classification by the proposer's authority.
///
/// A contract clause is not an edit, it is a claim: once `requires P` is in the
/// source, every later proof of that function gets to ASSUME `P`. An untrusted
/// frontend that could write one would have introduced exactly the unchecked
/// assumption the firewall exists to prevent — by a slower route, but the same
/// route. So provenance is a ceiling applied after the rules, not another rule:
/// a `PolicyRule` may make a frontend proposal stricter (`Block`), never
/// laxer, which is what stops a frontend from shipping a policy file that
/// promotes its own proposals.
#[must_use]
pub fn frontend_ceiling(
    provenance: ClaimProvenance,
    classified: ApprovalPolicy,
) -> ApprovalPolicy {
    if provenance.requires_review() && matches!(classified, ApprovalPolicy::Auto) {
        ApprovalPolicy::Review
    } else {
        classified
    }
}

fn classify_by_rules(rewrite: &SourceRewrite, rules: &[PolicyRule]) -> ApprovalPolicy {
    for rule in rules {
        let path_matches = if rule.path_pattern.is_empty() {
            true
        } else if rule.path_pattern.contains('/')
            || rule.path_pattern.contains('\\')
            || rule.path_pattern.ends_with(".rs")
        {
            rewrite.file_path.contains(&rule.path_pattern)
        } else {
            rewrite.function_name.contains(&rule.path_pattern)
                || rewrite.file_path.split(['/', '\\']).any(|segment| {
                    let stem = segment.strip_suffix(".rs").unwrap_or(segment);
                    stem == rule.path_pattern
                })
        };

        if !path_matches {
            continue;
        }

        let kind_matches = rule.kind_filter.as_ref().is_none_or(|f| f.matches(&rewrite.kind));

        if kind_matches {
            return rule.policy;
        }
    }

    // Default: safety-critical heuristics
    default_classify(rewrite)
}

/// Default classification when no explicit rule matches.
///
/// - Functions containing "unsafe" in the path -> Review
/// - Functions containing "pub" in the file path or with public-looking names -> Review
/// - ReplaceExpression rewrites -> Review (they change behavior)
/// - Everything else -> Auto
fn default_classify(rewrite: &SourceRewrite) -> ApprovalPolicy {
    // Unsafe functions always need review
    if rewrite.function_name.contains("unsafe") || rewrite.file_path.contains("unsafe") {
        return ApprovalPolicy::Review;
    }

    // Expression replacements change behavior and need review. Swapping `a + b`
    // for `a.checked_add(b).unwrap()` does not discharge the overflow
    // obligation — it moves the failure from a trapping add to a trapping
    // unwrap, which is a different program, chosen by a heuristic, with no
    // proof that the new behavior is the one the author wanted. The proposal is
    // worth making; making it silently is not.
    if matches!(rewrite.kind, RewriteKind::ReplaceExpression { .. }) {
        return ApprovalPolicy::Review;
    }

    // Trust (Pillar 2 — the compiler SUGGESTS specs to the author): an inserted
    // native `requires`/`ensures` clause is an UNVERIFIED semantic claim
    // about the function's contract. The strengthen layer proposes these from
    // heuristics (and, for low-confidence cases, boilerplate like `result >= 0`),
    // so silently auto-writing them into source risks landing a wrong or
    // non-compiling spec. Surfacing them for review — which is exactly the
    // "compiler talks back to the AI" loop the vision describes — is the sound
    // default. Only an explicitly verified-sufficient rewrite (governance rule /
    // R1-discharged) may promote back to Auto via a matching PolicyRule.
    if is_spec_clause_insertion(&rewrite.kind) {
        return ApprovalPolicy::Review;
    }

    ApprovalPolicy::Auto
}

/// A native signature-clause insertion is an unverified semantic contract
/// claim. Compatibility attributes remain ordinary input and are never
/// generated here.
fn is_spec_clause_insertion(kind: &RewriteKind) -> bool {
    matches!(kind, RewriteKind::InsertContractClause { .. })
}

/// Return the default policy rules for a typical Rust project.
///
/// Default rules:
/// 1. `test_` prefix functions -> Block (tests are immutable)
/// 2. `unsafe` in path -> Review
/// 3. `pub` in file path -> Review for expression replacements
/// 4. Everything else -> Auto
#[must_use]
pub fn default_rules() -> Vec<PolicyRule> {
    vec![
        // Test functions are never auto-rewritten
        PolicyRule {
            path_pattern: "test_".into(),
            kind_filter: None,
            policy: ApprovalPolicy::Block,
        },
        // Unsafe functions always need review
        PolicyRule {
            path_pattern: "unsafe".into(),
            kind_filter: None,
            policy: ApprovalPolicy::Review,
        },
        // Expression replacements in any file need review
        PolicyRule {
            path_pattern: String::new(), // matches everything
            kind_filter: Some(RewriteKindFilter::ReplaceExpression),
            policy: ApprovalPolicy::Review,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ContractClauseKind, RewriteKind, SourceRewrite};
    use trust_types::frontend_firewall::FrontendLanguage;

    fn make_rewrite(func_name: &str, file_path: &str, kind: RewriteKind) -> SourceRewrite {
        SourceRewrite {
            file_path: file_path.into(),
            offset: 0,
            kind,
            function_name: func_name.into(),
            rationale: "test".into(),
            expected_source_hash: None,
            provenance: ClaimProvenance::Authoritative,
        }
    }

    fn attr_kind() -> RewriteKind {
        RewriteKind::InsertContractClause {
            clause: ContractClauseKind::Requires,
            expression: "x > 0".into(),
        }
    }

    fn replace_kind() -> RewriteKind {
        RewriteKind::ReplaceExpression {
            old_text: "a + b".into(),
            new_text: "a.checked_add(b).unwrap()".into(),
        }
    }

    fn assert_kind() -> RewriteKind {
        RewriteKind::InsertAssertion { assertion: "assert!(i < v.len());".into() }
    }

    // --- ApprovalPolicy tests ---

    #[test]
    fn test_approval_policy_serialization_roundtrip() {
        let policies = [ApprovalPolicy::Auto, ApprovalPolicy::Review, ApprovalPolicy::Block];
        for policy in &policies {
            let json = serde_json::to_string(policy).unwrap();
            let deserialized: ApprovalPolicy = serde_json::from_str(&json).unwrap();
            assert_eq!(*policy, deserialized);
        }
    }

    // --- classify_rewrite tests ---

    #[test]
    fn test_classify_spec_clause_is_review() {
        // A native signature clause is
        // an unverified semantic claim — surfaced for review, never auto-written.
        let rewrite = make_rewrite("helper", "src/internal.rs", attr_kind());
        let policy = classify_rewrite(&rewrite, &[]);
        assert_eq!(policy, ApprovalPolicy::Review);
    }

    #[test]
    fn test_classify_nonspec_attr_is_auto() {
        // A mechanical, non-spec attribute carries no contract claim and stays Auto.
        let rewrite = make_rewrite(
            "helper",
            "src/internal.rs",
            RewriteKind::InsertAttribute { attribute: "#[inline]".into() },
        );
        assert_eq!(classify_rewrite(&rewrite, &[]), ApprovalPolicy::Auto);
    }

    #[test]
    fn test_classify_replace_expr_is_review() {
        let rewrite = make_rewrite("compute", "src/math.rs", replace_kind());
        let policy = classify_rewrite(&rewrite, &[]);
        assert_eq!(policy, ApprovalPolicy::Review);
    }

    #[test]
    fn test_classify_unsafe_func_is_review() {
        let rewrite = make_rewrite("unsafe_deref", "src/ptr.rs", attr_kind());
        let policy = classify_rewrite(&rewrite, &[]);
        assert_eq!(policy, ApprovalPolicy::Review);
    }

    #[test]
    fn test_classify_with_explicit_rule_overrides_default() {
        let rules = vec![PolicyRule {
            path_pattern: "helper".into(),
            kind_filter: None,
            policy: ApprovalPolicy::Block,
        }];
        let rewrite = make_rewrite("helper", "src/lib.rs", attr_kind());
        let policy = classify_rewrite(&rewrite, &rules);
        assert_eq!(policy, ApprovalPolicy::Block);
    }

    #[test]
    fn test_classify_first_matching_rule_wins() {
        let rules = vec![
            PolicyRule {
                path_pattern: "compute".into(),
                kind_filter: None,
                policy: ApprovalPolicy::Auto,
            },
            PolicyRule {
                path_pattern: "compute".into(),
                kind_filter: None,
                policy: ApprovalPolicy::Block,
            },
        ];
        let rewrite = make_rewrite("compute", "src/lib.rs", attr_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Auto);
    }

    #[test]
    fn test_classify_kind_filter_matches() {
        let rules = vec![PolicyRule {
            path_pattern: "compute".into(),
            kind_filter: Some(RewriteKindFilter::InsertContractClause),
            policy: ApprovalPolicy::Block,
        }];
        // Native clause rewrite matches the filter
        let attr_rewrite = make_rewrite("compute", "src/lib.rs", attr_kind());
        assert_eq!(classify_rewrite(&attr_rewrite, &rules), ApprovalPolicy::Block);

        // Assertion rewrite does NOT match the kind filter -> falls through to default
        let assert_rewrite = make_rewrite("compute", "src/lib.rs", assert_kind());
        assert_eq!(classify_rewrite(&assert_rewrite, &rules), ApprovalPolicy::Auto);
    }

    #[test]
    fn test_classify_no_rules_internal_assertion_is_auto() {
        let rewrite = make_rewrite("process", "src/internal.rs", assert_kind());
        assert_eq!(classify_rewrite(&rewrite, &[]), ApprovalPolicy::Auto);
    }

    #[test]
    fn test_classify_matches_file_path_pattern() {
        let rules = vec![PolicyRule {
            path_pattern: "critical".into(),
            kind_filter: None,
            policy: ApprovalPolicy::Block,
        }];
        let rewrite = make_rewrite("helper", "src/critical/mod.rs", attr_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Block);
    }

    // --- default_rules tests ---

    #[test]
    fn test_default_rules_block_test_functions() {
        let rules = default_rules();
        let rewrite = make_rewrite("test_overflow", "src/tests.rs", attr_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Block);
    }

    #[test]
    fn test_default_rules_review_unsafe() {
        let rules = default_rules();
        let rewrite = make_rewrite("unsafe_ptr", "src/ffi.rs", attr_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Review);
    }

    #[test]
    fn test_default_rules_review_replace_expr() {
        let rules = default_rules();
        let rewrite = make_rewrite("compute", "src/math.rs", replace_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Review);
    }

    #[test]
    fn test_default_rules_review_for_spec_clause() {
        let rules = default_rules();
        let rewrite = make_rewrite("helper", "src/internal.rs", attr_kind());
        assert_eq!(classify_rewrite(&rewrite, &rules), ApprovalPolicy::Review);
    }

    // --- RewriteKindFilter tests ---

    #[test]
    fn test_kind_filter_matches_correctly() {
        assert!(RewriteKindFilter::InsertContractClause.matches(&attr_kind()));
        assert!(!RewriteKindFilter::InsertContractClause.matches(&replace_kind()));
        assert!(!RewriteKindFilter::InsertContractClause.matches(&assert_kind()));

        assert!(RewriteKindFilter::ReplaceExpression.matches(&replace_kind()));
        assert!(!RewriteKindFilter::ReplaceExpression.matches(&attr_kind()));

        assert!(RewriteKindFilter::InsertAssertion.matches(&assert_kind()));
        assert!(!RewriteKindFilter::InsertAssertion.matches(&attr_kind()));
    }

    // --- ApprovalQueue tests ---

    #[test]
    fn test_queue_new_is_empty() {
        let queue = ApprovalQueue::new();
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_enqueue_and_len() {
        let mut queue = ApprovalQueue::new();
        let rewrite = make_rewrite("f", "a.rs", attr_kind());
        queue.enqueue(rewrite, ApprovalPolicy::Review);
        assert_eq!(queue.len(), 1);
        assert!(!queue.is_empty());
    }

    #[test]
    fn test_queue_approve_returns_rewrite() {
        let mut queue = ApprovalQueue::new();
        let rewrite = make_rewrite("f", "a.rs", attr_kind());
        queue.enqueue(rewrite, ApprovalPolicy::Review);

        let approved = queue.approve(0);
        assert!(approved.is_some());
        assert_eq!(approved.unwrap().function_name, "f");
        assert!(queue.is_empty());
    }

    #[test]
    fn test_queue_approve_out_of_bounds_returns_none() {
        let mut queue = ApprovalQueue::new();
        assert!(queue.approve(0).is_none());
    }

    #[test]
    fn test_queue_reject_removes_item() {
        let mut queue = ApprovalQueue::new();
        queue.enqueue(make_rewrite("f", "a.rs", attr_kind()), ApprovalPolicy::Review);
        let rejected = queue.reject(0);
        assert!(rejected.is_some());
        assert!(queue.is_empty());
    }

    #[test]
    fn test_queue_reject_out_of_bounds_returns_none() {
        let mut queue = ApprovalQueue::new();
        assert!(queue.reject(5).is_none());
    }

    #[test]
    fn test_queue_approve_all() {
        let mut queue = ApprovalQueue::new();
        queue.enqueue(make_rewrite("a", "a.rs", attr_kind()), ApprovalPolicy::Review);
        queue.enqueue(make_rewrite("b", "b.rs", assert_kind()), ApprovalPolicy::Review);

        let approved = queue.approve_all();
        assert_eq!(approved.len(), 2);
        assert!(queue.is_empty());
    }

    #[test]
    fn test_queue_drain_all() {
        let mut queue = ApprovalQueue::new();
        queue.enqueue(make_rewrite("a", "a.rs", attr_kind()), ApprovalPolicy::Review);
        queue.enqueue(make_rewrite("b", "b.rs", assert_kind()), ApprovalPolicy::Block);

        let drained = queue.drain_all();
        assert_eq!(drained.len(), 2);
        assert_eq!(drained[0].policy, ApprovalPolicy::Review);
        assert_eq!(drained[1].policy, ApprovalPolicy::Block);
        assert!(queue.is_empty());
    }

    #[test]
    fn test_queue_multiple_enqueue_preserves_order() {
        let mut queue = ApprovalQueue::new();
        queue.enqueue(make_rewrite("first", "a.rs", attr_kind()), ApprovalPolicy::Auto);
        queue.enqueue(make_rewrite("second", "b.rs", attr_kind()), ApprovalPolicy::Review);
        queue.enqueue(make_rewrite("third", "c.rs", attr_kind()), ApprovalPolicy::Block);

        assert_eq!(queue.pending[0].rewrite.function_name, "first");
        assert_eq!(queue.pending[1].rewrite.function_name, "second");
        assert_eq!(queue.pending[2].rewrite.function_name, "third");
    }

    #[test]
    fn test_queue_serialization_roundtrip() {
        let mut queue = ApprovalQueue::new();
        queue.enqueue(make_rewrite("f", "a.rs", attr_kind()), ApprovalPolicy::Review);

        let json = serde_json::to_string(&queue).unwrap();
        let deserialized: ApprovalQueue = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.len(), 1);
        assert_eq!(deserialized.pending[0].policy, ApprovalPolicy::Review);
    }

    // --- PolicyRule tests ---

    #[test]
    fn test_policy_rule_serialization_roundtrip() {
        let rule = PolicyRule {
            path_pattern: "critical".into(),
            kind_filter: Some(RewriteKindFilter::InsertAttribute),
            policy: ApprovalPolicy::Block,
        };
        let json = serde_json::to_string(&rule).unwrap();
        let deserialized: PolicyRule = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.path_pattern, "critical");
        assert_eq!(deserialized.policy, ApprovalPolicy::Block);
    }

    #[test]
    fn test_policy_rule_no_kind_filter_matches_all() {
        let rule = PolicyRule {
            path_pattern: "f".into(),
            kind_filter: None,
            policy: ApprovalPolicy::Review,
        };
        let rules = vec![rule];
        assert_eq!(
            classify_rewrite(&make_rewrite("f", "a.rs", attr_kind()), &rules),
            ApprovalPolicy::Review,
        );
        assert_eq!(
            classify_rewrite(&make_rewrite("f", "a.rs", replace_kind()), &rules),
            ApprovalPolicy::Review,
        );
        assert_eq!(
            classify_rewrite(&make_rewrite("f", "a.rs", assert_kind()), &rules),
            ApprovalPolicy::Review,
        );
    }

    // --- frontend firewall ---

    fn frontend_rewrite(kind: RewriteKind) -> SourceRewrite {
        let mut rewrite = make_rewrite("f", "a.rs", kind);
        rewrite.provenance = ClaimProvenance::Frontend(FrontendLanguage::JavaScript);
        rewrite
    }

    #[test]
    fn a_frontend_proposed_clause_never_applies_itself() {
        // An `InsertAssertion` from a Rust proposer is the Auto case, which is
        // exactly why it is the right probe: the ONLY difference here is who
        // proposed it.
        let assert_from_rust = make_rewrite("f", "a.rs", assert_kind());
        assert_eq!(classify_rewrite(&assert_from_rust, &[]), ApprovalPolicy::Auto);
        let assert_from_js = frontend_rewrite(assert_kind());
        assert_eq!(classify_rewrite(&assert_from_js, &[]), ApprovalPolicy::Review);
    }

    #[test]
    fn a_policy_rule_cannot_promote_a_frontend_proposal() {
        // The abuse this blocks: a frontend shipping a policy file that
        // whitelists its own proposals back to Auto.
        let permissive = vec![PolicyRule {
            path_pattern: String::new(),
            kind_filter: None,
            policy: ApprovalPolicy::Auto,
        }];
        assert_eq!(
            classify_rewrite(&make_rewrite("f", "a.rs", assert_kind()), &permissive),
            ApprovalPolicy::Auto,
            "control: the rule does promote an authoritative proposal"
        );
        assert_eq!(
            classify_rewrite(&frontend_rewrite(assert_kind()), &permissive),
            ApprovalPolicy::Review,
        );
    }

    #[test]
    fn a_policy_rule_may_still_make_a_frontend_proposal_stricter() {
        // The ceiling is one-directional: Block stays Block.
        let blocking = vec![PolicyRule {
            path_pattern: String::new(),
            kind_filter: None,
            policy: ApprovalPolicy::Block,
        }];
        assert_eq!(
            classify_rewrite(&frontend_rewrite(attr_kind()), &blocking),
            ApprovalPolicy::Block,
        );
    }

    // --- PendingRewrite tests ---

    #[test]
    fn test_pending_rewrite_reviewer_notes_default_none() {
        let pr = PendingRewrite {
            rewrite: make_rewrite("f", "a.rs", attr_kind()),
            policy: ApprovalPolicy::Review,
            reviewer_notes: None,
        };
        assert!(pr.reviewer_notes.is_none());
    }
}
