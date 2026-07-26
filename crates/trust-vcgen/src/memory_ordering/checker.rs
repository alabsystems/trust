// trust_vcgen/memory_ordering/checker.rs: MemoryModelChecker and related types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{
    AtomicOpKind, AtomicOperation, AtomicOrdering, Formula, Sort, SourceSpan, VcKind,
    VerificationCondition,
};

use super::atomic_access::AtomicAccessLog;
use super::happens_before::HappensBefore;
use super::race_condition::RaceCondition;
use crate::data_race::MemoryOrdering;

fn generated_memory_ordering_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("memory_ordering", unqualified)
}

/// An ordering requirement for an atomic access.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderingRequirement {
    /// Index into the access log.
    pub access_index: usize,
    /// The minimum required ordering.
    pub required: MemoryOrdering,
    /// Human-readable reason for the requirement.
    pub reason: String,
}

/// Result of a memory model check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryModelCheckResult {
    /// Detected data races.
    pub races: Vec<RaceCondition>,
    /// Ordering violations (too-weak atomic orderings).
    pub ordering_violations: Vec<OrderingViolation>,
    /// Coverage gaps where an ordering requirement could not be checked.
    #[serde(default)]
    pub ordering_coverage_gaps: Vec<OrderingCoverageGap>,
    /// Whether the check passed (no races, no violations).
    pub is_sound: bool,
}

/// An ordering violation: an atomic access uses a weaker ordering than required.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderingViolation {
    /// Index of the offending access.
    pub access_index: usize,
    /// The location accessed.
    pub location: String,
    /// The ordering actually used.
    pub actual: MemoryOrdering,
    /// The ordering required.
    pub required: MemoryOrdering,
    /// Reason the stronger ordering is needed.
    pub reason: String,
    /// Source span of the access.
    pub span: SourceSpan,
}

/// A memory-ordering obligation that could not be checked against concrete
/// atomic evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderingCoverageGap {
    /// Index requested by the ordering requirement.
    pub access_index: usize,
    /// Number of atomic access-log entries available.
    pub access_count: usize,
    /// The minimum required ordering.
    pub required: MemoryOrdering,
    /// Reason the requirement was requested.
    pub reason: String,
    /// Fail-closed diagnostic detail.
    pub detail: String,
    /// Source span when the malformed requirement names an existing entry.
    pub span: SourceSpan,
}

/// Verifies memory ordering constraints for a set of atomic accesses.
///
/// Combines data race detection with ordering sufficiency checking.
/// Produces VCs for any detected issues.
#[derive(Debug, Clone)]
pub struct MemoryModelChecker {
    /// The atomic access log to check.
    pub(in crate::memory_ordering) log: AtomicAccessLog,
    /// The happens-before relation.
    pub(in crate::memory_ordering) hb: HappensBefore,
    /// Ordering requirements for specific accesses.
    pub(in crate::memory_ordering) requirements: Vec<OrderingRequirement>,
}

impl MemoryModelChecker {
    /// Create a new checker with the given access log and happens-before relation.
    #[must_use]
    pub fn new(log: AtomicAccessLog, hb: HappensBefore) -> Self {
        Self { log, hb, requirements: Vec::new() }
    }

    /// Add an ordering requirement for a specific access.
    pub fn require_ordering(&mut self, requirement: OrderingRequirement) {
        self.requirements.push(requirement);
    }

    /// Run the full memory model check.
    ///
    /// Returns a result containing all detected issues.
    #[must_use]
    pub fn check(&self) -> MemoryModelCheckResult {
        let races = Vec::new(); // Atomic-only accesses don't race per C11 model
        let evidence_gaps = self.check_evidence_invariants();
        let (ordering_violations, ordering_coverage_gaps) = if evidence_gaps.is_empty() {
            self.check_ordering_requirements()
        } else {
            (Vec::new(), evidence_gaps)
        };
        let is_sound =
            races.is_empty() && ordering_violations.is_empty() && ordering_coverage_gaps.is_empty();

        MemoryModelCheckResult { races, ordering_violations, ordering_coverage_gaps, is_sound }
    }

    /// Reject malformed deserialized evidence before deriving ordering facts.
    fn check_evidence_invariants(&self) -> Vec<OrderingCoverageGap> {
        let mut coverage_gaps = Vec::new();

        if let Err(invalid_indices) = self.log.validate() {
            for access_index in invalid_indices {
                let requirement =
                    self.requirements.iter().find(|req| req.access_index == access_index);
                let required = requirement.map_or(MemoryOrdering::SeqCst, |req| req.required);
                let reason = requirement.map_or_else(
                    || "atomic access log evidence must be well-formed".to_string(),
                    |req| req.reason.clone(),
                );
                let (detail, span) = match self.log.entries().get(access_index) {
                    Some(entry) => (
                        format!(
                            "invalid atomic access log: non-atomic access `{}` at index {}",
                            entry.location, access_index
                        ),
                        entry.span.clone(),
                    ),
                    None => (
                        format!(
                            "invalid atomic access log references missing access index {}",
                            access_index
                        ),
                        SourceSpan::default(),
                    ),
                };

                coverage_gaps.push(OrderingCoverageGap {
                    access_index,
                    access_count: self.log.len(),
                    required,
                    reason,
                    detail,
                    span,
                });
            }
        }

        if let Err(invalid_edges) = self.hb.validate() {
            for (from, to) in invalid_edges {
                let (access_index, detail) = match to {
                    Some(to) => (
                        to,
                        format!(
                            "invalid happens-before edge {} -> {} references event outside \
                             event_count {}",
                            from,
                            to,
                            self.hb.event_count()
                        ),
                    ),
                    None => (
                        from,
                        format!(
                            "invalid happens-before source {} references event outside \
                             event_count {}",
                            from,
                            self.hb.event_count()
                        ),
                    ),
                };

                coverage_gaps.push(OrderingCoverageGap {
                    access_index,
                    access_count: self.hb.event_count(),
                    required: MemoryOrdering::SeqCst,
                    reason: "happens-before evidence must be well-formed".to_string(),
                    detail,
                    span: SourceSpan::default(),
                });
            }
        }

        coverage_gaps
    }

    /// Check all ordering requirements against actual orderings.
    fn check_ordering_requirements(&self) -> (Vec<OrderingViolation>, Vec<OrderingCoverageGap>) {
        let mut violations = Vec::new();
        let mut coverage_gaps = Vec::new();

        for req in &self.requirements {
            let Some(entry) = self.log.entries().get(req.access_index) else {
                coverage_gaps.push(OrderingCoverageGap {
                    access_index: req.access_index,
                    access_count: self.log.len(),
                    required: req.required,
                    reason: req.reason.clone(),
                    detail: format!(
                        "ordering requirement references missing atomic access index {} \
                         (access log length {})",
                        req.access_index,
                        self.log.len()
                    ),
                    span: SourceSpan::default(),
                });
                continue;
            };

            let Some(actual) = entry.access_kind.ordering() else {
                coverage_gaps.push(OrderingCoverageGap {
                    access_index: req.access_index,
                    access_count: self.log.len(),
                    required: req.required,
                    reason: req.reason.clone(),
                    detail: format!(
                        "ordering requirement references non-atomic access `{}` at index {}",
                        entry.location, req.access_index
                    ),
                    span: entry.span.clone(),
                });
                continue;
            };

            if !actual.is_at_least(req.required) {
                violations.push(OrderingViolation {
                    access_index: req.access_index,
                    location: entry.location.clone(),
                    actual,
                    required: req.required,
                    reason: req.reason.clone(),
                    span: entry.span.clone(),
                });
            }
        }

        (violations, coverage_gaps)
    }

    /// Check that release-acquire pairs establish proper synchronization.
    ///
    /// For each release-acquire pair on the same location, verifies that
    /// the release has at least Release ordering and the acquire has at
    /// least Acquire ordering.
    #[must_use]
    pub fn check_release_acquire_consistency(&self) -> Vec<OrderingViolation> {
        let mut violations = Vec::new();
        let pairs = self.log.find_release_acquire_pairs();

        for (release_idx, acquire_idx) in pairs {
            if let (Some(release), Some(acquire)) =
                (self.log.entries().get(release_idx), self.log.entries().get(acquire_idx))
            {
                // Release side must have at least Release ordering.
                if let Some(actual) = release.access_kind.ordering()
                    && !actual.is_at_least(MemoryOrdering::Release)
                {
                    violations.push(OrderingViolation {
                        access_index: release_idx,
                        location: release.location.clone(),
                        actual,
                        required: MemoryOrdering::Release,
                        reason: "release side of synchronization pair".to_string(),
                        span: release.span.clone(),
                    });
                }

                // Acquire side must have at least Acquire ordering.
                if let Some(actual) = acquire.access_kind.ordering()
                    && !actual.is_at_least(MemoryOrdering::Acquire)
                {
                    violations.push(OrderingViolation {
                        access_index: acquire_idx,
                        location: acquire.location.clone(),
                        actual,
                        required: MemoryOrdering::Acquire,
                        reason: "acquire side of synchronization pair".to_string(),
                        span: acquire.span.clone(),
                    });
                }
            }
        }

        violations
    }

    /// Generate verification conditions for all detected memory model issues.
    #[must_use]
    pub fn generate_vcs(&self, function_name: &str) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();
        let result = self.check();

        // VCs for data races
        for race in &result.races {
            let reach_a = Formula::Var(
                generated_memory_ordering_symbol(&format!(
                    "reach_{}_{}",
                    race.first_thread, race.first_access
                )),
                Sort::Bool,
            );
            let reach_b = Formula::Var(
                generated_memory_ordering_symbol(&format!(
                    "reach_{}_{}",
                    race.second_thread, race.second_access
                )),
                Sort::Bool,
            );
            let formula = Formula::And(vec![reach_a, reach_b, Formula::Bool(true)]);

            vcs.push(VerificationCondition {
                kind: VcKind::DataRace {
                    variable: race.location.clone(),
                    thread_a: race.first_thread.clone(),
                    thread_b: race.second_thread.clone(),
                },
                function: function_name.into(),
                location: race.first_span.clone(),
                formula,
                contract_metadata: None,
            });
        }

        // VCs for ordering violations
        for violation in &result.ordering_violations {
            let reach = Formula::Var(
                generated_memory_ordering_symbol(&format!("reach_{}", violation.access_index)),
                Sort::Bool,
            );

            vcs.push(VerificationCondition {
                kind: VcKind::InsufficientOrdering {
                    variable: violation.location.clone(),
                    actual: violation.actual.name().to_string(),
                    required: violation.required.name().to_string(),
                },
                function: function_name.into(),
                location: violation.span.clone(),
                formula: reach,
                contract_metadata: None,
            });
        }

        // VCs for coverage gaps. These are not solver-dischargeable proof
        // obligations; they preserve missing concurrency evidence as an
        // explicit fail-closed blocker for router/report accounting.
        for gap in &result.ordering_coverage_gaps {
            vcs.push(VerificationCondition {
                kind: VcKind::UnsupportedMir {
                    kind: "ConcurrencyOrderingCoverageGap".to_string(),
                    detail: format!(
                        "{}; required={}; reason={}",
                        gap.detail,
                        gap.required.name(),
                        gap.reason
                    ),
                },
                function: function_name.into(),
                location: gap.span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }

        vcs
    }

    /// Return a reference to the access log.
    #[must_use]
    pub fn log(&self) -> &AtomicAccessLog {
        &self.log
    }

    /// Return a reference to the happens-before relation.
    #[must_use]
    pub fn happens_before(&self) -> &HappensBefore {
        &self.hb
    }

    /// Check operation legality for a list of atomic operations.
    ///
    /// Validates each operation against the 5 C++ standard legality rules:
    ///
    /// - **L1**: `load` cannot use `Release` or `AcqRel` ordering.
    /// - **L2**: `store` cannot use `Acquire` or `AcqRel` ordering.
    /// - **L3**: CAS failure ordering cannot be `Release` or `AcqRel`.
    /// - **L4**: CAS failure ordering must be no stronger than the success
    ///   ordering (lattice comparison via `AtomicOrdering::is_at_least()`).
    /// - **L5**: `fence` / `compiler_fence` cannot use `Relaxed` ordering.
    ///
    /// Each violation produces a `VcKind::InsufficientOrdering` VC.
    ///
    /// # Arguments
    ///
    /// * `operations` - Atomic operations extracted from MIR `Terminator::Call`
    ///   nodes (the `atomic` field on Call terminators).
    /// * `function_name` - Name of the enclosing function, for VC metadata.
    ///
    /// Part of #607
    #[must_use]
    pub fn check_operation_legality(
        operations: &[AtomicOperation],
        function_name: &str,
    ) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();

        for op in operations {
            // L1: load cannot use Release or AcqRel.
            if op.op_kind.is_load()
                && matches!(op.ordering, AtomicOrdering::Release | AtomicOrdering::AcqRel)
            {
                vcs.push(Self::legality_vc(
                    op,
                    function_name,
                    &format!(
                        "L1: {} cannot use {} ordering (loads cannot release)",
                        op.op_kind, op.ordering
                    ),
                ));
            }

            // L2: store cannot use Acquire or AcqRel.
            if op.op_kind.is_store()
                && matches!(op.ordering, AtomicOrdering::Acquire | AtomicOrdering::AcqRel)
            {
                vcs.push(Self::legality_vc(
                    op,
                    function_name,
                    &format!(
                        "L2: {} cannot use {} ordering (stores cannot acquire)",
                        op.op_kind, op.ordering
                    ),
                ));
            }

            // L3 & L4: CAS failure ordering rules.
            if matches!(
                op.op_kind,
                AtomicOpKind::CompareExchange | AtomicOpKind::CompareExchangeWeak
            ) && let Some(failure_ord) = &op.failure_ordering
            {
                // L3: CAS failure ordering cannot be Release or AcqRel.
                if matches!(failure_ord, AtomicOrdering::Release | AtomicOrdering::AcqRel) {
                    vcs.push(Self::legality_vc(
                        op,
                        function_name,
                        &format!(
                            "L3: {} failure ordering cannot be {} \
                                 (failure path is load-only, cannot release)",
                            op.op_kind, failure_ord
                        ),
                    ));
                }

                // L4: CAS failure ordering must not be stronger than success ordering.
                if !op.ordering.is_at_least(failure_ord) {
                    vcs.push(Self::legality_vc(
                        op,
                        function_name,
                        &format!(
                            "L4: {} failure ordering {} is stronger than \
                                 success ordering {} (failure must be <= success)",
                            op.op_kind, failure_ord, op.ordering
                        ),
                    ));
                }
            }

            // L5: fence / compiler_fence cannot use Relaxed.
            if op.op_kind.is_fence() && op.ordering == AtomicOrdering::Relaxed {
                vcs.push(Self::legality_vc(
                    op,
                    function_name,
                    &format!(
                        "L5: {} cannot use Relaxed ordering (fences require \
                         at least Acquire, Release, AcqRel, or SeqCst)",
                        op.op_kind
                    ),
                ));
            }
        }

        vcs
    }

    /// Build a `VcKind::InsufficientOrdering` VC for a legality violation.
    fn legality_vc(
        op: &AtomicOperation,
        function_name: &str,
        reason: &str,
    ) -> VerificationCondition {
        let variable = format!("_{}", op.place.local);
        let reach = Formula::Var(
            generated_memory_ordering_symbol(&format!("reach_{variable}")),
            Sort::Bool,
        );
        VerificationCondition {
            kind: VcKind::InsufficientOrdering {
                variable,
                actual: op.ordering.to_string(),
                required: reason.to_string(),
            },
            function: function_name.into(),
            location: op.span.clone(),
            formula: reach,
            contract_metadata: None,
        }
    }
}
