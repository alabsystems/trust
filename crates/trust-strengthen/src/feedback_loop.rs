// trust-strengthen/feedback_loop.rs: Closed-loop feedback integration
//
// Connects verification results directly to spec improvement. Takes a
// CrateVerificationResult, analyzes failures, runs proposals through the
// structural gate, records outcomes in the FeedbackCollector, and produces
// improved proposals for the next iteration.
//
// This closes the loop: verify -> analyze -> propose -> gate -> feedback -> re-propose.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{CrateVerificationResult, VerificationResult};

use crate::analyzer::{self, FailureAnalysis, FailurePattern};
use crate::confidence::ProposalSource;
use crate::ensemble::{EnsembleGenerator, GeneratorConfig, ScoredProposal};
use crate::feedback::{
    FeedbackCollector, ImprovedProposal, StrategyAdjustment, VerificationOutcome,
};
use crate::proposer::{Proposal, ProposalKind};
use crate::structural_gate::{GateResult, StructuralGate};

/// A single feedback entry: one VC failure paired with its analysis and proposals.
#[derive(Debug, Clone)]
pub struct FeedbackEntry {
    /// The function containing the failure.
    pub function_name: String,
    /// The function path.
    pub function_path: String,
    /// Classified failure analysis.
    pub analysis: FailureAnalysis,
    /// Whether a counterexample was available.
    pub has_counterexample: bool,
    /// Solver that reported the failure.
    pub solver: String,
    /// Time the solver spent (ms).
    pub solver_time_ms: u64,
}

/// Classification of why a VC failed, for feedback purposes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FailureClass {
    /// Missing precondition on the function.
    MissingPrecondition,
    /// Missing postcondition or postcondition too strong.
    PostconditionIssue,
    /// Missing loop invariant.
    MissingInvariant,
    /// Arithmetic safety issue (overflow, div-by-zero).
    ArithmeticSafety,
    /// Memory safety issue (bounds, null).
    MemorySafety,
    /// Temporal/liveness issue.
    TemporalIssue,
    /// Unclassified.
    Other,
}

/// Result of one feedback loop iteration.
#[derive(Debug, Clone)]
pub struct FeedbackLoopResult {
    /// Failures analyzed in this iteration.
    pub entries: Vec<FeedbackEntry>,
    /// Proposals generated (post-gate).
    pub accepted_proposals: Vec<Proposal>,
    /// Proposals rejected by the structural gate.
    pub rejected_proposals: Vec<(Proposal, GateResult)>,
    /// Improved proposals from learning on previous failures.
    pub improved_proposals: Vec<ImprovedProposal>,
    /// Failure classification summary.
    pub failure_classes: FxHashMap<FailureClass, usize>,
    /// Strategy recommendation based on feedback history.
    pub strategy: StrategyAdjustment,
    /// Total failures in the input.
    pub total_failures: usize,
    /// Total proposals generated before gating.
    pub total_proposals_generated: usize,
}

/// Configuration for the feedback loop.
#[derive(Debug, Clone)]
pub struct FeedbackLoopConfig {
    /// Minimum confidence for proposals to enter gating.
    pub min_confidence: f64,
    /// Maximum proposals per function.
    pub max_proposals_per_function: usize,
    /// Whether to use the structural gate.
    pub use_structural_gate: bool,
    /// Whether to generate improved proposals from prior failures.
    pub learn_from_prior: bool,
    /// Maximum number of improved proposals to generate per failed proposal.
    pub max_improved_per_failure: usize,
}

impl Default for FeedbackLoopConfig {
    fn default() -> Self {
        Self {
            min_confidence: 0.3,
            max_proposals_per_function: 10,
            use_structural_gate: true,
            learn_from_prior: true,
            max_improved_per_failure: 3,
        }
    }
}

/// The feedback loop: connects verification results to spec improvement.
///
/// Maintains a `FeedbackCollector` across iterations and uses it to adapt
/// the proposal strategy over time. Each call to `run_iteration` processes
/// new verification results and returns proposals for the next verification round.
pub struct FeedbackLoop {
    collector: FeedbackCollector,
    gate: StructuralGate,
    config: FeedbackLoopConfig,
    /// History of proposals from prior iterations (for learning).
    prior_proposals: Vec<(Proposal, FailurePattern)>,
    /// Iteration counter.
    iteration: usize,
}

impl FeedbackLoop {
    /// Create a new feedback loop with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            collector: FeedbackCollector::new(),
            gate: StructuralGate::new(),
            config: FeedbackLoopConfig::default(),
            prior_proposals: Vec::new(),
            iteration: 0,
        }
    }

    /// Create a feedback loop with custom configuration.
    #[must_use]
    pub fn with_config(config: FeedbackLoopConfig) -> Self {
        Self {
            collector: FeedbackCollector::new(),
            gate: StructuralGate::new(),
            config,
            prior_proposals: Vec::new(),
            iteration: 0,
        }
    }

    /// Create a feedback loop with a pre-loaded collector (for cross-session persistence).
    #[must_use]
    pub fn with_collector(collector: FeedbackCollector, config: FeedbackLoopConfig) -> Self {
        Self {
            collector,
            gate: StructuralGate::new(),
            config,
            prior_proposals: Vec::new(),
            iteration: 0,
        }
    }

    /// Run one iteration of the feedback loop.
    ///
    /// 1. Analyzes failures in `results`
    /// 2. Generates proposals from failure patterns
    /// 3. Optionally learns from prior failed proposals
    /// 4. Runs proposals through the structural gate
    /// 5. Records outcomes in the feedback collector
    /// 6. Returns accepted proposals + strategy recommendation
    #[must_use]
    pub fn run_iteration(&mut self, results: &CrateVerificationResult) -> FeedbackLoopResult {
        self.iteration += 1;

        // Step 1: Analyze failures
        let entries = analyze_failures(results);
        let total_failures = entries.len();

        // Step 2: Classify failures
        let failure_classes = classify_failures(&entries);

        // Step 3: Generate proposals from failures
        let mut all_proposals: Vec<Proposal> = Vec::new();
        for entry in &entries {
            let proposals = crate::proposer::strengthen(
                &entry.function_path,
                &entry.function_name,
                std::slice::from_ref(&entry.analysis),
            );
            all_proposals.extend(proposals);
        }

        // Step 4: Learn from prior failed proposals
        let mut improved_proposals: Vec<ImprovedProposal> = Vec::new();
        if self.config.learn_from_prior {
            for (prior_proposal, failure_pattern) in &self.prior_proposals {
                let mut improved =
                    self.collector.learn_from_failure(prior_proposal, failure_pattern);
                improved.truncate(self.config.max_improved_per_failure);
                improved_proposals.extend(improved);
            }
        }

        // Add improved proposals to the pool
        for imp in &improved_proposals {
            all_proposals.push(Proposal {
                function_path: String::new(), // Improved proposals are generic
                function_name: String::new(),
                kind: imp.kind.clone(),
                confidence: imp.confidence,
                rationale: imp.rationale.clone(),
            });
        }

        // Step 5: Filter by confidence
        all_proposals.retain(|p| p.confidence >= self.config.min_confidence);

        let total_proposals_generated = all_proposals.len();

        // Step 6: Run through structural gate
        let (accepted, rejected) = if self.config.use_structural_gate {
            let mut accepted = Vec::new();
            let mut rejected = Vec::new();
            for proposal in all_proposals {
                let gate_result = self.gate.check(&proposal);
                if gate_result.passed {
                    accepted.push(proposal);
                } else {
                    rejected.push((proposal, gate_result));
                }
            }
            (accepted, rejected)
        } else {
            (all_proposals, Vec::new())
        };

        // Step 7: Record outcomes for accepted proposals
        for proposal in &accepted {
            self.collector.record(
                proposal,
                ProposalSource::Heuristic,
                &pattern_name_for_kind(&proposal.kind),
                true,
                VerificationOutcome::Proved,
                0,
            );
        }

        // Record rejections
        for (proposal, _gate_result) in &rejected {
            self.collector.record(
                proposal,
                ProposalSource::Heuristic,
                &pattern_name_for_kind(&proposal.kind),
                false,
                VerificationOutcome::Error,
                0,
            );
        }

        // Step 8: Update prior proposals for next iteration's learning
        self.prior_proposals.clear();
        for entry in &entries {
            for proposal in &accepted {
                self.prior_proposals.push((proposal.clone(), entry.analysis.pattern.clone()));
            }
        }

        // Step 9: Get strategy recommendation
        let strategy = self.collector.adapt_strategy();

        FeedbackLoopResult {
            entries,
            accepted_proposals: accepted,
            rejected_proposals: rejected,
            improved_proposals,
            failure_classes,
            strategy,
            total_failures,
            total_proposals_generated,
        }
    }

    /// Get the current feedback collector (for persistence or inspection).
    #[must_use]
    pub fn collector(&self) -> &FeedbackCollector {
        &self.collector
    }

    /// Get the current iteration number.
    #[must_use]
    pub fn iteration(&self) -> usize {
        self.iteration
    }

    /// Get the number of prior proposals tracked for learning.
    #[must_use]
    pub fn prior_proposal_count(&self) -> usize {
        self.prior_proposals.len()
    }

    /// Suggest specs from a set of failures, incorporating feedback history.
    ///
    /// This is a convenience method that combines analysis, proposal generation,
    /// and ensemble ranking in one call.
    #[must_use]
    pub fn suggest_from_failures(&self, entries: &[FeedbackEntry]) -> Vec<ScoredProposal> {
        let mut proposals_by_source: FxHashMap<ProposalSource, Vec<Proposal>> =
            FxHashMap::default();

        // Generate proposals from each entry
        for entry in entries {
            let proposals = crate::proposer::strengthen(
                &entry.function_path,
                &entry.function_name,
                std::slice::from_ref(&entry.analysis),
            );

            proposals_by_source.entry(ProposalSource::Heuristic).or_default().extend(proposals);
        }

        // Apply strategy adjustments from feedback history
        let strategy = self.collector.adapt_strategy();
        let config = GeneratorConfig {
            heuristic_weight: if strategy.prefer_heuristic { 0.4 } else { 0.2 },
            wp_weight: if strategy.prefer_wp { 0.35 } else { 0.15 },
            llm_weight: if strategy.prefer_llm { 0.2 } else { 0.1 },
            pattern_weight: 0.15,
        };

        let generator = EnsembleGenerator::new(config);
        generator.generate_ensemble(&proposals_by_source)
    }
}

impl Default for FeedbackLoop {
    fn default() -> Self {
        Self::new()
    }
}

/// Analyze all failures in a `CrateVerificationResult` into `FeedbackEntry` items.
#[must_use]
pub fn analyze_failures(results: &CrateVerificationResult) -> Vec<FeedbackEntry> {
    let mut entries = Vec::new();

    for func in &results.functions {
        for (vc, result) in &func.results {
            if !matches!(result, VerificationResult::Failed { .. }) {
                continue;
            }

            let analysis = analyzer::analyze_failure(vc, result);

            let (solver, time_ms, has_cex) = match result {
                VerificationResult::Failed { solver, time_ms, counterexample } => {
                    (solver.to_string(), *time_ms, counterexample.is_some())
                }
                _ => (String::new(), 0, false),
            };

            entries.push(FeedbackEntry {
                function_name: func.function_name.clone(),
                function_path: func.function_path.clone(),
                analysis,
                has_counterexample: has_cex,
                solver,
                solver_time_ms: time_ms,
            });
        }
    }

    entries
}

/// Classify failures into high-level categories for reporting.
#[must_use]
pub fn classify_failures(entries: &[FeedbackEntry]) -> FxHashMap<FailureClass, usize> {
    let mut classes: FxHashMap<FailureClass, usize> = FxHashMap::default();

    for entry in entries {
        let class = match &entry.analysis.pattern {
            FailurePattern::ArithmeticOverflow { .. }
            | FailurePattern::DivisionByZero
            | FailurePattern::NegationOverflow
            | FailurePattern::ShiftOverflow => FailureClass::ArithmeticSafety,

            FailurePattern::IndexOutOfBounds | FailurePattern::CastOverflow => {
                FailureClass::MemorySafety
            }

            FailurePattern::PreconditionViolation { .. }
            | FailurePattern::AssertionFailure { .. } => FailureClass::MissingPrecondition,

            FailurePattern::PostconditionViolation => FailureClass::PostconditionIssue,

            FailurePattern::UnreachableReached => FailureClass::MissingInvariant,

            FailurePattern::Temporal => FailureClass::TemporalIssue,

            FailurePattern::UnboundedAllocation { .. } => FailureClass::Other,

            FailurePattern::Unknown => FailureClass::Other,
        };

        *classes.entry(class).or_insert(0) += 1;
    }

    classes
}

/// Get a pattern name string from a proposal kind (for feedback tracking).
fn pattern_name_for_kind(kind: &ProposalKind) -> String {
    match kind {
        ProposalKind::AddPrecondition { .. } => "precondition".to_string(),
        ProposalKind::AddPostcondition { .. } => "postcondition".to_string(),
        ProposalKind::AddInvariant { .. } => "invariant".to_string(),
        ProposalKind::SafeArithmetic { .. } => "safe_arithmetic".to_string(),
        ProposalKind::AddBoundsCheck { .. } => "bounds_check".to_string(),
        ProposalKind::AddNonZeroCheck { .. } => "nonzero_check".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinOp, Formula, FunctionVerificationResult, SourceSpan, Ty, VcKind, VerificationCondition,
    };

    use super::*;

    fn make_overflow_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "get_midpoint".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_div_zero_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_divide".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_oob_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "get_element".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 5, counterexample: None }
    }

    fn failed_with_cex() -> VerificationResult {
        VerificationResult::Failed {
            solver: "ay".into(),
            time_ms: 10,
            counterexample: Some(trust_types::Counterexample::new(vec![
                ("a".into(), trust_types::CounterexampleValue::Uint(u64::MAX as u128)),
                ("b".into(), trust_types::CounterexampleValue::Uint(1)),
            ])),
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 2,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn make_crate_result(
        failures: Vec<(VerificationCondition, VerificationResult)>,
    ) -> CrateVerificationResult {
        CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::func".into(),
                function_name: "func".into(),
                results: failures,
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        }
    }

    fn make_multi_function_result() -> CrateVerificationResult {
        CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![
                FunctionVerificationResult {
                    function_path: "test::get_midpoint".into(),
                    function_name: "get_midpoint".into(),
                    results: vec![(make_overflow_vc(), failed_result())],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: "test::safe_divide".into(),
                    function_name: "safe_divide".into(),
                    results: vec![(make_div_zero_vc(), failed_result())],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: "test::get_element".into(),
                    function_name: "get_element".into(),
                    results: vec![(make_oob_vc(), failed_result())],
                    from_notes: 0,
                    with_assumptions: 0,
                },
            ],
            total_from_notes: 0,
            total_with_assumptions: 0,
        }
    }

    // --- analyze_failures ---

    #[test]
    fn test_analyze_failures_empty() {
        let results = CrateVerificationResult::new("empty");
        let entries = analyze_failures(&results);
        assert!(entries.is_empty());
    }

    #[test]
    fn test_analyze_failures_skips_proved() {
        let results = make_crate_result(vec![(make_overflow_vc(), proved_result())]);
        let entries = analyze_failures(&results);
        assert!(entries.is_empty());
    }

    #[test]
    fn test_analyze_failures_single_failure() {
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let entries = analyze_failures(&results);
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].function_name, "func");
        assert_eq!(entries[0].solver, "ay");
        assert!(!entries[0].has_counterexample);
    }

    #[test]
    fn test_analyze_failures_with_counterexample() {
        let results = make_crate_result(vec![(make_overflow_vc(), failed_with_cex())]);
        let entries = analyze_failures(&results);
        assert_eq!(entries.len(), 1);
        assert!(entries[0].has_counterexample);
    }

    #[test]
    fn test_analyze_failures_multiple_functions() {
        let results = make_multi_function_result();
        let entries = analyze_failures(&results);
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].function_name, "get_midpoint");
        assert_eq!(entries[1].function_name, "safe_divide");
        assert_eq!(entries[2].function_name, "get_element");
    }

    #[test]
    fn test_analyze_failures_mixed_results() {
        let results = make_crate_result(vec![
            (make_overflow_vc(), proved_result()),
            (make_div_zero_vc(), failed_result()),
        ]);
        let entries = analyze_failures(&results);
        assert_eq!(entries.len(), 1);
    }

    // --- classify_failures ---

    #[test]
    fn test_classify_failures_empty() {
        let classes = classify_failures(&[]);
        assert!(classes.is_empty());
    }

    #[test]
    fn test_classify_failures_arithmetic() {
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        assert_eq!(classes[&FailureClass::ArithmeticSafety], 1);
    }

    #[test]
    fn test_classify_failures_memory() {
        let results = make_crate_result(vec![(make_oob_vc(), failed_result())]);
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        assert_eq!(classes[&FailureClass::MemorySafety], 1);
    }

    #[test]
    fn test_classify_failures_multiple_classes() {
        let results = make_multi_function_result();
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        // overflow -> ArithmeticSafety, div_zero -> ArithmeticSafety, oob -> MemorySafety
        assert_eq!(classes[&FailureClass::ArithmeticSafety], 2);
        assert_eq!(classes[&FailureClass::MemorySafety], 1);
    }

    // --- FeedbackLoop ---

    #[test]
    fn test_feedback_loop_new_defaults() {
        let fl = FeedbackLoop::new();
        assert_eq!(fl.iteration(), 0);
        assert_eq!(fl.prior_proposal_count(), 0);
    }

    #[test]
    fn test_feedback_loop_empty_results() {
        let mut fl = FeedbackLoop::new();
        let results = CrateVerificationResult::new("empty");
        let result = fl.run_iteration(&results);
        assert_eq!(result.total_failures, 0);
        assert!(result.accepted_proposals.is_empty());
        assert!(result.entries.is_empty());
        assert_eq!(fl.iteration(), 1);
    }

    #[test]
    fn test_feedback_loop_single_failure() {
        let mut fl = FeedbackLoop::new();
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let result = fl.run_iteration(&results);
        assert_eq!(result.total_failures, 1);
        assert!(!result.accepted_proposals.is_empty());
        assert_eq!(fl.iteration(), 1);
    }

    #[test]
    fn test_feedback_loop_multiple_failures() {
        let mut fl = FeedbackLoop::new();
        let results = make_multi_function_result();
        let result = fl.run_iteration(&results);
        assert_eq!(result.total_failures, 3);
        assert!(result.accepted_proposals.len() >= 3);
    }

    #[test]
    fn test_feedback_loop_records_in_collector() {
        let mut fl = FeedbackLoop::new();
        let results = make_crate_result(vec![(make_div_zero_vc(), failed_result())]);
        let _ = fl.run_iteration(&results);
        assert!(fl.collector().outcome_count() > 0);
    }

    #[test]
    fn test_feedback_loop_tracks_prior_proposals() {
        let mut fl = FeedbackLoop::new();
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let _ = fl.run_iteration(&results);
        assert!(fl.prior_proposal_count() > 0);
    }

    #[test]
    fn test_feedback_loop_learns_from_prior() {
        let mut fl = FeedbackLoop::new();

        // First iteration: generates proposals and stores them as prior
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let _ = fl.run_iteration(&results);

        // Second iteration: should have improved proposals from learning
        let result2 = fl.run_iteration(&results);
        assert!(
            !result2.improved_proposals.is_empty(),
            "second iteration should produce improved proposals from learning"
        );
    }

    #[test]
    fn test_feedback_loop_iteration_increments() {
        let mut fl = FeedbackLoop::new();
        let results = CrateVerificationResult::new("test");
        let _ = fl.run_iteration(&results);
        assert_eq!(fl.iteration(), 1);
        let _ = fl.run_iteration(&results);
        assert_eq!(fl.iteration(), 2);
        let _ = fl.run_iteration(&results);
        assert_eq!(fl.iteration(), 3);
    }

    #[test]
    fn test_feedback_loop_no_gate() {
        let config = FeedbackLoopConfig { use_structural_gate: false, ..Default::default() };
        let mut fl = FeedbackLoop::with_config(config);
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let result = fl.run_iteration(&results);
        assert!(result.rejected_proposals.is_empty(), "no gate means no rejections");
        assert!(!result.accepted_proposals.is_empty());
    }

    #[test]
    fn test_feedback_loop_no_learning() {
        let config = FeedbackLoopConfig { learn_from_prior: false, ..Default::default() };
        let mut fl = FeedbackLoop::with_config(config);
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let _ = fl.run_iteration(&results);
        let result2 = fl.run_iteration(&results);
        assert!(result2.improved_proposals.is_empty(), "learning disabled");
    }

    #[test]
    fn test_feedback_loop_confidence_filter() {
        let config = FeedbackLoopConfig { min_confidence: 0.99, ..Default::default() };
        let mut fl = FeedbackLoop::with_config(config);
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let result = fl.run_iteration(&results);
        // Most proposals have confidence < 0.99, so few should pass
        assert!(
            result.total_proposals_generated <= 1,
            "high confidence filter should remove most proposals"
        );
    }

    #[test]
    fn test_feedback_loop_with_collector() {
        let mut collector = FeedbackCollector::new();
        // Pre-load some history
        collector.record(
            &Proposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: ProposalKind::AddPrecondition { spec_body: "x != 0".into() },
                confidence: 0.9,
                rationale: "test".into(),
            },
            ProposalSource::Heuristic,
            "div_zero",
            true,
            VerificationOutcome::Proved,
            5,
        );

        let fl = FeedbackLoop::with_collector(collector, FeedbackLoopConfig::default());
        assert!(fl.collector().outcome_count() > 0);
    }

    #[test]
    fn test_feedback_loop_strategy_adapts() {
        let mut fl = FeedbackLoop::new();
        let results = make_multi_function_result();

        // Run several iterations
        for _ in 0..3 {
            let _ = fl.run_iteration(&results);
        }

        let strategy = fl.collector().adapt_strategy();
        // After several iterations of successful heuristic proposals, heuristic should be preferred
        assert!(strategy.prefer_heuristic);
    }

    // --- suggest_from_failures ---

    #[test]
    fn test_suggest_from_failures_empty() {
        let fl = FeedbackLoop::new();
        let suggestions = fl.suggest_from_failures(&[]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_suggest_from_failures_ranked() {
        let fl = FeedbackLoop::new();
        let results = make_multi_function_result();
        let entries = analyze_failures(&results);
        let suggestions = fl.suggest_from_failures(&entries);

        assert!(!suggestions.is_empty());
        // Verify ranks are sequential
        for (i, sp) in suggestions.iter().enumerate() {
            assert_eq!(sp.rank, i + 1);
        }
        // Verify sorted by confidence descending
        for window in suggestions.windows(2) {
            assert!(window[0].confidence >= window[1].confidence);
        }
    }

    #[test]
    fn test_suggest_from_failures_all_have_confidence() {
        let fl = FeedbackLoop::new();
        let results = make_crate_result(vec![(make_div_zero_vc(), failed_result())]);
        let entries = analyze_failures(&results);
        let suggestions = fl.suggest_from_failures(&entries);

        for sp in &suggestions {
            assert!(sp.confidence > 0.0, "all suggestions should have positive confidence");
            assert!(sp.confidence <= 1.0, "confidence should be <= 1.0");
        }
    }

    // --- FeedbackLoopResult ---

    #[test]
    fn test_feedback_loop_result_has_failure_classes() {
        let mut fl = FeedbackLoop::new();
        let results = make_multi_function_result();
        let result = fl.run_iteration(&results);
        assert!(!result.failure_classes.is_empty());
        assert!(result.failure_classes.contains_key(&FailureClass::ArithmeticSafety));
    }

    #[test]
    fn test_feedback_loop_result_strategy_present() {
        let mut fl = FeedbackLoop::new();
        let results = make_crate_result(vec![(make_overflow_vc(), failed_result())]);
        let result = fl.run_iteration(&results);
        // Strategy should always be present
        assert!(result.strategy.confidence_threshold > 0.0);
    }

    // --- pattern_name_for_kind ---

    #[test]
    fn test_pattern_name_for_all_kinds() {
        let kinds = [
            ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            ProposalKind::AddPostcondition { spec_body: "result > 0".into() },
            ProposalKind::AddInvariant { spec_body: "i < n".into() },
            ProposalKind::SafeArithmetic {
                original: "a+b".into(),
                replacement: "a.checked_add(b)".into(),
            },
            ProposalKind::AddBoundsCheck { check_expr: "assert!(i < len)".into() },
            ProposalKind::AddNonZeroCheck { check_expr: "assert!(y != 0)".into() },
        ];

        let expected = [
            "precondition",
            "postcondition",
            "invariant",
            "safe_arithmetic",
            "bounds_check",
            "nonzero_check",
        ];
        for (kind, exp) in kinds.iter().zip(expected.iter()) {
            assert_eq!(pattern_name_for_kind(kind), *exp);
        }
    }

    // --- FailureClass ---

    #[test]
    fn test_failure_class_precondition_violation() {
        let vc = VerificationCondition {
            kind: VcKind::Precondition { callee: "safe_divide".into() },
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let results = make_crate_result(vec![(vc, failed_result())]);
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        assert_eq!(classes[&FailureClass::MissingPrecondition], 1);
    }

    #[test]
    fn test_failure_class_postcondition() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "build".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let results = make_crate_result(vec![(vc, failed_result())]);
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        assert_eq!(classes[&FailureClass::PostconditionIssue], 1);
    }

    #[test]
    fn test_failure_class_temporal() {
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "event_loop".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let results = make_crate_result(vec![(vc, failed_result())]);
        let entries = analyze_failures(&results);
        let classes = classify_failures(&entries);
        assert_eq!(classes[&FailureClass::TemporalIssue], 1);
    }
}
