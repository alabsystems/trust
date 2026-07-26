// dead_code audit: crate-level suppression removed
//! trust-strengthen: AI-driven spec inference for the prove-strengthen-backprop loop.
//!
//! Reads proof reports (which VCs failed), analyzes failure patterns, and proposes
//! specifications (preconditions, postconditions, invariants) that would make the
//! code provable. Part of Idea 2 from VISION.md.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod abstract_domains;
pub(crate) mod abstract_invariant;
mod analyzer;
pub(crate) mod backward_inference;
pub(crate) mod cex_guided;
pub(crate) mod cex_guided_refinement;
// Counterexample-guided spec refinement loop with Formula-level suggestions.
pub(crate) mod cex_refine;
pub(crate) mod confidence;
pub(crate) mod counterexample;
pub(crate) mod ensemble;
pub(crate) mod feedback;
pub(crate) mod feedback_loop;
pub(crate) mod gate_diagnostics;
pub(crate) mod heuristic;
pub(crate) mod heuristic_rules;
// Houdini conjunctive refinement for invariant inference.
pub(crate) mod houdini;
// ICE (Implication CounterExample) guided learning for invariant inference.
pub(crate) mod ice;
pub(crate) mod pattern_library;
pub(crate) mod patterns;
mod proposer;
pub(crate) mod scoring;
pub(crate) mod source_reader;
pub(crate) mod spec_inference;
pub(crate) mod spec_mining;
pub(crate) mod spec_proposal;
pub(crate) mod spec_quality;
pub(crate) mod strategy;
pub(crate) mod structural_gate;
// trust-wp-direct verification oracle for CEGIS loop.
#[cfg(feature = "trust-wp")]
pub(crate) mod trust_wp_oracle;
pub(crate) mod template_match;
pub(crate) mod templates;
pub(crate) mod weakest_precondition;
// Loop invariant feedback from trust_wp via MIR router.
pub(crate) mod invariant_feedback;

// Re-export abstract domain hierarchy types.
pub use abstract_domains::{
    AbstractDomainOps, Bound, CongruenceDomain, CongruenceValue, IntervalDomain, OctagonDomain,
    ReducedProduct, reduce_interval_congruence, reduce_interval_octagon,
};
pub use abstract_invariant::{
    AbstractDomain, AbstractInferenceConfig, AbstractInferenceResult, DomainPrecision,
    InvariantCandidate, InvariantInferrer,
};
pub use analyzer::{FailureAnalysis, FailurePattern, analyze_failure};
// Trust: the prompt-format / response-parse contract an out-of-tree spec
// inference client would speak. Published, not wired: no caller in this tree
// reaches it since the in-tree LLM lane was removed.
pub use backward_inference::{
    FailureDescription, FunctionSummary, InferredSpec, InferredSpecItem, SpecCategory,
    SpecInferenceRequest, SpecParseError, ValidationError,
    ValidationResult as BackwardValidationResult, format_inference_prompt,
    parse_inference_response, validate_inferred_spec,
};
pub use cex_guided::{CexModel, CexValue, CounterexampleAnalyzer};
pub use cex_guided_refinement::{
    CexAnalyzer, Counterexample, RefinementStrategy, RefinementSuggestion, apply_refinement,
    is_spurious, rank_suggestions,
};
// Re-export counterexample-guided refinement loop types.
pub use cex_refine::{
    CexRefinementSuggestion, CounterexampleAnalysis, IterationResult, RefineVerifier,
    RefinementLoop, SpecWeakness, analyze_counterexample, suggest_refinement,
};
pub use confidence::{
    CalibrationTracker, ConfidenceBreakdown, ConfidenceEstimator, ConfidenceScore,
    ConfidenceWeights, ProposalSource, RankingStrategy, ScoredProposal, rank_proposals,
};
pub use counterexample::{CounterexampleHint, HintKind};
pub use ensemble::{
    EnsembleGenerator, EnsembleResult, GeneratorConfig, ScoredProposal as EnsembleScoredProposal,
    consensus, dedup_proposals as ensemble_dedup, diversity_bonus, vote,
};
pub use feedback::{
    FeedbackCollector, FeedbackError, FeedbackReport, ImprovedProposal, ProposalOutcome,
    StrategyAdjustment, VerificationOutcome,
};
pub use feedback_loop::{
    FailureClass, FeedbackEntry, FeedbackLoop, FeedbackLoopConfig, FeedbackLoopResult,
    analyze_failures, classify_failures,
};
pub use gate_diagnostics::{
    DiagnosticKind, FixSuggestion, GateDiagnostic, Severity, format_diagnostics, suggest_fix,
};
pub use heuristic::{FunctionSignature, HeuristicStrengthener, VerificationFailure};
pub use heuristic_rules::{
    BoundsCheck, DivisionGuard, HeuristicRule, NonNullReturn, OverflowGuard, ResultOk, RuleEngine,
};
// Re-export Houdini conjunctive refinement types.
pub use houdini::{
    Counterexample as HoudiniCounterexample, HoudiniConfig, HoudiniError, HoudiniRefiner,
    HoudiniResult, HoudiniVerifier,
};
// Re-export ICE learning types.
pub use ice::{
    ConcreteState, IceConfig, IceCounterexample, IceError, IceLearner, IceResult, IceVerifier,
    ImplicationExample,
};
// Re-export loop invariant feedback types.
pub use invariant_feedback::{
    InvariantHint, apply_invariant_hints, from_trust_wp_invariants, rank_invariant_hints,
};
// trust-wp-direct verification oracle for CEGIS loop.
pub use pattern_library::{
    CatalogEntry, CatalogMatch, MonotonicDirection, PatternCatalog, PatternCategory,
    PatternDatabase, PatternMatcher, PatternSuggestion, SpecPattern, apply_patterns,
    apply_patterns_with_db, builtin_patterns, instantiate_pattern, match_pattern,
};
pub use patterns::{
    CodePattern, PatternLibrary, PatternMatch, pattern_matches_to_proposals, recognize_patterns,
};
pub use proposer::{Proposal, ProposalKind, strengthen, strengthen_with_context};
pub use scoring::{
    ScoringWeights, SpecScore, rank_by_score, rank_by_score_weighted, score_proposal,
    score_proposal_weighted,
};
pub use source_reader::{SourceContext, extract_function, read_function};
pub use spec_inference::{
    InsertionTarget, StrengtheningProposal, infer_binary_search_specs, infer_null_deref,
    infer_specs, infer_specs_with_cex,
};
pub use spec_mining::{
    AssertionKind, MinedAssertion, MinedSpec, SpecMiner, TestCase, TestValue, format_as_ensures,
    format_as_requires, merge_specs,
};
pub use spec_proposal::{SpecKind, SpecProposal, format_suggestions, validate_spec};
pub use spec_quality::{
    MetricKind, QualityConfig, QualityEvaluator, QualityMetrics, QualityReport, QualityScore,
    SpecCoverage,
};
pub use strategy::{Strategy, StrategyRecord, StrategySelector, StrategySummary};
pub use structural_gate::{GateConfig, GateResult, ScopedVar, StructuralGate};
#[cfg(feature = "trust-wp")]
pub use trust_wp_oracle::{
    TrustWpDirectOracle, VerificationOracle, VerifyOutcome, import_stdlib_seed_specs,
};
pub use template_match::{
    FunctionCategory, TemplateMatchResult, classify_function, match_and_propose,
    proposal_from_template,
};
pub use templates::{SpecTemplate, SpecTemplateKind, instantiate_template, standard_templates};
use trust_types::{CrateVerificationResult, VerificationResult};
pub use weakest_precondition::{Statement, compute_weakest_precondition, substitute, wp_transform};

/// Configuration for the strengthen pass.
#[derive(Debug, Clone)]
pub struct StrengthenConfig {
    /// Minimum confidence threshold for proposals (0.0-1.0).
    pub min_confidence: f64,
    /// Maximum number of proposals per function.
    pub max_proposals_per_function: usize,
}

impl Default for StrengthenConfig {
    fn default() -> Self {
        Self { min_confidence: 0.5, max_proposals_per_function: 10 }
    }
}

/// Result of a strengthen pass over a crate's verification results.
#[derive(Debug, Clone)]
pub struct StrengthenOutput {
    /// Proposed specifications, grouped by function.
    pub proposals: Vec<Proposal>,
    /// Number of failures analyzed.
    pub failures_analyzed: usize,
    /// Whether strengthen produced any actionable proposals.
    pub has_proposals: bool,
}

/// Run the strengthen pass over a crate's verification results.
///
/// This is the main entry point. It:
/// 1. Analyzes which VCs failed and why
/// 2. Classifies failures into patterns (overflow, div-by-zero, OOB, etc.)
/// 3. Proposes specs that would make the VCs provable
pub fn run(results: &CrateVerificationResult, config: &StrengthenConfig) -> StrengthenOutput {
    let mut all_proposals = Vec::new();
    let mut total_failures = 0;

    for func in &results.functions {
        let failures: Vec<_> = func
            .results
            .iter()
            .filter(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
            .collect();

        if failures.is_empty() {
            continue;
        }

        total_failures += failures.len();

        // Analyze failure patterns
        let analyses: Vec<_> =
            failures.iter().map(|(vc, result)| analyzer::analyze_failure(vc, result)).collect();

        // Generate pattern-based proposals
        let mut proposals =
            proposer::strengthen(&func.function_path, &func.function_name, &analyses);

        // Filter by confidence and limit
        proposals.retain(|p| p.confidence >= config.min_confidence);
        proposals.truncate(config.max_proposals_per_function);

        all_proposals.extend(proposals);
    }

    StrengthenOutput {
        has_proposals: !all_proposals.is_empty(),
        proposals: all_proposals,
        failures_analyzed: total_failures,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinOp, Formula, FunctionVerificationResult, SourceSpan, Ty, VcKind, VerificationCondition,
    };

    use super::*;

    fn make_overflow_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
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
        };
        let result =
            VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None };
        (vc, result)
    }

    fn make_div_zero_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_divide".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result =
            VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None };
        (vc, result)
    }

    fn make_oob_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "get_element".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result =
            VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None };
        (vc, result)
    }

    #[test]
    fn test_strengthen_proposes_overflow_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_midpoint".into(),
                function_name: "get_midpoint".into(),
                results: vec![make_overflow_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert!(output.has_proposals);
        assert_eq!(output.failures_analyzed, 1);
        assert!(!output.proposals.is_empty());

        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
        assert!(proposal.confidence > 0.0);
    }

    #[test]
    fn test_strengthen_proposes_div_zero_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::safe_divide".into(),
                function_name: "safe_divide".into(),
                results: vec![make_div_zero_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert!(output.has_proposals);
        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_strengthen_proposes_oob_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_element".into(),
                function_name: "get_element".into(),
                results: vec![make_oob_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert!(output.has_proposals);
        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_strengthen_skips_proved_functions() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::always_ok".into(),
                function_name: "always_ok".into(),
                results: vec![(
                    VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: "always_ok".into(),
                        location: SourceSpan::default(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    },
                    VerificationResult::Proved {
                        solver: "ay".into(),
                        time_ms: 1,
                        strength: trust_types::ProofStrength::smt_unsat(),
                        proof_certificate: None,
                        solver_warnings: None,
                        native_proof_envelope: None,
                    },
                )],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert!(!output.has_proposals);
        assert_eq!(output.failures_analyzed, 0);
    }

    #[test]
    fn test_strengthen_respects_confidence_threshold() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_midpoint".into(),
                function_name: "get_midpoint".into(),
                results: vec![make_overflow_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let config = StrengthenConfig {
            min_confidence: 1.0, // impossibly high
            ..Default::default()
        };
        let output = run(&results, &config);
        assert!(!output.has_proposals);
    }

    #[test]
    fn test_strengthen_multiple_failures() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![
                FunctionVerificationResult {
                    function_path: "test::get_midpoint".into(),
                    function_name: "get_midpoint".into(),
                    results: vec![make_overflow_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: "test::safe_divide".into(),
                    function_name: "safe_divide".into(),
                    results: vec![make_div_zero_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
            ],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert!(output.has_proposals);
        assert_eq!(output.failures_analyzed, 2);
        assert!(output.proposals.len() >= 2);
    }
}
