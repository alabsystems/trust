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
pub(crate) mod template_match;
pub(crate) mod templates;
// Fail-closed compatibility shim for the retired direct TrustWP CEGIS oracle.
#[cfg(feature = "trust-wp")]
pub(crate) mod trust_wp_oracle;
pub(crate) mod weakest_precondition;
// Standalone conversion for historical TrustWP invariant diagnostics; the MIR
// router does not feed this module into proof authority.
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
pub use proposer::{
    Proposal, ProposalKind, strengthen, strengthen_for_function, strengthen_with_context,
};
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
pub use template_match::{
    FunctionCategory, TemplateMatchResult, classify_function, match_and_propose,
    proposal_from_template,
};
pub use templates::{SpecTemplate, SpecTemplateKind, instantiate_template, standard_templates};
use trust_types::fx::FxHashMap;
use trust_types::{CrateVerificationResult, VerificationResult};
#[cfg(feature = "trust-wp")]
pub use trust_wp_oracle::{
    TrustWpDirectOracle, VerificationOracle, VerifyOutcome, import_stdlib_seed_specs,
};
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
/// 3. Proposes specs that would make the VCs provable, using the function's
///    source (read from `function_path` when that is a file) for variable names
pub fn run(results: &CrateVerificationResult, config: &StrengthenConfig) -> StrengthenOutput {
    let mut all_proposals = Vec::new();
    let mut total_failures = 0;
    let mut source_cache: FxHashMap<&str, Option<String>> = FxHashMap::default();

    for func in &results.functions {
        // Analyze failure patterns in a single pass without intermediate failure Vec allocation.
        let analyses: Vec<_> = func
            .results
            .iter()
            .filter_map(|(vc, result)| {
                matches!(result, VerificationResult::Failed { .. })
                    .then(|| analyzer::analyze_failure(vc, result))
            })
            .collect();

        if analyses.is_empty() {
            continue;
        }

        total_failures += analyses.len();

        // Generate pattern-based proposals, reading each source file at most once per run
        // when `function_path` names a file so proposals use real names.
        let source_text = source_cache
            .entry(func.function_path.as_str())
            .or_insert_with(|| std::fs::read_to_string(&func.function_path).ok())
            .as_deref();
        let mut proposals = proposer::strengthen_for_function_in_source(
            &func.function_path,
            &func.function_name,
            &analyses,
            source_text,
        );

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
            obligation: None,
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
            obligation: None,
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
            obligation: None,
        };
        let result =
            VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None };
        (vc, result)
    }

    /// A source file in the temp dir, removed on drop.
    struct TempSource(std::path::PathBuf);

    impl TempSource {
        fn new(tag: &str, source: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "trust_strengthen_{tag}_{}_{:?}.rs",
                std::process::id(),
                std::thread::current().id()
            ));
            std::fs::write(&path, source).expect("write temp source");
            Self(path)
        }

        fn path(&self) -> String {
            self.0.display().to_string()
        }
    }

    impl Drop for TempSource {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    fn one_function(
        path: String,
        name: &str,
        failure: (VerificationCondition, VerificationResult),
    ) -> CrateVerificationResult {
        CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: path,
                function_name: name.into(),
                results: vec![failure],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        }
    }

    const MIDPOINT_SOURCE: &str =
        "pub fn get_midpoint(a: usize, b: usize) -> usize {\n    (a + b) / 2\n}\n";

    #[test]
    fn test_strengthen_proposes_overflow_precondition() {
        let file = TempSource::new("midpoint", MIDPOINT_SOURCE);
        let results = one_function(file.path(), "get_midpoint", make_overflow_failure());

        let output = run(&results, &StrengthenConfig::default());
        assert!(output.has_proposals);
        assert_eq!(output.failures_analyzed, 1);

        let proposal = &output.proposals[0];
        assert_eq!(
            proposal.kind,
            ProposalKind::AddPrecondition { spec_body: "a <= 18446744073709551615 - b".into() }
        );
        assert!(proposal.confidence > 0.0);
    }

    #[test]
    fn test_strengthen_overflow_without_source_proposes_nothing() {
        // A module path is not a file: no operand names can be recovered, so
        // nothing is proposed (previously the placeholder `a + b >= a`).
        let results =
            one_function("test::get_midpoint".into(), "get_midpoint", make_overflow_failure());
        let output = run(&results, &StrengthenConfig::default());
        assert_eq!(output.failures_analyzed, 1);
        assert!(!output.has_proposals, "{:?}", output.proposals);
    }

    /// Identifiers a proposal text names as variables: skips string literals,
    /// method/field names after `.`, keywords and numeric literals.
    fn named_variables(text: &str) -> Vec<String> {
        let mut names = Vec::new();
        let mut chars = text.char_indices().peekable();
        let mut prev = ' ';
        while let Some((start, c)) = chars.next() {
            if c == '"' {
                for (_, d) in chars.by_ref() {
                    if d == '"' {
                        break;
                    }
                }
                prev = '"';
                continue;
            }
            if c.is_alphabetic() || c == '_' {
                let mut end = start + c.len_utf8();
                while let Some(&(i, d)) = chars.peek() {
                    if d.is_alphanumeric() || d == '_' {
                        end = i + d.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                let word = &text[start..end];
                if prev != '.' && !matches!(word, "true" | "false") {
                    names.push(word.to_string());
                }
                prev = 'x';
                continue;
            }
            if c.is_ascii_digit() {
                while chars.peek().is_some_and(|&(_, d)| d.is_alphanumeric() || d == '_') {
                    chars.next();
                }
                prev = '0';
                continue;
            }
            if !c.is_whitespace() {
                prev = c;
            }
        }
        names
    }

    #[test]
    fn test_run_never_names_variables_absent_from_the_function() {
        use std::collections::BTreeMap;

        use trust_types::{Sort, SourceContractClause, validate_source_spec_expr};

        let cases = [
            (
                "midpoint_lo_hi",
                "midpoint",
                "pub fn midpoint(lo: usize, hi: usize) -> usize {\n    (lo + hi) / 2\n}\n",
            ),
            (
                "binary_search",
                "binary_search",
                "pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {\n    \
                 let mut low: usize = 0;\n    let mut high: usize = arr.len() - 1;\n    \
                 while low <= high {\n        let mid = (low + high) / 2;\n        \
                 if arr[mid] == target { return Some(mid); }\n        \
                 else if arr[mid] < target { low = mid + 1; } else { high = mid - 1; }\n    \
                 }\n    None\n}\n",
            ),
            ("scale", "scale", "pub fn scale(n: u32, k: u32) -> u32 {\n    n * k\n}\n"),
            ("field", "field", "pub fn field(p: &Pair) -> u64 {\n    p.x + p.y\n}\n"),
            ("noop", "noop", "pub fn noop(x: u64) -> u64 {\n    x\n}\n"),
        ];

        for (tag, name, source) in cases {
            let file = TempSource::new(tag, source);
            let ctx = extract_function(source, name).expect("fixture parses");
            let mut bound: Vec<String> = ctx.params.iter().map(|(n, _)| n.clone()).collect();
            bound.extend(named_variables(&ctx.full_source));
            let sorts: BTreeMap<String, Sort> = ctx
                .params
                .iter()
                .map(|(n, ty)| (n.clone(), if ty == "bool" { Sort::Bool } else { Sort::Int }))
                .collect();

            for (op, results) in [BinOp::Add, BinOp::Sub, BinOp::Mul].map(|op| {
                let (mut vc, result) = make_overflow_failure();
                vc.kind = VcKind::ArithmeticOverflow {
                    op,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                };
                (op, one_function(file.path(), name, (vc, result)))
            }) {
                let output = run(&results, &StrengthenConfig::default());
                for proposal in &output.proposals {
                    let texts: Vec<&str> = match &proposal.kind {
                        ProposalKind::AddPrecondition { spec_body }
                        | ProposalKind::AddPostcondition { spec_body }
                        | ProposalKind::AddInvariant { spec_body } => vec![spec_body],
                        ProposalKind::SafeArithmetic { original, replacement } => {
                            assert!(
                                source.contains(original.as_str()),
                                "{tag}/{op:?}: rewrite target `{original}` is not in the source"
                            );
                            vec![original, replacement]
                        }
                        ProposalKind::AddBoundsCheck { check_expr }
                        | ProposalKind::AddNonZeroCheck { check_expr } => vec![check_expr],
                    };
                    for text in texts {
                        for var in named_variables(text) {
                            assert!(
                                bound.contains(&var),
                                "{tag}/{op:?}: `{var}` in `{text}` is not in the function"
                            );
                        }
                    }
                    if let ProposalKind::AddPrecondition { spec_body } = &proposal.kind {
                        validate_source_spec_expr(
                            spec_body,
                            SourceContractClause::Requires,
                            &sorts,
                        )
                        .unwrap_or_else(|error| {
                            panic!("{tag}/{op:?}: `requires {spec_body}` is invalid: {error}")
                        });
                    }
                }
            }
        }

        // The pairs that must still be found: parameters get a precondition,
        // body locals only a checked rewrite.
        let file = TempSource::new(
            "midpoint_pin",
            "pub fn midpoint(lo: usize, hi: usize) -> usize {\n    (lo + hi) / 2\n}\n",
        );
        let output = run(
            &one_function(file.path(), "midpoint", make_overflow_failure()),
            &StrengthenConfig::default(),
        );
        let kinds: Vec<_> = output.proposals.iter().map(|p| p.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                ProposalKind::AddPrecondition {
                    spec_body: "lo <= 18446744073709551615 - hi".into()
                },
                ProposalKind::SafeArithmetic {
                    original: "lo + hi".into(),
                    replacement: "lo.checked_add(hi).expect(\"addition overflow\")".into(),
                },
            ]
        );
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
                        obligation: None,
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
        let file = TempSource::new("threshold", MIDPOINT_SOURCE);
        let results = one_function(file.path(), "get_midpoint", make_overflow_failure());
        assert!(run(&results, &StrengthenConfig::default()).has_proposals);

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

    #[test]
    fn wave492_run_reuses_source_file_for_multiple_functions_in_same_file() {
        let shared = TempSource::new(
            "wave492_shared",
            r#"
fn add_counts(lhs: usize, rhs: usize) -> usize {
    lhs + rhs
}

fn divide_counts(numer: usize, denom: usize) -> usize {
    numer / denom
}

fn read_slot(items: &[u64], slot: usize) -> u64 {
    items[slot]
}
"#,
        );
        let path = shared.path();
        let results = CrateVerificationResult {
            crate_name: "wave492".into(),
            functions: vec![
                FunctionVerificationResult {
                    function_path: path.clone(),
                    function_name: "add_counts".into(),
                    results: vec![make_overflow_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: path.clone(),
                    function_name: "divide_counts".into(),
                    results: vec![make_div_zero_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: path,
                    function_name: "read_slot".into(),
                    results: vec![make_oob_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
            ],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default());
        assert_eq!(output.failures_analyzed, 3);
        assert!(output.proposals.iter().any(|p| {
            p.function_name == "add_counts"
                && p.kind
                    == ProposalKind::AddPrecondition {
                        spec_body: "lhs <= 18446744073709551615 - rhs".into(),
                    }
        }));
        assert!(output.proposals.iter().any(|p| {
            p.function_name == "divide_counts"
                && p.kind == ProposalKind::AddPrecondition { spec_body: "denom != 0".into() }
        }));
        assert!(output.proposals.iter().any(|p| {
            p.function_name == "read_slot"
                && p.kind
                    == ProposalKind::AddPrecondition {
                        spec_body: "slot < items.len()".into(),
                    }
        }));
    }
}
