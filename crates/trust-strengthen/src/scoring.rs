// trust-strengthen/scoring.rs: Multi-dimensional spec scoring
//
// Scores specifications on multiple dimensions: correctness (passes verification),
// precision (rejects invalid inputs), simplicity (fewer conjuncts), coverage
// (handles edge cases). Used by the ensemble generator to rank candidates.
//
// Part of #154
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::proposer::{Proposal, ProposalKind};

/// Multi-dimensional score for a specification.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecScore {
    /// Overall score in [0.0, 1.0], computed as weighted sum of dimensions.
    pub overall: f64,
    /// Whether the spec passes verification (1.0 if proved, 0.0 if failed).
    pub correctness: f64,
    /// How precise the spec is -- rejects more invalid inputs = higher.
    pub precision: f64,
    /// Simplicity: fewer conjuncts and lower complexity = higher.
    pub simplicity: f64,
    /// Coverage: handles more edge cases (counterexamples) = higher.
    pub coverage: f64,
}

impl SpecScore {
    /// Create a score with all dimensions set to zero.
    #[must_use]
    pub fn zero() -> Self {
        Self { overall: 0.0, correctness: 0.0, precision: 0.0, simplicity: 0.0, coverage: 0.0 }
    }

    /// Create a score from individual dimensions using default weights.
    #[must_use]
    pub fn from_dimensions(
        correctness: f64,
        precision: f64,
        simplicity: f64,
        coverage: f64,
    ) -> Self {
        let weights = ScoringWeights::default();
        let overall = weights.compute(correctness, precision, simplicity, coverage);
        Self { overall, correctness, precision, simplicity, coverage }
    }

    /// Create a score from individual dimensions using custom weights.
    #[must_use]
    pub fn from_dimensions_weighted(
        correctness: f64,
        precision: f64,
        simplicity: f64,
        coverage: f64,
        weights: &ScoringWeights,
    ) -> Self {
        let overall = weights.compute(correctness, precision, simplicity, coverage);
        Self { overall, correctness, precision, simplicity, coverage }
    }
}

/// Weights for combining scoring dimensions into an overall score.
#[derive(Debug, Clone, PartialEq)]
pub struct ScoringWeights {
    /// Weight for correctness dimension.
    pub correctness: f64,
    /// Weight for precision dimension.
    pub precision: f64,
    /// Weight for simplicity dimension.
    pub simplicity: f64,
    /// Weight for coverage dimension.
    pub coverage: f64,
}

impl Default for ScoringWeights {
    fn default() -> Self {
        Self { correctness: 0.4, precision: 0.25, simplicity: 0.15, coverage: 0.2 }
    }
}

impl ScoringWeights {
    /// Compute weighted overall score from individual dimensions.
    #[must_use]
    pub fn compute(&self, correctness: f64, precision: f64, simplicity: f64, coverage: f64) -> f64 {
        let total_weight = self.correctness + self.precision + self.simplicity + self.coverage;
        if total_weight <= f64::EPSILON {
            return 0.0;
        }
        let raw = self.correctness * correctness
            + self.precision * precision
            + self.simplicity * simplicity
            + self.coverage * coverage;
        (raw / total_weight).clamp(0.0, 1.0)
    }

    /// Create weights that prioritize correctness above all else.
    #[must_use]
    pub fn correctness_first() -> Self {
        Self { correctness: 0.6, precision: 0.15, simplicity: 0.1, coverage: 0.15 }
    }

    /// Create weights that balance precision and simplicity equally.
    #[must_use]
    pub fn balanced() -> Self {
        Self { correctness: 0.3, precision: 0.25, simplicity: 0.25, coverage: 0.2 }
    }
}

/// Scores a proposal based on its structural properties.
///
/// This is a static analysis score -- it does not run verification. It estimates
/// correctness potential, precision, simplicity, and coverage from the proposal's
/// spec body and kind.
#[must_use]
pub fn score_proposal(proposal: &Proposal) -> SpecScore {
    let simplicity = compute_simplicity(&proposal.kind);
    let precision = compute_precision(&proposal.kind);
    let coverage = estimate_coverage(&proposal.kind);
    // Correctness is based on the proposal's own confidence (from its generator)
    let correctness = proposal.confidence;

    SpecScore::from_dimensions(correctness, precision, simplicity, coverage)
}

/// Score a proposal with custom weights.
#[must_use]
pub fn score_proposal_weighted(proposal: &Proposal, weights: &ScoringWeights) -> SpecScore {
    let simplicity = compute_simplicity(&proposal.kind);
    let precision = compute_precision(&proposal.kind);
    let coverage = estimate_coverage(&proposal.kind);
    let correctness = proposal.confidence;

    SpecScore::from_dimensions_weighted(correctness, precision, simplicity, coverage, weights)
}

/// Score and rank a list of proposals, returning them sorted by overall score descending.
#[must_use]
pub fn rank_by_score(proposals: &[Proposal]) -> Vec<(usize, SpecScore)> {
    let mut scored: Vec<(usize, SpecScore)> =
        proposals.iter().enumerate().map(|(i, p)| (i, score_proposal(p))).collect();
    scored
        .sort_by(|a, b| b.1.overall.partial_cmp(&a.1.overall).unwrap_or(std::cmp::Ordering::Equal));
    scored
}

/// Score and rank with custom weights.
#[must_use]
pub fn rank_by_score_weighted(
    proposals: &[Proposal],
    weights: &ScoringWeights,
) -> Vec<(usize, SpecScore)> {
    let mut scored: Vec<(usize, SpecScore)> = proposals
        .iter()
        .enumerate()
        .map(|(i, p)| (i, score_proposal_weighted(p, weights)))
        .collect();
    scored
        .sort_by(|a, b| b.1.overall.partial_cmp(&a.1.overall).unwrap_or(std::cmp::Ordering::Equal));
    scored
}

/// Compute simplicity score for a proposal kind.
///
/// Simpler specs score higher. Measures conjunct count, string length,
/// and nesting depth.
fn compute_simplicity(kind: &ProposalKind) -> f64 {
    let body = extract_body(kind);
    if body.is_empty() {
        return 0.0;
    }

    // Count conjuncts (split on &&)
    let conjuncts = body.matches("&&").count() + 1;
    let conjunct_score = 1.0 / (1.0 + (conjuncts as f64 - 1.0).max(0.0) * 0.3);

    // Length penalty: longer specs are less simple
    let length_score = 1.0 / (1.0 + (body.len() as f64 / 50.0));

    // Nesting penalty
    let max_depth = body
        .chars()
        .fold((0i32, 0i32), |(max, cur), ch| match ch {
            '(' => (max.max(cur + 1), cur + 1),
            ')' => (max, (cur - 1).max(0)),
            _ => (max, cur),
        })
        .0;
    let nesting_score = 1.0 / (1.0 + max_depth as f64 * 0.2);

    // Weighted combination
    (0.4 * conjunct_score + 0.3 * length_score + 0.3 * nesting_score).clamp(0.0, 1.0)
}

/// Compute precision score for a proposal kind.
///
/// More specific specs score higher. A precondition `x > 0 && x < 100` is
/// more precise than just `x > 0`.
fn compute_precision(kind: &ProposalKind) -> f64 {
    let body = extract_body(kind);
    if body.is_empty() {
        return 0.0;
    }

    let mut score: f64 = 0.5; // baseline

    // More conjuncts = more precise (up to a point)
    let conjuncts = body.matches("&&").count() + 1;
    if conjuncts >= 2 {
        score += 0.15;
    }
    if conjuncts >= 3 {
        score += 0.1;
    }

    // Specific comparisons (!=, <, >, <=, >=) are more precise than just booleans
    let comparison_ops = ["!=", "<=", ">=", "==", " < ", " > "];
    let comparison_count = comparison_ops.iter().filter(|op| body.contains(*op)).count();
    score += comparison_count as f64 * 0.05;

    // Bound checks (mentions of MAX, MIN, len) are precise
    if body.contains("MAX") || body.contains("MIN") || body.contains("len") {
        score += 0.1;
    }

    // Type-specific methods (checked_add, etc.) are precise
    if body.contains("checked_") || body.contains("saturating_") {
        score += 0.1;
    }

    score.clamp(0.0, 1.0)
}

/// Estimate coverage from the proposal kind.
///
/// Coverage measures how many edge cases the spec handles. Specs that
/// address overflow, bounds, and division are higher coverage.
fn estimate_coverage(kind: &ProposalKind) -> f64 {
    match kind {
        ProposalKind::AddPrecondition { spec_body } => {
            let mut score: f64 = 0.4;
            if spec_body.contains("&&") {
                score += 0.15; // Multiple conditions = more coverage
            }
            if spec_body.contains("!=") || spec_body.contains("> 0") {
                score += 0.1; // Guards against zero/null
            }
            if spec_body.contains("< ") || spec_body.contains("<= ") {
                score += 0.1; // Upper bound
            }
            score.clamp(0.0, 1.0)
        }
        ProposalKind::AddPostcondition { spec_body } => {
            let mut score: f64 = 0.3;
            if spec_body.contains("result") || spec_body.contains("ret") {
                score += 0.2; // Constrains return value
            }
            if spec_body.contains("&&") {
                score += 0.1;
            }
            score.clamp(0.0, 1.0)
        }
        ProposalKind::AddInvariant { .. } => 0.6, // Invariants inherently have good coverage
        ProposalKind::SafeArithmetic { .. } => 0.7, // Addresses overflow edge case directly
        ProposalKind::AddBoundsCheck { .. } => 0.65, // Addresses bounds edge case
        ProposalKind::AddNonZeroCheck { .. } => 0.6, // Addresses division by zero
    }
}

/// Extract the body string from a ProposalKind.
fn extract_body(kind: &ProposalKind) -> String {
    match kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { replacement, .. } => replacement.clone(),
        ProposalKind::AddBoundsCheck { check_expr }
        | ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proposer::{Proposal, ProposalKind};

    fn make_proposal(kind: ProposalKind, confidence: f64) -> Proposal {
        Proposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind,
            confidence,
            rationale: "test".into(),
        }
    }

    fn precondition(spec: &str, confidence: f64) -> Proposal {
        make_proposal(ProposalKind::AddPrecondition { spec_body: spec.into() }, confidence)
    }

    fn postcondition(spec: &str, confidence: f64) -> Proposal {
        make_proposal(ProposalKind::AddPostcondition { spec_body: spec.into() }, confidence)
    }

    // --- SpecScore ---

    #[test]
    fn test_spec_score_zero() {
        let score = SpecScore::zero();
        assert!((score.overall - 0.0).abs() < f64::EPSILON);
        assert!((score.correctness - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_spec_score_from_dimensions() {
        let score = SpecScore::from_dimensions(1.0, 0.8, 0.6, 0.7);
        assert!(score.overall > 0.0);
        assert!(score.overall <= 1.0);
        assert!((score.correctness - 1.0).abs() < f64::EPSILON);
        assert!((score.precision - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_spec_score_from_dimensions_weighted() {
        let weights = ScoringWeights::correctness_first();
        let score = SpecScore::from_dimensions_weighted(1.0, 0.5, 0.5, 0.5, &weights);
        let default_score = SpecScore::from_dimensions(1.0, 0.5, 0.5, 0.5);
        // Correctness-first weights should give higher overall when correctness is high
        assert!(score.overall >= default_score.overall - 0.01);
    }

    // --- ScoringWeights ---

    #[test]
    fn test_scoring_weights_default_sum() {
        let w = ScoringWeights::default();
        let sum = w.correctness + w.precision + w.simplicity + w.coverage;
        assert!((sum - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_scoring_weights_correctness_first_sum() {
        let w = ScoringWeights::correctness_first();
        let sum = w.correctness + w.precision + w.simplicity + w.coverage;
        assert!((sum - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_scoring_weights_balanced_sum() {
        let w = ScoringWeights::balanced();
        let sum = w.correctness + w.precision + w.simplicity + w.coverage;
        assert!((sum - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_scoring_weights_compute_all_ones() {
        let w = ScoringWeights::default();
        let score = w.compute(1.0, 1.0, 1.0, 1.0);
        assert!((score - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_scoring_weights_compute_all_zeros() {
        let w = ScoringWeights::default();
        let score = w.compute(0.0, 0.0, 0.0, 0.0);
        assert!(score.abs() < 1e-10);
    }

    #[test]
    fn test_scoring_weights_compute_zero_weights() {
        let w = ScoringWeights { correctness: 0.0, precision: 0.0, simplicity: 0.0, coverage: 0.0 };
        let score = w.compute(1.0, 1.0, 1.0, 1.0);
        assert!(score.abs() < 1e-10);
    }

    // --- score_proposal ---

    #[test]
    fn test_score_proposal_simple_precondition() {
        let p = precondition("x != 0", 0.9);
        let score = score_proposal(&p);
        assert!(score.overall > 0.0);
        assert!(score.overall <= 1.0);
        assert!((score.correctness - 0.9).abs() < 1e-10);
        assert!(score.simplicity > 0.5, "simple spec should have high simplicity");
    }

    #[test]
    fn test_score_proposal_complex_precondition() {
        let p = precondition("x > 0 && x < u64::MAX && y != 0 && z >= 1", 0.7);
        let score = score_proposal(&p);
        assert!(score.precision > 0.5, "complex spec should have higher precision");
    }

    #[test]
    fn test_score_proposal_higher_confidence_higher_overall() {
        let high = precondition("x != 0", 0.95);
        let low = precondition("x != 0", 0.3);
        let high_score = score_proposal(&high);
        let low_score = score_proposal(&low);
        assert!(
            high_score.overall > low_score.overall,
            "higher confidence should yield higher overall score"
        );
    }

    #[test]
    fn test_score_proposal_postcondition() {
        let p = postcondition("result > 0", 0.8);
        let score = score_proposal(&p);
        assert!(score.overall > 0.0);
        assert!(score.coverage > 0.3);
    }

    #[test]
    fn test_score_proposal_safe_arithmetic() {
        let p = make_proposal(
            ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b)".into(),
            },
            0.8,
        );
        let score = score_proposal(&p);
        assert!(score.coverage >= 0.7, "safe arithmetic should have high coverage");
    }

    #[test]
    fn test_score_proposal_bounds_check() {
        let p = make_proposal(
            ProposalKind::AddBoundsCheck { check_expr: "assert!(i < arr.len())".into() },
            0.85,
        );
        let score = score_proposal(&p);
        assert!(score.coverage >= 0.6);
    }

    // --- rank_by_score ---

    #[test]
    fn test_rank_by_score_empty() {
        let ranked = rank_by_score(&[]);
        assert!(ranked.is_empty());
    }

    #[test]
    fn test_rank_by_score_sorted_descending() {
        let proposals = vec![
            precondition("x != 0", 0.5),
            precondition("y > 0", 0.9),
            precondition("z >= 1", 0.7),
        ];
        let ranked = rank_by_score(&proposals);
        assert_eq!(ranked.len(), 3);
        // Scores should be descending
        for window in ranked.windows(2) {
            assert!(window[0].1.overall >= window[1].1.overall, "should be sorted descending");
        }
    }

    #[test]
    fn test_rank_by_score_preserves_indices() {
        let proposals = vec![precondition("x != 0", 0.3), precondition("y > 0", 0.9)];
        let ranked = rank_by_score(&proposals);
        // The high-confidence proposal (index 1) should be first
        assert_eq!(ranked[0].0, 1);
        assert_eq!(ranked[1].0, 0);
    }

    #[test]
    fn test_rank_by_score_weighted() {
        let proposals =
            vec![precondition("x != 0", 0.9), precondition("x > 0 && x < MAX && y != 0", 0.5)];
        // With correctness-first weights, high confidence should win
        let ranked = rank_by_score_weighted(&proposals, &ScoringWeights::correctness_first());
        assert_eq!(
            ranked[0].0, 0,
            "high confidence should rank first with correctness-first weights"
        );
    }

    // --- compute_simplicity ---

    #[test]
    fn test_simplicity_short_spec() {
        let kind = ProposalKind::AddPrecondition { spec_body: "x > 0".into() };
        let score = compute_simplicity(&kind);
        assert!(score > 0.5, "short spec should be simple: {score}");
    }

    #[test]
    fn test_simplicity_long_spec() {
        let kind = ProposalKind::AddPrecondition {
            spec_body: "a > 0 && b > 0 && c > 0 && d > 0 && e > 0".into(),
        };
        let score = compute_simplicity(&kind);
        let short_kind = ProposalKind::AddPrecondition { spec_body: "x > 0".into() };
        let short_score = compute_simplicity(&short_kind);
        assert!(
            score < short_score,
            "long spec ({score}) should be less simple than short ({short_score})"
        );
    }

    #[test]
    fn test_simplicity_empty_body() {
        let kind = ProposalKind::AddPrecondition { spec_body: String::new() };
        let score = compute_simplicity(&kind);
        assert!(score.abs() < f64::EPSILON);
    }

    // --- compute_precision ---

    #[test]
    fn test_precision_simple_comparison() {
        let kind = ProposalKind::AddPrecondition { spec_body: "x != 0".into() };
        let score = compute_precision(&kind);
        assert!(score >= 0.5);
    }

    #[test]
    fn test_precision_with_bounds() {
        let kind = ProposalKind::AddPrecondition { spec_body: "x > 0 && x < MAX".into() };
        let score = compute_precision(&kind);
        let simple_kind = ProposalKind::AddPrecondition { spec_body: "x > 0".into() };
        let simple_score = compute_precision(&simple_kind);
        assert!(
            score > simple_score,
            "bounded spec ({score}) should be more precise than unbounded ({simple_score})"
        );
    }

    #[test]
    fn test_precision_empty_body() {
        let kind = ProposalKind::AddPrecondition { spec_body: String::new() };
        let score = compute_precision(&kind);
        assert!(score.abs() < f64::EPSILON);
    }

    // --- estimate_coverage ---

    #[test]
    fn test_coverage_precondition_basic() {
        let kind = ProposalKind::AddPrecondition { spec_body: "x > 0".into() };
        let score = estimate_coverage(&kind);
        assert!(score > 0.3);
    }

    #[test]
    fn test_coverage_precondition_with_conjuncts() {
        let basic = ProposalKind::AddPrecondition { spec_body: "x > 0".into() };
        let conj = ProposalKind::AddPrecondition { spec_body: "x > 0 && y != 0".into() };
        assert!(estimate_coverage(&conj) > estimate_coverage(&basic));
    }

    #[test]
    fn test_coverage_safe_arithmetic_high() {
        let kind = ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b)".into(),
        };
        assert!(estimate_coverage(&kind) >= 0.7);
    }

    #[test]
    fn test_coverage_invariant() {
        let kind = ProposalKind::AddInvariant { spec_body: "i < n".into() };
        assert!(estimate_coverage(&kind) >= 0.6);
    }

    #[test]
    fn test_coverage_bounds_check() {
        let kind = ProposalKind::AddBoundsCheck { check_expr: "assert!(i < len)".into() };
        assert!(estimate_coverage(&kind) >= 0.6);
    }

    #[test]
    fn test_coverage_nonzero_check() {
        let kind = ProposalKind::AddNonZeroCheck { check_expr: "assert!(d != 0)".into() };
        assert!(estimate_coverage(&kind) >= 0.6);
    }
}
