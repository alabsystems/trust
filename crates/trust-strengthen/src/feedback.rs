// trust-strengthen/feedback.rs: Feedback loop for spec proposal improvement
//
// Tracks which proposals succeeded/failed, learns from failures to generate
// improved proposals, and adapts strategy over time. Supports cross-session
// persistence via JSON serialization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::analyzer::FailurePattern;
use crate::confidence::ProposalSource;
use crate::proposer::{Proposal, ProposalKind};

/// Outcome of applying a proposed spec to verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProposalOutcome {
    /// The proposal that was applied.
    pub proposal_kind: SerializableProposalKind,
    /// Source that generated the proposal.
    pub source: ProposalSource,
    /// Pattern name (e.g., "overflow_add", "div_zero").
    pub pattern_name: String,
    /// Whether the proposal was accepted (verification succeeded with it).
    pub was_accepted: bool,
    /// Verification result after applying the proposal.
    pub verification_result: VerificationOutcome,
    /// Time spent verifying (milliseconds).
    pub time_to_verify_ms: u64,
    /// Function the proposal targeted.
    pub function_name: String,
}

/// Simplified verification outcome for feedback tracking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationOutcome {
    /// Verification succeeded after applying the proposal.
    Proved,
    /// Verification still failed, but a different (weaker) failure.
    WeakerFailure,
    /// Verification failed with the same failure as before.
    SameFailure,
    /// Verification timed out.
    Timeout,
    /// Verification produced an error (malformed spec, etc.).
    Error,
}

/// Serializable version of ProposalKind for persistence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SerializableProposalKind {
    Precondition { spec_body: String },
    Postcondition { spec_body: String },
    Invariant { spec_body: String },
    SafeArithmetic { original: String, replacement: String },
    BoundsCheck { check_expr: String },
    NonZeroCheck { check_expr: String },
}

impl From<&ProposalKind> for SerializableProposalKind {
    fn from(kind: &ProposalKind) -> Self {
        match kind {
            ProposalKind::AddPrecondition { spec_body } => {
                Self::Precondition { spec_body: spec_body.clone() }
            }
            ProposalKind::AddPostcondition { spec_body } => {
                Self::Postcondition { spec_body: spec_body.clone() }
            }
            ProposalKind::AddInvariant { spec_body } => {
                Self::Invariant { spec_body: spec_body.clone() }
            }
            ProposalKind::SafeArithmetic { original, replacement } => Self::SafeArithmetic {
                original: original.clone(),
                replacement: replacement.clone(),
            },
            ProposalKind::AddBoundsCheck { check_expr } => {
                Self::BoundsCheck { check_expr: check_expr.clone() }
            }
            ProposalKind::AddNonZeroCheck { check_expr } => {
                Self::NonZeroCheck { check_expr: check_expr.clone() }
            }
        }
    }
}

/// An improved proposal derived from learning on a failure.
#[derive(Debug, Clone)]
pub struct ImprovedProposal {
    /// The refined proposal kind.
    pub kind: ProposalKind,
    /// The refined confidence score.
    pub confidence: f64,
    /// Human-readable rationale for the refinement.
    pub rationale: String,
}

/// Strategy adjustment based on feedback history.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StrategyAdjustment {
    /// Whether to prefer heuristic-based proposals.
    pub prefer_heuristic: bool,
    /// Whether to prefer weakest-precondition proposals.
    pub prefer_wp: bool,
    /// Whether to prefer LLM-based proposals.
    pub prefer_llm: bool,
    /// Adjusted confidence threshold for filtering.
    pub confidence_threshold: f64,
    /// Per-source weight adjustments in [0.0, 1.0].
    pub source_weights: BTreeMap<ProposalSource, f64>,
}

impl Default for StrategyAdjustment {
    fn default() -> Self {
        Self {
            prefer_heuristic: true,
            prefer_wp: true,
            prefer_llm: false,
            confidence_threshold: 0.5,
            source_weights: BTreeMap::new(),
        }
    }
}

/// Summary report of feedback trends.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeedbackReport {
    /// Total outcomes recorded.
    pub total_outcomes: usize,
    /// Overall success rate.
    pub overall_success_rate: f64,
    /// Success rate per source.
    pub by_source: BTreeMap<ProposalSource, SourceStats>,
    /// Success rate per pattern name.
    pub by_pattern: BTreeMap<String, PatternStats>,
    /// Recommended strategy adjustment.
    pub recommended_strategy: StrategyAdjustment,
}

/// Per-source statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceStats {
    pub total: usize,
    pub accepted: usize,
    pub success_rate: f64,
    pub avg_verify_time_ms: f64,
}

/// Per-pattern statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternStats {
    pub total: usize,
    pub accepted: usize,
    pub success_rate: f64,
}

/// Persistent feedback state (serializable for cross-session learning).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct FeedbackState {
    pub outcomes: Vec<ProposalOutcome>,
}

/// Collects and analyzes feedback on proposal outcomes.
#[derive(Debug, Clone)]
pub struct FeedbackCollector {
    outcomes: Vec<ProposalOutcome>,
}

impl FeedbackCollector {
    /// Create a new empty feedback collector.
    #[must_use]
    pub fn new() -> Self {
        Self { outcomes: Vec::new() }
    }

    /// Record an outcome from applying a proposal.
    pub fn record_outcome(&mut self, outcome: ProposalOutcome) {
        self.outcomes.push(outcome);
    }

    /// Record a proposal outcome from its components.
    pub fn record(
        &mut self,
        proposal: &Proposal,
        source: ProposalSource,
        pattern_name: &str,
        was_accepted: bool,
        verification_result: VerificationOutcome,
        time_to_verify_ms: u64,
    ) {
        self.outcomes.push(ProposalOutcome {
            proposal_kind: SerializableProposalKind::from(&proposal.kind),
            source,
            pattern_name: pattern_name.to_string(),
            was_accepted,
            verification_result,
            time_to_verify_ms,
            function_name: proposal.function_name.clone(),
        });
    }

    /// Number of outcomes recorded.
    #[must_use]
    pub fn outcome_count(&self) -> usize {
        self.outcomes.len()
    }

    /// Compute success rate grouped by proposal source.
    #[must_use]
    pub fn success_rate_by_source(&self) -> BTreeMap<ProposalSource, f64> {
        let mut counts: BTreeMap<ProposalSource, (usize, usize)> = BTreeMap::new();
        for outcome in &self.outcomes {
            let entry = counts.entry(outcome.source).or_insert((0, 0));
            entry.1 += 1;
            if outcome.was_accepted {
                entry.0 += 1;
            }
        }
        counts
            .into_iter()
            .map(|(source, (accepted, total))| {
                (source, if total > 0 { accepted as f64 / total as f64 } else { 0.0 })
            })
            .collect()
    }

    /// Compute success rate grouped by pattern name.
    #[must_use]
    pub fn success_rate_by_pattern(&self) -> BTreeMap<String, f64> {
        let mut counts: BTreeMap<String, (usize, usize)> = BTreeMap::new();
        for outcome in &self.outcomes {
            let entry = counts.entry(outcome.pattern_name.clone()).or_insert((0, 0));
            entry.1 += 1;
            if outcome.was_accepted {
                entry.0 += 1;
            }
        }
        counts
            .into_iter()
            .map(|(pattern, (accepted, total))| {
                (pattern, if total > 0 { accepted as f64 / total as f64 } else { 0.0 })
            })
            .collect()
    }

    /// Learn from a failed proposal to generate improved proposals.
    ///
    /// Analyzes the failure pattern and the proposal that failed to suggest
    /// refinements: stronger preconditions, alternative formulations, or
    /// complementary postconditions.
    #[must_use]
    pub fn learn_from_failure(
        &self,
        proposal: &Proposal,
        failure_pattern: &FailurePattern,
    ) -> Vec<ImprovedProposal> {
        let mut improved = Vec::new();

        match &proposal.kind {
            ProposalKind::AddPrecondition { spec_body } => {
                // Strategy: strengthen the precondition
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{spec_body} && input_is_valid"),
                    },
                    confidence: (proposal.confidence * 0.9).clamp(0.0, 1.0),
                    rationale: format!(
                        "Strengthened precondition: original '{spec_body}' was insufficient"
                    ),
                });

                // Strategy: add complementary invariant
                if matches!(
                    failure_pattern,
                    FailurePattern::ArithmeticOverflow { .. } | FailurePattern::IndexOutOfBounds
                ) {
                    improved.push(ImprovedProposal {
                        kind: ProposalKind::AddInvariant {
                            spec_body: format!("maintains: {spec_body}"),
                        },
                        confidence: (proposal.confidence * 0.7).clamp(0.0, 1.0),
                        rationale: "Add invariant to preserve precondition through loops"
                            .to_string(),
                    });
                }
            }
            ProposalKind::AddPostcondition { spec_body } => {
                // Strategy: weaken the postcondition
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddPostcondition {
                        spec_body: format!("partial: {spec_body}"),
                    },
                    confidence: (proposal.confidence * 0.8).clamp(0.0, 1.0),
                    rationale: format!(
                        "Weakened postcondition: original '{spec_body}' was too strong"
                    ),
                });
            }
            ProposalKind::SafeArithmetic { original, .. } => {
                // Strategy: try a precondition instead of safe arithmetic
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{original} does not overflow"),
                    },
                    confidence: (proposal.confidence * 0.85).clamp(0.0, 1.0),
                    rationale: "Replace safe arithmetic with precondition approach".to_string(),
                });
            }
            ProposalKind::AddBoundsCheck { check_expr } => {
                // Strategy: convert bounds check to precondition
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddPrecondition {
                        spec_body: check_expr.replace("assert!(", "").replace(')', ""),
                    },
                    confidence: (proposal.confidence * 0.8).clamp(0.0, 1.0),
                    rationale: "Convert runtime bounds check to static precondition".to_string(),
                });
            }
            ProposalKind::AddInvariant { spec_body } => {
                // Strategy: strengthen the invariant with more conditions
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddInvariant {
                        spec_body: format!("{spec_body} && loop_variant_decreases"),
                    },
                    confidence: (proposal.confidence * 0.85).clamp(0.0, 1.0),
                    rationale: format!(
                        "Strengthened invariant: original '{spec_body}' was insufficient"
                    ),
                });
            }
            ProposalKind::AddNonZeroCheck { .. } => {
                // Strategy: make it a precondition
                improved.push(ImprovedProposal {
                    kind: ProposalKind::AddPrecondition { spec_body: "divisor != 0".to_string() },
                    confidence: (proposal.confidence * 0.9).clamp(0.0, 1.0),
                    rationale: "Convert non-zero runtime check to static precondition".to_string(),
                });
            }
        }

        improved
    }

    /// Adapt the strengthening strategy based on accumulated history.
    ///
    /// Analyzes success rates per source and recommends which generators
    /// to prefer and what confidence threshold to use.
    #[must_use]
    pub fn adapt_strategy(&self) -> StrategyAdjustment {
        let source_rates = self.success_rate_by_source();

        let heuristic_rate = source_rates.get(&ProposalSource::Heuristic).copied().unwrap_or(0.5);
        let wp_rate =
            source_rates.get(&ProposalSource::WeakestPrecondition).copied().unwrap_or(0.5);
        let llm_rate = source_rates.get(&ProposalSource::Llm).copied().unwrap_or(0.3);

        // Prefer sources with >50% success rate
        let prefer_heuristic = heuristic_rate >= 0.5;
        let prefer_wp = wp_rate >= 0.5;
        let prefer_llm = llm_rate >= 0.5;

        // Compute adaptive confidence threshold: lower if overall success is low
        let overall_rate = self.overall_success_rate();
        let confidence_threshold = if overall_rate < 0.3 {
            0.3 // Lower threshold to allow more speculative proposals
        } else if overall_rate > 0.7 {
            0.6 // Higher threshold since we have good proposals
        } else {
            0.5 // Default
        };

        let mut source_weights = BTreeMap::new();
        for (source, rate) in source_rates {
            source_weights.insert(source, rate);
        }

        StrategyAdjustment {
            prefer_heuristic,
            prefer_wp,
            prefer_llm,
            confidence_threshold,
            source_weights,
        }
    }

    /// Generate a full feedback report with trends and recommendations.
    #[must_use]
    pub fn report(&self) -> FeedbackReport {
        let mut by_source: BTreeMap<ProposalSource, (usize, usize, u64)> = BTreeMap::new();
        let mut by_pattern: BTreeMap<String, (usize, usize)> = BTreeMap::new();

        for outcome in &self.outcomes {
            let source_entry = by_source.entry(outcome.source).or_insert((0, 0, 0));
            source_entry.1 += 1;
            source_entry.2 += outcome.time_to_verify_ms;
            if outcome.was_accepted {
                source_entry.0 += 1;
            }

            let pattern_entry = by_pattern.entry(outcome.pattern_name.clone()).or_insert((0, 0));
            pattern_entry.1 += 1;
            if outcome.was_accepted {
                pattern_entry.0 += 1;
            }
        }

        let source_stats: BTreeMap<ProposalSource, SourceStats> = by_source
            .into_iter()
            .map(|(source, (accepted, total, time))| {
                (
                    source,
                    SourceStats {
                        total,
                        accepted,
                        success_rate: if total > 0 { accepted as f64 / total as f64 } else { 0.0 },
                        avg_verify_time_ms: if total > 0 {
                            time as f64 / total as f64
                        } else {
                            0.0
                        },
                    },
                )
            })
            .collect();

        let pattern_stats: BTreeMap<String, PatternStats> = by_pattern
            .into_iter()
            .map(|(pattern, (accepted, total))| {
                (
                    pattern,
                    PatternStats {
                        total,
                        accepted,
                        success_rate: if total > 0 { accepted as f64 / total as f64 } else { 0.0 },
                    },
                )
            })
            .collect();

        FeedbackReport {
            total_outcomes: self.outcomes.len(),
            overall_success_rate: self.overall_success_rate(),
            by_source: source_stats,
            by_pattern: pattern_stats,
            recommended_strategy: self.adapt_strategy(),
        }
    }

    /// Persist feedback data to a JSON file for cross-session learning.
    ///
    /// # Errors
    /// Returns an error if the file cannot be written or serialization fails.
    pub fn persist_feedback(&self, path: &Path) -> Result<(), FeedbackError> {
        let state = FeedbackState { outcomes: self.outcomes.clone() };
        let json = serde_json::to_string_pretty(&state)
            .map_err(|e| FeedbackError::Serialization(e.to_string()))?;
        std::fs::write(path, json).map_err(|e| FeedbackError::Io(e.to_string()))?;
        Ok(())
    }

    /// Load feedback data from a previously persisted JSON file.
    ///
    /// # Errors
    /// Returns an error if the file cannot be read or deserialization fails.
    pub fn load_feedback(path: &Path) -> Result<Self, FeedbackError> {
        let json = std::fs::read_to_string(path).map_err(|e| FeedbackError::Io(e.to_string()))?;
        let state: FeedbackState = serde_json::from_str(&json)
            .map_err(|e| FeedbackError::Deserialization(e.to_string()))?;
        Ok(Self { outcomes: state.outcomes })
    }

    /// Overall success rate across all outcomes.
    fn overall_success_rate(&self) -> f64 {
        if self.outcomes.is_empty() {
            return 0.0;
        }
        let accepted = self.outcomes.iter().filter(|o| o.was_accepted).count();
        accepted as f64 / self.outcomes.len() as f64
    }
}

impl Default for FeedbackCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Errors from feedback persistence operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum FeedbackError {
    #[error("IO error: {0}")]
    Io(String),
    #[error("serialization error: {0}")]
    Serialization(String),
    #[error("deserialization error: {0}")]
    Deserialization(String),
}

// Serde impls for ProposalSource (needed for HashMap key serialization and persistence)
impl Serialize for ProposalSource {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let s = match self {
            Self::Heuristic => "heuristic",
            Self::WeakestPrecondition => "weakest_precondition",
            Self::Llm => "llm",
            Self::CounterexampleGuided => "counterexample_guided",
            Self::SignatureBased => "signature_based",
        };
        serializer.serialize_str(s)
    }
}

impl<'de> Deserialize<'de> for ProposalSource {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        match s.as_str() {
            "heuristic" => Ok(Self::Heuristic),
            "weakest_precondition" => Ok(Self::WeakestPrecondition),
            "llm" => Ok(Self::Llm),
            "counterexample_guided" => Ok(Self::CounterexampleGuided),
            "signature_based" => Ok(Self::SignatureBased),
            other => Err(serde::de::Error::unknown_variant(
                other,
                &[
                    "heuristic",
                    "weakest_precondition",
                    "llm",
                    "counterexample_guided",
                    "signature_based",
                ],
            )),
        }
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

    fn make_outcome(
        source: ProposalSource,
        pattern: &str,
        accepted: bool,
        time_ms: u64,
    ) -> ProposalOutcome {
        ProposalOutcome {
            proposal_kind: SerializableProposalKind::Precondition { spec_body: "x != 0".into() },
            source,
            pattern_name: pattern.to_string(),
            was_accepted: accepted,
            verification_result: if accepted {
                VerificationOutcome::Proved
            } else {
                VerificationOutcome::SameFailure
            },
            time_to_verify_ms: time_ms,
            function_name: "f".into(),
        }
    }

    // --- FeedbackCollector basics ---

    #[test]
    fn test_new_collector_empty() {
        let collector = FeedbackCollector::new();
        assert_eq!(collector.outcome_count(), 0);
        assert!(collector.success_rate_by_source().is_empty());
        assert!(collector.success_rate_by_pattern().is_empty());
    }

    #[test]
    fn test_record_outcome_increments_count() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        assert_eq!(collector.outcome_count(), 1);
    }

    #[test]
    fn test_record_via_proposal() {
        let mut collector = FeedbackCollector::new();
        let proposal =
            make_proposal(ProposalKind::AddPrecondition { spec_body: "x != 0".into() }, 0.9);
        collector.record(
            &proposal,
            ProposalSource::Heuristic,
            "div_zero",
            true,
            VerificationOutcome::Proved,
            5,
        );
        assert_eq!(collector.outcome_count(), 1);
    }

    // --- Success rate by source ---

    #[test]
    fn test_success_rate_by_source_single_source() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "a", true, 10));
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "b", false, 20));
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "c", true, 15));

        let rates = collector.success_rate_by_source();
        let rate = rates.get(&ProposalSource::Heuristic).unwrap();
        assert!((rate - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_success_rate_by_source_multiple_sources() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "a", true, 10));
        collector.record_outcome(make_outcome(ProposalSource::Llm, "a", false, 100));
        collector.record_outcome(make_outcome(ProposalSource::WeakestPrecondition, "a", true, 50));

        let rates = collector.success_rate_by_source();
        assert!((rates[&ProposalSource::Heuristic] - 1.0).abs() < 1e-10);
        assert!(rates[&ProposalSource::Llm].abs() < 1e-10);
        assert!((rates[&ProposalSource::WeakestPrecondition] - 1.0).abs() < 1e-10);
    }

    // --- Success rate by pattern ---

    #[test]
    fn test_success_rate_by_pattern() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", false, 10));
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "div_zero", true, 5));

        let rates = collector.success_rate_by_pattern();
        assert!((rates["overflow"] - 0.5).abs() < 1e-10);
        assert!((rates["div_zero"] - 1.0).abs() < 1e-10);
    }

    // --- learn_from_failure ---

    #[test]
    fn test_learn_from_precondition_failure() {
        let collector = FeedbackCollector::new();
        let proposal =
            make_proposal(ProposalKind::AddPrecondition { spec_body: "x > 0".into() }, 0.8);
        let improved = collector.learn_from_failure(
            &proposal,
            &FailurePattern::ArithmeticOverflow { op: trust_types::BinOp::Add },
        );

        assert!(improved.len() >= 2, "should produce strengthened precondition and invariant");
        assert!(matches!(improved[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(improved[1].kind, ProposalKind::AddInvariant { .. }));
    }

    #[test]
    fn test_learn_from_postcondition_failure() {
        let collector = FeedbackCollector::new();
        let proposal =
            make_proposal(ProposalKind::AddPostcondition { spec_body: "result > 0".into() }, 0.7);
        let improved =
            collector.learn_from_failure(&proposal, &FailurePattern::PostconditionViolation);

        assert!(!improved.is_empty());
        assert!(matches!(improved[0].kind, ProposalKind::AddPostcondition { .. }));
        // Confidence should be reduced
        assert!(improved[0].confidence < proposal.confidence);
    }

    #[test]
    fn test_learn_from_safe_arithmetic_failure() {
        let collector = FeedbackCollector::new();
        let proposal = make_proposal(
            ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b)".into(),
            },
            0.75,
        );
        let improved = collector.learn_from_failure(
            &proposal,
            &FailurePattern::ArithmeticOverflow { op: trust_types::BinOp::Add },
        );

        assert!(!improved.is_empty());
        // Should suggest precondition instead
        assert!(matches!(improved[0].kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_learn_from_bounds_check_failure() {
        let collector = FeedbackCollector::new();
        let proposal = make_proposal(
            ProposalKind::AddBoundsCheck { check_expr: "assert!(i < arr.len())".into() },
            0.8,
        );
        let improved = collector.learn_from_failure(&proposal, &FailurePattern::IndexOutOfBounds);

        assert!(!improved.is_empty());
        assert!(matches!(improved[0].kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_learn_from_invariant_failure() {
        let collector = FeedbackCollector::new();
        let proposal = make_proposal(ProposalKind::AddInvariant { spec_body: "i < n".into() }, 0.6);
        let improved = collector.learn_from_failure(
            &proposal,
            &FailurePattern::ArithmeticOverflow { op: trust_types::BinOp::Add },
        );

        assert!(!improved.is_empty());
        assert!(matches!(improved[0].kind, ProposalKind::AddInvariant { .. }));
    }

    #[test]
    fn test_learn_from_nonzero_check_failure() {
        let collector = FeedbackCollector::new();
        let proposal = make_proposal(
            ProposalKind::AddNonZeroCheck { check_expr: "assert!(y != 0)".into() },
            0.8,
        );
        let improved = collector.learn_from_failure(&proposal, &FailurePattern::DivisionByZero);

        assert!(!improved.is_empty());
        assert!(matches!(improved[0].kind, ProposalKind::AddPrecondition { .. }));
    }

    // --- adapt_strategy ---

    #[test]
    fn test_adapt_strategy_default_on_empty() {
        let collector = FeedbackCollector::new();
        let strategy = collector.adapt_strategy();
        // With no data, defaults apply
        assert_eq!(strategy.confidence_threshold, 0.3);
    }

    #[test]
    fn test_adapt_strategy_prefers_successful_sources() {
        let mut collector = FeedbackCollector::new();
        // Heuristic succeeds often
        for _ in 0..10 {
            collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        }
        // LLM fails often
        for _ in 0..10 {
            collector.record_outcome(make_outcome(ProposalSource::Llm, "overflow", false, 100));
        }

        let strategy = collector.adapt_strategy();
        assert!(strategy.prefer_heuristic);
        assert!(!strategy.prefer_llm);
    }

    #[test]
    fn test_adapt_strategy_lowers_threshold_on_low_success() {
        let mut collector = FeedbackCollector::new();
        // All failures
        for _ in 0..10 {
            collector.record_outcome(make_outcome(
                ProposalSource::Heuristic,
                "overflow",
                false,
                10,
            ));
        }

        let strategy = collector.adapt_strategy();
        assert!(
            strategy.confidence_threshold <= 0.3,
            "should lower threshold on low success: {}",
            strategy.confidence_threshold
        );
    }

    #[test]
    fn test_adapt_strategy_raises_threshold_on_high_success() {
        let mut collector = FeedbackCollector::new();
        // All successes
        for _ in 0..10 {
            collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        }

        let strategy = collector.adapt_strategy();
        assert!(
            strategy.confidence_threshold >= 0.6,
            "should raise threshold on high success: {}",
            strategy.confidence_threshold
        );
    }

    // --- FeedbackReport ---

    #[test]
    fn test_report_empty() {
        let collector = FeedbackCollector::new();
        let report = collector.report();
        assert_eq!(report.total_outcomes, 0);
        assert!(report.overall_success_rate.abs() < 1e-10);
    }

    #[test]
    fn test_report_with_data() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "div_zero", false, 20));
        collector.record_outcome(make_outcome(
            ProposalSource::WeakestPrecondition,
            "overflow",
            true,
            50,
        ));

        let report = collector.report();
        assert_eq!(report.total_outcomes, 3);
        assert!((report.overall_success_rate - 2.0 / 3.0).abs() < 1e-10);
        assert!(report.by_source.contains_key(&ProposalSource::Heuristic));
        assert!(report.by_pattern.contains_key("overflow"));

        let heuristic = &report.by_source[&ProposalSource::Heuristic];
        assert_eq!(heuristic.total, 2);
        assert_eq!(heuristic.accepted, 1);
        assert!((heuristic.avg_verify_time_ms - 15.0).abs() < 1e-10);
    }

    // --- Persistence ---

    #[test]
    fn test_persist_and_load_roundtrip() {
        let mut collector = FeedbackCollector::new();
        collector.record_outcome(make_outcome(ProposalSource::Heuristic, "overflow", true, 10));
        collector.record_outcome(make_outcome(ProposalSource::Llm, "div_zero", false, 100));

        let dir = std::env::temp_dir().join("trust_feedback_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("feedback.json");

        collector.persist_feedback(&path).unwrap();
        let loaded = FeedbackCollector::load_feedback(&path).unwrap();

        assert_eq!(loaded.outcome_count(), 2);
        let rates = loaded.success_rate_by_source();
        assert!((rates[&ProposalSource::Heuristic] - 1.0).abs() < 1e-10);
        assert!(rates[&ProposalSource::Llm].abs() < 1e-10);

        // Cleanup
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_load_nonexistent_file_errors() {
        let result = FeedbackCollector::load_feedback(Path::new("/tmp/nonexistent_feedback.json"));
        assert!(result.is_err());
    }

    // --- SerializableProposalKind conversion ---

    #[test]
    fn test_serializable_proposal_kind_from_all_variants() {
        let kinds = vec![
            ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            ProposalKind::AddPostcondition { spec_body: "result > 0".into() },
            ProposalKind::AddInvariant { spec_body: "i < n".into() },
            ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b)".into(),
            },
            ProposalKind::AddBoundsCheck { check_expr: "assert!(i < len)".into() },
            ProposalKind::AddNonZeroCheck { check_expr: "assert!(y != 0)".into() },
        ];

        for kind in &kinds {
            let serializable = SerializableProposalKind::from(kind);
            let json = serde_json::to_string(&serializable).unwrap();
            let _: SerializableProposalKind = serde_json::from_str(&json).unwrap();
        }
    }

    // --- ProposalSource serde ---

    #[test]
    fn test_proposal_source_serde_roundtrip() {
        let sources = vec![
            ProposalSource::Heuristic,
            ProposalSource::WeakestPrecondition,
            ProposalSource::Llm,
            ProposalSource::CounterexampleGuided,
            ProposalSource::SignatureBased,
        ];
        for source in sources {
            let json = serde_json::to_string(&source).unwrap();
            let back: ProposalSource = serde_json::from_str(&json).unwrap();
            assert_eq!(back, source);
        }
    }
}
