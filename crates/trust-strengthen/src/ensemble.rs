// trust-strengthen/ensemble.rs: Ensemble spec generation combining multiple approaches
//
// Runs multiple generators (heuristic, WP, LLM, pattern) and combines their
// proposals via weighted voting, consensus detection, and diversity scoring.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use trust_types::fx::FxHashMap;

use crate::confidence::ProposalSource;
use crate::proposer::{Proposal, ProposalKind};

/// Configuration for ensemble generator weights.
#[derive(Debug, Clone, PartialEq)]
pub struct GeneratorConfig {
    /// Weight for heuristic-based generator.
    pub heuristic_weight: f64,
    /// Weight for weakest-precondition generator.
    pub wp_weight: f64,
    /// Weight for LLM-based generator.
    pub llm_weight: f64,
    /// Weight for pattern-library generator.
    pub pattern_weight: f64,
}

impl Default for GeneratorConfig {
    fn default() -> Self {
        Self { heuristic_weight: 0.3, wp_weight: 0.35, llm_weight: 0.15, pattern_weight: 0.2 }
    }
}

impl GeneratorConfig {
    /// Normalize weights so they sum to 1.0.
    #[must_use]
    pub fn normalized(&self) -> Self {
        let total = self.heuristic_weight + self.wp_weight + self.llm_weight + self.pattern_weight;
        if total <= f64::EPSILON {
            return Self::default();
        }
        Self {
            heuristic_weight: self.heuristic_weight / total,
            wp_weight: self.wp_weight / total,
            llm_weight: self.llm_weight / total,
            pattern_weight: self.pattern_weight / total,
        }
    }

    /// Get the weight for a given proposal source.
    #[must_use]
    pub fn weight_for(&self, source: ProposalSource) -> f64 {
        match source {
            ProposalSource::Heuristic => self.heuristic_weight,
            ProposalSource::WeakestPrecondition => self.wp_weight,
            ProposalSource::Llm => self.llm_weight,
            ProposalSource::CounterexampleGuided | ProposalSource::SignatureBased => {
                self.pattern_weight
            }
        }
    }
}

/// A proposal with ensemble scoring metadata.
#[derive(Debug, Clone)]
pub struct ScoredProposal {
    /// The underlying proposal.
    pub proposal: Proposal,
    /// Ensemble confidence score in [0.0, 1.0].
    pub confidence: f64,
    /// Source that generated this proposal.
    pub source: ProposalSource,
    /// Rank within the ensemble (1 = best).
    pub rank: usize,
}

/// Result of ensemble generation with per-source statistics.
#[derive(Debug, Clone)]
pub struct EnsembleResult {
    /// Final ranked proposals.
    pub proposals: Vec<ScoredProposal>,
    /// Number of proposals generated per source.
    pub per_source_counts: BTreeMap<ProposalSource, usize>,
    /// Consensus proposals (agreed on by multiple sources).
    pub consensus_count: usize,
}

/// Ensemble generator that combines proposals from multiple sources.
pub struct EnsembleGenerator {
    config: GeneratorConfig,
}

impl EnsembleGenerator {
    /// Create a new ensemble generator with the given configuration.
    #[must_use]
    pub fn new(config: GeneratorConfig) -> Self {
        Self { config }
    }

    /// Generate ensemble proposals from a verification failure.
    ///
    /// Collects proposals from each generator (passed as pre-computed lists),
    /// scores them using the ensemble config, deduplicates, and ranks.
    #[must_use]
    pub fn generate_ensemble(
        &self,
        proposals_by_source: &FxHashMap<ProposalSource, Vec<Proposal>>,
    ) -> Vec<ScoredProposal> {
        let config = self.config.normalized();
        let mut all_scored: Vec<ScoredProposal> = Vec::new();

        for (source, proposals) in sorted_source_entries(proposals_by_source) {
            let weight = config.weight_for(*source);
            for proposal in proposals {
                let confidence = (proposal.confidence * weight).clamp(0.0, 1.0);
                all_scored.push(ScoredProposal {
                    proposal: proposal.clone(),
                    confidence,
                    source: *source,
                    rank: 0,
                });
            }
        }

        // Apply voting boost: proposals appearing in multiple sources get a bonus
        let voted = self.apply_voting_boost(&all_scored, proposals_by_source);

        // Deduplicate
        let deduped = dedup_proposals(voted);

        // Sort by confidence descending and assign ranks
        let mut final_proposals = deduped;
        final_proposals.sort_by(compare_scored_proposals);
        for (i, sp) in final_proposals.iter_mut().enumerate() {
            sp.rank = i + 1;
        }

        final_proposals
    }

    /// Build a full ensemble result with per-source statistics.
    #[must_use]
    pub fn generate_result(
        &self,
        proposals_by_source: &FxHashMap<ProposalSource, Vec<Proposal>>,
    ) -> EnsembleResult {
        let proposals = self.generate_ensemble(proposals_by_source);

        let mut per_source_counts: BTreeMap<ProposalSource, usize> = BTreeMap::new();
        for (source, props) in sorted_source_entries(proposals_by_source) {
            per_source_counts.insert(*source, props.len());
        }

        let consensus_count = proposals.iter().filter(|p| p.confidence > 0.8).count();

        EnsembleResult { proposals, per_source_counts, consensus_count }
    }

    /// Apply voting boost to proposals that appear across multiple sources.
    fn apply_voting_boost(
        &self,
        scored: &[ScoredProposal],
        by_source: &FxHashMap<ProposalSource, Vec<Proposal>>,
    ) -> Vec<ScoredProposal> {
        // Count how many sources proposed each spec body
        let mut spec_source_count: BTreeMap<String, usize> = BTreeMap::new();
        for (_, proposals) in sorted_source_entries(by_source) {
            let mut seen_in_source: BTreeSet<String> = BTreeSet::new();
            for p in proposals {
                let key = spec_body_key(&p.kind);
                if seen_in_source.insert(key.clone()) {
                    *spec_source_count.entry(key).or_insert(0) += 1;
                }
            }
        }

        let source_count = by_source.len();
        scored
            .iter()
            .map(|sp| {
                let key = spec_body_key(&sp.proposal.kind);
                let count = spec_source_count.get(&key).copied().unwrap_or(1);
                let boost = if source_count > 1 && count > 1 {
                    // Boost proportional to agreement across sources
                    0.1 * (count as f64 / source_count as f64)
                } else {
                    0.0
                };
                ScoredProposal {
                    proposal: sp.proposal.clone(),
                    confidence: (sp.confidence + boost).clamp(0.0, 1.0),
                    source: sp.source,
                    rank: sp.rank,
                }
            })
            .collect()
    }
}

impl Default for EnsembleGenerator {
    fn default() -> Self {
        Self::new(GeneratorConfig::default())
    }
}

/// Weighted voting across proposals from different sources.
///
/// Combines proposals from multiple sources, weighting each by the source's
/// configured weight. Proposals appearing in multiple sources get a consensus bonus.
#[must_use]
pub fn vote(
    proposals_by_source: &FxHashMap<ProposalSource, Vec<Proposal>>,
    config: &GeneratorConfig,
) -> Vec<ScoredProposal> {
    let config = config.normalized();
    let mut aggregated: BTreeMap<String, (Proposal, f64, ProposalSource, usize)> = BTreeMap::new();

    for (source, proposals) in sorted_source_entries(proposals_by_source) {
        let weight = config.weight_for(*source);
        for proposal in proposals {
            let key = spec_body_key(&proposal.kind);
            let score = proposal.confidence * weight;
            aggregated
                .entry(key)
                .and_modify(|(_, existing_score, _, count)| {
                    *existing_score += score;
                    *count += 1;
                })
                .or_insert((proposal.clone(), score, *source, 1));
        }
    }

    let source_count = proposals_by_source.len().max(1);
    let mut results: Vec<ScoredProposal> = aggregated
        .into_iter()
        .map(|(_, (proposal, score, source, count))| {
            // Normalize score and add consensus bonus
            let consensus_bonus =
                if count > 1 { 0.1 * (count as f64 / source_count as f64) } else { 0.0 };
            ScoredProposal {
                proposal,
                confidence: (score + consensus_bonus).clamp(0.0, 1.0),
                source,
                rank: 0,
            }
        })
        .collect();

    results.sort_by(compare_scored_proposals);
    for (i, sp) in results.iter_mut().enumerate() {
        sp.rank = i + 1;
    }

    results
}

/// Find proposals that all sources agree on (appear in every source).
#[must_use]
pub fn consensus(proposals_by_source: &FxHashMap<ProposalSource, Vec<Proposal>>) -> Vec<Proposal> {
    if proposals_by_source.is_empty() {
        return Vec::new();
    }

    let source_count = proposals_by_source.len();

    // Count in how many sources each spec body appears
    let mut spec_sources: BTreeMap<String, usize> = BTreeMap::new();
    let mut spec_proposals: BTreeMap<String, Proposal> = BTreeMap::new();

    for (_, proposals) in sorted_source_entries(proposals_by_source) {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for p in proposals {
            let key = spec_body_key(&p.kind);
            if seen.insert(key.clone()) {
                *spec_sources.entry(key.clone()).or_insert(0) += 1;
                spec_proposals.entry(key).or_insert_with(|| p.clone());
            }
        }
    }

    let consensus_keys: Vec<String> = spec_sources
        .into_iter()
        .filter_map(|(key, count)| if count == source_count { Some(key) } else { None })
        .collect();

    consensus_keys.into_iter().filter_map(|key| spec_proposals.remove(&key)).collect()
}

/// Compute a diversity bonus for a proposal relative to existing proposals.
///
/// Rewards proposals that are different from what has already been proposed,
/// encouraging exploration of the spec space.
#[must_use]
pub fn diversity_bonus(proposal: &Proposal, existing: &[Proposal]) -> f64 {
    if existing.is_empty() {
        return 0.1; // Small bonus for being the first proposal
    }

    let proposal_key = spec_body_key(&proposal.kind);
    let proposal_kind_disc = std::mem::discriminant(&proposal.kind);

    let mut same_kind_count = 0;
    let mut similar_count = 0;

    for existing_p in existing {
        let existing_key = spec_body_key(&existing_p.kind);

        // Same kind of proposal (precondition, postcondition, etc.)
        if std::mem::discriminant(&existing_p.kind) == proposal_kind_disc {
            same_kind_count += 1;
        }

        // Similar spec body (shared prefix or substring)
        if has_significant_overlap(&proposal_key, &existing_key) {
            similar_count += 1;
        }
    }

    // More diverse = higher bonus
    let kind_diversity = 1.0 / (1.0 + same_kind_count as f64);
    let body_diversity = 1.0 / (1.0 + similar_count as f64);

    (0.05 * kind_diversity + 0.05 * body_diversity).clamp(0.0, 0.2)
}

/// Remove semantically equivalent proposals, keeping the highest-confidence one.
#[must_use]
pub fn dedup_proposals(mut proposals: Vec<ScoredProposal>) -> Vec<ScoredProposal> {
    // Sort by confidence descending so we keep the best
    proposals.sort_by(compare_scored_proposals);

    let mut seen: BTreeSet<String> = BTreeSet::new();
    proposals
        .into_iter()
        .filter(|sp| {
            let key = format!(
                "{}:{}",
                kind_discriminant_name(&sp.proposal.kind),
                spec_body_key(&sp.proposal.kind)
            );
            seen.insert(key)
        })
        .collect()
}

/// Extract a string key from a proposal kind for dedup and comparison.
fn spec_body_key(kind: &ProposalKind) -> String {
    match kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { original, replacement } => {
            format!("{original}->{replacement}")
        }
        ProposalKind::AddBoundsCheck { check_expr }
        | ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    }
}

/// Get a stable name for the ProposalKind discriminant.
fn kind_discriminant_name(kind: &ProposalKind) -> &'static str {
    match kind {
        ProposalKind::AddPrecondition { .. } => "precondition",
        ProposalKind::AddPostcondition { .. } => "postcondition",
        ProposalKind::AddInvariant { .. } => "invariant",
        ProposalKind::SafeArithmetic { .. } => "safe_arith",
        ProposalKind::AddBoundsCheck { .. } => "bounds_check",
        ProposalKind::AddNonZeroCheck { .. } => "nonzero_check",
    }
}

/// Check if two spec body strings have significant overlap.
fn has_significant_overlap(a: &str, b: &str) -> bool {
    if a.is_empty() || b.is_empty() {
        return false;
    }
    if a == b {
        return true;
    }
    // Check if one is a substring of the other
    if a.len() >= 4 && b.contains(a) {
        return true;
    }
    if b.len() >= 4 && a.contains(b) {
        return true;
    }
    // Check shared prefix (at least 60% overlap)
    let min_len = a.len().min(b.len());
    if min_len == 0 {
        return false;
    }
    let shared = a.chars().zip(b.chars()).take_while(|(ca, cb)| ca == cb).count();
    shared as f64 / min_len as f64 > 0.6
}

fn sorted_source_entries(
    proposals_by_source: &FxHashMap<ProposalSource, Vec<Proposal>>,
) -> Vec<(&ProposalSource, &Vec<Proposal>)> {
    const SOURCES: [ProposalSource; 5] = [
        ProposalSource::Heuristic,
        ProposalSource::WeakestPrecondition,
        ProposalSource::Llm,
        ProposalSource::CounterexampleGuided,
        ProposalSource::SignatureBased,
    ];

    SOURCES.iter().filter_map(|source| proposals_by_source.get_key_value(source)).collect()
}

fn compare_scored_proposals(a: &ScoredProposal, b: &ScoredProposal) -> Ordering {
    b.confidence
        .partial_cmp(&a.confidence)
        .unwrap_or(Ordering::Equal)
        .then_with(|| proposal_source_sort_key(a.source).cmp(&proposal_source_sort_key(b.source)))
        .then_with(|| compare_proposals(&a.proposal, &b.proposal))
}

fn compare_proposals(a: &Proposal, b: &Proposal) -> Ordering {
    a.function_path
        .cmp(&b.function_path)
        .then_with(|| a.function_name.cmp(&b.function_name))
        .then_with(|| kind_discriminant_name(&a.kind).cmp(kind_discriminant_name(&b.kind)))
        .then_with(|| spec_body_key(&a.kind).cmp(&spec_body_key(&b.kind)))
        .then_with(|| a.rationale.cmp(&b.rationale))
}

fn proposal_source_sort_key(source: ProposalSource) -> u8 {
    match source {
        ProposalSource::Heuristic => 0,
        ProposalSource::WeakestPrecondition => 1,
        ProposalSource::Llm => 2,
        ProposalSource::CounterexampleGuided => 3,
        ProposalSource::SignatureBased => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proposer::{Proposal, ProposalKind};

    fn make_proposal(kind: ProposalKind, confidence: f64, name: &str) -> Proposal {
        Proposal {
            function_path: format!("test::{name}"),
            function_name: name.into(),
            kind,
            confidence,
            rationale: "test".into(),
        }
    }

    fn precondition(spec: &str, confidence: f64) -> Proposal {
        make_proposal(ProposalKind::AddPrecondition { spec_body: spec.into() }, confidence, "f")
    }

    fn postcondition(spec: &str, confidence: f64) -> Proposal {
        make_proposal(ProposalKind::AddPostcondition { spec_body: spec.into() }, confidence, "f")
    }

    // --- GeneratorConfig ---

    #[test]
    fn test_generator_config_default_weights_sum_to_one() {
        let config = GeneratorConfig::default();
        let sum =
            config.heuristic_weight + config.wp_weight + config.llm_weight + config.pattern_weight;
        assert!((sum - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_generator_config_normalize() {
        let config = GeneratorConfig {
            heuristic_weight: 2.0,
            wp_weight: 2.0,
            llm_weight: 2.0,
            pattern_weight: 2.0,
        };
        let norm = config.normalized();
        let sum = norm.heuristic_weight + norm.wp_weight + norm.llm_weight + norm.pattern_weight;
        assert!((sum - 1.0).abs() < 1e-10);
        assert!((norm.heuristic_weight - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_generator_config_normalize_zero_returns_default() {
        let config = GeneratorConfig {
            heuristic_weight: 0.0,
            wp_weight: 0.0,
            llm_weight: 0.0,
            pattern_weight: 0.0,
        };
        let norm = config.normalized();
        let default = GeneratorConfig::default();
        assert!((norm.heuristic_weight - default.heuristic_weight).abs() < 1e-10);
    }

    #[test]
    fn test_weight_for_source() {
        let config = GeneratorConfig::default();
        assert!((config.weight_for(ProposalSource::Heuristic) - 0.3).abs() < 1e-10);
        assert!((config.weight_for(ProposalSource::WeakestPrecondition) - 0.35).abs() < 1e-10);
        assert!((config.weight_for(ProposalSource::Llm) - 0.15).abs() < 1e-10);
    }

    // --- EnsembleGenerator ---

    #[test]
    fn test_ensemble_empty_input() {
        let generator = EnsembleGenerator::default();
        let result = generator.generate_ensemble(&FxHashMap::default());
        assert!(result.is_empty());
    }

    #[test]
    fn test_ensemble_single_source() {
        let generator = EnsembleGenerator::default();
        let mut by_source = FxHashMap::default();
        by_source.insert(
            ProposalSource::Heuristic,
            vec![precondition("x != 0", 0.9), precondition("y > 0", 0.7)],
        );

        let result = generator.generate_ensemble(&by_source);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].rank, 1);
        assert_eq!(result[1].rank, 2);
        assert!(result[0].confidence >= result[1].confidence);
    }

    #[test]
    fn test_ensemble_multiple_sources() {
        let generator = EnsembleGenerator::default();
        let mut by_source = FxHashMap::default();
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.9)]);
        by_source.insert(ProposalSource::WeakestPrecondition, vec![precondition("x > 0", 0.85)]);

        let result = generator.generate_ensemble(&by_source);
        assert!(result.len() >= 2);
        // All should have ranks assigned
        for sp in &result {
            assert!(sp.rank > 0);
        }
    }

    #[test]
    fn test_ensemble_boosts_consensus() {
        let generator = EnsembleGenerator::default();
        let mut by_source = FxHashMap::default();
        // Same proposal from two sources
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.8)]);
        by_source.insert(ProposalSource::WeakestPrecondition, vec![precondition("x != 0", 0.8)]);

        let result = generator.generate_ensemble(&by_source);
        // The consensus proposal should have a boost
        let consensus_prop = result
            .iter()
            .find(|sp| {
                matches!(
                    &sp.proposal.kind,
                    ProposalKind::AddPrecondition { spec_body } if spec_body == "x != 0"
                )
            })
            .expect("should find consensus proposal");

        // It should be ranked #1
        assert_eq!(consensus_prop.rank, 1);
    }

    #[test]
    fn test_ensemble_result_has_stats() {
        let generator = EnsembleGenerator::default();
        let mut by_source = FxHashMap::default();
        by_source.insert(
            ProposalSource::Heuristic,
            vec![precondition("x != 0", 0.9), precondition("y > 0", 0.7)],
        );
        by_source.insert(ProposalSource::Llm, vec![postcondition("result >= 0", 0.6)]);

        let result = generator.generate_result(&by_source);
        assert_eq!(result.per_source_counts[&ProposalSource::Heuristic], 2);
        assert_eq!(result.per_source_counts[&ProposalSource::Llm], 1);
    }

    // --- vote ---

    #[test]
    fn test_vote_empty() {
        let result = vote(&FxHashMap::default(), &GeneratorConfig::default());
        assert!(result.is_empty());
    }

    #[test]
    fn test_vote_single_source() {
        let mut by_source = FxHashMap::default();
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.9)]);

        let result = vote(&by_source, &GeneratorConfig::default());
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].rank, 1);
    }

    #[test]
    fn test_vote_consensus_gets_higher_score() {
        let mut by_source = FxHashMap::default();
        // Same spec from two sources
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.8)]);
        by_source.insert(ProposalSource::WeakestPrecondition, vec![precondition("x != 0", 0.8)]);

        // Unique proposal from one source
        let mut unique_source = FxHashMap::default();
        unique_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.8)]);

        let consensus_result = vote(&by_source, &GeneratorConfig::default());
        let unique_result = vote(&unique_source, &GeneratorConfig::default());

        // Consensus score should be higher due to accumulation + bonus
        assert!(
            consensus_result[0].confidence > unique_result[0].confidence,
            "consensus {} should beat unique {}",
            consensus_result[0].confidence,
            unique_result[0].confidence
        );
    }

    #[test]
    fn test_vote_ranks_assigned() {
        let mut by_source = FxHashMap::default();
        by_source.insert(
            ProposalSource::Heuristic,
            vec![precondition("x != 0", 0.9), precondition("y > 0", 0.5)],
        );

        let result = vote(&by_source, &GeneratorConfig::default());
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].rank, 1);
        assert_eq!(result[1].rank, 2);
        assert!(result[0].confidence >= result[1].confidence);
    }

    // --- consensus ---

    #[test]
    fn test_consensus_empty() {
        assert!(consensus(&FxHashMap::default()).is_empty());
    }

    #[test]
    fn test_consensus_single_source() {
        let mut by_source = FxHashMap::default();
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.9)]);

        let result = consensus(&by_source);
        // Single source: everything is consensus
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_consensus_finds_agreement() {
        let mut by_source = FxHashMap::default();
        by_source.insert(
            ProposalSource::Heuristic,
            vec![precondition("x != 0", 0.9), precondition("y > 0", 0.7)],
        );
        by_source.insert(ProposalSource::WeakestPrecondition, vec![precondition("x != 0", 0.85)]);

        let result = consensus(&by_source);
        assert_eq!(result.len(), 1);
        if let ProposalKind::AddPrecondition { ref spec_body } = result[0].kind {
            assert_eq!(spec_body, "x != 0");
        } else {
            panic!("expected precondition");
        }
    }

    #[test]
    fn test_consensus_no_agreement() {
        let mut by_source = FxHashMap::default();
        by_source.insert(ProposalSource::Heuristic, vec![precondition("x != 0", 0.9)]);
        by_source.insert(ProposalSource::Llm, vec![precondition("y > 0", 0.7)]);

        let result = consensus(&by_source);
        assert!(result.is_empty());
    }

    // --- diversity_bonus ---

    #[test]
    fn test_diversity_bonus_first_proposal() {
        let proposal = precondition("x != 0", 0.9);
        let bonus = diversity_bonus(&proposal, &[]);
        assert!(bonus > 0.0, "first proposal should get a bonus");
    }

    #[test]
    fn test_diversity_bonus_different_kinds() {
        let proposal = postcondition("result > 0", 0.8);
        let existing = vec![precondition("x != 0", 0.9)];
        let bonus = diversity_bonus(&proposal, &existing);
        assert!(bonus > 0.0, "different kind should get diversity bonus");
    }

    #[test]
    fn test_diversity_bonus_same_kind_lower() {
        let proposal = precondition("y > 0", 0.8);
        let existing = vec![precondition("x != 0", 0.9)];

        let diverse_proposal = postcondition("result > 0", 0.8);

        let same_kind_bonus = diversity_bonus(&proposal, &existing);
        let diff_kind_bonus = diversity_bonus(&diverse_proposal, &existing);

        assert!(
            diff_kind_bonus >= same_kind_bonus,
            "different kind ({diff_kind_bonus}) should get >= bonus vs same kind ({same_kind_bonus})"
        );
    }

    #[test]
    fn test_diversity_bonus_similar_body_lower() {
        let proposal = precondition("x != 0", 0.8);
        let existing = vec![precondition("x != 0", 0.9)]; // identical body

        let bonus = diversity_bonus(&proposal, &existing);
        let unique_proposal = precondition("completely_different_spec", 0.8);
        let unique_bonus = diversity_bonus(&unique_proposal, &existing);

        assert!(
            unique_bonus >= bonus,
            "unique body ({unique_bonus}) should get >= bonus vs similar ({bonus})"
        );
    }

    // --- dedup_proposals ---

    #[test]
    fn test_dedup_removes_exact_duplicates() {
        let proposals = vec![
            ScoredProposal {
                proposal: precondition("x != 0", 0.9),
                confidence: 0.9,
                source: ProposalSource::Heuristic,
                rank: 1,
            },
            ScoredProposal {
                proposal: precondition("x != 0", 0.7),
                confidence: 0.7,
                source: ProposalSource::Llm,
                rank: 2,
            },
        ];

        let result = dedup_proposals(proposals);
        assert_eq!(result.len(), 1);
        // Should keep the higher-confidence one
        assert!((result[0].confidence - 0.9).abs() < 1e-10);
    }

    #[test]
    fn test_dedup_keeps_different_kinds() {
        let proposals = vec![
            ScoredProposal {
                proposal: precondition("x != 0", 0.9),
                confidence: 0.9,
                source: ProposalSource::Heuristic,
                rank: 1,
            },
            ScoredProposal {
                proposal: postcondition("x != 0", 0.7),
                confidence: 0.7,
                source: ProposalSource::Heuristic,
                rank: 2,
            },
        ];

        let result = dedup_proposals(proposals);
        assert_eq!(result.len(), 2, "different kinds should not be deduped");
    }

    #[test]
    fn test_dedup_keeps_different_bodies() {
        let proposals = vec![
            ScoredProposal {
                proposal: precondition("x != 0", 0.9),
                confidence: 0.9,
                source: ProposalSource::Heuristic,
                rank: 1,
            },
            ScoredProposal {
                proposal: precondition("y > 0", 0.7),
                confidence: 0.7,
                source: ProposalSource::Heuristic,
                rank: 2,
            },
        ];

        let result = dedup_proposals(proposals);
        assert_eq!(result.len(), 2, "different bodies should not be deduped");
    }

    #[test]
    fn test_dedup_empty() {
        let result = dedup_proposals(Vec::new());
        assert!(result.is_empty());
    }

    // --- has_significant_overlap ---

    #[test]
    fn test_overlap_identical() {
        assert!(has_significant_overlap("x != 0", "x != 0"));
    }

    #[test]
    fn test_overlap_substring() {
        assert!(has_significant_overlap("x != 0 && y > 0", "x != 0"));
    }

    #[test]
    fn test_overlap_no_match() {
        assert!(!has_significant_overlap("x != 0", "completely different"));
    }

    #[test]
    fn test_overlap_empty() {
        assert!(!has_significant_overlap("", ""));
    }

    // --- Integration ---

    #[test]
    fn test_end_to_end_ensemble_flow() {
        let generator = EnsembleGenerator::default();
        let mut by_source = FxHashMap::default();

        // Heuristic proposals
        by_source.insert(
            ProposalSource::Heuristic,
            vec![precondition("x != 0", 0.9), precondition("y > 0", 0.7)],
        );

        // WP proposals (one overlaps with heuristic)
        by_source.insert(
            ProposalSource::WeakestPrecondition,
            vec![precondition("x != 0", 0.85), postcondition("result >= 0", 0.8)],
        );

        // LLM proposals
        by_source.insert(ProposalSource::Llm, vec![precondition("x >= 0 && y >= 0", 0.6)]);

        let result = generator.generate_result(&by_source);

        // Should have proposals from all sources
        assert!(!result.proposals.is_empty());

        // Ranks should be sequential
        for (i, sp) in result.proposals.iter().enumerate() {
            assert_eq!(sp.rank, i + 1);
        }

        // Per-source counts should be correct
        assert_eq!(result.per_source_counts[&ProposalSource::Heuristic], 2);
        assert_eq!(result.per_source_counts[&ProposalSource::WeakestPrecondition], 2);
        assert_eq!(result.per_source_counts[&ProposalSource::Llm], 1);

        // Consensus proposal "x != 0" should rank high
        let x_ne_0 = result.proposals.iter().find(|sp| {
            matches!(
                &sp.proposal.kind,
                ProposalKind::AddPrecondition { spec_body } if spec_body == "x != 0"
            )
        });
        assert!(x_ne_0.is_some(), "consensus proposal should be present");
    }
}
