// trust-strengthen/strategy.rs: Strategy selection for spec strengthening
//
// Based on verification history, selects the most promising strengthening
// strategy for the next iteration. Uses UCB1 (Upper Confidence Bound) for
// exploration/exploitation balance across different proposal sources.
//
// Part of #154
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use crate::confidence::ProposalSource;

/// A strengthening strategy that can be selected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Strategy {
    /// Use heuristic pattern matching to generate specs.
    Heuristic,
    /// Use weakest precondition calculus.
    WeakestPrecondition,
    /// Use LLM inference.
    Llm,
    /// Use counterexample-guided refinement.
    CounterexampleGuided,
    /// Use template matching from the pattern library.
    TemplateBased,
    /// Use an ensemble of multiple strategies.
    Ensemble,
}

impl Strategy {
    /// All available strategies (excluding Ensemble, which is a meta-strategy).
    pub const ALL_BASE: &'static [Strategy] = &[
        Strategy::Heuristic,
        Strategy::WeakestPrecondition,
        Strategy::Llm,
        Strategy::CounterexampleGuided,
        Strategy::TemplateBased,
    ];

    /// Convert to the corresponding ProposalSource, if applicable.
    #[must_use]
    pub fn to_proposal_source(self) -> Option<ProposalSource> {
        match self {
            Self::Heuristic => Some(ProposalSource::Heuristic),
            Self::WeakestPrecondition => Some(ProposalSource::WeakestPrecondition),
            Self::Llm => Some(ProposalSource::Llm),
            Self::CounterexampleGuided => Some(ProposalSource::CounterexampleGuided),
            Self::TemplateBased => Some(ProposalSource::SignatureBased),
            Self::Ensemble => None,
        }
    }
}

/// Record of a strategy's performance in past iterations.
#[derive(Debug, Clone)]
pub struct StrategyRecord {
    /// Number of times this strategy has been selected.
    pub times_selected: usize,
    /// Number of times this strategy produced a successful proposal.
    pub successes: usize,
    /// Total reward accumulated (can be fractional for partial successes).
    pub total_reward: f64,
    /// Most recent reward received.
    pub last_reward: f64,
}

impl Default for StrategyRecord {
    fn default() -> Self {
        Self { times_selected: 0, successes: 0, total_reward: 0.0, last_reward: 0.0 }
    }
}

impl StrategyRecord {
    /// Average reward across all selections.
    #[must_use]
    pub fn average_reward(&self) -> f64 {
        if self.times_selected == 0 {
            return 0.0;
        }
        self.total_reward / self.times_selected as f64
    }

    /// Success rate (successes / selections).
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.times_selected == 0 {
            return 0.0;
        }
        self.successes as f64 / self.times_selected as f64
    }
}

/// Strategy selector using UCB1 (Upper Confidence Bound) for exploration/exploitation.
///
/// UCB1 balances:
/// - **Exploitation**: choosing strategies that have performed well historically
/// - **Exploration**: trying strategies that have been selected fewer times
///
/// The UCB1 score for strategy i is:
///   UCB1(i) = mean_reward(i) + C * sqrt(ln(N) / n_i)
///
/// where N is total selections, n_i is selections of strategy i, and C is
/// the exploration constant.
pub struct StrategySelector {
    /// Performance records for each strategy.
    records: BTreeMap<Strategy, StrategyRecord>,
    /// Total number of strategy selections across all strategies.
    total_selections: usize,
    /// Exploration constant (higher = more exploration).
    exploration_constant: f64,
}

impl StrategySelector {
    /// Create a new strategy selector with default exploration constant.
    #[must_use]
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
            total_selections: 0,
            exploration_constant: 1.41, // sqrt(2), standard UCB1 constant
        }
    }

    /// Create a strategy selector with a custom exploration constant.
    #[must_use]
    pub fn with_exploration(exploration_constant: f64) -> Self {
        Self { records: BTreeMap::new(), total_selections: 0, exploration_constant }
    }

    /// Select the best strategy using UCB1.
    ///
    /// If any strategy has never been tried, it is selected first (exploration).
    /// Otherwise, the strategy with the highest UCB1 score is selected.
    #[must_use]
    pub fn select(&self) -> Strategy {
        // First, try any strategy that hasn't been selected yet
        for strategy in Strategy::ALL_BASE {
            if !self.records.contains_key(strategy) || self.records[strategy].times_selected == 0 {
                return *strategy;
            }
        }

        // UCB1 selection
        let mut best_strategy = Strategy::Heuristic;
        let mut best_ucb = f64::NEG_INFINITY;

        for strategy in Strategy::ALL_BASE {
            let ucb = self.ucb1_score(*strategy);
            if ucb > best_ucb {
                best_ucb = ucb;
                best_strategy = *strategy;
            }
        }

        best_strategy
    }

    /// Select the top-k strategies by UCB1 score.
    #[must_use]
    pub fn select_top_k(&self, k: usize) -> Vec<Strategy> {
        let mut scored: Vec<(Strategy, f64)> =
            Strategy::ALL_BASE.iter().map(|s| (*s, self.ucb1_score(*s))).collect();
        scored.sort_by(|a, b| {
            b.1.partial_cmp(&a.1)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| strategy_sort_key(a.0).cmp(&strategy_sort_key(b.0)))
        });
        scored.into_iter().take(k).map(|(s, _)| s).collect()
    }

    /// Compute the UCB1 score for a strategy.
    #[must_use]
    pub fn ucb1_score(&self, strategy: Strategy) -> f64 {
        let record = match self.records.get(&strategy) {
            Some(r) if r.times_selected > 0 => r,
            _ => return f64::INFINITY, // Untried strategies get infinite UCB
        };

        let mean_reward = record.average_reward();
        let exploration_term = if self.total_selections > 0 {
            self.exploration_constant
                * ((self.total_selections as f64).ln() / record.times_selected as f64).sqrt()
        } else {
            0.0
        };

        mean_reward + exploration_term
    }

    /// Record the outcome of using a strategy.
    ///
    /// `reward` should be in [0.0, 1.0] where 1.0 = full success.
    pub fn record_outcome(&mut self, strategy: Strategy, reward: f64, success: bool) {
        let record = self.records.entry(strategy).or_default();
        record.times_selected += 1;
        record.total_reward += reward;
        record.last_reward = reward;
        if success {
            record.successes += 1;
        }
        self.total_selections += 1;
    }

    /// Get the performance record for a strategy.
    #[must_use]
    pub fn record_for(&self, strategy: Strategy) -> Option<&StrategyRecord> {
        self.records.get(&strategy)
    }

    /// Get the total number of strategy selections.
    #[must_use]
    pub fn total_selections(&self) -> usize {
        self.total_selections
    }

    /// Get all strategy records.
    #[must_use]
    pub fn all_records(&self) -> &BTreeMap<Strategy, StrategyRecord> {
        &self.records
    }

    /// Get a summary of strategy performance, sorted by success rate.
    #[must_use]
    pub fn performance_summary(&self) -> Vec<StrategySummary> {
        let mut summaries: Vec<StrategySummary> = self
            .records
            .iter()
            .map(|(strategy, record)| StrategySummary {
                strategy: *strategy,
                times_selected: record.times_selected,
                successes: record.successes,
                success_rate: record.success_rate(),
                average_reward: record.average_reward(),
                ucb1_score: self.ucb1_score(*strategy),
            })
            .collect();
        summaries.sort_by(|a, b| {
            b.success_rate
                .partial_cmp(&a.success_rate)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| strategy_sort_key(a.strategy).cmp(&strategy_sort_key(b.strategy)))
        });
        summaries
    }

    /// Reset all records (e.g., when the problem domain changes).
    pub fn reset(&mut self) {
        self.records.clear();
        self.total_selections = 0;
    }

    /// Decay old rewards to give more weight to recent performance.
    ///
    /// Multiplies all total_reward values by `decay_factor` (typically 0.9-0.99).
    pub fn decay_rewards(&mut self, decay_factor: f64) {
        let mut strategies: Vec<_> = self.records.keys().copied().collect();
        strategies.sort_by_key(|strategy| strategy_sort_key(*strategy));
        for strategy in strategies {
            if let Some(record) = self.records.get_mut(&strategy) {
                record.total_reward *= decay_factor;
            }
        }
    }
}

impl Default for StrategySelector {
    fn default() -> Self {
        Self::new()
    }
}

/// Summary of a strategy's performance.
#[derive(Debug, Clone)]
pub struct StrategySummary {
    /// The strategy.
    pub strategy: Strategy,
    /// How many times it was selected.
    pub times_selected: usize,
    /// How many times it succeeded.
    pub successes: usize,
    /// Success rate (successes / selections).
    pub success_rate: f64,
    /// Average reward per selection.
    pub average_reward: f64,
    /// Current UCB1 score.
    pub ucb1_score: f64,
}

fn strategy_sort_key(strategy: Strategy) -> u8 {
    match strategy {
        Strategy::Heuristic => 0,
        Strategy::WeakestPrecondition => 1,
        Strategy::Llm => 2,
        Strategy::CounterexampleGuided => 3,
        Strategy::TemplateBased => 4,
        Strategy::Ensemble => 5,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    // --- Strategy ---

    #[test]
    fn test_strategy_all_base_count() {
        assert_eq!(Strategy::ALL_BASE.len(), 5);
    }

    #[test]
    fn test_strategy_to_proposal_source() {
        assert_eq!(Strategy::Heuristic.to_proposal_source(), Some(ProposalSource::Heuristic));
        assert_eq!(
            Strategy::WeakestPrecondition.to_proposal_source(),
            Some(ProposalSource::WeakestPrecondition)
        );
        assert_eq!(Strategy::Llm.to_proposal_source(), Some(ProposalSource::Llm));
        assert_eq!(
            Strategy::CounterexampleGuided.to_proposal_source(),
            Some(ProposalSource::CounterexampleGuided)
        );
        assert_eq!(
            Strategy::TemplateBased.to_proposal_source(),
            Some(ProposalSource::SignatureBased)
        );
        assert!(Strategy::Ensemble.to_proposal_source().is_none());
    }

    // --- StrategyRecord ---

    #[test]
    fn test_strategy_record_default() {
        let record = StrategyRecord::default();
        assert_eq!(record.times_selected, 0);
        assert_eq!(record.successes, 0);
        assert!(record.total_reward.abs() < f64::EPSILON);
    }

    #[test]
    fn test_strategy_record_average_reward() {
        let record =
            StrategyRecord { times_selected: 4, successes: 3, total_reward: 3.2, last_reward: 0.8 };
        assert!((record.average_reward() - 0.8).abs() < 1e-10);
    }

    #[test]
    fn test_strategy_record_average_reward_zero_selections() {
        let record = StrategyRecord::default();
        assert!(record.average_reward().abs() < f64::EPSILON);
    }

    #[test]
    fn test_strategy_record_success_rate() {
        let record = StrategyRecord {
            times_selected: 10,
            successes: 7,
            total_reward: 7.0,
            last_reward: 1.0,
        };
        assert!((record.success_rate() - 0.7).abs() < 1e-10);
    }

    #[test]
    fn test_strategy_record_success_rate_zero() {
        let record = StrategyRecord::default();
        assert!(record.success_rate().abs() < f64::EPSILON);
    }

    // --- StrategySelector ---

    #[test]
    fn test_selector_new_defaults() {
        let selector = StrategySelector::new();
        assert_eq!(selector.total_selections(), 0);
        assert!(selector.all_records().is_empty());
    }

    #[test]
    fn test_selector_select_untried_first() {
        let selector = StrategySelector::new();
        // With no history, should select the first untried strategy
        let selected = selector.select();
        assert!(Strategy::ALL_BASE.contains(&selected));
    }

    #[test]
    fn test_selector_select_explores_all() {
        let mut selector = StrategySelector::new();
        let mut seen = BTreeSet::new();

        // First 5 selections should try each strategy once
        for _ in 0..5 {
            let selected = selector.select();
            seen.insert(selected);
            selector.record_outcome(selected, 0.5, true);
        }

        assert_eq!(seen.len(), 5, "should explore all 5 base strategies first");
    }

    #[test]
    fn test_selector_select_exploits_after_exploration() {
        let mut selector = StrategySelector::new();

        // Give each strategy many tries with low reward to build a solid baseline
        for strategy in Strategy::ALL_BASE {
            for _ in 0..10 {
                selector.record_outcome(*strategy, 0.1, false);
            }
        }

        // Give Heuristic a much higher reward many times to dominate
        for _ in 0..50 {
            selector.record_outcome(Strategy::Heuristic, 1.0, true);
        }

        // Heuristic should have a much higher average reward
        let heuristic_record = selector.record_for(Strategy::Heuristic).unwrap();
        let llm_record = selector.record_for(Strategy::Llm).unwrap();
        assert!(
            heuristic_record.average_reward() > llm_record.average_reward(),
            "Heuristic avg reward ({}) should beat Llm avg reward ({})",
            heuristic_record.average_reward(),
            llm_record.average_reward()
        );

        // With enough data, UCB should favor Heuristic over Llm
        let heuristic_ucb = selector.ucb1_score(Strategy::Heuristic);
        let llm_ucb = selector.ucb1_score(Strategy::Llm);
        assert!(
            heuristic_ucb > llm_ucb,
            "Heuristic UCB ({heuristic_ucb}) should be higher than Llm UCB ({llm_ucb})"
        );

        // Selected strategy should be Heuristic
        let selected = selector.select();
        assert_eq!(selected, Strategy::Heuristic);
    }

    #[test]
    fn test_selector_ucb1_untried_is_infinity() {
        let selector = StrategySelector::new();
        let score = selector.ucb1_score(Strategy::Heuristic);
        assert!(score.is_infinite());
    }

    #[test]
    fn test_selector_ucb1_after_one_try() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 0.8, true);
        let score = selector.ucb1_score(Strategy::Heuristic);
        // With N=1, n_i=1: mean + C*sqrt(ln(1)/1) = 0.8 + C*0 = 0.8
        assert!((score - 0.8).abs() < 1e-10);
    }

    #[test]
    fn test_selector_ucb1_exploration_term_increases() {
        let mut selector = StrategySelector::new();

        // Try Heuristic once, record many others
        selector.record_outcome(Strategy::Heuristic, 0.5, true);
        for _ in 0..20 {
            selector.record_outcome(Strategy::Llm, 0.5, true);
        }

        // Heuristic's UCB should have a large exploration term since it was tried only once
        let heuristic_ucb = selector.ucb1_score(Strategy::Heuristic);
        // Mean is 0.5, exploration term should be significant
        assert!(
            heuristic_ucb > 0.5,
            "UCB with exploration should exceed mean reward: {heuristic_ucb}"
        );
    }

    #[test]
    fn test_selector_record_outcome_updates() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 0.8, true);
        selector.record_outcome(Strategy::Heuristic, 0.4, false);

        let record = selector.record_for(Strategy::Heuristic).unwrap();
        assert_eq!(record.times_selected, 2);
        assert_eq!(record.successes, 1);
        assert!((record.total_reward - 1.2).abs() < 1e-10);
        assert!((record.last_reward - 0.4).abs() < 1e-10);
    }

    #[test]
    fn test_selector_select_top_k() {
        let mut selector = StrategySelector::new();

        // Give varied rewards
        for _ in 0..5 {
            selector.record_outcome(Strategy::Heuristic, 0.9, true);
        }
        for _ in 0..5 {
            selector.record_outcome(Strategy::WeakestPrecondition, 0.7, true);
        }
        for _ in 0..5 {
            selector.record_outcome(Strategy::Llm, 0.3, false);
        }
        for _ in 0..5 {
            selector.record_outcome(Strategy::CounterexampleGuided, 0.5, true);
        }
        for _ in 0..5 {
            selector.record_outcome(Strategy::TemplateBased, 0.4, false);
        }

        let top2 = selector.select_top_k(2);
        assert_eq!(top2.len(), 2);
        // Top 2 should include Heuristic (best reward)
        assert!(top2.contains(&Strategy::Heuristic));
    }

    #[test]
    fn test_selector_select_top_k_with_untried() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 0.9, true);

        // With 4 untried strategies, top 3 should include some untried ones
        let top3 = selector.select_top_k(3);
        assert_eq!(top3.len(), 3);
    }

    #[test]
    fn test_selector_performance_summary() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 0.9, true);
        selector.record_outcome(Strategy::Heuristic, 0.8, true);
        selector.record_outcome(Strategy::Llm, 0.3, false);

        let summary = selector.performance_summary();
        assert_eq!(summary.len(), 2);
        // Sorted by success rate descending
        assert_eq!(summary[0].strategy, Strategy::Heuristic);
        assert!((summary[0].success_rate - 1.0).abs() < 1e-10);
        assert_eq!(summary[1].strategy, Strategy::Llm);
        assert!(summary[1].success_rate.abs() < 1e-10);
    }

    #[test]
    fn test_selector_performance_summary_empty() {
        let selector = StrategySelector::new();
        let summary = selector.performance_summary();
        assert!(summary.is_empty());
    }

    #[test]
    fn test_selector_reset() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 0.9, true);
        selector.record_outcome(Strategy::Llm, 0.3, false);
        assert_eq!(selector.total_selections(), 2);

        selector.reset();
        assert_eq!(selector.total_selections(), 0);
        assert!(selector.all_records().is_empty());
    }

    #[test]
    fn test_selector_decay_rewards() {
        let mut selector = StrategySelector::new();
        selector.record_outcome(Strategy::Heuristic, 1.0, true);
        selector.record_outcome(Strategy::Heuristic, 1.0, true);

        let before = selector.record_for(Strategy::Heuristic).unwrap().total_reward;
        selector.decay_rewards(0.5);
        let after = selector.record_for(Strategy::Heuristic).unwrap().total_reward;

        assert!((after - before * 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_selector_with_custom_exploration() {
        let selector = StrategySelector::with_exploration(2.0);
        assert!((selector.exploration_constant - 2.0).abs() < f64::EPSILON);
    }

    // --- Integration ---

    #[test]
    fn test_strategy_selection_full_cycle() {
        let mut selector = StrategySelector::new();

        // Simulate 20 iterations
        for iteration in 0..20 {
            let strategy = selector.select();

            // Simulate reward: Heuristic is best, WP is decent, others are poor
            let reward = match strategy {
                Strategy::Heuristic => 0.8 + (iteration as f64 * 0.01).min(0.15),
                Strategy::WeakestPrecondition => 0.6,
                Strategy::Llm => 0.3,
                Strategy::CounterexampleGuided => 0.4,
                Strategy::TemplateBased => 0.35,
                Strategy::Ensemble => 0.5,
            };
            let success = reward > 0.5;
            selector.record_outcome(strategy, reward, success);
        }

        // After 20 iterations, Heuristic should be the clear winner
        let summary = selector.performance_summary();
        assert!(!summary.is_empty());

        // The selector should strongly prefer Heuristic
        let selected = selector.select();
        let heuristic_ucb = selector.ucb1_score(Strategy::Heuristic);
        let llm_ucb = selector.ucb1_score(Strategy::Llm);
        assert!(
            heuristic_ucb > llm_ucb,
            "after 20 iterations, Heuristic ({heuristic_ucb}) should dominate Llm ({llm_ucb})"
        );

        // Most selections should have been Heuristic (exploitation)
        let heuristic_record = selector.record_for(Strategy::Heuristic);
        assert!(heuristic_record.is_some(), "Heuristic should have been selected at least once");
        // Verify the selected strategy is reasonable
        assert!(
            selected == Strategy::Heuristic || selected == Strategy::WeakestPrecondition,
            "should select one of the top strategies, got {:?}",
            selected
        );
    }
}
