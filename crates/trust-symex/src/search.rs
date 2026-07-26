// trust-symex search strategies
//
// Provides multiple path exploration strategies for symbolic execution:
// DFS, BFS, coverage-guided, random path selection, and heuristic-based.
// Inspired by KLEE's search strategies (refs/klee/).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, VecDeque};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::engine::ExecutionFork;
use crate::path::PathConstraint;

/// Strategy for choosing which execution fork to explore next.
pub trait SearchStrategy {
    /// Given a set of available forks, choose the next one to explore.
    ///
    /// Returns `None` when the strategy has no more paths to offer.
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork>;

    /// Notify the strategy that a block was covered (for coverage-guided strategies).
    fn notify_coverage(&mut self, _block_id: usize) {}
}

/// Trait for reordering a slice of symbolic paths by priority.
///
/// Implementations define a policy for which paths should be explored first,
/// allowing pluggable prioritization without changing the search loop.
pub trait PathPrioritizer {
    /// Reorder `paths` in place so that higher-priority paths come first.
    fn prioritize(&self, paths: &mut [SymbolicPath]);
}

/// A symbolic execution path: a path constraint paired with metadata
/// used for prioritization and search decisions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolicPath {
    /// The accumulated path constraints.
    pub constraints: PathConstraint,
    /// The next block to explore along this path.
    pub next_block: usize,
    /// Path depth (number of branch decisions so far).
    pub depth: usize,
    /// Number of unique blocks covered on this path.
    pub coverage_count: usize,
}

/// Which search strategy to use for path exploration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SearchStrategyKind {
    /// Depth-first: always explore the most recently discovered fork.
    DepthFirst,
    /// Breadth-first: explore forks in FIFO order.
    BreadthFirst,
    /// Prioritize forks targeting uncovered blocks.
    CoverageGuided,
    /// Select forks uniformly at random (deterministic with seed).
    RandomPath,
    /// Heuristic-based: use a scoring function combining multiple signals.
    Heuristic,
}

/// Configuration for search-based exploration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchConfig {
    /// Maximum depth (branch decisions) any single path may reach.
    pub max_depth: usize,
    /// Maximum number of paths to explore before stopping.
    pub max_paths: usize,
    /// Maximum wall-clock time for the search.
    pub timeout: Duration,
    /// Which search strategy to apply.
    pub strategy: SearchStrategyKind,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_depth: 256,
            max_paths: 4096,
            timeout: Duration::from_secs(60),
            strategy: SearchStrategyKind::CoverageGuided,
        }
    }
}

// ---------------------------------------------------------------------------
// Strategy implementations
// ---------------------------------------------------------------------------

/// Depth-first search: always explore the most recently discovered fork.
#[derive(Debug, Default)]
pub struct DfsStrategy {
    stack: Vec<ExecutionFork>,
}

impl DfsStrategy {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl SearchStrategy for DfsStrategy {
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork> {
        self.stack.extend(forks);
        self.stack.pop()
    }
}

/// Breadth-first search: explore forks in FIFO order.
#[derive(Debug, Default)]
pub struct BfsStrategy {
    queue: VecDeque<ExecutionFork>,
}

impl BfsStrategy {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl SearchStrategy for BfsStrategy {
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork> {
        self.queue.extend(forks);
        self.queue.pop_front()
    }
}

/// Coverage-guided search: prioritize forks targeting uncovered blocks.
///
/// Falls back to DFS for blocks that have already been covered.
#[derive(Debug, Default)]
pub struct CoverageGuidedStrategy {
    /// Blocks that have been covered so far.
    covered: BTreeSet<usize>,
    /// Forks targeting uncovered blocks (priority queue).
    uncovered_forks: VecDeque<ExecutionFork>,
    /// Forks targeting already-covered blocks (fallback).
    fallback: Vec<ExecutionFork>,
}

impl CoverageGuidedStrategy {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of covered blocks.
    #[must_use]
    pub fn covered_count(&self) -> usize {
        self.covered.len()
    }
}

impl SearchStrategy for CoverageGuidedStrategy {
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork> {
        for fork in forks {
            if !self.covered.contains(&fork.next_block) {
                self.uncovered_forks.push_back(fork);
            } else {
                self.fallback.push(fork);
            }
        }
        self.uncovered_forks.pop_front().or_else(|| self.fallback.pop())
    }

    fn notify_coverage(&mut self, block_id: usize) {
        self.covered.insert(block_id);
    }
}

/// Random path selection using a deterministic PRNG seeded at construction.
///
/// At each step, selects uniformly among available forks. Useful for
/// avoiding systematic bias that DFS/BFS can introduce.
#[derive(Debug)]
pub struct RandomPathStrategy {
    pool: Vec<ExecutionFork>,
    /// Simple xorshift64 state for deterministic randomness.
    rng_state: u64,
}

impl RandomPathStrategy {
    /// Create a new random path strategy with the given seed.
    #[must_use]
    pub fn new(seed: u64) -> Self {
        // Avoid zero seed (xorshift degenerate case).
        let rng_state = if seed == 0 { 1 } else { seed };
        Self { pool: Vec::new(), rng_state }
    }

    /// xorshift64 step.
    fn next_rand(&mut self) -> u64 {
        let mut s = self.rng_state;
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        self.rng_state = s;
        s
    }
}

impl SearchStrategy for RandomPathStrategy {
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork> {
        self.pool.extend(forks);
        if self.pool.is_empty() {
            return None;
        }
        let idx = (self.next_rand() as usize) % self.pool.len();
        Some(self.pool.swap_remove(idx))
    }
}

/// Heuristic search: scores each fork and picks the highest-scoring one.
///
/// Scoring combines: (a) preference for uncovered blocks,
/// (b) penalty for deep paths, (c) path constraint simplicity.
#[derive(Debug, Default)]
pub struct HeuristicStrategy {
    covered: BTreeSet<usize>,
    pool: Vec<ExecutionFork>,
}

impl HeuristicStrategy {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Score a fork: higher is better.
    fn score(&self, fork: &ExecutionFork) -> i64 {
        let mut s: i64 = 0;
        // Strongly prefer uncovered blocks.
        if !self.covered.contains(&fork.next_block) {
            s += 1000;
        }
        // Penalise deep paths to encourage breadth.
        s -= fork.path.depth() as i64;
        s
    }
}

impl SearchStrategy for HeuristicStrategy {
    fn next(&mut self, forks: Vec<ExecutionFork>) -> Option<ExecutionFork> {
        self.pool.extend(forks);
        if self.pool.is_empty() {
            return None;
        }
        // Find the best-scoring fork.
        let best_idx = self
            .pool
            .iter()
            .enumerate()
            .max_by_key(|(_, f)| self.score(f))
            .map(|(i, _)| i)
            // SAFETY: We checked pool.is_empty() above and returned None.
            .unwrap_or_else(|| unreachable!("pool empty after non-empty check"));
        Some(self.pool.swap_remove(best_idx))
    }

    fn notify_coverage(&mut self, block_id: usize) {
        self.covered.insert(block_id);
    }
}

// ---------------------------------------------------------------------------
// PathPrioritizer implementations
// ---------------------------------------------------------------------------

/// Construct the appropriate `SearchStrategy` from a `SearchStrategyKind`.
#[must_use]
pub fn make_strategy(kind: SearchStrategyKind) -> Box<dyn SearchStrategy> {
    match kind {
        SearchStrategyKind::DepthFirst => Box::new(DfsStrategy::new()),
        SearchStrategyKind::BreadthFirst => Box::new(BfsStrategy::new()),
        SearchStrategyKind::CoverageGuided => Box::new(CoverageGuidedStrategy::new()),
        SearchStrategyKind::RandomPath => Box::new(RandomPathStrategy::new(42)),
        SearchStrategyKind::Heuristic => Box::new(HeuristicStrategy::new()),
    }
}

#[cfg(test)]
mod tests {
    use crate::path::PathConstraint;
    use crate::state::SymbolicState;

    use super::*;

    fn make_fork(next_block: usize) -> ExecutionFork {
        ExecutionFork { state: SymbolicState::new(), path: PathConstraint::new(), next_block }
    }

    fn make_fork_with_depth(next_block: usize, depth: usize) -> ExecutionFork {
        let mut path = PathConstraint::new();
        for _ in 0..depth {
            path.add_constraint(crate::state::SymbolicValue::Concrete(1), true);
        }
        ExecutionFork { state: SymbolicState::new(), path, next_block }
    }

    // --- DFS ---

    #[test]
    fn test_search_dfs_order() {
        let mut dfs = DfsStrategy::new();
        let forks = vec![make_fork(1), make_fork(2), make_fork(3)];
        let first = dfs.next(forks).expect("should have a fork");
        assert_eq!(first.next_block, 3);
        let second = dfs.next(vec![]).expect("should have a fork");
        assert_eq!(second.next_block, 2);
        let third = dfs.next(vec![]).expect("should have a fork");
        assert_eq!(third.next_block, 1);
        assert!(dfs.next(vec![]).is_none());
    }

    // --- BFS ---

    #[test]
    fn test_search_bfs_order() {
        let mut bfs = BfsStrategy::new();
        let forks = vec![make_fork(1), make_fork(2), make_fork(3)];
        let first = bfs.next(forks).expect("should have a fork");
        assert_eq!(first.next_block, 1);
        let second = bfs.next(vec![]).expect("should have a fork");
        assert_eq!(second.next_block, 2);
        let third = bfs.next(vec![]).expect("should have a fork");
        assert_eq!(third.next_block, 3);
        assert!(bfs.next(vec![]).is_none());
    }

    // --- Coverage-guided ---

    #[test]
    fn test_search_coverage_guided_prefers_uncovered() {
        let mut cg = CoverageGuidedStrategy::new();
        cg.notify_coverage(1);

        let forks = vec![make_fork(1), make_fork(2), make_fork(3)];
        let first = cg.next(forks).expect("should have a fork");
        assert!(first.next_block == 2 || first.next_block == 3);
    }

    #[test]
    fn test_search_coverage_guided_falls_back() {
        let mut cg = CoverageGuidedStrategy::new();
        cg.notify_coverage(1);
        cg.notify_coverage(2);

        let forks = vec![make_fork(1), make_fork(2)];
        let result = cg.next(forks).expect("should fall back");
        assert!(result.next_block == 1 || result.next_block == 2);
    }

    #[test]
    fn test_search_coverage_guided_empty() {
        let mut cg = CoverageGuidedStrategy::new();
        assert!(cg.next(vec![]).is_none());
    }

    // --- Random path ---

    #[test]
    fn test_search_random_path_returns_all() {
        let mut rp = RandomPathStrategy::new(12345);
        let forks = vec![make_fork(1), make_fork(2), make_fork(3)];
        rp.next(forks); // drain one
        let second = rp.next(vec![]).expect("should have a fork");
        let third = rp.next(vec![]).expect("should have a fork");
        // All should eventually be returned.
        assert!(second.next_block != third.next_block);
        assert!(rp.next(vec![]).is_none());
    }

    #[test]
    fn test_search_random_path_deterministic() {
        // Same seed produces same selection order.
        let mut rp1 = RandomPathStrategy::new(42);
        let mut rp2 = RandomPathStrategy::new(42);
        let forks1 = vec![make_fork(10), make_fork(20), make_fork(30)];
        let forks2 = vec![make_fork(10), make_fork(20), make_fork(30)];
        let a = rp1.next(forks1).expect("fork");
        let b = rp2.next(forks2).expect("fork");
        assert_eq!(a.next_block, b.next_block);
    }

    #[test]
    fn test_search_random_path_empty() {
        let mut rp = RandomPathStrategy::new(1);
        assert!(rp.next(vec![]).is_none());
    }

    // --- Heuristic ---

    #[test]
    fn test_search_heuristic_prefers_uncovered() {
        let mut h = HeuristicStrategy::new();
        h.notify_coverage(1);
        let forks = vec![make_fork(1), make_fork(2)];
        let first = h.next(forks).expect("should pick uncovered");
        assert_eq!(first.next_block, 2);
    }

    #[test]
    fn test_search_heuristic_penalises_depth() {
        let mut h = HeuristicStrategy::new();
        // Both uncovered but different depths.
        let forks = vec![make_fork_with_depth(1, 10), make_fork_with_depth(2, 1)];
        let first = h.next(forks).expect("should pick shallower");
        assert_eq!(first.next_block, 2);
    }

    #[test]
    fn test_search_heuristic_empty() {
        let mut h = HeuristicStrategy::new();
        assert!(h.next(vec![]).is_none());
    }

    // --- SearchConfig ---

    #[test]
    fn test_search_config_default() {
        let cfg = SearchConfig::default();
        assert_eq!(cfg.max_depth, 256);
        assert_eq!(cfg.max_paths, 4096);
        assert_eq!(cfg.timeout, Duration::from_secs(60));
        assert_eq!(cfg.strategy, SearchStrategyKind::CoverageGuided);
    }

    // --- make_strategy factory ---

    #[test]
    fn test_search_make_strategy_all_kinds() {
        // Just verifies that all kinds produce a usable strategy.
        for kind in [
            SearchStrategyKind::DepthFirst,
            SearchStrategyKind::BreadthFirst,
            SearchStrategyKind::CoverageGuided,
            SearchStrategyKind::RandomPath,
            SearchStrategyKind::Heuristic,
        ] {
            let mut s = make_strategy(kind);
            assert!(s.next(vec![]).is_none());
        }
    }
}
