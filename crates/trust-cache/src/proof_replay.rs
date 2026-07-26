// trust-cache/proof_replay.rs: Proof replay cache
//
// Stores and reuses proof strategies for VCs with similar structure.
// When a VC is proved, the strategy (solver, hints, timeout) is cached.
// Future VCs with similar structure can try the same strategy first.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Proof strategy
// ---------------------------------------------------------------------------

/// A proof strategy that successfully proved a VC.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofStrategy {
    /// Solver name that worked.
    pub solver: String,
    /// Timeout used (ms).
    pub timeout_ms: u64,
    /// Solver-specific hints (e.g., tactic names, quantifier instantiation strategies).
    pub hints: Vec<String>,
}

impl ProofStrategy {
    pub fn new(solver: impl Into<String>, timeout_ms: u64) -> Self {
        Self { solver: solver.into(), timeout_ms, hints: Vec::new() }
    }

    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hints.push(hint.into());
        self
    }
}

// ---------------------------------------------------------------------------
// Strategy key
// ---------------------------------------------------------------------------

/// Structural fingerprint of a VC for cache matching.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StrategyKey {
    /// VC kind name.
    pub kind: String,
    /// Formula structure hash (depth, node count, operator mix).
    pub structure_hash: u64,
    /// Number of variables.
    pub var_count: usize,
    /// Nesting depth of the formula.
    pub depth: usize,
}

impl StrategyKey {
    pub fn new(
        kind: impl Into<String>,
        structure_hash: u64,
        var_count: usize,
        depth: usize,
    ) -> Self {
        Self { kind: kind.into(), structure_hash, var_count, depth }
    }
}

// ---------------------------------------------------------------------------
// Replay result
// ---------------------------------------------------------------------------

/// Result of attempting to replay a cached strategy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplayResult {
    /// Exact match found — high confidence of success.
    ExactMatch(ProofStrategy),
    /// Structural match — worth trying but may not work.
    PartialMatch(ProofStrategy),
    /// No match found.
    Miss,
}

// ---------------------------------------------------------------------------
// Replay cache
// ---------------------------------------------------------------------------

/// Cache mapping VC structural keys to successful proof strategies.
pub struct ReplayCache {
    /// Exact match cache: key -> strategy.
    exact: FxHashMap<StrategyKey, CacheEntry>,
    /// Partial match: kind -> strategies (for fallback).
    by_kind: FxHashMap<String, Vec<CacheEntry>>,
    /// Statistics.
    stats: ReplayCacheStats,
}

#[derive(Debug, Clone)]
struct CacheEntry {
    strategy: ProofStrategy,
    successes: u32,
    attempts: u32,
}

impl CacheEntry {
    fn new(strategy: ProofStrategy) -> Self {
        Self { strategy, successes: 1, attempts: 1 }
    }

    fn success_rate(&self) -> f64 {
        if self.attempts == 0 { 0.0 } else { self.successes as f64 / self.attempts as f64 }
    }
}

/// Cache statistics.
#[derive(Debug, Clone, Default)]
pub struct ReplayCacheStats {
    pub lookups: u64,
    pub exact_hits: u64,
    pub partial_hits: u64,
    pub misses: u64,
    pub entries: usize,
}

impl ReplayCacheStats {
    /// Hit rate (exact + partial).
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        if self.lookups == 0 {
            0.0
        } else {
            (self.exact_hits + self.partial_hits) as f64 / self.lookups as f64
        }
    }
}

impl ReplayCache {
    pub fn new() -> Self {
        Self {
            exact: FxHashMap::default(),
            by_kind: FxHashMap::default(),
            stats: ReplayCacheStats::default(),
        }
    }

    /// Record a successful proof strategy for a VC key.
    pub fn record(&mut self, key: StrategyKey, strategy: ProofStrategy) {
        let kind = key.kind.clone();

        if let Some(entry) = self.exact.get_mut(&key) {
            entry.successes += 1;
            entry.attempts += 1;
        } else {
            self.exact.insert(key, CacheEntry::new(strategy.clone()));
            self.stats.entries += 1;
        }

        self.by_kind.entry(kind).or_default().push(CacheEntry::new(strategy));
    }

    /// Look up a strategy for a VC key.
    pub fn lookup(&mut self, key: &StrategyKey) -> ReplayResult {
        self.stats.lookups += 1;

        // Try exact match.
        if let Some(entry) = self.exact.get(key) {
            self.stats.exact_hits += 1;
            return ReplayResult::ExactMatch(entry.strategy.clone());
        }

        // Try partial match by kind.
        if let Some(entries) = self.by_kind.get(&key.kind)
            && let Some(best) = entries.iter().filter(|e| e.success_rate() > 0.5).max_by(|a, b| {
                a.success_rate().partial_cmp(&b.success_rate()).unwrap_or(std::cmp::Ordering::Equal)
            })
        {
            self.stats.partial_hits += 1;
            return ReplayResult::PartialMatch(best.strategy.clone());
        }

        self.stats.misses += 1;
        ReplayResult::Miss
    }

    /// Record that a replayed strategy failed (for success rate tracking).
    pub fn record_failure(&mut self, key: &StrategyKey) {
        if let Some(entry) = self.exact.get_mut(key) {
            entry.attempts += 1;
        }
    }

    /// Get cache statistics.
    #[must_use]
    pub fn stats(&self) -> &ReplayCacheStats {
        &self.stats
    }

    /// Number of cached strategies.
    #[must_use]
    pub fn len(&self) -> usize {
        self.stats.entries
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.stats.entries == 0
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.exact.clear();
        self.by_kind.clear();
        self.stats = ReplayCacheStats::default();
    }
}

impl Default for ReplayCache {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn key1() -> StrategyKey {
        StrategyKey::new("DivisionByZero", 12345, 2, 3)
    }

    fn key2() -> StrategyKey {
        StrategyKey::new("DivisionByZero", 99999, 3, 4)
    }

    fn strategy() -> ProofStrategy {
        ProofStrategy::new("ay", 5000).with_hint("simplify")
    }

    #[test]
    fn test_empty_cache() {
        let mut cache = ReplayCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.lookup(&key1()), ReplayResult::Miss);
    }

    #[test]
    fn test_record_and_exact_lookup() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        match cache.lookup(&key1()) {
            ReplayResult::ExactMatch(s) => assert_eq!(s.solver, "ay"),
            other => panic!("expected ExactMatch, got {other:?}"),
        }
    }

    #[test]
    fn test_partial_match_by_kind() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        // key2 has same kind but different structure
        match cache.lookup(&key2()) {
            ReplayResult::PartialMatch(s) => assert_eq!(s.solver, "ay"),
            other => panic!("expected PartialMatch, got {other:?}"),
        }
    }

    #[test]
    fn test_miss_different_kind() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        let diff_key = StrategyKey::new("IndexOutOfBounds", 12345, 2, 3);
        assert_eq!(cache.lookup(&diff_key), ReplayResult::Miss);
    }

    #[test]
    fn test_record_duplicate_increments_count() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        cache.record(key1(), strategy());
        assert_eq!(cache.len(), 1); // same key, same entry
    }

    #[test]
    fn test_stats() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        cache.lookup(&key1()); // exact hit
        cache.lookup(&key2()); // partial hit
        let diff_key = StrategyKey::new("Overflow", 0, 0, 0);
        cache.lookup(&diff_key); // miss

        let stats = cache.stats();
        assert_eq!(stats.lookups, 3);
        assert_eq!(stats.exact_hits, 1);
        assert_eq!(stats.partial_hits, 1);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn test_hit_rate() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        cache.lookup(&key1());
        cache.lookup(&key1());
        let diff_key = StrategyKey::new("Overflow", 0, 0, 0);
        cache.lookup(&diff_key);
        let stats = cache.stats();
        assert!((stats.hit_rate() - 2.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_record_failure() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        cache.record_failure(&key1());
        // Entry should still exist
        assert!(matches!(cache.lookup(&key1()), ReplayResult::ExactMatch(_)));
    }

    #[test]
    fn test_clear() {
        let mut cache = ReplayCache::new();
        cache.record(key1(), strategy());
        assert!(!cache.is_empty());
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.lookup(&key1()), ReplayResult::Miss);
    }

    #[test]
    fn test_strategy_builder() {
        let s = ProofStrategy::new("ay", 5000).with_hint("simplify").with_hint("elim-quantifiers");
        assert_eq!(s.hints.len(), 2);
        assert_eq!(s.solver, "ay");
        assert_eq!(s.timeout_ms, 5000);
    }

    #[test]
    fn test_empty_stats_hit_rate() {
        let stats = ReplayCacheStats::default();
        assert_eq!(stats.hit_rate(), 0.0);
    }

    #[test]
    fn test_strategy_key_equality() {
        let k1 = key1();
        let k2 = key1();
        assert_eq!(k1, k2);
    }
}
