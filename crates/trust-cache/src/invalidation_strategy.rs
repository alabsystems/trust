// trust-cache/invalidation_strategy.rs: Configurable cache invalidation strategies
//
// Provides three invalidation strategies for when specs change:
//   - Full: flush the entire cache (simple but wasteful)
//   - Selective: only invalidate entries for changed functions
//   - Dependency: follow call graph to invalidate transitive callers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use crate::VerificationCache;
use crate::invalidation::DependencyTracker;
use crate::spec_change_detector::{SpecChangeSummary, affected_vcs};

/// Strategy for cache invalidation when specs change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum InvalidationStrategy {
    /// Flush the entire cache. Simple but discards valid entries.
    Full,
    /// Only invalidate cache entries for functions whose specs changed.
    /// Does NOT follow the call graph — callers retain stale results.
    Selective,
    /// Invalidate changed functions AND all transitive callers via the
    /// dependency graph. This is the correct default for soundness.
    #[default]
    Dependency,
}

/// Result of applying an invalidation strategy.
#[derive(Debug, Clone, Default)]
pub struct InvalidationResult {
    /// Functions whose cache entries were actually removed.
    pub invalidated: Vec<String>,
    /// Functions whose cache entries were checked but already absent.
    pub already_absent: Vec<String>,
    /// Total entries in cache before invalidation.
    pub cache_size_before: usize,
    /// Total entries in cache after invalidation.
    pub cache_size_after: usize,
}

impl InvalidationResult {
    /// Number of entries actually removed from the cache.
    #[must_use]
    pub fn removed_count(&self) -> usize {
        self.invalidated.len()
    }

    /// Whether any entries were removed.
    #[must_use]
    pub fn had_effect(&self) -> bool {
        !self.invalidated.is_empty()
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "invalidated {} entries ({} already absent), cache {} -> {}",
            self.invalidated.len(),
            self.already_absent.len(),
            self.cache_size_before,
            self.cache_size_after,
        )
    }
}

/// Apply full invalidation: flush the entire cache.
pub(crate) fn full_invalidate(cache: &mut VerificationCache) -> InvalidationResult {
    let before = cache.len();
    cache.invalidate_all();
    InvalidationResult {
        invalidated: vec!["*".to_string()],
        already_absent: vec![],
        cache_size_before: before,
        cache_size_after: 0,
    }
}

/// Apply selective invalidation: only invalidate entries for the directly
/// changed functions. Does NOT follow the dependency graph.
pub(crate) fn selective_invalidate(
    cache: &mut VerificationCache,
    changes: &SpecChangeSummary,
) -> InvalidationResult {
    let before = cache.len();
    let targets = changes.invalidation_roots();
    let (invalidated, already_absent) = invalidate_targets(cache, &targets);
    InvalidationResult {
        invalidated,
        already_absent,
        cache_size_before: before,
        cache_size_after: cache.len(),
    }
}

/// Apply dependency-based invalidation: invalidate changed functions AND
/// all their transitive callers via the dependency graph.
pub(crate) fn dependency_invalidate(
    cache: &mut VerificationCache,
    changes: &SpecChangeSummary,
    deps: &DependencyTracker,
) -> InvalidationResult {
    let before = cache.len();
    let plan = affected_vcs(changes, deps);
    let (invalidated, already_absent) = invalidate_targets(cache, &plan.functions);
    InvalidationResult {
        invalidated,
        already_absent,
        cache_size_before: before,
        cache_size_after: cache.len(),
    }
}

/// Apply the given strategy to a cache.
pub(crate) fn apply_strategy(
    strategy: InvalidationStrategy,
    cache: &mut VerificationCache,
    changes: &SpecChangeSummary,
    deps: &DependencyTracker,
) -> InvalidationResult {
    match strategy {
        InvalidationStrategy::Full => full_invalidate(cache),
        InvalidationStrategy::Selective => selective_invalidate(cache, changes),
        InvalidationStrategy::Dependency => dependency_invalidate(cache, changes, deps),
    }
}

/// Invalidate a list of targets in the cache, returning (removed, absent) lists.
fn invalidate_targets(
    cache: &mut VerificationCache,
    targets: &[String],
) -> (Vec<String>, Vec<String>) {
    let mut invalidated = Vec::new();
    let mut already_absent = Vec::new();
    // Deduplicate targets
    let mut seen = FxHashSet::default();
    for target in targets {
        if seen.insert(target.clone()) {
            if cache.invalidate(target) {
                invalidated.push(target.clone());
            } else {
                already_absent.push(target.clone());
            }
        }
    }
    (invalidated, already_absent)
}

#[cfg(test)]
mod tests {
    use trust_types::FunctionVerdict;

    use super::*;
    use crate::CacheEntry;

    fn sample_entry(hash: &str) -> CacheEntry {
        CacheEntry {
            content_hash: hash.to_string(),
            verdict: FunctionVerdict::Verified,
            total_obligations: 1,
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            cached_at: 0,
            spec_hash: String::new(),
            solver_fingerprint: String::new(),
            obligation_results: vec![],
        }
    }

    fn populated_cache() -> VerificationCache {
        let mut cache = VerificationCache::in_memory();
        cache.store("lib::a", sample_entry("ha"));
        cache.store("lib::b", sample_entry("hb"));
        cache.store("lib::c", sample_entry("hc"));
        cache.store("lib::d", sample_entry("hd"));
        cache
    }

    fn chain_deps() -> DependencyTracker {
        // a -> b -> c (a calls b, b calls c)
        let mut deps = DependencyTracker::new();
        deps.add_dependency("lib::a", "lib::b");
        deps.add_dependency("lib::b", "lib::c");
        deps
    }

    // -----------------------------------------------------------------------
    // InvalidationStrategy defaults and equality
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_strategy_is_dependency() {
        assert_eq!(InvalidationStrategy::default(), InvalidationStrategy::Dependency);
    }

    #[test]
    fn test_strategy_equality() {
        assert_eq!(InvalidationStrategy::Full, InvalidationStrategy::Full);
        assert_ne!(InvalidationStrategy::Full, InvalidationStrategy::Selective);
        assert_ne!(InvalidationStrategy::Selective, InvalidationStrategy::Dependency);
    }

    // -----------------------------------------------------------------------
    // Full invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_invalidate_clears_everything() {
        let mut cache = populated_cache();
        let result = full_invalidate(&mut cache);
        assert!(cache.is_empty());
        assert_eq!(result.cache_size_before, 4);
        assert_eq!(result.cache_size_after, 0);
        assert!(result.had_effect());
    }

    #[test]
    fn test_full_invalidate_empty_cache() {
        let mut cache = VerificationCache::in_memory();
        let result = full_invalidate(&mut cache);
        assert_eq!(result.cache_size_before, 0);
        assert_eq!(result.cache_size_after, 0);
    }

    // -----------------------------------------------------------------------
    // Selective invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_selective_only_removes_changed() {
        let mut cache = populated_cache();
        let changes = SpecChangeSummary {
            modified: vec!["lib::b".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = selective_invalidate(&mut cache, &changes);

        assert_eq!(result.removed_count(), 1);
        assert!(result.invalidated.contains(&"lib::b".to_string()));
        assert_eq!(cache.len(), 3); // a, c, d remain
        assert_eq!(result.cache_size_before, 4);
        assert_eq!(result.cache_size_after, 3);
    }

    #[test]
    fn test_selective_does_not_follow_deps() {
        let mut cache = populated_cache();
        let changes = SpecChangeSummary {
            modified: vec!["lib::c".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = selective_invalidate(&mut cache, &changes);

        // Only c is removed, not b or a (even though they depend on c)
        assert_eq!(result.removed_count(), 1);
        assert!(result.invalidated.contains(&"lib::c".to_string()));
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_selective_includes_removed_functions() {
        let mut cache = populated_cache();
        let changes = SpecChangeSummary {
            modified: vec![],
            added: vec![],
            removed: vec!["lib::d".to_string()],
        };
        let result = selective_invalidate(&mut cache, &changes);
        assert_eq!(result.removed_count(), 1);
        assert!(result.invalidated.contains(&"lib::d".to_string()));
    }

    #[test]
    fn test_selective_absent_target() {
        let mut cache = populated_cache();
        let changes = SpecChangeSummary {
            modified: vec!["lib::nonexistent".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = selective_invalidate(&mut cache, &changes);
        assert_eq!(result.removed_count(), 0);
        assert_eq!(result.already_absent.len(), 1);
        assert_eq!(cache.len(), 4);
    }

    #[test]
    fn test_selective_no_changes() {
        let mut cache = populated_cache();
        let changes = SpecChangeSummary::default();
        let result = selective_invalidate(&mut cache, &changes);
        assert!(!result.had_effect());
        assert_eq!(cache.len(), 4);
    }

    // -----------------------------------------------------------------------
    // Dependency-based invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_dependency_follows_call_graph() {
        let mut cache = populated_cache();
        let deps = chain_deps();
        let changes = SpecChangeSummary {
            modified: vec!["lib::c".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = dependency_invalidate(&mut cache, &changes, &deps);

        // c changed -> b (calls c) and a (calls b) also invalidated
        assert!(result.invalidated.contains(&"lib::c".to_string()));
        assert!(result.invalidated.contains(&"lib::b".to_string()));
        assert!(result.invalidated.contains(&"lib::a".to_string()));
        assert_eq!(result.removed_count(), 3);
        assert_eq!(cache.len(), 1); // only d remains
    }

    #[test]
    fn test_dependency_leaf_change_only_self() {
        let mut cache = populated_cache();
        let deps = chain_deps();
        let changes = SpecChangeSummary {
            modified: vec!["lib::a".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = dependency_invalidate(&mut cache, &changes, &deps);

        // a is the top of the chain, nobody depends on it
        assert_eq!(result.removed_count(), 1);
        assert!(result.invalidated.contains(&"lib::a".to_string()));
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_dependency_no_deps_same_as_selective() {
        let mut cache = populated_cache();
        let deps = DependencyTracker::new(); // no deps registered
        let changes = SpecChangeSummary {
            modified: vec!["lib::b".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = dependency_invalidate(&mut cache, &changes, &deps);

        assert_eq!(result.removed_count(), 1);
        assert!(result.invalidated.contains(&"lib::b".to_string()));
    }

    #[test]
    fn test_dependency_with_removed_function() {
        let mut cache = populated_cache();
        let deps = chain_deps();
        let changes = SpecChangeSummary {
            modified: vec![],
            added: vec![],
            removed: vec!["lib::c".to_string()],
        };
        let result = dependency_invalidate(&mut cache, &changes, &deps);
        // Removing c also invalidates b and a
        assert_eq!(result.removed_count(), 3);
    }

    // -----------------------------------------------------------------------
    // apply_strategy dispatch
    // -----------------------------------------------------------------------

    #[test]
    fn test_apply_strategy_full() {
        let mut cache = populated_cache();
        let deps = DependencyTracker::new();
        let changes = SpecChangeSummary {
            modified: vec!["lib::a".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = apply_strategy(InvalidationStrategy::Full, &mut cache, &changes, &deps);
        assert!(cache.is_empty());
        assert_eq!(result.cache_size_after, 0);
    }

    #[test]
    fn test_apply_strategy_selective() {
        let mut cache = populated_cache();
        let deps = chain_deps();
        let changes = SpecChangeSummary {
            modified: vec!["lib::c".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = apply_strategy(InvalidationStrategy::Selective, &mut cache, &changes, &deps);
        // Selective doesn't follow deps
        assert_eq!(result.removed_count(), 1);
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_apply_strategy_dependency() {
        let mut cache = populated_cache();
        let deps = chain_deps();
        let changes = SpecChangeSummary {
            modified: vec!["lib::c".to_string()],
            added: vec![],
            removed: vec![],
        };
        let result = apply_strategy(InvalidationStrategy::Dependency, &mut cache, &changes, &deps);
        // Dependency follows call graph
        assert_eq!(result.removed_count(), 3);
        assert_eq!(cache.len(), 1);
    }

    // -----------------------------------------------------------------------
    // InvalidationResult
    // -----------------------------------------------------------------------

    #[test]
    fn test_invalidation_result_summary() {
        let result = InvalidationResult {
            invalidated: vec!["a".to_string(), "b".to_string()],
            already_absent: vec!["c".to_string()],
            cache_size_before: 10,
            cache_size_after: 8,
        };
        let s = result.summary();
        assert!(s.contains("2 entries"));
        assert!(s.contains("1 already absent"));
        assert!(s.contains("10 -> 8"));
    }

    #[test]
    fn test_invalidation_result_no_effect() {
        let result = InvalidationResult::default();
        assert!(!result.had_effect());
        assert_eq!(result.removed_count(), 0);
    }
}
