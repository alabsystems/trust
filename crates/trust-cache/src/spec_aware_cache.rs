// trust-cache/spec_aware_cache.rs: Spec-aware cache manager for Trust
//
// Unified orchestrator combining VerificationCache + SpecChangeDetector +
// DependencyTracker. Detects spec changes, computes invalidation plans,
// and applies them to the cache in a single coherent API.
//
// The two directions are not symmetric. Invalidation is monotone — dropping an
// entry can only cause more verification — so the caller->callee graph is a
// sound authority for it even though it covers only the contract-change
// channel. Serving is the opposite: a hit asserts that everything the stored
// verdict rested on is captured by the key, which this graph does not do. The
// lookup path therefore refuses proof-bearing records outright; see
// `lookup_with_spec_check` for the enumeration of what is missing and what
// would be needed to lift it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::invalidation::DependencyTracker;
use crate::invalidation_strategy::{InvalidationResult, InvalidationStrategy, apply_strategy};
use crate::spec_change_detector::{SpecChangeDetector, SpecChangeSummary, SpecFingerprint};
use crate::{CacheEntry, CacheLookup, VerificationCache};

/// Event emitted when invalidation occurs, for diagnostics and logging.
#[derive(Debug, Clone)]
pub struct InvalidationEvent {
    /// Summary of which specs changed.
    pub changes: SpecChangeSummary,
    /// Result of applying the invalidation strategy.
    pub result: InvalidationResult,
    /// The strategy that was used.
    pub strategy: InvalidationStrategy,
}

/// Unified cache manager that is aware of spec changes.
///
/// Combines three components:
/// - `VerificationCache`: stores/retrieves cached verification results
/// - `SpecChangeDetector`: detects spec fingerprint changes across iterations
/// - `DependencyTracker`: tracks caller/callee relationships for transitive invalidation
///
/// The manager ensures that when a spec changes, all affected cache entries
/// (the changed function plus its transitive callers) are invalidated before
/// the next verification pass.
pub struct SpecAwareCacheManager {
    cache: VerificationCache,
    detector: SpecChangeDetector,
    deps: DependencyTracker,
    strategy: InvalidationStrategy,
    /// History of invalidation events for diagnostics.
    events: Vec<InvalidationEvent>,
    /// Stored spec hashes from the cache entries, used for cross-session detection.
    stored_spec_hashes: FxHashMap<String, String>,
}

impl SpecAwareCacheManager {
    /// Create a new manager with an in-memory cache and default (Dependency) strategy.
    pub fn new() -> Self {
        Self {
            cache: VerificationCache::in_memory(),
            detector: SpecChangeDetector::new(),
            deps: DependencyTracker::new(),
            strategy: InvalidationStrategy::default(),
            events: Vec::new(),
            stored_spec_hashes: FxHashMap::default(),
        }
    }

    /// Create a manager wrapping an existing cache.
    pub fn with_cache(cache: VerificationCache) -> Self {
        Self {
            cache,
            detector: SpecChangeDetector::new(),
            deps: DependencyTracker::new(),
            strategy: InvalidationStrategy::default(),
            events: Vec::new(),
            stored_spec_hashes: FxHashMap::default(),
        }
    }

    /// Set the invalidation strategy.
    pub fn set_strategy(&mut self, strategy: InvalidationStrategy) {
        self.strategy = strategy;
    }

    /// Get the current invalidation strategy.
    #[must_use]
    pub fn strategy(&self) -> InvalidationStrategy {
        self.strategy
    }

    /// Access the underlying cache (immutable).
    ///
    /// Deliberately not part of the public surface: handing out the raw cache
    /// would route around [`Self::lookup_with_spec_check`]'s proof-authority
    /// firewall, and this type's whole reason for existing is that its
    /// dependency graph is not a sufficient key for a proof-bearing verdict.
    #[must_use]
    pub(crate) fn cache(&self) -> &VerificationCache {
        &self.cache
    }

    /// Access the underlying cache (mutable).
    pub(crate) fn cache_mut(&mut self) -> &mut VerificationCache {
        &mut self.cache
    }

    /// Access the dependency tracker in tests.
    #[must_use]
    #[cfg(test)]
    fn deps(&self) -> &DependencyTracker {
        &self.deps
    }

    /// Register a dependency: `caller` depends on `callee`.
    pub fn add_dependency(&mut self, caller: &str, callee: &str) {
        self.deps.add_dependency(caller, callee);
    }

    /// Register multiple dependencies at once.
    pub fn add_dependencies(&mut self, caller: &str, callees: &[&str]) {
        self.deps.add_dependencies(caller, callees);
    }

    /// Process a new set of spec fingerprints, detect changes, and invalidate.
    ///
    /// This is the primary entry point for each verification iteration:
    /// 1. Compare current fingerprints against the previous snapshot
    /// 2. If specs changed, compute the invalidation plan
    /// 3. Apply the configured strategy to the cache
    /// 4. Record the event for diagnostics
    ///
    /// Returns the change summary and invalidation result.
    pub fn process_specs(
        &mut self,
        current_fingerprints: &[SpecFingerprint],
    ) -> (SpecChangeSummary, Option<InvalidationResult>) {
        let changes = self.detector.detect_changes(current_fingerprints);

        if !changes.has_changes() {
            return (changes, None);
        }

        let result = apply_strategy(self.strategy, &mut self.cache, &changes, &self.deps);

        self.events.push(InvalidationEvent {
            changes: changes.clone(),
            result: result.clone(),
            strategy: self.strategy,
        });

        (changes, Some(result))
    }

    /// Check for spec changes using stored spec hashes from CacheEntry.
    ///
    /// This enables cross-session spec change detection: even if the
    /// SpecChangeDetector has no previous snapshot (fresh session), we can
    /// compare current fingerprints against the spec_hash stored in each
    /// CacheEntry from the previous session.
    ///
    /// Returns the list of def_paths whose specs changed since they were cached.
    #[must_use]
    pub fn detect_stale_entries(&self, current_fingerprints: &[SpecFingerprint]) -> Vec<String> {
        let mut stale = Vec::new();
        for fp in current_fingerprints {
            if let Some(stored_hash) = self.stored_spec_hashes.get(&fp.def_path)
                && !stored_hash.is_empty()
                && stored_hash != &fp.hash
            {
                stale.push(fp.def_path.clone());
            }
        }
        stale.sort();
        stale
    }

    /// Invalidate stale entries detected via cross-session spec hash comparison.
    ///
    /// Call this at session start after loading a cache from disk:
    /// 1. Load spec hashes from cache entries via `load_spec_hashes_from_cache`
    /// 2. Compute current fingerprints
    /// 3. Call this method to invalidate entries with changed specs
    ///
    /// Returns the list of def_paths that were actually invalidated.
    pub fn invalidate_stale_entries(
        &mut self,
        current_fingerprints: &[SpecFingerprint],
    ) -> Vec<String> {
        let stale = self.detect_stale_entries(current_fingerprints);
        let mut invalidated = Vec::new();

        // Build a change summary from the stale entries
        if !stale.is_empty() {
            let changes =
                SpecChangeSummary { modified: stale.clone(), added: vec![], removed: vec![] };
            let result = apply_strategy(self.strategy, &mut self.cache, &changes, &self.deps);
            invalidated = result.invalidated;

            self.events.push(InvalidationEvent {
                changes,
                result: InvalidationResult {
                    invalidated: invalidated.clone(),
                    already_absent: vec![],
                    cache_size_before: 0,
                    cache_size_after: self.cache.len(),
                },
                strategy: self.strategy,
            });
        }

        invalidated
    }

    /// Load spec hashes from existing cache entries for cross-session detection.
    ///
    /// Call this after loading a cache from disk. Extracts the spec_hash field
    /// from each CacheEntry and stores it for comparison against current fingerprints.
    pub fn load_spec_hashes(&mut self, entries: &[(String, CacheEntry)]) {
        self.stored_spec_hashes.clear();
        for (def_path, entry) in entries {
            if !entry.spec_hash.is_empty() {
                self.stored_spec_hashes.insert(def_path.clone(), entry.spec_hash.clone());
            }
        }
    }

    /// Lookup a function in the cache, also checking spec freshness.
    ///
    /// Returns `CacheLookup::Miss` if:
    /// - The function is not in the cache
    /// - The content hash does not match
    /// - The spec hash does not match the current fingerprint (spec changed)
    /// - The stored record would assert proof authority (see below)
    ///
    /// ## Why a matching key is still not enough for a proof
    ///
    /// The caller->callee graph this manager maintains covers exactly one of the
    /// channels a Trust verdict consumes: a change to a transitive callee's
    /// declared contract. It does not observe R1 caller coverage, callee
    /// panic-freedom, backing certificates, callee return summaries, sealed
    /// dyn-Trait postcondition covariance, `#[trust::single_writer]`/`backing`
    /// hints, or non-unwinding-ABI demotion — every one of which can be the
    /// reason a function proved, and none of which appears in this key. A hit
    /// that returned `Verified` would therefore be a proof claim justified by
    /// facts nobody checked; a conservative outcome replayed under the same key
    /// can only make a caller re-solve or report a weaker verdict.
    ///
    /// So the discipline is structural, not a caller's responsibility: the hit
    /// is refused here rather than documented as a hazard. Lifting it needs a
    /// key that captures those facts, or a tripwire that detects "verification
    /// consumed a fact outside the key" — not another exclusion list, since
    /// three independent audits each found a channel the previous list missed.
    pub fn lookup_with_spec_check(
        &mut self,
        def_path: &str,
        content_hash: &str,
        current_spec_hash: &str,
        solver_fingerprint: &str,
    ) -> CacheLookup {
        // #690: spec_hash validation is now built into VerificationCache::lookup(),
        // so we pass current_spec_hash directly. No redundant post-hoc check needed.
        // v5: solver_fingerprint must also match so out-of-process solver rebuilds
        // invalidate dependent entries.
        match self.cache.lookup(def_path, content_hash, current_spec_hash, solver_fingerprint) {
            CacheLookup::Hit(entry) if entry.claims_proof_authority() => CacheLookup::Miss,
            lookup => lookup,
        }
    }

    /// Number of invalidation events recorded.
    #[must_use]
    pub fn event_count(&self) -> usize {
        self.events.len()
    }

    /// Get all recorded invalidation events.
    #[must_use]
    pub fn events(&self) -> &[InvalidationEvent] {
        &self.events
    }

    /// Get the most recent invalidation event, if any.
    #[must_use]
    pub fn last_event(&self) -> Option<&InvalidationEvent> {
        self.events.last()
    }

    /// Total number of entries invalidated across all events.
    #[must_use]
    pub fn total_invalidated(&self) -> usize {
        self.events.iter().map(|e| e.result.invalidated.len()).sum()
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "cache: {}, deps: {} functions, {} invalidation events ({} total removed)",
            self.cache.summary(),
            self.deps.len(),
            self.events.len(),
            self.total_invalidated(),
        )
    }

    /// Save the underlying cache to disk.
    pub fn save(&mut self) -> Result<(), crate::CacheError> {
        self.cache.save()
    }
}

impl Default for SpecAwareCacheManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use trust_types::FunctionVerdict;

    use super::*;

    /// A record whose replay would be a conservative outcome: one unresolved
    /// obligation, nothing proved. Key-matching tests use this because a
    /// proof-bearing record can never be served from here by construction.
    fn conservative_entry(hash: &str, spec_hash: &str) -> CacheEntry {
        CacheEntry {
            verdict: FunctionVerdict::Inconclusive,
            proved: 0,
            unknown: 1,
            ..sample_entry(hash, spec_hash)
        }
    }

    fn sample_entry(hash: &str, spec_hash: &str) -> CacheEntry {
        CacheEntry {
            content_hash: hash.to_string(),
            verdict: FunctionVerdict::Verified,
            total_obligations: 1,
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            cached_at: 100,
            spec_hash: spec_hash.to_string(),
            solver_fingerprint: String::new(),
            obligation_results: vec![],
        }
    }

    fn fp(def_path: &str, requires: &[&str]) -> SpecFingerprint {
        let req: Vec<String> = requires.iter().map(|s| s.to_string()).collect();
        SpecFingerprint::from_clauses(def_path, &req, &[], &[])
    }

    // -----------------------------------------------------------------------
    // Construction and defaults
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_manager_is_empty() {
        let mgr = SpecAwareCacheManager::new();
        assert!(mgr.cache().is_empty());
        assert!(mgr.deps().is_empty());
        assert_eq!(mgr.event_count(), 0);
        assert_eq!(mgr.strategy(), InvalidationStrategy::Dependency);
    }

    #[test]
    fn test_set_strategy() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.set_strategy(InvalidationStrategy::Selective);
        assert_eq!(mgr.strategy(), InvalidationStrategy::Selective);
    }

    // -----------------------------------------------------------------------
    // process_specs: no changes
    // -----------------------------------------------------------------------

    #[test]
    fn test_process_specs_no_changes_no_invalidation() {
        let mut mgr = SpecAwareCacheManager::new();
        let fps = vec![fp("f", &["x > 0"])];

        // First call: all added (no previous)
        let (changes, result) = mgr.process_specs(&fps);
        assert!(!changes.added.is_empty());
        // Added functions have no cached entries to invalidate
        assert!(result.is_none() || !result.as_ref().unwrap().had_effect());

        // Second call: same fingerprints, no changes
        let (changes2, result2) = mgr.process_specs(&fps);
        assert!(!changes2.has_changes());
        assert!(result2.is_none());
    }

    // -----------------------------------------------------------------------
    // process_specs: spec modified -> invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_process_specs_modified_invalidates() {
        let mut mgr = SpecAwareCacheManager::new();

        // Populate cache
        mgr.cache_mut().store("f", sample_entry("h1", "old_spec"));
        mgr.cache_mut().store("g", sample_entry("h2", "g_spec"));

        // Setup deps: g calls f
        mgr.add_dependency("g", "f");

        // First pass: establish baseline
        let fps_v1 = vec![fp("f", &["x > 0"]), fp("g", &["y > 0"])];
        let _ = mgr.process_specs(&fps_v1);

        // Second pass: f's spec changed
        let fps_v2 = vec![fp("f", &["x > 1"]), fp("g", &["y > 0"])];
        let (changes, result) = mgr.process_specs(&fps_v2);

        assert_eq!(changes.modified, vec!["f"]);
        let result = result.expect("should have invalidation result");
        assert!(result.had_effect());
        // With dependency strategy: both f and g should be invalidated
        assert!(result.invalidated.contains(&"f".to_string()));
        assert!(result.invalidated.contains(&"g".to_string()));
    }

    // -----------------------------------------------------------------------
    // process_specs: selective strategy only invalidates direct changes
    // -----------------------------------------------------------------------

    #[test]
    fn test_process_specs_selective_no_transitive() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.set_strategy(InvalidationStrategy::Selective);

        // Populate cache
        mgr.cache_mut().store("f", sample_entry("h1", ""));
        mgr.cache_mut().store("g", sample_entry("h2", ""));

        // g calls f
        mgr.add_dependency("g", "f");

        // Establish baseline
        let fps_v1 = vec![fp("f", &["x > 0"]), fp("g", &["y > 0"])];
        let _ = mgr.process_specs(&fps_v1);

        // f's spec changed
        let fps_v2 = vec![fp("f", &["x > 1"]), fp("g", &["y > 0"])];
        let (_, result) = mgr.process_specs(&fps_v2);

        let result = result.expect("should invalidate");
        // Selective: only f, not g
        assert_eq!(result.invalidated, vec!["f"]);
    }

    // -----------------------------------------------------------------------
    // process_specs: full strategy flushes everything
    // -----------------------------------------------------------------------

    #[test]
    fn test_process_specs_full_flushes_all() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.set_strategy(InvalidationStrategy::Full);

        mgr.cache_mut().store("f", sample_entry("h1", ""));
        mgr.cache_mut().store("g", sample_entry("h2", ""));
        mgr.cache_mut().store("h", sample_entry("h3", ""));

        let fps_v1 = vec![fp("f", &["x > 0"])];
        let _ = mgr.process_specs(&fps_v1);

        // Change f's spec
        let fps_v2 = vec![fp("f", &["x > 1"])];
        let (_, result) = mgr.process_specs(&fps_v2);

        let result = result.expect("should invalidate");
        assert!(mgr.cache().is_empty());
        assert!(result.had_effect());
    }

    // -----------------------------------------------------------------------
    // Cross-session spec change detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_detect_stale_entries_from_stored_hashes() {
        let mut mgr = SpecAwareCacheManager::new();

        let fp_current = fp("f", &["x > 1"]);
        let old_fp = fp("f", &["x > 0"]);

        // Simulate loading cache entries from a previous session
        mgr.load_spec_hashes(&[("f".to_string(), sample_entry("h1", &old_fp.hash))]);

        let stale = mgr.detect_stale_entries(&[fp_current]);
        assert_eq!(stale, vec!["f"]);
    }

    #[test]
    fn test_detect_stale_entries_no_change() {
        let mut mgr = SpecAwareCacheManager::new();
        let current_fp = fp("f", &["x > 0"]);

        mgr.load_spec_hashes(&[("f".to_string(), sample_entry("h1", &current_fp.hash))]);

        let stale = mgr.detect_stale_entries(&[current_fp]);
        assert!(stale.is_empty());
    }

    #[test]
    fn test_detect_stale_entries_empty_spec_hash_not_stale() {
        let mut mgr = SpecAwareCacheManager::new();
        let current_fp = fp("f", &["x > 0"]);

        // Entry with empty spec_hash (pre-spec-tracking)
        mgr.load_spec_hashes(&[("f".to_string(), sample_entry("h1", ""))]);

        // Empty spec_hash should NOT trigger staleness (backward compat)
        let stale = mgr.detect_stale_entries(&[current_fp]);
        assert!(stale.is_empty());
    }

    #[test]
    fn test_invalidate_stale_entries() {
        let mut mgr = SpecAwareCacheManager::new();

        let old_fp = fp("f", &["x > 0"]);
        let new_fp = fp("f", &["x > 1"]);

        // Populate cache and stored hashes
        mgr.cache_mut().store("f", sample_entry("h1", &old_fp.hash));
        mgr.cache_mut().store("g", sample_entry("h2", "other"));
        mgr.add_dependency("g", "f");
        mgr.load_spec_hashes(&[("f".to_string(), sample_entry("h1", &old_fp.hash))]);

        let invalidated = mgr.invalidate_stale_entries(&[new_fp]);
        // With dependency strategy: f changed, g depends on f
        assert!(invalidated.contains(&"f".to_string()));
        assert!(invalidated.contains(&"g".to_string()));
    }

    // -----------------------------------------------------------------------
    // lookup_with_spec_check
    // -----------------------------------------------------------------------

    #[test]
    fn test_lookup_with_spec_check_hit() {
        let mut mgr = SpecAwareCacheManager::new();
        let spec_hash = "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890";
        mgr.cache_mut().store("f", conservative_entry("h1", spec_hash));

        let result = mgr.lookup_with_spec_check("f", "h1", spec_hash, "");
        assert!(matches!(result, CacheLookup::Hit(_)));
    }

    #[test]
    fn matching_key_still_cannot_replay_a_proof_bearing_record() {
        // The caller->callee graph below observes contract changes and nothing
        // else. Every other fact a Trust verdict can rest on is outside this
        // key, so a `Verified` record must fail closed no matter how exactly
        // the key matches — otherwise adopting this manager would reintroduce
        // the discharge channel the compiler's unpopulated proof cache exists
        // to avoid.
        let mut mgr = SpecAwareCacheManager::new();
        let spec_hash = "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890";
        mgr.cache_mut().store("f", sample_entry("h1", spec_hash));

        assert!(matches!(
            mgr.lookup_with_spec_check("f", "h1", spec_hash, ""),
            CacheLookup::Miss
        ));

        // A zero-obligation record is itself the claim that there was nothing
        // to prove, so it is proof-bearing too.
        let mut empty = conservative_entry("h2", spec_hash);
        empty.total_obligations = 0;
        empty.unknown = 0;
        mgr.cache_mut().store("g", empty);
        assert!(matches!(
            mgr.lookup_with_spec_check("g", "h2", spec_hash, ""),
            CacheLookup::Miss
        ));
    }

    #[test]
    fn test_lookup_with_spec_check_miss_on_spec_change() {
        let mut mgr = SpecAwareCacheManager::new();
        let old_spec = "old_spec_hash_value_that_is_long_enough_for_testing_purposes_here";
        let new_spec = "new_spec_hash_value_that_is_long_enough_for_testing_purposes_here";
        mgr.cache_mut().store("f", sample_entry("h1", old_spec));

        let result = mgr.lookup_with_spec_check("f", "h1", new_spec, "");
        assert!(matches!(result, CacheLookup::Miss));
    }

    #[test]
    fn test_lookup_with_spec_check_empty_stored_spec_misses_real_spec() {
        // an entry stored without a spec fingerprint (empty
        // spec_hash, e.g. from before spec tracking) must NOT be served as
        // `proved` once the function carries a real spec. The empty stored hash
        // is no longer a wildcard that matches any incoming hash — it fails
        // closed to a miss and re-verifies. (Previously this hit, which served a
        // pre-spec verdict as proof of a now-specced function — a false-PROVE.)
        let mut mgr = SpecAwareCacheManager::new();
        mgr.cache_mut().store("f", conservative_entry("h1", ""));

        // Function now has a real spec -> must MISS (re-verify), not hit stale.
        let result = mgr.lookup_with_spec_check("f", "h1", "any_spec_hash", "");
        assert!(
            matches!(result, CacheLookup::Miss),
            "spec-less entry must not serve a now-specced function as proved"
        );

        // A genuinely spec-less function (empty incoming) still hits by equality.
        let result_empty = mgr.lookup_with_spec_check("f", "h1", "", "");
        assert!(
            matches!(result_empty, CacheLookup::Hit(_)),
            "both-empty spec hashes still hit by true equality"
        );
    }

    #[test]
    fn test_lookup_with_spec_check_content_miss() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.cache_mut().store("f", sample_entry("h1", "spec"));

        // Content hash mismatch -> miss regardless of spec
        let result = mgr.lookup_with_spec_check("f", "wrong_hash", "spec", "");
        assert!(matches!(result, CacheLookup::Miss));
    }

    // -----------------------------------------------------------------------
    // Event tracking
    // -----------------------------------------------------------------------

    #[test]
    fn test_event_tracking() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.cache_mut().store("f", sample_entry("h1", ""));

        let fps_v1 = vec![fp("f", &["x > 0"])];
        let _ = mgr.process_specs(&fps_v1);
        // First iteration: added, may or may not produce event
        let initial_events = mgr.event_count();

        let fps_v2 = vec![fp("f", &["x > 1"])];
        let _ = mgr.process_specs(&fps_v2);
        assert_eq!(mgr.event_count(), initial_events + 1);

        let event = mgr.last_event().expect("should have event");
        assert_eq!(event.strategy, InvalidationStrategy::Dependency);
        assert_eq!(event.changes.modified, vec!["f"]);
    }

    #[test]
    fn test_total_invalidated() {
        let mut mgr = SpecAwareCacheManager::new();
        mgr.cache_mut().store("f", sample_entry("h1", ""));
        mgr.cache_mut().store("g", sample_entry("h2", ""));
        mgr.add_dependency("g", "f");

        let fps_v1 = vec![fp("f", &["x > 0"]), fp("g", &["y > 0"])];
        let _ = mgr.process_specs(&fps_v1);

        let fps_v2 = vec![fp("f", &["x > 1"]), fp("g", &["y > 0"])];
        let _ = mgr.process_specs(&fps_v2);

        assert!(mgr.total_invalidated() >= 1);
    }

    // -----------------------------------------------------------------------
    // Summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_format() {
        let mgr = SpecAwareCacheManager::new();
        let s = mgr.summary();
        assert!(s.contains("cache:"));
        assert!(s.contains("deps:"));
        assert!(s.contains("invalidation events"));
    }

    // -----------------------------------------------------------------------
    // Diamond dependency invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_diamond_dependency_invalidation() {
        let mut mgr = SpecAwareCacheManager::new();

        //   a
        //  / \
        // b   c
        //  \ /
        //   d
        mgr.add_dependency("a", "b");
        mgr.add_dependency("a", "c");
        mgr.add_dependency("b", "d");
        mgr.add_dependency("c", "d");

        for name in &["a", "b", "c", "d"] {
            mgr.cache_mut().store(name, sample_entry(&format!("h_{name}"), ""));
        }

        let fps_v1 = vec![fp("a", &[]), fp("b", &[]), fp("c", &[]), fp("d", &["x > 0"])];
        let _ = mgr.process_specs(&fps_v1);

        // d's spec changes
        let fps_v2 = vec![fp("a", &[]), fp("b", &[]), fp("c", &[]), fp("d", &["x > 1"])];
        let (changes, result) = mgr.process_specs(&fps_v2);
        assert_eq!(changes.modified, vec!["d"]);

        let result = result.expect("should invalidate");
        // d, b, c, a all invalidated (transitive callers through diamond)
        assert_eq!(result.invalidated.len(), 4);
        assert!(result.invalidated.contains(&"a".to_string()));
        assert!(result.invalidated.contains(&"b".to_string()));
        assert!(result.invalidated.contains(&"c".to_string()));
        assert!(result.invalidated.contains(&"d".to_string()));
    }

    // -----------------------------------------------------------------------
    // Multiple spec changes in one iteration
    // -----------------------------------------------------------------------

    #[test]
    fn test_multiple_spec_changes_deduped() {
        let mut mgr = SpecAwareCacheManager::new();

        mgr.add_dependency("top", "mid");
        mgr.add_dependency("mid", "leaf1");
        mgr.add_dependency("mid", "leaf2");

        for name in &["top", "mid", "leaf1", "leaf2"] {
            mgr.cache_mut().store(name, sample_entry(&format!("h_{name}"), ""));
        }

        let fps_v1 = vec![fp("top", &[]), fp("mid", &[]), fp("leaf1", &["a"]), fp("leaf2", &["b"])];
        let _ = mgr.process_specs(&fps_v1);

        // Both leaf specs change
        let fps_v2 =
            vec![fp("top", &[]), fp("mid", &[]), fp("leaf1", &["a2"]), fp("leaf2", &["b2"])];
        let (changes, result) = mgr.process_specs(&fps_v2);
        assert_eq!(changes.modified.len(), 2);

        let result = result.expect("should invalidate");
        // All four should be invalidated (leaf1, leaf2 changed; mid and top are callers)
        assert_eq!(result.invalidated.len(), 4);
    }

    // -----------------------------------------------------------------------
    // Function removal triggers invalidation of callers
    // -----------------------------------------------------------------------

    #[test]
    fn test_removed_function_invalidates_callers() {
        let mut mgr = SpecAwareCacheManager::new();

        mgr.add_dependency("caller", "removed_fn");
        mgr.cache_mut().store("caller", sample_entry("h_caller", ""));
        mgr.cache_mut().store("removed_fn", sample_entry("h_rem", ""));

        let fps_v1 = vec![fp("caller", &[]), fp("removed_fn", &["pre"])];
        let _ = mgr.process_specs(&fps_v1);

        // removed_fn disappears
        let fps_v2 = vec![fp("caller", &[])];
        let (changes, result) = mgr.process_specs(&fps_v2);
        assert_eq!(changes.removed, vec!["removed_fn"]);

        let result = result.expect("should invalidate");
        assert!(result.invalidated.contains(&"caller".to_string()));
    }
}
