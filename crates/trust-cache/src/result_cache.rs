// trust-cache/src/result_cache.rs: Solver result caching with replay
//
// Remembers solver answers keyed by (formula_hash, solver_name) and can replay
// them on cache hit. Supports configurable cache policies (always, on-success,
// TTL-based, never) and stale-entry invalidation.
//
// Consolidated from trust-router into trust-cache so that all
// caching implementations live in the dedicated cache crate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::fx::{FxHashMap, FxHashSet};

/// Default upper bound on the number of in-memory `ResultCache` entries.
///
/// The unbounded solver result cache otherwise grows one entry per unique
/// `(formula_hash, solver)` for the lifetime of a compile and is never pruned
/// on the hot path (`invalidate_*` are not called during compilation). A few
/// thousand entries is ample for cross-VC reuse within a crate while keeping
/// memory bounded; override with `TRUST_RESULT_CACHE_CAP` (see
/// [`ResultCache::resolve_capacity`]).
pub const DEFAULT_RESULT_CACHE_CAP: usize = 8192;

/// Environment variable that overrides [`DEFAULT_RESULT_CACHE_CAP`].
///
/// Parsed as a `usize`. A value of `0` disables the bound entirely (unbounded,
/// legacy behavior). Unset or unparseable values fall back to the default.
const RESULT_CACHE_CAP_ENV: &str = "TRUST_RESULT_CACHE_CAP";

/// Key for a cached solver result: (formula_hash, solver_name).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResultCacheKey {
    pub formula_hash: String,
    pub solver_name: String,
}

/// A cached solver result entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CachedResult {
    pub key: ResultCacheKey,
    pub verdict: String,
    pub model: Option<String>,
    pub time_ms: u64,
    pub cached_at: u64,
    /// JSON-serialized `ProofStrength` for proved results.
    /// `None` for non-proved verdicts or legacy entries (defaults to `smt_unsat()`).
    #[serde(default)]
    pub strength_json: Option<String>,
    /// Raw proof-certificate bytes (e.g. LRAT from ay) for proved results.
    ///
    /// Threaded so a session-cache replay is EVIDENCE-EQUIVALENT to the fresh
    /// solve that populated it: the `-full` evidence lane is fail-closed ("no
    /// retained bytes -> no exact certificate artifact -> no evidence"), so an
    /// entry without this field silently weakens the evidence DAG of every
    /// deduplicated obligation. This is certificate DATA riding alongside the
    /// memoized verdict — it does not change the authority model (replay still
    /// requires `locally_validated`, i.e. this process solved the key).
    /// `None` for non-proved verdicts, solvers that emit no certificate, or
    /// legacy entries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_certificate: Option<Vec<u8>>,
}

/// Policy controlling when results are cached.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CachePolicy {
    /// Cache every result regardless of verdict.
    AlwaysCache,
    /// Cache only results where the verdict indicates success ("proved").
    CacheOnSuccess,
    /// Cache all results but with a TTL (seconds) after which they are stale.
    CacheWithTTL(u64),
    /// Never cache any result.
    NeverCache,
}

/// Statistics about cache usage.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CacheStats {
    pub total_entries: usize,
    pub hits: usize,
    pub misses: usize,
    pub evictions: usize,
    pub replays: usize,
}

/// Solver result cache with replay support.
///
/// The in-memory entry map is bounded by an LRU cap (see
/// [`DEFAULT_RESULT_CACHE_CAP`] / [`RESULT_CACHE_CAP_ENV`]) so it cannot grow
/// without limit over a long compile. `lru` tracks access recency: the front is
/// the least-recently-used key (next eviction candidate) and the back is the
/// most-recently-used. It is kept in lock-step with `entries`.
///
/// **Why eviction is sound.** This cache only ever stores *proved* verdicts
/// under `CacheOnSuccess` (the compile-path policy), and a cache entry is a
/// pure memoization of a deterministic solver answer. Evicting an entry never
/// changes a verdict, drops a proof obligation, or yields a false proof: it
/// only discards a *successful* memo, forcing the next lookup to miss and the
/// VC to be re-solved from scratch (fail-closed by construction). The cache key
/// `(formula_hash, solver)` is unchanged, so identity/replay semantics for any
/// live entry are byte-for-byte identical to the unbounded cache.
pub struct ResultCache {
    policy: CachePolicy,
    entries: FxHashMap<ResultCacheKey, CachedResult>,
    /// Keys whose results were produced by a solver in this cache instance.
    ///
    /// This authority state is deliberately not serialized. Entries loaded by
    /// [`Self::warm_cache`] remain lookup hints until the current process
    /// re-solves the obligation and [`Self::cache_result`] promotes the key.
    /// A forged or stale on-disk `CachedResult` therefore cannot mint a proof.
    locally_validated: FxHashSet<ResultCacheKey>,
    /// LRU recency order over the keys in `entries`. Front = LRU, back = MRU.
    lru: VecDeque<ResultCacheKey>,
    /// Maximum number of entries; `0` means unbounded (legacy behavior).
    capacity: usize,
    stats: CacheStats,
}

impl ResultCache {
    /// Create a new result cache with the given caching policy.
    ///
    /// The entry bound defaults to [`DEFAULT_RESULT_CACHE_CAP`], overridable via
    /// the `TRUST_RESULT_CACHE_CAP` environment variable.
    #[must_use]
    pub fn new(policy: CachePolicy) -> Self {
        Self::with_capacity(policy, Self::resolve_capacity())
    }

    /// Create a new result cache with an explicit entry cap.
    ///
    /// A `capacity` of `0` disables the bound (unbounded, legacy behavior).
    #[must_use]
    pub fn with_capacity(policy: CachePolicy, capacity: usize) -> Self {
        Self {
            policy,
            entries: FxHashMap::default(),
            locally_validated: FxHashSet::default(),
            lru: VecDeque::new(),
            capacity,
            stats: CacheStats::default(),
        }
    }

    /// Resolve the entry cap from `TRUST_RESULT_CACHE_CAP`, falling back to
    /// [`DEFAULT_RESULT_CACHE_CAP`] when unset or unparseable.
    #[must_use]
    fn resolve_capacity() -> usize {
        std::env::var(RESULT_CACHE_CAP_ENV)
            .ok()
            .and_then(|raw| raw.trim().parse::<usize>().ok())
            .unwrap_or(DEFAULT_RESULT_CACHE_CAP)
    }

    /// Mark `key` as most-recently-used, moving it to the back of `lru`.
    ///
    /// Linear in the recency list; the cap keeps this bounded by `capacity`.
    fn touch(&mut self, key: &ResultCacheKey) {
        if let Some(pos) = self.lru.iter().position(|k| k == key) {
            if let Some(k) = self.lru.remove(pos) {
                self.lru.push_back(k);
            }
        }
    }

    /// Whether an entry is still eligible under the active replay policy. A
    /// timestamp in the future fails closed: wall-clock rollback or corrupted
    /// metadata must not extend a TTL indefinitely.
    fn entry_is_fresh(&self, entry: &CachedResult, now: u64) -> bool {
        match self.policy {
            CachePolicy::CacheWithTTL(ttl) => {
                now.checked_sub(entry.cached_at).is_some_and(|age| age <= ttl)
            }
            _ => true,
        }
    }

    /// Remove one entry while keeping every index and authority set in sync.
    fn remove_entry(&mut self, key: &ResultCacheKey) -> bool {
        let removed = self.entries.remove(key).is_some();
        self.locally_validated.remove(key);
        if let Some(pos) = self.lru.iter().position(|candidate| candidate == key) {
            self.lru.remove(pos);
        }
        if removed {
            self.stats.evictions += 1;
        }
        removed
    }

    /// Cache a solver result under the given key.
    ///
    /// Respects the cache policy: `NeverCache` silently drops, `CacheOnSuccess`
    /// only stores results with verdict "proved".
    ///
    /// `strength_json`: JSON-serialized `ProofStrength` for proved results.
    /// Pass `None` for non-proved verdicts.
    pub fn cache_result(
        &mut self,
        key: ResultCacheKey,
        verdict: &str,
        model: Option<String>,
        time_ms: u64,
        strength_json: Option<String>,
    ) {
        self.cache_result_with_certificate(key, verdict, model, time_ms, strength_json, None);
    }

    /// [`Self::cache_result`] carrying the solver's proof-certificate bytes, so
    /// a later replay of this entry is evidence-equivalent to the fresh solve
    /// (see [`CachedResult::proof_certificate`]). Same policy and authority
    /// semantics as `cache_result` — the certificate is data, not authority.
    pub fn cache_result_with_certificate(
        &mut self,
        key: ResultCacheKey,
        verdict: &str,
        model: Option<String>,
        time_ms: u64,
        strength_json: Option<String>,
        proof_certificate: Option<Vec<u8>>,
    ) {
        match &self.policy {
            CachePolicy::NeverCache => return,
            CachePolicy::CacheOnSuccess if verdict != "proved" => return,
            _ => {}
        }

        let cached_at = self.current_time_secs();
        let entry = CachedResult {
            key: key.clone(),
            verdict: verdict.to_string(),
            model,
            time_ms,
            cached_at,
            strength_json,
            proof_certificate,
        };

        let is_update = self.entries.insert(key.clone(), entry).is_some();
        self.locally_validated.insert(key.clone());
        if is_update {
            // Re-cache of an existing key: refresh recency, no growth.
            self.touch(&key);
        } else {
            // New key: record as most-recently-used, then enforce the cap by
            // evicting least-recently-used entries. Sound because every entry
            // is a memoized *successful* (proved) verdict -- dropping one only
            // forces a deterministic, fail-closed re-solve of that VC.
            self.lru.push_back(key);
            self.enforce_capacity();
        }
        self.stats.total_entries = self.entries.len();
    }

    /// Evict least-recently-used entries until at or below `capacity`.
    ///
    /// No-op when `capacity == 0` (unbounded). Eviction is sound: the cache
    /// holds only memoized proved verdicts, so removing one never weakens a
    /// verdict or drops an obligation -- the next lookup simply misses and the
    /// VC is re-solved.
    fn enforce_capacity(&mut self) {
        if self.capacity == 0 {
            return;
        }
        while self.entries.len() > self.capacity {
            match self.lru.pop_front() {
                Some(victim) => {
                    if self.entries.remove(&victim).is_some() {
                        self.locally_validated.remove(&victim);
                        self.stats.evictions += 1;
                    }
                }
                // Recency list exhausted but map still over cap: should be
                // unreachable given lock-step maintenance. Stop rather than spin.
                None => break,
            }
        }
    }

    /// Replay a locally validated cached result, updating hit/miss stats.
    ///
    /// Warmed/deserialized entries intentionally miss until a real solver run
    /// records the same key through [`Self::cache_result`]. Cache persistence is
    /// therefore an optimization hint, never proof authority.
    pub fn replay_result(&mut self, key: &ResultCacheKey) -> Option<&CachedResult> {
        let now = self.current_time_secs();
        let locally_present =
            self.entries.contains_key(key) && self.locally_validated.contains(key);
        if locally_present
            && !self.entries.get(key).is_some_and(|entry| self.entry_is_fresh(entry, now))
        {
            self.remove_entry(key);
        }

        if self.entries.contains_key(key) && self.locally_validated.contains(key) {
            self.stats.hits += 1;
            self.stats.replays += 1;
            // A hit makes this the most-recently-used entry for LRU ordering.
            self.touch(key);
            self.entries.get(key)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Replay the first locally validated result present in `keys`, preserving
    /// key order.
    ///
    /// This records a single logical cache lookup: one hit if any candidate key
    /// is present, otherwise one miss. Use this when a caller has a deterministic
    /// fallback chain and any later key represents the result of running earlier
    /// solvers to non-definitive outcomes.
    pub fn replay_first_result(&mut self, keys: &[ResultCacheKey]) -> Option<&CachedResult> {
        let now = self.current_time_secs();
        let mut hit_index = None;
        for (index, key) in keys.iter().enumerate() {
            if !self.entries.contains_key(key) || !self.locally_validated.contains(key) {
                continue;
            }
            if self.entries.get(key).is_some_and(|entry| self.entry_is_fresh(entry, now)) {
                hit_index = Some(index);
                break;
            }
            self.remove_entry(key);
        }
        if let Some(index) = hit_index {
            self.stats.hits += 1;
            self.stats.replays += 1;
            // A hit makes this the most-recently-used entry for LRU ordering.
            self.touch(&keys[index]);
            self.entries.get(&keys[index])
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Invalidate entries older than `max_age_seconds`. Returns eviction count.
    pub fn invalidate_stale(&mut self, max_age_seconds: u64) -> usize {
        let now = self.current_time_secs();
        let before = self.entries.len();
        self.entries.retain(|_, entry| {
            now.checked_sub(entry.cached_at).is_some_and(|age| age <= max_age_seconds)
        });
        self.locally_validated.retain(|key| self.entries.contains_key(key));
        let evicted = before - self.entries.len();
        // Keep the recency list in lock-step with the surviving entries.
        self.lru.retain(|key| self.entries.contains_key(key));
        self.stats.evictions += evicted;
        self.stats.total_entries = self.entries.len();
        evicted
    }

    /// Invalidate all entries from a specific solver. Returns eviction count.
    pub fn invalidate_by_solver(&mut self, solver: &str) -> usize {
        let before = self.entries.len();
        self.entries.retain(|key, _| key.solver_name != solver);
        self.locally_validated.retain(|key| self.entries.contains_key(key));
        let evicted = before - self.entries.len();
        // Keep the recency list in lock-step with the surviving entries.
        self.lru.retain(|key| self.entries.contains_key(key));
        self.stats.evictions += evicted;
        self.stats.total_entries = self.entries.len();
        evicted
    }

    /// Warm the cache with pre-existing entries (e.g., loaded from disk).
    ///
    /// Honors the entry cap: if the warm set plus existing entries exceed the
    /// bound, the least-recently-used entries are evicted afterwards. Warmed
    /// entries are appended to the recency list in iteration order. Warmed
    /// entries are not replay-authoritative: the first lookup misses, and a
    /// successful local solve promotes its replacement through
    /// [`Self::cache_result`].
    pub fn warm_cache(&mut self, entries: Vec<CachedResult>) {
        for entry in entries {
            let key = entry.key.clone();
            self.locally_validated.remove(&key);
            if self.entries.insert(key.clone(), entry).is_some() {
                self.touch(&key);
            } else {
                self.lru.push_back(key);
            }
        }
        self.enforce_capacity();
        self.stats.total_entries = self.entries.len();
    }

    /// Return current cache statistics.
    #[must_use]
    pub fn cache_stats(&self) -> CacheStats {
        let mut stats = self.stats.clone();
        stats.total_entries = self.entries.len();
        stats
    }

    /// Return the number of cached entries.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Remove all cached entries.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.locally_validated.clear();
        self.lru.clear();
        self.stats.total_entries = 0;
    }

    /// Monotonic timestamp in seconds. In production this would use
    /// `std::time::SystemTime`; here we use a simple epoch-based approach.
    fn current_time_secs(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }
}

/// Hash a formula string into a hex-encoded SHA-256 digest.
///
/// Uses SHA-256 for collision resistance. A 64-bit hash (DefaultHasher/SipHash)
/// has birthday collisions at ~2^32 formulas, which could cause one formula's
/// cached verdict to be returned for a different formula -- a soundness bug.
/// SHA-256 pushes that threshold to ~2^128. See #692.
#[must_use]
pub fn hash_formula(formula: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(formula.as_bytes());
    format!("{:x}", hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_key(formula: &str, solver: &str) -> ResultCacheKey {
        ResultCacheKey { formula_hash: hash_formula(formula), solver_name: solver.to_string() }
    }

    #[test]
    fn test_cache_result_and_replay_hit() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 42, None);

        let result = cache.replay_result(&key);
        assert!(result.is_some());
        let entry = result.unwrap();
        assert_eq!(entry.verdict, "proved");
        assert_eq!(entry.time_ms, 42);
    }

    #[test]
    fn test_cache_result_with_certificate_round_trips_bytes() {
        // Certificate bytes stored at solve time must come back on replay
        // (evidence-equivalence of session replays; see
        // `CachedResult::proof_certificate`).
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("y > 1", "ay");
        let cert: Vec<u8> = b"lrat bytes".to_vec();
        cache.cache_result_with_certificate(
            key.clone(),
            "proved",
            None,
            7,
            None,
            Some(cert.clone()),
        );

        let entry = cache.replay_result(&key).expect("locally validated entry replays");
        assert_eq!(entry.proof_certificate.as_ref(), Some(&cert));

        // The certificate-less path stores None (existing callers unchanged).
        let key2 = make_key("z > 2", "ay");
        cache.cache_result(key2.clone(), "proved", None, 7, None);
        assert!(cache.replay_result(&key2).expect("replays").proof_certificate.is_none());
    }

    #[test]
    fn test_cached_result_legacy_json_without_certificate_field_parses() {
        // Entries serialized before `proof_certificate` existed (or written by
        // older builds) must still deserialize — the field is #[serde(default)].
        let legacy = r#"{
            "key": {"formula_hash": "abc123", "solver_name": "ay"},
            "verdict": "proved",
            "model": null,
            "time_ms": 5,
            "cached_at": 1000
        }"#;
        let entry: CachedResult =
            serde_json::from_str(legacy).expect("legacy JSON without new fields parses");
        assert_eq!(entry.verdict, "proved");
        assert!(entry.strength_json.is_none());
        assert!(entry.proof_certificate.is_none());
    }

    #[test]
    fn test_replay_miss_returns_none() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");

        assert!(cache.replay_result(&key).is_none());
    }

    #[test]
    fn test_replay_first_result_counts_one_logical_lookup() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let first = make_key("x > 0", "primary");
        let second = make_key("x > 0", "fallback");
        cache.cache_result(second.clone(), "proved", None, 42, None);

        let result = cache.replay_first_result(&[first, second]);

        assert!(result.is_some());
        assert_eq!(result.expect("cached fallback").key.solver_name, "fallback");
        let stats = cache.cache_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 0);
    }

    #[test]
    fn test_replay_first_result_misses_once_when_all_candidates_absent() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let first = make_key("x > 0", "primary");
        let second = make_key("x > 0", "fallback");

        assert!(cache.replay_first_result(&[first, second]).is_none());

        let stats = cache.cache_stats();
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn test_replay_first_skips_expired_candidate_and_hits_fresh_fallback() {
        let mut cache = ResultCache::new(CachePolicy::CacheWithTTL(60));
        let first = make_key("x > 0", "primary");
        let second = make_key("x > 0", "fallback");
        cache.cache_result(first.clone(), "proved", None, 1, None);
        cache.cache_result(second.clone(), "proved", None, 2, None);
        cache.entries.get_mut(&first).expect("first exists").cached_at = 1;

        let result = cache.replay_first_result(&[first.clone(), second]);

        assert_eq!(result.expect("fresh fallback remains").key.solver_name, "fallback");
        assert!(!cache.entries.contains_key(&first), "expired candidate is evicted");
        let stats = cache.cache_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 0);
        assert_eq!(stats.evictions, 1);
    }

    #[test]
    fn test_cache_on_success_skips_non_proved() {
        let mut cache = ResultCache::new(CachePolicy::CacheOnSuccess);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "failed", None, 10, None);

        assert_eq!(cache.entry_count(), 0);
        assert!(cache.replay_result(&key).is_none());
    }

    #[test]
    fn test_cache_on_success_stores_proved() {
        let mut cache = ResultCache::new(CachePolicy::CacheOnSuccess);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key).is_some());
    }

    #[test]
    fn test_never_cache_stores_nothing() {
        let mut cache = ResultCache::new(CachePolicy::NeverCache);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_invalidate_stale_removes_old_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");

        // Insert an entry with a very old timestamp by warming.
        let old_entry = CachedResult {
            key: key.clone(),
            verdict: "proved".to_string(),
            model: None,
            time_ms: 10,
            cached_at: 1, // epoch second 1 -- ancient
            strength_json: None,
            proof_certificate: None,
        };
        cache.warm_cache(vec![old_entry]);
        assert_eq!(cache.entry_count(), 1);

        let evicted = cache.invalidate_stale(60);
        assert_eq!(evicted, 1);
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_invalidate_stale_keeps_fresh_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        // Very large TTL -- nothing should be evicted.
        let evicted = cache.invalidate_stale(u64::MAX);
        assert_eq!(evicted, 0);
        assert_eq!(cache.entry_count(), 1);
    }

    #[test]
    fn test_invalidate_by_solver() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key_ay = make_key("x > 0", "ay");
        let key_trust_wp = make_key("x > 0", "trust-wp");
        cache.cache_result(key_ay.clone(), "proved", None, 10, None);
        cache.cache_result(key_trust_wp.clone(), "proved", None, 20, None);
        assert_eq!(cache.entry_count(), 2);

        let evicted = cache.invalidate_by_solver("ay");
        assert_eq!(evicted, 1);
        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key_trust_wp).is_some());
    }

    #[test]
    fn test_warm_cache_loads_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let entries = vec![
            CachedResult {
                key: make_key("a", "ay"),
                verdict: "proved".to_string(),
                model: None,
                time_ms: 1,
                cached_at: 100,
                strength_json: None,
                proof_certificate: None,
            },
            CachedResult {
                key: make_key("b", "ay"),
                verdict: "failed".to_string(),
                model: Some("x=5".to_string()),
                time_ms: 2,
                cached_at: 200,
                strength_json: None,
                proof_certificate: None,
            },
        ];
        cache.warm_cache(entries);
        assert_eq!(cache.entry_count(), 2);
    }

    #[test]
    fn test_clear_removes_all() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        cache.cache_result(make_key("a", "ay"), "proved", None, 1, None);
        cache.cache_result(make_key("b", "ay"), "failed", None, 2, None);
        assert_eq!(cache.entry_count(), 2);

        cache.clear();
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_cache_stats_tracks_hits_and_misses() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        // Miss
        let _ = cache.replay_result(&make_key("unknown", "ay"));
        // Hit
        let _ = cache.replay_result(&key);

        let stats = cache.cache_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.replays, 1);
        assert_eq!(stats.total_entries, 1);
    }

    #[test]
    fn test_cache_stats_tracks_evictions() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let old = CachedResult {
            key: make_key("old", "ay"),
            verdict: "proved".to_string(),
            model: None,
            time_ms: 1,
            cached_at: 1,
            strength_json: None,
            proof_certificate: None,
        };
        cache.warm_cache(vec![old]);
        cache.invalidate_stale(60);

        let stats = cache.cache_stats();
        assert_eq!(stats.evictions, 1);
    }

    #[test]
    fn test_hash_formula_deterministic() {
        let h1 = hash_formula("x > 0 && y < 10");
        let h2 = hash_formula("x > 0 && y < 10");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_hash_formula_different_inputs_differ() {
        let h1 = hash_formula("x > 0");
        let h2 = hash_formula("x < 0");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_hash_formula_returns_hex_string() {
        let h = hash_formula("test");
        assert_eq!(h.len(), 64, "SHA-256 -> 64 hex chars");
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_cache_with_model() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "failed", Some("x=0".to_string()), 5, None);

        let result = cache.replay_result(&key).unwrap();
        assert_eq!(result.model.as_deref(), Some("x=0"));
    }

    #[test]
    fn test_cache_with_ttl_stores_all_verdicts() {
        let mut cache = ResultCache::new(CachePolicy::CacheWithTTL(3600));
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "unknown", None, 100, None);

        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key).is_some());
    }

    #[test]
    fn test_cache_with_ttl_expires_automatically_on_replay() {
        let mut cache = ResultCache::new(CachePolicy::CacheWithTTL(60));
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 100, None);
        cache.entries.get_mut(&key).expect("entry exists").cached_at = 1;

        assert!(cache.replay_result(&key).is_none(), "expired TTL entry must miss");
        assert_eq!(cache.entry_count(), 0, "expired entry is evicted eagerly");
        assert_eq!(cache.cache_stats().evictions, 1);
    }

    #[test]
    fn test_cache_with_ttl_rejects_future_timestamp() {
        let mut cache = ResultCache::new(CachePolicy::CacheWithTTL(u64::MAX));
        let key = make_key("x > 0", "ay");
        cache.cache_result(key.clone(), "proved", None, 100, None);
        cache.entries.get_mut(&key).expect("entry exists").cached_at = u64::MAX;

        assert!(
            cache.replay_result(&key).is_none(),
            "clock rollback or corrupt future timestamp must fail closed"
        );
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_warmed_result_requires_local_solver_validation_before_replay() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "ay");
        cache.warm_cache(vec![CachedResult {
            key: key.clone(),
            verdict: "proved".to_string(),
            model: None,
            time_ms: 1,
            cached_at: 1,
            strength_json: Some("forged-strength".to_string()),
            proof_certificate: None,
        }]);

        assert!(
            cache.replay_result(&key).is_none(),
            "deserialized data must not be proof authority"
        );
        cache.cache_result(key.clone(), "proved", None, 2, None);
        assert!(
            cache.replay_result(&key).is_some(),
            "a result produced in this cache instance may be replayed"
        );
    }

    #[test]
    fn test_lru_cap_evicts_oldest_and_resolve_returns_same_verdict() {
        // Cap of 2: inserting a third distinct key must evict the LRU one.
        let mut cache = ResultCache::with_capacity(CachePolicy::CacheOnSuccess, 2);
        let a = make_key("a", "ay");
        let b = make_key("b", "ay");
        let c = make_key("c", "ay");

        cache.cache_result(a.clone(), "proved", None, 1, None);
        cache.cache_result(b.clone(), "proved", None, 2, None);
        assert_eq!(cache.entry_count(), 2);

        // `a` is now LRU; inserting `c` evicts `a` (oldest), keeps `b` and `c`.
        cache.cache_result(c.clone(), "proved", None, 3, None);
        assert_eq!(cache.entry_count(), 2, "cap holds at 2");
        assert!(cache.replay_result(&a).is_none(), "oldest entry evicted");
        assert!(cache.replay_result(&b).is_some(), "newer entry retained");
        assert!(cache.replay_result(&c).is_some(), "newest entry retained");
        assert_eq!(cache.cache_stats().evictions, 1, "exactly one cap eviction");

        // Soundness: re-solving the evicted VC yields the identical verdict.
        // Eviction only discarded a memo; the deterministic answer is unchanged.
        cache.cache_result(a.clone(), "proved", None, 7, None);
        let replayed = cache.replay_result(&a).expect("re-solved entry present");
        assert_eq!(replayed.verdict, "proved", "re-solve returns same verdict");
    }

    #[test]
    fn test_lru_hit_refreshes_recency() {
        // A hit on the oldest key should protect it from the next eviction.
        let mut cache = ResultCache::with_capacity(CachePolicy::CacheOnSuccess, 2);
        let a = make_key("a", "ay");
        let b = make_key("b", "ay");
        let c = make_key("c", "ay");

        cache.cache_result(a.clone(), "proved", None, 1, None);
        cache.cache_result(b.clone(), "proved", None, 2, None);

        // Touch `a` so `b` becomes the LRU victim instead.
        assert!(cache.replay_result(&a).is_some());

        cache.cache_result(c.clone(), "proved", None, 3, None);
        assert!(cache.replay_result(&a).is_some(), "recently-used `a` survives");
        assert!(cache.replay_result(&b).is_none(), "`b` evicted as LRU");
        assert!(cache.replay_result(&c).is_some());
    }

    #[test]
    fn test_capacity_zero_is_unbounded() {
        let mut cache = ResultCache::with_capacity(CachePolicy::AlwaysCache, 0);
        for i in 0..1000u32 {
            cache.cache_result(make_key(&format!("f{i}"), "ay"), "proved", None, 1, None);
        }
        assert_eq!(cache.entry_count(), 1000, "cap of 0 disables eviction");
        assert_eq!(cache.cache_stats().evictions, 0);
    }

    #[test]
    fn test_re_cache_same_key_does_not_grow_or_evict() {
        let mut cache = ResultCache::with_capacity(CachePolicy::CacheOnSuccess, 2);
        let a = make_key("a", "ay");
        let b = make_key("b", "ay");
        cache.cache_result(a.clone(), "proved", None, 1, None);
        cache.cache_result(b.clone(), "proved", None, 2, None);

        // Re-caching an existing key updates in place; it must not evict.
        cache.cache_result(a.clone(), "proved", None, 99, None);
        assert_eq!(cache.entry_count(), 2);
        assert_eq!(cache.cache_stats().evictions, 0);
        assert_eq!(cache.replay_result(&a).expect("present").time_ms, 99);
    }

    #[test]
    fn test_warm_cache_respects_capacity() {
        let mut cache = ResultCache::with_capacity(CachePolicy::AlwaysCache, 2);
        let entries = vec![
            CachedResult {
                key: make_key("a", "ay"),
                verdict: "proved".to_string(),
                model: None,
                time_ms: 1,
                cached_at: 100,
                strength_json: None,
                proof_certificate: None,
            },
            CachedResult {
                key: make_key("b", "ay"),
                verdict: "proved".to_string(),
                model: None,
                time_ms: 2,
                cached_at: 200,
                strength_json: None,
                proof_certificate: None,
            },
            CachedResult {
                key: make_key("c", "ay"),
                verdict: "proved".to_string(),
                model: None,
                time_ms: 3,
                cached_at: 300,
                strength_json: None,
                proof_certificate: None,
            },
        ];
        cache.warm_cache(entries);
        assert_eq!(cache.entry_count(), 2, "warm honors the cap");
        // First-inserted ("a") is LRU and evicted; "b","c" survive.
        assert!(!cache.entries.contains_key(&make_key("a", "ay")));
        assert!(cache.entries.contains_key(&make_key("b", "ay")));
        assert!(cache.entries.contains_key(&make_key("c", "ay")));
        assert!(
            cache.replay_result(&make_key("b", "ay")).is_none(),
            "warm data remains non-authoritative until locally validated"
        );
    }

    #[test]
    fn test_invalidate_keeps_lru_consistent() {
        // After solver invalidation the recency list must not reference dead
        // keys, otherwise a later eviction could mis-target.
        let mut cache = ResultCache::with_capacity(CachePolicy::AlwaysCache, 3);
        cache.cache_result(make_key("a", "ay"), "proved", None, 1, None);
        cache.cache_result(make_key("b", "trust-wp"), "proved", None, 2, None);
        cache.cache_result(make_key("c", "ay"), "proved", None, 3, None);

        let evicted = cache.invalidate_by_solver("ay");
        assert_eq!(evicted, 2);
        assert_eq!(cache.lru.len(), cache.entries.len(), "lru tracks live entries");
        assert!(cache.replay_result(&make_key("b", "trust-wp")).is_some());
    }
}
