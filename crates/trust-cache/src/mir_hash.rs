// trust-cache/mir_hash.rs: MIR structural hashing and per-function incremental cache
//
// Trust: Provides MirHash-based incremental verification so that unchanged
// functions are skipped entirely. Complements the dependency-aware
// IncrementalVerifier (incremental.rs) by adding structural MIR hashing,
// a standalone IncrementalCache with persistence, and a DependencyGraph
// for tracking which functions depend on which.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use std::path::Path;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{FunctionVerdict, VerifiableBody};

// Trust: MirHash — structural hash of a MIR body for change detection.
/// A stable 64-bit structural fingerprint of a function's MIR body.
///
/// Used as a fast fingerprint to detect whether a function's body has changed
/// since the last verification run. The value is the first 64 bits of a
/// domain-separated SHA-256 digest, so it is stable across Rust releases.
/// It is only a change detector, never proof authentication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MirHash(pub u64);

impl MirHash {
    /// Extract the inner u64 value.
    #[must_use]
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

impl From<u64> for MirHash {
    fn from(val: u64) -> Self {
        MirHash(val)
    }
}

impl std::fmt::Display for MirHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MirHash({:#018x})", self.0)
    }
}

// Trust: Compute a structural hash of a MIR body keyed by function name.
/// Compute a structural hash of a function's MIR body.
///
/// Hashes the function name together with the serde-serialized MIR body to
/// produce a deterministic 64-bit fingerprint. The persisted value is a
/// compact change detector derived from SHA-256; it is not proof authority.
#[must_use]
pub fn compute_mir_hash(func_name: &str, mir_body: &VerifiableBody) -> MirHash {
    try_compute_mir_hash(func_name, mir_body).expect(
        "VerifiableBody contains only the canonical serializable Trust model; \
         refusing to manufacture cache identity after serialization failure",
    )
}

/// Fallible MIR fingerprint construction for callers that can propagate an
/// internal model-serialization error.
///
/// The legacy implementation used `DefaultHasher` (whose algorithm is not a
/// stable persistence contract) and replaced serialization failures with an
/// empty string. That made unrelated failures share one cache key. This form
/// fails closed and hashes length-delimited fields under an explicit schema
/// domain.
pub fn try_compute_mir_hash(
    func_name: &str,
    mir_body: &VerifiableBody,
) -> Result<MirHash, serde_json::Error> {
    use sha2::{Digest, Sha256};

    let body_json = serde_json::to_vec(mir_body)?;
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cache/mir-hash/v3\0");
    hasher.update((func_name.len() as u64).to_be_bytes());
    hasher.update(func_name.as_bytes());
    hasher.update((body_json.len() as u64).to_be_bytes());
    hasher.update(&body_json);
    let digest = hasher.finalize();
    Ok(MirHash(u64::from_be_bytes(
        digest[..8].try_into().expect("SHA-256 digest has at least eight bytes"),
    )))
}

// Trust: VerificationResult — cached outcome for a single function.
/// Cached verification result for a single function.
///
/// Stores the verdict along with obligation counts so that cache consumers
/// can reconstruct summary statistics without re-running verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationResult {
    /// The overall verdict for this function.
    pub verdict: FunctionVerdict,
    /// Total number of verification obligations.
    pub total_obligations: usize,
    /// Number of obligations proved safe.
    pub proved: usize,
    /// Number of obligations that failed (counterexample found).
    pub failed: usize,
    /// Number of obligations with unknown outcome.
    pub unknown: usize,
}

impl VerificationResult {
    /// Create a new verification result.
    pub fn new(
        verdict: FunctionVerdict,
        total_obligations: usize,
        proved: usize,
        failed: usize,
        unknown: usize,
    ) -> Self {
        Self { verdict, total_obligations, proved, failed, unknown }
    }

    /// Create a result representing a fully verified function.
    #[must_use]
    pub fn verified(total: usize) -> Self {
        Self {
            verdict: FunctionVerdict::Verified,
            total_obligations: total,
            proved: total,
            failed: 0,
            unknown: 0,
        }
    }

    /// Whether replaying this user-writable record would assert proof or a
    /// successful runtime-check conclusion. Zero obligations is itself an
    /// authoritative conclusion and must be re-established in-process.
    fn claims_proof_authority(&self) -> bool {
        self.total_obligations == 0
            || self.proved != 0
            || matches!(
                self.verdict,
                FunctionVerdict::Verified
                    | FunctionVerdict::RuntimeChecked
                    | FunctionVerdict::NoObligations
            )
    }
}

// Trust: Errors for MIR-hash incremental cache operations.
/// Errors that can occur during incremental cache I/O.
#[derive(Debug, Error)]
pub enum MirHashCacheError {
    /// I/O error reading or writing cache file.
    #[error("mir hash cache I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Deserialization error loading cache file.
    #[error("mir hash cache deserialization error: {0}")]
    Deserialize(#[from] serde_json::Error),
}

// Trust: On-disk format for the MIR hash cache.
/// Persistent format for the incremental cache.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CacheFile {
    /// Schema version for forward compatibility.
    version: u32,
    /// Map from function name to (MirHash, VerificationResult).
    entries: FxHashMap<String, (MirHash, VerificationResult)>,
    /// Dependency graph edges: caller -> set of callees.
    #[serde(default)]
    dependencies: FxHashMap<String, Vec<String>>,
}

/// Current schema version for the MIR hash cache file.
const MIR_HASH_CACHE_VERSION: u32 = 3;

impl Default for CacheFile {
    fn default() -> Self {
        CacheFile {
            version: MIR_HASH_CACHE_VERSION,
            entries: FxHashMap::default(),
            dependencies: FxHashMap::default(),
        }
    }
}

// Trust: IncrementalCache — MIR-hash-based per-function cache with persistence.
/// MIR-hash-based incremental verification cache.
///
/// Maintains a mapping from function name to `(MirHash, VerificationResult)`.
/// On each compilation, the caller computes the current `MirHash` for each
/// function and queries the cache: if the hash matches, the cached result is
/// returned and verification is skipped.
pub struct IncrementalCache {
    /// Map from function name to (hash, result).
    entries: FxHashMap<String, (MirHash, VerificationResult)>,
    /// Session hit counter.
    hits: usize,
    /// Session miss counter.
    misses: usize,
    /// Session skip counter (functions skipped due to cache hit).
    skipped: usize,
}

impl IncrementalCache {
    /// Create a new empty incremental cache.
    pub fn new() -> Self {
        Self { entries: FxHashMap::default(), hits: 0, misses: 0, skipped: 0 }
    }

    /// Check whether a function has changed since the last cached run.
    ///
    /// Returns `true` if the function is not in the cache or if its MIR hash
    /// differs from `current_hash`. Returns `false` (unchanged) if the hash
    /// matches.
    #[must_use]
    pub fn is_changed(&self, func_name: &str, current_hash: MirHash) -> bool {
        match self.entries.get(func_name) {
            Some((cached_hash, _)) => *cached_hash != current_hash,
            None => true,
        }
    }

    /// Look up a cached verification result for a function.
    ///
    /// Returns `Some(&VerificationResult)` only if the function is in the cache
    /// AND its stored hash matches `current_hash`. Returns `None` otherwise.
    #[must_use]
    pub fn get_cached_result(
        &self,
        func_name: &str,
        current_hash: MirHash,
    ) -> Option<&VerificationResult> {
        self.entries
            .get(func_name)
            .filter(|(cached_hash, _)| *cached_hash == current_hash)
            .map(|(_, result)| result)
    }

    /// Record a verification result for a function.
    ///
    /// Overwrites any previous entry for `func_name`.
    pub fn record(&mut self, func_name: &str, hash: MirHash, result: VerificationResult) {
        self.entries.insert(func_name.to_string(), (hash, result));
    }

    /// Increment the hit counter (call when a cache lookup succeeds).
    pub fn record_hit(&mut self) {
        self.hits += 1;
        self.skipped += 1;
    }

    /// Increment the miss counter (call when a cache lookup fails).
    pub fn record_miss(&mut self) {
        self.misses += 1;
    }

    /// Number of cache hits this session.
    #[must_use]
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Number of cache misses this session.
    #[must_use]
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Number of functions skipped this session.
    #[must_use]
    pub fn skipped(&self) -> usize {
        self.skipped
    }

    /// Number of entries in the cache.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Remove a single function from the cache.
    ///
    /// Returns `true` if the entry existed.
    pub fn invalidate(&mut self, func_name: &str) -> bool {
        self.entries.remove(func_name).is_some()
    }

    /// Remove all entries from the cache.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Save conservative, non-proof outcomes to a JSON file on disk.
    ///
    /// Proof and runtime-check conclusions remain in-memory only. This cache is
    /// user-writable and a 64-bit structural hash is not proof authentication;
    /// a later process must independently re-establish every successful result.
    pub fn save(&self, path: &Path) -> Result<(), MirHashCacheError> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let file = CacheFile {
            version: MIR_HASH_CACHE_VERSION,
            entries: self
                .entries
                .iter()
                .filter(|(_, (_, result))| !result.claims_proof_authority())
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect(),
            dependencies: FxHashMap::default(),
        };
        let json = serde_json::to_string_pretty(&file)?;
        crate::coordination::atomic_write_replace(path, json.as_bytes())?;
        Ok(())
    }

    /// Load a cache from a JSON file on disk.
    ///
    /// Proof-shaped records are filtered again on read to reject forged or
    /// legacy data. Returns an empty cache if the file does not exist, is
    /// corrupt, or has a version mismatch.
    pub fn load(path: &Path) -> Self {
        if !path.exists() {
            return Self::new();
        }
        let Ok(contents) = std::fs::read_to_string(path) else {
            return Self::new();
        };
        match serde_json::from_str::<CacheFile>(&contents) {
            Ok(cf) if cf.version == MIR_HASH_CACHE_VERSION => {
                let entries = cf
                    .entries
                    .into_iter()
                    .filter(|(_, (_, result))| !result.claims_proof_authority())
                    .collect();
                Self { entries, hits: 0, misses: 0, skipped: 0 }
            }
            _ => Self::new(),
        }
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{} entries, {} hits, {} misses, {} skipped",
            self.entries.len(),
            self.hits,
            self.misses,
            self.skipped,
        )
    }
}

impl Default for IncrementalCache {
    fn default() -> Self {
        Self::new()
    }
}

// Trust: DependencyGraph — tracks which functions depend on which.
/// Tracks function-level dependencies for incremental verification.
///
/// When function A calls function B, A depends on B. If B's MIR changes,
/// A may need re-verification because its verification might have relied
/// on B's specification or behavior.
///
/// The graph supports both forward (callees) and reverse (callers) lookups,
/// and transitive closure for computing full invalidation sets.
pub struct DependencyGraph {
    /// Forward edges: function -> set of functions it calls.
    forward: FxHashMap<String, FxHashSet<String>>,
    /// Reverse edges: function -> set of functions that call it.
    reverse: FxHashMap<String, FxHashSet<String>>,
}

impl DependencyGraph {
    /// Create an empty dependency graph.
    pub fn new() -> Self {
        Self { forward: FxHashMap::default(), reverse: FxHashMap::default() }
    }

    /// Add an edge: `caller` depends on `callee`.
    pub fn add_edge(&mut self, caller: &str, callee: &str) {
        self.forward.entry(caller.to_string()).or_default().insert(callee.to_string());
        self.reverse.entry(callee.to_string()).or_default().insert(caller.to_string());
    }

    /// Get the direct callees of a function.
    #[must_use]
    pub fn callees(&self, func: &str) -> FxHashSet<String> {
        self.forward.get(func).cloned().unwrap_or_default()
    }

    /// Get the direct callers of a function.
    #[must_use]
    pub fn callers(&self, func: &str) -> FxHashSet<String> {
        self.reverse.get(func).cloned().unwrap_or_default()
    }

    /// Compute the transitive closure of all functions affected by a change
    /// to `changed_func`. Includes `changed_func` itself plus all transitive
    /// callers.
    #[must_use]
    pub fn transitive_dependents(&self, changed_func: &str) -> FxHashSet<String> {
        let mut affected = FxHashSet::default();
        let mut queue = VecDeque::new();
        queue.push_back(changed_func.to_string());
        affected.insert(changed_func.to_string());

        while let Some(func) = queue.pop_front() {
            if let Some(callers) = self.reverse.get(&func) {
                for caller in callers {
                    if affected.insert(caller.clone()) {
                        queue.push_back(caller.clone());
                    }
                }
            }
        }

        affected
    }

    /// Compute the transitive closure of dependents for multiple changed
    /// functions simultaneously.
    #[must_use]
    pub fn transitive_dependents_of_all(&self, changed: &[&str]) -> FxHashSet<String> {
        let mut affected = FxHashSet::default();
        for func in changed {
            affected.extend(self.transitive_dependents(func));
        }
        affected
    }

    /// Number of functions tracked in the graph (as callers or callees).
    #[must_use]
    pub fn node_count(&self) -> usize {
        let mut nodes = FxHashSet::default();
        for (k, vs) in &self.forward {
            nodes.insert(k.as_str());
            for v in vs {
                nodes.insert(v.as_str());
            }
        }
        nodes.len()
    }

    /// Number of dependency edges in the graph.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.forward.values().map(|vs| vs.len()).sum()
    }

    /// Whether the graph has no edges.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.forward.is_empty()
    }

    /// Clear all edges.
    pub fn clear(&mut self) {
        self.forward.clear();
        self.reverse.clear();
    }

    /// Serialize the dependency graph to JSON for persistence.
    #[must_use]
    pub fn to_json(&self) -> FxHashMap<String, Vec<String>> {
        self.forward.iter().map(|(k, vs)| (k.clone(), vs.iter().cloned().collect())).collect()
    }

    /// Deserialize a dependency graph from JSON.
    pub fn from_json(data: &FxHashMap<String, Vec<String>>) -> Self {
        let mut graph = Self::new();
        for (caller, callees) in data {
            for callee in callees {
                graph.add_edge(caller, callee);
            }
        }
        graph
    }
}

impl Default for DependencyGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BasicBlock, BlockId, FunctionVerdict, Terminator, Ty, VerifiableBody};

    use super::*;

    // -- Helper to build a simple MIR body --

    fn make_body(arg_count: usize) -> VerifiableBody {
        VerifiableBody {
            locals: vec![],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty: Ty::Unit,
        }
    }

    fn make_body_with_args(arg_count: usize, return_ty: Ty) -> VerifiableBody {
        VerifiableBody {
            locals: vec![],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty,
        }
    }

    // -----------------------------------------------------------------------
    // MirHash tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_mir_hash_deterministic() {
        let body = make_body(0);
        let h1 = compute_mir_hash("foo", &body);
        let h2 = compute_mir_hash("foo", &body);
        assert_eq!(h1, h2, "mir hash must be deterministic for the same input");
    }

    #[test]
    fn test_mir_hash_differs_by_name() {
        let body = make_body(0);
        let h1 = compute_mir_hash("foo", &body);
        let h2 = compute_mir_hash("bar", &body);
        assert_ne!(h1, h2, "different function names should produce different hashes");
    }

    #[test]
    fn test_mir_hash_differs_by_body() {
        let body1 = make_body(0);
        let body2 = make_body(2);
        let h1 = compute_mir_hash("foo", &body1);
        let h2 = compute_mir_hash("foo", &body2);
        assert_ne!(h1, h2, "different bodies should produce different hashes");
    }

    #[test]
    fn test_mir_hash_display() {
        let h = MirHash(0xDEADBEEF);
        let display = format!("{h}");
        assert!(display.contains("deadbeef"), "display should show hex: {display}");
    }

    #[test]
    fn test_mir_hash_from_u64() {
        let h: MirHash = 42u64.into();
        assert_eq!(h.as_u64(), 42);
    }

    // -----------------------------------------------------------------------
    // IncrementalCache basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_new_is_empty() {
        let cache = IncrementalCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_cache_record_and_lookup() {
        let mut cache = IncrementalCache::new();
        let hash = MirHash(123);
        let result = VerificationResult::verified(3);

        cache.record("foo", hash, result.clone());

        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);
        assert!(!cache.is_changed("foo", hash));
        assert_eq!(cache.get_cached_result("foo", hash), Some(&result));
    }

    #[test]
    fn test_cache_is_changed_detects_new_function() {
        let cache = IncrementalCache::new();
        assert!(cache.is_changed("unknown_func", MirHash(999)));
    }

    #[test]
    fn test_cache_is_changed_detects_hash_mismatch() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(100), VerificationResult::verified(1));

        assert!(cache.is_changed("foo", MirHash(200)), "different hash should be a change");
        assert!(!cache.is_changed("foo", MirHash(100)), "same hash should not be a change");
    }

    #[test]
    fn test_cache_get_cached_result_returns_none_on_mismatch() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(100), VerificationResult::verified(1));

        assert!(cache.get_cached_result("foo", MirHash(200)).is_none());
        assert!(cache.get_cached_result("bar", MirHash(100)).is_none());
    }

    #[test]
    fn test_cache_record_overwrites() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(1), VerificationResult::verified(1));
        cache.record(
            "foo",
            MirHash(2),
            VerificationResult::new(FunctionVerdict::HasViolations, 3, 1, 2, 0),
        );

        assert_eq!(cache.len(), 1);
        assert!(cache.get_cached_result("foo", MirHash(1)).is_none());
        let result = cache.get_cached_result("foo", MirHash(2)).unwrap();
        assert_eq!(result.verdict, FunctionVerdict::HasViolations);
    }

    // -----------------------------------------------------------------------
    // IncrementalCache invalidation
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_invalidate_single() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(1), VerificationResult::verified(1));
        cache.record("bar", MirHash(2), VerificationResult::verified(1));

        assert!(cache.invalidate("foo"));
        assert!(!cache.invalidate("foo")); // already removed
        assert_eq!(cache.len(), 1);
        assert!(cache.is_changed("foo", MirHash(1)));
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(1), VerificationResult::verified(1));
        cache.record("bar", MirHash(2), VerificationResult::verified(2));

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    // -----------------------------------------------------------------------
    // IncrementalCache statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_hit_miss_counters() {
        let mut cache = IncrementalCache::new();
        cache.record_hit();
        cache.record_hit();
        cache.record_miss();

        assert_eq!(cache.hits(), 2);
        assert_eq!(cache.misses(), 1);
        assert_eq!(cache.skipped(), 2);
    }

    #[test]
    fn test_cache_summary_format() {
        let mut cache = IncrementalCache::new();
        cache.record("foo", MirHash(1), VerificationResult::verified(1));
        cache.record_hit();
        cache.record_miss();

        let summary = cache.summary();
        assert!(summary.contains("1 entries"), "summary: {summary}");
        assert!(summary.contains("1 hits"), "summary: {summary}");
        assert!(summary.contains("1 misses"), "summary: {summary}");
    }

    // -----------------------------------------------------------------------
    // IncrementalCache persistence
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_save_and_load() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mir_hash_cache.json");

        // Save
        {
            let mut cache = IncrementalCache::new();
            cache.record("foo", MirHash(100), VerificationResult::verified(3));
            cache.record(
                "bar",
                MirHash(200),
                VerificationResult::new(FunctionVerdict::HasViolations, 5, 0, 3, 2),
            );
            cache.save(&path).unwrap();
        }

        // Load
        {
            let cache = IncrementalCache::load(&path);
            assert_eq!(cache.len(), 1);
            assert!(
                cache.is_changed("foo", MirHash(100)),
                "a later process must re-establish successful proof results"
            );
            assert!(!cache.is_changed("bar", MirHash(200)));

            assert!(cache.get_cached_result("foo", MirHash(100)).is_none());

            let bar_result = cache.get_cached_result("bar", MirHash(200)).unwrap();
            assert_eq!(bar_result.verdict, FunctionVerdict::HasViolations);
            assert_eq!(bar_result.failed, 3);
        }
    }

    #[test]
    fn test_cache_load_filters_forged_zero_obligation_result() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("forged-zero-obligations.json");
        let mut entries = FxHashMap::default();
        entries.insert(
            "forged".to_string(),
            (MirHash(42), VerificationResult::new(FunctionVerdict::Inconclusive, 0, 0, 0, 0)),
        );
        let file = CacheFile {
            version: MIR_HASH_CACHE_VERSION,
            entries,
            dependencies: FxHashMap::default(),
        };
        std::fs::write(&path, serde_json::to_vec(&file).unwrap()).unwrap();

        let cache = IncrementalCache::load(&path);
        assert!(
            cache.get_cached_result("forged", MirHash(42)).is_none(),
            "disk JSON cannot authorize a zero-obligation conclusion"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_cache_save_replaces_symlink_without_truncating_target() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mir-cache.json");
        let victim = dir.path().join("victim.txt");
        std::fs::write(&victim, b"do not overwrite").unwrap();
        symlink(&victim, &path).unwrap();

        let mut cache = IncrementalCache::new();
        cache.record(
            "failed",
            MirHash(1),
            VerificationResult::new(FunctionVerdict::HasViolations, 1, 0, 1, 0),
        );
        cache.save(&path).unwrap();

        assert_eq!(std::fs::read(&victim).unwrap(), b"do not overwrite");
        assert!(!std::fs::symlink_metadata(&path).unwrap().file_type().is_symlink());
        assert!(IncrementalCache::load(&path).get_cached_result("failed", MirHash(1)).is_some());
    }

    #[test]
    fn test_cache_load_missing_file() {
        let cache = IncrementalCache::load(Path::new("/nonexistent/path/cache.json"));
        assert!(cache.is_empty());
    }

    #[test]
    fn test_cache_load_corrupt_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("corrupt.json");
        std::fs::write(&path, "not valid json{{{").unwrap();

        let cache = IncrementalCache::load(&path);
        assert!(cache.is_empty(), "corrupt file should produce empty cache");
    }

    #[test]
    fn test_cache_load_version_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("old_version.json");
        std::fs::write(&path, r#"{"version": 999, "entries": {}}"#).unwrap();

        let cache = IncrementalCache::load(&path);
        assert!(cache.is_empty(), "version mismatch should produce empty cache");
    }

    #[test]
    fn test_cache_save_creates_parent_dirs() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("nested").join("deep").join("cache.json");

        let mut cache = IncrementalCache::new();
        cache.record("f", MirHash(1), VerificationResult::verified(1));
        cache.save(&path).unwrap();
        assert!(path.exists());
    }

    // -----------------------------------------------------------------------
    // DependencyGraph tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_dep_graph_empty() {
        let graph = DependencyGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn test_dep_graph_add_edge() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");

        assert_eq!(graph.callees("A"), ["B".to_string()].into_iter().collect::<FxHashSet<_>>());
        assert_eq!(graph.callers("B"), ["A".to_string()].into_iter().collect::<FxHashSet<_>>());
        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 1);
    }

    #[test]
    fn test_dep_graph_transitive_dependents() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");
        graph.add_edge("B", "C");

        let affected = graph.transitive_dependents("C");
        assert!(affected.contains("A"));
        assert!(affected.contains("B"));
        assert!(affected.contains("C"));
        assert_eq!(affected.len(), 3);
    }

    #[test]
    fn test_dep_graph_diamond() {
        let mut graph = DependencyGraph::new();
        // A -> B -> D
        // A -> C -> D
        graph.add_edge("A", "B");
        graph.add_edge("A", "C");
        graph.add_edge("B", "D");
        graph.add_edge("C", "D");

        let affected = graph.transitive_dependents("D");
        assert_eq!(affected.len(), 4, "all four nodes should be affected: {affected:?}");
    }

    #[test]
    fn test_dep_graph_independent_subtree() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");
        graph.add_edge("C", "D"); // independent

        let affected = graph.transitive_dependents("B");
        assert!(affected.contains("A"));
        assert!(affected.contains("B"));
        assert!(!affected.contains("C"));
        assert!(!affected.contains("D"));
    }

    #[test]
    fn test_dep_graph_transitive_dependents_of_all() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");
        graph.add_edge("C", "D");

        let affected = graph.transitive_dependents_of_all(&["B", "D"]);
        assert_eq!(affected.len(), 4);
    }

    #[test]
    fn test_dep_graph_clear() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");
        graph.clear();
        assert!(graph.is_empty());
        assert_eq!(graph.node_count(), 0);
    }

    #[test]
    fn test_dep_graph_json_roundtrip() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "B");
        graph.add_edge("A", "C");
        graph.add_edge("B", "C");

        let json = graph.to_json();
        let graph2 = DependencyGraph::from_json(&json);

        assert_eq!(graph2.edge_count(), 3);
        assert_eq!(
            graph2.callees("A"),
            ["B".to_string(), "C".to_string()].into_iter().collect::<FxHashSet<_>>()
        );
        assert_eq!(
            graph2.callers("C"),
            ["A".to_string(), "B".to_string()].into_iter().collect::<FxHashSet<_>>()
        );
    }

    #[test]
    fn test_dep_graph_self_loop() {
        let mut graph = DependencyGraph::new();
        graph.add_edge("A", "A"); // recursive function

        let affected = graph.transitive_dependents("A");
        assert_eq!(affected.len(), 1);
        assert!(affected.contains("A"));
    }

    // -----------------------------------------------------------------------
    // Integration: IncrementalCache + DependencyGraph
    // -----------------------------------------------------------------------

    #[test]
    fn test_incremental_workflow() {
        // Simulate a two-compilation incremental workflow:
        // 1. First compilation: verify all, cache results
        // 2. Second compilation: only re-verify changed functions + dependents

        let mut cache = IncrementalCache::new();
        let mut deps = DependencyGraph::new();

        // First compilation: A calls B, both verified
        deps.add_edge("A", "B");
        let body_a = make_body(1);
        let body_b = make_body(0);
        let hash_a = compute_mir_hash("A", &body_a);
        let hash_b = compute_mir_hash("B", &body_b);

        cache.record("A", hash_a, VerificationResult::verified(2));
        cache.record("B", hash_b, VerificationResult::verified(1));

        // Second compilation: B changed, A did not
        let body_b_v2 = make_body_with_args(0, Ty::Bool);
        let hash_b_v2 = compute_mir_hash("B", &body_b_v2);

        // Check what changed
        let a_changed = cache.is_changed("A", hash_a);
        let b_changed = cache.is_changed("B", hash_b_v2);
        assert!(!a_changed, "A should not be changed (same hash)");
        assert!(b_changed, "B should be changed (different hash)");

        // Find all affected functions via dependency graph
        let affected = deps.transitive_dependents("B");
        assert!(affected.contains("A"), "A depends on B, so it's affected");
        assert!(affected.contains("B"));

        // Invalidate affected
        for func in &affected {
            cache.invalidate(func);
        }

        // A and B both need re-verification
        assert!(cache.is_changed("A", hash_a));
        assert!(cache.is_changed("B", hash_b_v2));
    }

    #[test]
    fn test_verification_result_new() {
        let r = VerificationResult::new(FunctionVerdict::Inconclusive, 10, 5, 2, 3);
        assert_eq!(r.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(r.total_obligations, 10);
        assert_eq!(r.proved, 5);
        assert_eq!(r.failed, 2);
        assert_eq!(r.unknown, 3);
    }

    #[test]
    fn test_verification_result_verified_shorthand() {
        let r = VerificationResult::verified(7);
        assert_eq!(r.verdict, FunctionVerdict::Verified);
        assert_eq!(r.total_obligations, 7);
        assert_eq!(r.proved, 7);
        assert_eq!(r.failed, 0);
        assert_eq!(r.unknown, 0);
    }

    #[test]
    fn test_mir_hash_differs_by_return_type() {
        let body1 = make_body_with_args(0, Ty::Unit);
        let body2 = make_body_with_args(0, Ty::Bool);
        let h1 = compute_mir_hash("f", &body1);
        let h2 = compute_mir_hash("f", &body2);
        assert_ne!(h1, h2, "different return types should produce different hashes");
    }
}
