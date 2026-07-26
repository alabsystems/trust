//! [`VerificationCache`] — the public incremental verification cache.
//!
//! Stores verification results keyed by function def_path and content hash.
//! Proof-bearing results may be skipped only after they were independently
//! produced/revalidated in this process. User-writable disk records are useful
//! for non-proof metadata and invalidation, but are never proof authority by
//! themselves.
//!
//! Supports coordinated access for concurrent compilations:
//! use [`VerificationCache::load_coordinated`] and
//! [`VerificationCache::save_coordinated`] for file-locking and content-hash
//! validation. The original [`VerificationCache::load`] and
//! [`VerificationCache::save`] methods remain available for single-process
//! use or backward compatibility.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use thiserror::Error;
use trust_types::fx::FxHashSet;
use trust_types::{FunctionVerdict, TransportObligationResult, VerifiableFunction};

use crate::entry::{CACHE_VERSION, CacheEntry, CacheFile, CacheLookup};
use crate::fingerprint::{compute_content_hash, now_unix_secs};
use crate::{coordination, integrity};

/// Errors from cache operations.
#[derive(Debug, Error)]
pub enum CacheError {
    #[error("cache I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("cache deserialization error: {0}")]
    Deserialize(#[from] serde_json::Error),
}

/// Incremental verification cache.
///
/// Stores verification results keyed by function def_path and content hash.
/// Matching proof-bearing entries can be skipped only after `store` attests
/// that this process independently produced/revalidated them. Loaded disk
/// records never receive that authority implicitly.
///
/// Supports coordinated access for concurrent compilations:
/// use [`VerificationCache::load_coordinated`] and [`VerificationCache::save_coordinated`]
/// for file-locking and content-hash validation. The original [`VerificationCache::load`]
/// and [`VerificationCache::save`] methods remain available for single-process use or
/// backward compatibility.
pub struct VerificationCache {
    path: PathBuf,
    data: CacheFile,
    hits: usize,
    misses: usize,
    /// Whether this process has made a real in-memory cache mutation that has
    /// not been successfully persisted.
    dirty: bool,
    /// Locally removed keys that must be removed from an on-disk cache during a
    /// coordinated merge.
    removed_def_paths: FxHashSet<String>,
    /// A full invalidation happened locally; coordinated save should ignore all
    /// existing on-disk entries before applying this cache's entries.
    removed_all: bool,
    /// The strongest retain-only allowlist applied locally. Used during
    /// coordinated merge so stale on-disk keys are not reintroduced.
    retained_def_paths: Option<FxHashSet<String>>,
    /// SHA-256 hash of the cache file contents at load time.
    /// Used for content-hash-based invalidation in coordinated mode.
    /// Empty if the cache was created in-memory or loaded without coordination.
    content_hash_at_load: String,
    /// Entries independently produced/revalidated during this process.
    ///
    /// This set is intentionally never serialized. The on-disk HMAC key is
    /// derived from public/local material and is forgeable by a writer who can
    /// edit the cache, so loading a valid tag cannot confer proof authority.
    /// A proof-bearing disk entry remains a miss until `store` records the
    /// result of a fresh in-process verification.
    session_validated_def_paths: FxHashSet<String>,
}

impl VerificationCache {
    /// Load or create a cache at the given path.
    ///
    /// Verifies the HMAC-SHA256 compatibility tag on load. If the tag is
    /// missing, invalid, or does not match, the cache is discarded and a fresh
    /// one is created. A valid tag detects corruption/incompatible producers;
    /// it does not authenticate a local writer, so loaded proof claims remain
    /// ineligible for replay until independently revalidated in this process.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CacheError> {
        let path = path.as_ref().to_path_buf();
        let data = if path.exists() {
            let contents = std::fs::read_to_string(&path)?;
            match serde_json::from_str::<CacheFile>(&contents) {
                Ok(cf) if cf.version == CACHE_VERSION => {
                    // Verify the HMAC compatibility/corruption tag.
                    match serde_json::to_string(&cf.entries) {
                        Ok(entries_json) => {
                            let key = integrity::derive_cache_key();
                            if cf.hmac.is_empty()
                                || !integrity::verify_hmac(&key, entries_json.as_bytes(), &cf.hmac)
                            {
                                // Tag missing or invalid: start fresh.
                                CacheFile::default()
                            } else {
                                cf
                            }
                        }
                        // A cache record that cannot reproduce its signed bytes
                        // has no valid identity. Never verify an empty fallback.
                        Err(_) => CacheFile::default(),
                    }
                }
                // Version mismatch or corrupt: start fresh
                _ => CacheFile::default(),
            }
        } else {
            CacheFile::default()
        };
        Ok(VerificationCache {
            path,
            data,
            hits: 0,
            misses: 0,
            dirty: false,
            removed_def_paths: FxHashSet::default(),
            removed_all: false,
            retained_def_paths: None,
            content_hash_at_load: String::new(),
            session_validated_def_paths: FxHashSet::default(),
        })
    }

    /// Create an empty in-memory cache (no file backing).
    pub fn in_memory() -> Self {
        VerificationCache {
            path: PathBuf::new(),
            data: CacheFile::default(),
            hits: 0,
            misses: 0,
            dirty: false,
            removed_def_paths: FxHashSet::default(),
            removed_all: false,
            retained_def_paths: None,
            content_hash_at_load: String::new(),
            session_validated_def_paths: FxHashSet::default(),
        }
    }

    /// Load or create a cache at the given path with file locking.
    ///
    /// Acquires a shared (read) lock on the cache file before reading.
    /// The lock is released after loading. Records the content hash at
    /// load time for use by [`Self::save_coordinated`].
    ///
    /// If the file does not exist, returns an empty cache (no lock needed).
    pub fn load_coordinated(
        path: impl AsRef<Path>,
        config: &coordination::CoordinationConfig,
    ) -> Result<Self, CacheError> {
        let path = path.as_ref().to_path_buf();
        if !path.exists() {
            return Ok(VerificationCache {
                path,
                data: CacheFile::default(),
                hits: 0,
                misses: 0,
                dirty: false,
                removed_def_paths: FxHashSet::default(),
                removed_all: false,
                retained_def_paths: None,
                content_hash_at_load: String::new(),
                session_validated_def_paths: FxHashSet::default(),
            });
        }

        let (contents, content_hash, _guard) = coordination::coordinated_read(&path, config)
            .map_err(|e| CacheError::Io(std::io::Error::other(e.to_string())))?;
        // _guard is dropped here, releasing the shared lock.

        let data = verified_cache_file_from_str(&contents).unwrap_or_default();

        Ok(VerificationCache {
            path,
            data,
            hits: 0,
            misses: 0,
            dirty: false,
            removed_def_paths: FxHashSet::default(),
            removed_all: false,
            retained_def_paths: None,
            content_hash_at_load: content_hash,
            session_validated_def_paths: FxHashSet::default(),
        })
    }

    /// Write the cache to disk with file locking and content-hash validation.
    ///
    /// Acquires an exclusive (write) lock before writing. While holding that lock,
    /// reads the current on-disk cache and merges in this process's local changes.
    /// Concurrent non-overlapping entries are preserved, and local entries take
    /// precedence for matching def_paths.
    ///
    /// Uses atomic write (write to temp, then rename) to prevent readers from
    /// seeing partial data.
    pub fn save_coordinated(
        &mut self,
        config: &coordination::CoordinationConfig,
    ) -> Result<(), CacheError> {
        if self.path.as_os_str().is_empty() {
            self.mark_clean();
            return Ok(()); // in-memory cache
        }
        if !self.dirty {
            return Ok(());
        }
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        let _guard = coordination::acquire_exclusive_lock(&self.path, config)
            .map_err(|e| CacheError::Io(std::io::Error::other(e.to_string())))?;

        let current = read_verified_cache_file(&self.path)?.unwrap_or_default();
        let mut entries = if self.removed_all { BTreeMap::new() } else { current.entries };
        if let Some(retained) = &self.retained_def_paths {
            entries.retain(|key, _| retained.contains(key));
        }
        for key in &self.removed_def_paths {
            entries.remove(key);
        }
        for (key, entry) in &self.data.entries {
            entries.insert(key.clone(), entry.clone());
        }

        let entries_json = serde_json::to_string(&entries)?;
        let key = integrity::derive_cache_key();
        let tag = integrity::compute_hmac(&key, entries_json.as_bytes());

        let file = CacheFile { version: CACHE_VERSION, entries, hmac: tag };
        let json = serde_json::to_string_pretty(&file)?;

        // Publish through a private create-new temp file. The destination is
        // never opened for writing, so a planted cache-path or legacy temp-path
        // symlink cannot redirect truncation into an unrelated file.
        coordination::atomic_write_replace(&self.path, json.as_bytes())?;

        self.data = file;
        self.content_hash_at_load = coordination::file_content_hash(&self.path);
        self.mark_clean();
        Ok(())
    }

    /// The content hash of the cache file at load time.
    ///
    /// Empty if loaded without coordination or created in-memory.
    #[must_use]
    pub fn content_hash_at_load(&self) -> &str {
        &self.content_hash_at_load
    }

    /// Whether the cache has real local mutations that have not been saved.
    #[must_use]
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Look up a function by def_path, content hash, spec hash, and solver fingerprint.
    ///
    /// A cache hit requires the content hash, spec hash, AND solver fingerprint
    /// to match. A proof-bearing entry additionally must have been independently
    /// produced/revalidated in this process. This prevents a user-writable disk
    /// cache—even one carrying a recomputed valid HMAC—from becoming proof
    /// authority.
    pub fn lookup(
        &mut self,
        def_path: &str,
        content_hash: &str,
        spec_hash: &str,
        solver_fingerprint: &str,
    ) -> CacheLookup {
        match self.data.entries.get(def_path) {
            Some(entry)
                if entry.content_hash == content_hash
                    // the spec hash must match exactly. The
                    // previous `entry.spec_hash.is_empty() || ...` disjunct made
                    // an empty *stored* spec hash a wildcard that matched ANY
                    // incoming spec hash, so a stale entry written without a spec
                    // fingerprint would be served as `proved` even after a real
                    // spec was added — a false-PROVE on cache hit. An empty
                    // stored hash now only matches an empty incoming hash;
                    // otherwise it fails closed to a miss and re-verifies.
                    && entry.spec_hash == spec_hash
                    && entry.solver_fingerprint == solver_fingerprint
                    && (!entry.claims_proof_authority()
                        || self.session_validated_def_paths.contains(def_path)) =>
            {
                // Statistics counter: saturate instead of wrapping. Wrapping
                // to 0 after usize::MAX lookups would silently corrupt the
                // reported stats; saturation preserves exact counts for every
                // reachable value and pins at the (unreachable) extreme.
                self.hits = self.hits.saturating_add(1);
                CacheLookup::Hit(entry.clone())
            }
            _ => {
                // Statistics counter: saturate, same rationale as `hits`.
                self.misses = self.misses.saturating_add(1);
                CacheLookup::Miss
            }
        }
    }

    /// Look up a function using its VerifiableFunction directly.
    ///
    /// Computes the SHA-256 content hash and spec fingerprint, then checks
    /// the cache. All three keys (content, spec, solver) must match for a hit.
    /// This is the primary entry point for the trust_verify MIR pass.
    pub fn lookup_function(
        &mut self,
        func: &VerifiableFunction,
        solver_fingerprint: &str,
    ) -> CacheLookup {
        let hash = compute_content_hash(func);
        let spec_fp = crate::spec_change_detector::SpecFingerprint::from_contracts(
            &func.def_path,
            &func.contracts,
        );
        self.lookup(&func.def_path, &hash, &spec_fp.hash, solver_fingerprint)
    }

    fn entries_equivalent(existing: &CacheEntry, new_entry: &CacheEntry) -> bool {
        existing.content_hash == new_entry.content_hash
            && existing.verdict == new_entry.verdict
            && existing.total_obligations == new_entry.total_obligations
            && existing.proved == new_entry.proved
            && existing.failed == new_entry.failed
            && existing.unknown == new_entry.unknown
            && existing.runtime_checked == new_entry.runtime_checked
            && existing.spec_hash == new_entry.spec_hash
            && existing.solver_fingerprint == new_entry.solver_fingerprint
            && existing.obligation_results == new_entry.obligation_results
    }

    /// Store a verification result for a function.
    ///
    /// Returns `true` when the cache contents changed and `false` when the new
    /// entry is semantically identical to the existing one.
    pub fn store(&mut self, def_path: &str, entry: CacheEntry) -> bool {
        // `store` is the trust boundary: its caller attests that this process
        // just independently computed/revalidated `entry`. Mark it before the
        // equivalence fast path so a byte-identical disk entry becomes eligible
        // for honest in-session reuse without requiring an unnecessary rewrite.
        self.session_validated_def_paths.insert(def_path.to_string());
        if self
            .data
            .entries
            .get(def_path)
            .is_some_and(|existing| Self::entries_equivalent(existing, &entry))
        {
            return false;
        }

        self.data.entries.insert(def_path.to_string(), entry);
        self.removed_def_paths.remove(def_path);
        if let Some(retained) = &mut self.retained_def_paths {
            retained.insert(def_path.to_string());
        }
        self.dirty = true;
        true
    }

    /// Store a verification result computed from a VerifiableFunction.
    ///
    /// Builds a CacheEntry with the SHA-256 content hash and current timestamp.
    /// The spec_hash is computed from the function's contracts for cross-session
    /// spec change detection. `solver_fingerprint` should be the value produced
    /// by [`crate::compute_solver_fingerprint`] for the active solver. Returns
    /// `true` when the cached entry changed.
    #[allow(clippy::too_many_arguments)]
    pub fn store_function(
        &mut self,
        func: &VerifiableFunction,
        verdict: FunctionVerdict,
        total_obligations: usize,
        proved: usize,
        failed: usize,
        unknown: usize,
        runtime_checked: usize,
        solver_fingerprint: &str,
    ) -> bool {
        self.store_function_with_obligation_results(
            func,
            verdict,
            total_obligations,
            proved,
            failed,
            unknown,
            runtime_checked,
            solver_fingerprint,
            Vec::new(),
        )
    }

    /// Store a verification result and the transport rows needed to replay
    /// stable cached JSON/human reporting without re-running verification.
    #[allow(clippy::too_many_arguments)]
    pub fn store_function_with_obligation_results(
        &mut self,
        func: &VerifiableFunction,
        verdict: FunctionVerdict,
        total_obligations: usize,
        proved: usize,
        failed: usize,
        unknown: usize,
        runtime_checked: usize,
        solver_fingerprint: &str,
        obligation_results: Vec<TransportObligationResult>,
    ) -> bool {
        let spec_fp = crate::spec_change_detector::SpecFingerprint::from_contracts(
            &func.def_path,
            &func.contracts,
        );
        let entry = CacheEntry {
            content_hash: compute_content_hash(func),
            verdict,
            total_obligations,
            proved,
            failed,
            unknown,
            runtime_checked,
            cached_at: now_unix_secs(),
            spec_hash: spec_fp.hash,
            solver_fingerprint: solver_fingerprint.to_string(),
            obligation_results,
        };
        self.store(&func.def_path, entry)
    }

    /// Remove a cached entry (e.g., when a callee spec changes).
    pub fn invalidate(&mut self, def_path: &str) -> bool {
        self.session_validated_def_paths.remove(def_path);
        if self.data.entries.remove(def_path).is_some() {
            self.removed_def_paths.insert(def_path.to_string());
            if let Some(retained) = &mut self.retained_def_paths {
                retained.remove(def_path);
            }
            self.dirty = true;
            true
        } else {
            false
        }
    }

    /// Remove all cached entries.
    pub fn invalidate_all(&mut self) {
        if self.data.entries.is_empty() && self.path.as_os_str().is_empty() {
            return;
        }
        self.data.entries.clear();
        self.session_validated_def_paths.clear();
        self.removed_def_paths.clear();
        self.retained_def_paths = None;
        self.removed_all = true;
        self.dirty = true;
    }

    /// Remove all entries whose def_path does not appear in the provided set.
    /// This is useful for garbage-collecting entries for deleted functions.
    pub fn retain_only(&mut self, active_def_paths: &[&str]) {
        let active: FxHashSet<&str> = active_def_paths.iter().copied().collect();
        let active_owned: FxHashSet<String> =
            active_def_paths.iter().map(|path| (*path).to_string()).collect();
        let removed: Vec<String> = self
            .data
            .entries
            .keys()
            .filter(|key| !active.contains(key.as_str()))
            .cloned()
            .collect();
        if removed.is_empty() && self.path.as_os_str().is_empty() {
            return;
        }
        self.data.entries.retain(|key, _| active.contains(key.as_str()));
        self.session_validated_def_paths.retain(|key| active.contains(key.as_str()));
        if !self.removed_all {
            self.removed_def_paths.extend(removed);
        }
        self.retained_def_paths = Some(match self.retained_def_paths.take() {
            Some(previous) => previous.intersection(&active_owned).cloned().collect(),
            None => active_owned,
        });
        self.dirty = true;
    }

    /// Write the cache to disk with an HMAC compatibility tag.
    ///
    /// The tag is computed over the serialized entries (without the hmac field
    /// itself) using deterministic material derived from the Trust executable +
    /// machine hostname. This detects corruption and producer mismatch; it is
    /// not a secret-backed authentication mechanism and cannot authorize proof
    /// replay. See #725.
    pub fn save(&mut self) -> Result<(), CacheError> {
        if self.path.as_os_str().is_empty() {
            self.mark_clean();
            return Ok(()); // in-memory cache, nothing to persist
        }
        if !self.dirty {
            return Ok(());
        }
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        // Serialize entries alone for tag input (excludes the hmac field itself
        // to avoid circular dependency).
        let entries_json = serde_json::to_string(&self.data.entries)?;
        let key = integrity::derive_cache_key();
        let tag = integrity::compute_hmac(&key, entries_json.as_bytes());

        // Build the on-disk structure with the computed compatibility tag.
        let file =
            CacheFile { version: CACHE_VERSION, entries: self.data.entries.clone(), hmac: tag };
        let json = serde_json::to_string_pretty(&file)?;
        // Even the legacy single-process API uses the same symlink-safe atomic
        // publisher: never open/truncate a user-controlled destination path.
        coordination::atomic_write_replace(&self.path, json.as_bytes())?;
        self.data = file;
        self.content_hash_at_load = coordination::file_content_hash(&self.path);
        self.mark_clean();
        Ok(())
    }

    /// Number of cache hits during this session.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Number of cache misses during this session.
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Total number of cached entries.
    pub fn len(&self) -> usize {
        self.data.entries.len()
    }

    /// Whether the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.data.entries.is_empty()
    }

    /// Summary string for diagnostics (e.g., "3 hits, 2 misses, 5 cached").
    #[must_use]
    pub fn summary(&self) -> String {
        format!("{} hits, {} misses, {} cached", self.hits, self.misses, self.data.entries.len())
    }

    fn mark_clean(&mut self) {
        self.dirty = false;
        self.removed_def_paths.clear();
        self.removed_all = false;
        self.retained_def_paths = None;
    }
}

fn verified_cache_file_from_str(contents: &str) -> Option<CacheFile> {
    let cf = serde_json::from_str::<CacheFile>(contents).ok()?;
    if cf.version != CACHE_VERSION {
        return None;
    }

    let entries_json = serde_json::to_string(&cf.entries).ok()?;
    let key = integrity::derive_cache_key();
    if cf.hmac.is_empty() || !integrity::verify_hmac(&key, entries_json.as_bytes(), &cf.hmac) {
        return None;
    }

    Some(cf)
}

fn read_verified_cache_file(path: &Path) -> Result<Option<CacheFile>, CacheError> {
    match std::fs::read_to_string(path) {
        Ok(contents) => Ok(verified_cache_file_from_str(&contents)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(CacheError::Io(error)),
    }
}

#[cfg(test)]
#[path = "cache_tests.rs"]
mod tests;
