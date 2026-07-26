//! On-disk and in-memory cache entry types.
//!
//! - [`CacheEntry`] is the public record stored for each function: content
//!   hash, verdict, counts, spec hash, solver fingerprint, and the transport
//!   rows needed to replay reporting on a cache hit.
//! - [`CacheFile`] is the serialized container with a schema [`CACHE_VERSION`]
//! and a compatibility/corruption-detection tag. The tag is not proof
//! authentication: its derivation material is available to a local writer.
//! - [`CacheLookup`] is the public result of a cache query.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::{FunctionVerdict, TransportObligationResult};

/// Current cache schema version. Bump when [`CacheEntry`] format changes.
///
/// - v2: Added `spec_hash` field.
/// - v3: Added an HMAC corruption/producer-compatibility tag (not proof auth).
/// - v4: Persisted per-obligation transport results for stable cached reporting.
/// - v5: Added `solver_fingerprint` — out-of-process solver (ay) rebuilds now
///   invalidate cached proofs that depended on them.
/// - v6: Folded the target triple + pointer width into the semantics key — proofs
///   are target-specific (pointer-width obligations, `cfg(target_*)`), so a HIT
///   across cross-compile targets is no longer possible (closed a false-PROVE).
pub(crate) const CACHE_VERSION: u32 = 6;

/// A single cached entry for one function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CacheEntry {
    /// The SHA-256 content hash of the function body + contracts at verification time.
    pub content_hash: String,
    /// The verification verdict.
    pub verdict: FunctionVerdict,
    /// Number of obligations that were checked.
    pub total_obligations: usize,
    /// Number proved.
    pub proved: usize,
    /// Number failed.
    pub failed: usize,
    /// Number unknown.
    pub unknown: usize,
    /// Number runtime-checked.
    #[serde(default)]
    pub runtime_checked: usize,
    /// Unix timestamp (seconds since epoch) when this entry was cached.
    #[serde(default)]
    pub cached_at: u64,
    /// SHA-256 fingerprint of the function's spec clauses (requires/ensures/invariants).
    ///
    /// Used for cross-session spec change detection: if this hash differs from the
    /// current spec fingerprint, the cached result is stale even if the body hash
    /// matches. Absent (empty) for entries created before spec tracking was added.
    #[serde(default)]
    pub spec_hash: String,
    /// Fingerprint of the solver toolchain that produced this entry.
    ///
    /// Set by [`crate::compute_solver_fingerprint`]. A ay rebuild rotates this
    /// value so cached proofs from an older solver are not silently reused.
    /// Lookup requires a strict match; legacy entries (empty) miss unless the
    /// query also passes empty (in-process tests).
    #[serde(default)]
    pub solver_fingerprint: String,
    /// Cached per-obligation transport results for stable human/json reporting on cache hits.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub obligation_results: Vec<TransportObligationResult>,
}

impl CacheEntry {
    /// Whether replaying this record would assert any proof authority.
    ///
    /// Disk/shared-cache contents are user-writable. Even a structurally valid
    /// record with a matching compatibility tag must therefore be independently
    /// revalidated before this predicate may be replayed as a hit. Keep this
    /// deliberately conservative: a zero-obligation verdict is itself a claim
    /// that there was nothing to prove, and nested proof-shaped transport data
    /// is authority even when summary counters were forged to zero.
    #[must_use]
    pub(crate) fn claims_proof_authority(&self) -> bool {
        self.total_obligations == 0
            || self.proved != 0
            || self.runtime_checked != 0
            || matches!(
                self.verdict,
                FunctionVerdict::Verified
                    | FunctionVerdict::RuntimeChecked
                    | FunctionVerdict::NoObligations
            )
            || self.obligation_results.iter().any(|result| {
                result.outcome.is_proved()
                    || result.outcome.is_runtime_checked()
                    || result.design_mandate
                    || result.proof_evidence.is_some()
                    || result.native_trust_ir.is_some()
                    || result.monitor.is_some()
            })
    }
}

/// On-disk cache format.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CacheFile {
    /// Schema version for forward compatibility.
    pub(crate) version: u32,
    /// Map from function def_path to cached entry.
    pub(crate) entries: BTreeMap<String, CacheEntry>,
    /// HMAC-SHA256 compatibility tag over the serialized entries, hex-encoded.
    /// Computed from public/local derivation material (the executable and host),
    /// so it detects corruption and incompatible cache provenance but does NOT
    /// authenticate proof claims against a writer who can edit this file.
    /// Empty string for in-memory caches or legacy files. See #725.
    #[serde(default)]
    pub(crate) hmac: String,
}

impl Default for CacheFile {
    fn default() -> Self {
        CacheFile { version: CACHE_VERSION, entries: BTreeMap::new(), hmac: String::new() }
    }
}

/// Result of a cache lookup.
#[derive(Debug, Clone, PartialEq)]
pub enum CacheLookup {
    /// Cache hit: the function body has not changed since last verification.
    Hit(CacheEntry),
    /// Cache miss: the function is new or its body changed.
    Miss,
}
