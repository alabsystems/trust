// trust-cache/src/vc_artifact_cache.rs: QUARANTINED VC-vector container.
//
// This module is wired into the compiler only as an opt-in telemetry and
// population experiment; it is NOT capable of serving proof-authoritative
// verification obligations. The compiler may observe an in-memory/disk hit and
// store a freshly captured raw pre-discharge vector, but it always runs fresh
// VC generation and never substitutes the cached vector into verdict production. A production
// read-side skip remains quarantined until a complete invalidation design and
// runtime validation exist.
//
// The current key is intentionally authority-incomplete. In particular, the
// lowered module digest does not bind every source contract (including
// decreases/modifies), callee/spec fingerprints, all VcgenContext inputs,
// hardened mode, synthetic/preclassified obligations, or the fresh-context
// binding and certified-monitor rows. The value stores only
// Vec<VerificationCondition>, so using it as the complete production outcome
// could drop fail-closed Unknown or already-classified rows and false-prove.
//
// The disk tier can retain vectors across invocations, but computing the module
// digest already requires extraction/lowering and persistence does not make a
// hit authoritative. A production read-substitution tier would additionally
// need a canonical vcgen/schema version, the full invalidation envelope, exact
// current-lowering validation, complete fresh-vs-hit outcome parity, and
// integrity that is not forgeable by a writer of the cache directory.
// trust-cache's existing locally derivable HMAC is a compatibility/corruption
// tag, not such authentication.
//
// Do not wire this API into verdict production until those conditions are
// independently ratified. Re-solving a truncated cached vector does not repair
// obligations that were omitted from that vector.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use std::io::Read as _;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::VerificationCondition;
use trust_types::fx::FxHashMap;

/// Machine-readable authority boundary for this experimental container.
pub const VC_ARTIFACT_CACHE_AUTHORITY_CAPABLE: bool = false;

use crate::{coordination, integrity};

/// Default upper bound on the number of in-memory VC-artifact entries.
///
/// One entry per unique `(module_digest, semantics, vcgen_version)` — i.e. per
/// distinct lowered function shape reached this compile. A few thousand is
/// ample for a large crate while keeping memory bounded; override with
/// `TRUST_VC_ARTIFACT_CACHE_CAP` (`0` disables the bound).
pub const DEFAULT_VC_ARTIFACT_CACHE_CAP: usize = 8192;

/// Environment variable overriding [`DEFAULT_VC_ARTIFACT_CACHE_CAP`].
const VC_ARTIFACT_CACHE_CAP_ENV: &str = "TRUST_VC_ARTIFACT_CACHE_CAP";

/// Experimental identity for an in-memory or on-disk VC-vector entry.
///
/// - `module_digest`: canonical trust-ir module digest of the FAITHFULLY
///   lowered function (`trust_ir_bridge::module_stable_content_hash`).
/// - `semantics_key`: the verification-semantics fingerprint (proof level,
///   policy, solver identity, whole-program bit) — the same envelope the
///   solver/result caches key on, so a policy change can never replay VCs
///   generated under a different obligation set.
/// - `vcgen_version`: the VC-generation identity (compiler binary + format
///   version), so a compiler whose generation could differ reads a different
///   key and a stale entry misses rather than serving an obsolete vector.
///
/// These fields still do not bind the complete production VC-generation
/// context: `module_digest` is a compatibility lowering rather than an exact
/// digest of every generator input, and `vcgen_version` is a caller-supplied
/// 64-bit hash rather than a canonical collision-resistant schema identity.
/// Consequently equality of this key does not authorize reuse in verdict
/// production; it is only an experimental container identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VcArtifactKey {
    pub module_digest: String,
    pub semantics_key: String,
    pub vcgen_version: u64,
}

impl VcArtifactKey {
    #[must_use]
    pub fn new(module_digest: &str, semantics_key: &str, vcgen_version: u64) -> Self {
        Self {
            module_digest: module_digest.to_string(),
            semantics_key: semantics_key.to_string(),
            vcgen_version,
        }
    }

    /// Content-addressed digest of the full key, used as the on-disk file stem.
    ///
    /// Length-prefixed field framing so no two distinct key tuples can alias by
    /// concatenation. The digest only chooses the *file*; a hit still rests on
    /// the exact field-by-field key check in
    /// [`VcArtifactDiskTier::observe_lookup`].
    #[must_use]
    pub fn digest(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(VC_ARTIFACT_TIER_VERSION.to_le_bytes());
        for field in [self.module_digest.as_str(), self.semantics_key.as_str()] {
            hasher.update((field.len() as u64).to_le_bytes());
            hasher.update(field.as_bytes());
        }
        hasher.update(self.vcgen_version.to_le_bytes());
        format!("{:x}", hasher.finalize())
    }
}

/// A stored raw pre-discharge VC vector, private to this non-authoritative
/// container.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CachedVcArtifact {
    key: VcArtifactKey,
    /// A caller-provided raw body vector captured during fresh generation. It
    /// excludes non-VC outcome rows and has no authority claim that it equals
    /// a fresh complete generation.
    vcs: Vec<VerificationCondition>,
}

/// Non-authoritative telemetry exposed for a matching stored record.
///
/// The vector itself is deliberately not exposed. In particular, this value
/// cannot replace fresh VC generation or establish obligation completeness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VcArtifactObservation {
    vc_count: usize,
}

impl VcArtifactObservation {
    /// Number of vector elements observed in the experimental record.
    #[must_use]
    pub fn vc_count(self) -> usize {
        self.vc_count
    }
}

/// In-memory, LRU-bounded experimental VC-vector container.
///
/// Eviction is only a container operation: it removes stored data and turns a
/// later lookup into a miss. Because the current compiler integration is
/// telemetry/population-only and never substitutes a hit for fresh generation,
/// that fact carries no proof-soundness claim. Any future verdict consumer must
/// independently prove that every miss regenerates a complete fresh outcome
/// and that no hit can omit an obligation before wiring this type to verdicts.
pub struct VcArtifactCache {
    entries: FxHashMap<VcArtifactKey, CachedVcArtifact>,
    /// LRU recency order over the keys in `entries`. Front = LRU, back = MRU.
    lru: VecDeque<VcArtifactKey>,
    capacity: usize,
    stats: VcArtifactCacheStats,
}

/// Usage statistics.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VcArtifactCacheStats {
    pub entries: usize,
    pub hits: usize,
    pub misses: usize,
    pub evictions: usize,
    /// Stored vector elements counted across all observations. They were not
    /// returned to a verdict-producing caller and were never replayed.
    pub vcs_observed: usize,
}

impl Default for VcArtifactCache {
    fn default() -> Self {
        Self::new()
    }
}

impl VcArtifactCache {
    /// Create a cache with the default (env-overridable) entry bound.
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(Self::resolve_capacity())
    }

    /// Create a cache with an explicit entry cap (`0` = unbounded).
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: FxHashMap::default(),
            lru: VecDeque::new(),
            capacity,
            stats: VcArtifactCacheStats::default(),
        }
    }

    fn resolve_capacity() -> usize {
        std::env::var(VC_ARTIFACT_CACHE_CAP_ENV)
            .ok()
            .and_then(|raw| raw.trim().parse::<usize>().ok())
            .unwrap_or(DEFAULT_VC_ARTIFACT_CACHE_CAP)
    }

    /// Observe whether a stored experimental raw body vector matches `key`.
    ///
    /// Only a count is exposed; callers cannot obtain the stored vector or use
    /// it in place of fresh VC generation. This operation updates
    /// recency/statistics but establishes no completeness or authority.
    pub fn observe_lookup(&mut self, key: &VcArtifactKey) -> Option<VcArtifactObservation> {
        if self.entries.contains_key(key) {
            self.stats.hits += 1;
            self.touch(key);
            let vc_count = self.entries.get(key).expect("present").vcs.len();
            self.stats.vcs_observed += vc_count;
            Some(VcArtifactObservation { vc_count })
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Store a freshly captured raw pre-discharge body vector under `key`.
    ///
    /// Overwriting an existing key refreshes recency without growth; a new key
    /// is inserted most-recently-used and the LRU bound is enforced.
    pub fn store(&mut self, key: VcArtifactKey, vcs: Vec<VerificationCondition>) {
        let entry = CachedVcArtifact { key: key.clone(), vcs };
        let is_update = self.entries.insert(key.clone(), entry).is_some();
        if is_update {
            self.touch(&key);
        } else {
            self.lru.push_back(key);
            self.enforce_capacity();
        }
        self.stats.entries = self.entries.len();
    }

    /// Mark `key` most-recently-used.
    fn touch(&mut self, key: &VcArtifactKey) {
        if let Some(pos) = self.lru.iter().position(|k| k == key) {
            if let Some(k) = self.lru.remove(pos) {
                self.lru.push_back(k);
            }
        }
    }

    /// Evict least-recently-used entries until at or below `capacity`.
    fn enforce_capacity(&mut self) {
        if self.capacity == 0 {
            return;
        }
        while self.entries.len() > self.capacity {
            match self.lru.pop_front() {
                Some(victim) => {
                    if self.entries.remove(&victim).is_some() {
                        self.stats.evictions += 1;
                    }
                }
                None => break,
            }
        }
        self.stats.entries = self.entries.len();
    }

    #[must_use]
    pub fn stats(&self) -> &VcArtifactCacheStats {
        &self.stats
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Schema version of an on-disk VC-artifact record. Bump on any wire-format or
/// key-composition change so older records fail closed.
/// v2: `vcgen_version` widened u32 -> u64. The current observation-only tier is
/// verdict-inert, but a future read-substitution tier would make a collision the
/// unsound direction (a stale cross-build vector rather than a miss).
/// v3: stored values are raw pre-discharge body vectors captured during fresh
/// generation, not post-discharge solver vectors. The read surface remains
/// observation-only and exposes only a count.
pub const VC_ARTIFACT_TIER_VERSION: u32 = 3;

/// Hard cap for one experimental disk record. Observation is best-effort, so
/// oversized records safely degrade to a miss before JSON allocation/parsing.
const MAX_VC_ARTIFACT_RECORD_BYTES: u64 = 16 * 1024 * 1024;

/// One on-disk VC-artifact record: the key, the raw body vector, and an HMAC
/// compatibility tag over `(version, key, vcs)`.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct VcArtifactRecord {
    version: u32,
    key: VcArtifactKey,
    vcs: Vec<VerificationCondition>,
    /// HMAC-SHA256 over the canonical serialization of `(version, key, vcs)`,
    /// hex-encoded. A machine-local corruption/foreign-record check, NOT a
    /// secret-backed signature (see [`VcArtifactDiskTier`] soundness note).
    #[serde(default)]
    hmac: String,
}

/// Bytes covered by the HMAC: `(version, key, vcs)`, NOT the tag itself.
/// Serialized as a fixed tuple for a deterministic, field-order-stable payload.
/// The error is PROPAGATED (never defaulted to empty) so `store` refuses to sign
/// and `lookup` misses on the same unserializable data — no un-authenticated
/// record can be minted or accepted.
fn record_mac_payload(
    version: u32,
    key: &VcArtifactKey,
    vcs: &[VerificationCondition],
) -> Result<Vec<u8>, serde_json::Error> {
    serde_json::to_vec(&(version, key, vcs))
}

/// Cross-invocation experimental disk tier, rooted at a directory of
/// content-addressed `<key.digest()>.json` records.
///
/// # Soundness
///
/// A record stores an authority-incomplete vector. Its HMAC detects ordinary
/// corruption, but its key is locally derivable and therefore cannot prove
/// origin or completeness to a compiler reading a writable build directory.
/// Re-solving a truncated vector would not recover omitted obligations. For
/// that reason the public read surface exposes only non-authoritative telemetry
/// and can never return the vector to verdict production. Every observation
/// must be followed by fresh VC generation.
///
/// Reads are lock-free (immutable content-addressed files); writes are atomic
/// create-if-absent, so concurrent writers of the same key publish byte-identical
/// records without corruption.
#[derive(Debug, Clone)]
pub struct VcArtifactDiskTier {
    root: PathBuf,
}

impl VcArtifactDiskTier {
    /// Create a tier rooted at `root` (e.g. `target/trust-cache/vc-artifacts`).
    #[must_use]
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    /// The directory holding the content-addressed records.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    fn record_path(&self, key: &VcArtifactKey) -> PathBuf {
        self.root.join(format!("{}.json", key.digest()))
    }

    /// Observe a matching experimental disk record.
    ///
    /// Returns only a vector-element count after the schema, compatibility tag,
    /// exact key, and bounded-record checks succeed. The stored vector remains
    /// private and cannot substitute for fresh VC generation.
    #[must_use]
    pub fn observe_lookup(&self, key: &VcArtifactKey) -> Option<VcArtifactObservation> {
        let path = self.record_path(key);
        if std::fs::metadata(&path).ok()?.len() > MAX_VC_ARTIFACT_RECORD_BYTES {
            return None;
        }
        // The metadata check avoids ordinary oversized reads; `take` also caps
        // a concurrent growth race between metadata and open/read.
        let mut contents = Vec::new();
        std::fs::File::open(path)
            .ok()?
            .take(MAX_VC_ARTIFACT_RECORD_BYTES + 1)
            .read_to_end(&mut contents)
            .ok()?;
        if contents.len() as u64 > MAX_VC_ARTIFACT_RECORD_BYTES {
            return None;
        }
        let record: VcArtifactRecord = serde_json::from_slice(&contents).ok()?;

        if record.version != VC_ARTIFACT_TIER_VERSION {
            return None;
        }
        if record.hmac.is_empty() {
            return None;
        }
        let mac_key = integrity::derive_cache_key();
        let Ok(payload) = record_mac_payload(record.version, &record.key, &record.vcs) else {
            return None;
        };
        if !integrity::verify_hmac(&mac_key, &payload, &record.hmac) {
            return None;
        }
        // The digest only located the file. This exact-key check makes a
        // collision a telemetry miss; it does not authorize vector reuse.
        if record.key != *key {
            return None;
        }
        Some(VcArtifactObservation { vc_count: record.vcs.len() })
    }

    /// Best-effort atomic write of a raw body vector into the disk tier.
    ///
    /// Content-addressed and idempotent: a pre-existing record for the same key
    /// is left untouched (`Ok(false)`); a fresh write returns `Ok(true)`. Refuses
    /// to sign an unserializable payload. I/O errors are propagated for the
    /// caller to log-and-ignore (the in-memory tier and fresh vcgen remain
    /// authoritative).
    pub fn store(
        &self,
        key: &VcArtifactKey,
        vcs: &[VerificationCondition],
    ) -> std::io::Result<bool> {
        let payload = record_mac_payload(VC_ARTIFACT_TIER_VERSION, key, vcs)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        let mac_key = integrity::derive_cache_key();
        let hmac = integrity::compute_hmac(&mac_key, &payload);
        let record = VcArtifactRecord {
            version: VC_ARTIFACT_TIER_VERSION,
            key: key.clone(),
            vcs: vcs.to_vec(),
            hmac,
        };
        let json = serde_json::to_string(&record)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        coordination::atomic_write_create_new(&self.record_path(key), json.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind};

    use super::*;

    fn vc(name: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: name.into(),
            location: SourceSpan::default(),
            formula: Formula::Var(name.into(), Sort::Bool),
            contract_metadata: None,
        }
    }

    fn key(digest: &str) -> VcArtifactKey {
        VcArtifactKey::new(digest, "sem=L0;wp=true", 1)
    }

    #[test]
    fn store_then_hit_exposes_only_non_authoritative_observation() {
        let mut cache = VcArtifactCache::new();
        let k = key("modA");
        cache.store(k.clone(), vec![vc("f"), vc("f")]);

        let got = cache.observe_lookup(&k).expect("hit");
        assert_eq!(got.vc_count(), 2, "observation reports only vector length");
        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().vcs_observed, 2);
    }

    #[test]
    fn miss_on_absent_key() {
        let mut cache = VcArtifactCache::new();
        assert!(cache.observe_lookup(&key("nope")).is_none());
        assert_eq!(cache.stats().misses, 1);
        assert_eq!(cache.stats().hits, 0);
    }

    #[test]
    fn key_discriminates_on_every_component() {
        // Container-key behavior only. Even an exact hit is non-authoritative
        // because the key omits production VC/fresh-context inputs.
        let mut cache = VcArtifactCache::new();
        cache.store(key("modA"), vec![vc("f")]);

        assert!(cache.observe_lookup(&key("modB")).is_none(), "different digest misses");
        assert!(
            cache.observe_lookup(&VcArtifactKey::new("modA", "sem=L1;wp=true", 1)).is_none(),
            "different semantics misses"
        );
        assert!(
            cache.observe_lookup(&VcArtifactKey::new("modA", "sem=L0;wp=true", 2)).is_none(),
            "different vcgen version misses"
        );
        assert!(cache.observe_lookup(&key("modA")).is_some(), "exact key hits");
    }

    #[test]
    fn lru_bound_evicts_oldest() {
        let mut cache = VcArtifactCache::with_capacity(2);
        cache.store(key("m1"), vec![vc("a")]);
        cache.store(key("m2"), vec![vc("b")]);
        cache.store(key("m3"), vec![vc("c")]); // evicts m1 (LRU)

        assert_eq!(cache.len(), 2);
        assert!(cache.observe_lookup(&key("m1")).is_none(), "oldest evicted");
        assert!(cache.observe_lookup(&key("m2")).is_some());
        assert!(cache.observe_lookup(&key("m3")).is_some());
        assert_eq!(cache.stats().evictions, 1);
    }

    #[test]
    fn hit_refreshes_recency_protecting_from_eviction() {
        let mut cache = VcArtifactCache::with_capacity(2);
        cache.store(key("m1"), vec![vc("a")]);
        cache.store(key("m2"), vec![vc("b")]);
        // Touch m1 so m2 becomes LRU.
        assert!(cache.observe_lookup(&key("m1")).is_some());
        cache.store(key("m3"), vec![vc("c")]); // should evict m2, not m1

        assert!(cache.observe_lookup(&key("m1")).is_some(), "recently-used survives");
        assert!(cache.observe_lookup(&key("m2")).is_none(), "LRU evicted");
    }

    #[test]
    fn entry_serde_round_trips() {
        // Serialization supports the integrity-tagged disk container; it does
        // not make cached VC vectors proof-authoritative.
        let entry = CachedVcArtifact { key: key("modA"), vcs: vec![vc("f")] };
        let json = serde_json::to_string(&entry).expect("serialize");
        let back: CachedVcArtifact = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.key, entry.key);
        assert_eq!(back.vcs.len(), 1);
    }

    #[test]
    fn authority_boundary_is_explicitly_quarantined() {
        assert!(!VC_ARTIFACT_CACHE_AUTHORITY_CAPABLE);
    }

    // --- disk tier ---

    fn temp_tier() -> (VcArtifactDiskTier, std::path::PathBuf) {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "trust-vc-artifact-{}-{}-{seq}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0),
        ));
        std::fs::create_dir_all(&dir).expect("mkdir tier root");
        (VcArtifactDiskTier::new(&dir), dir)
    }

    #[test]
    fn disk_store_then_observe_reports_only_count() {
        let (tier, dir) = temp_tier();
        let k = key("modDisk");
        let vcs = vec![vc("g"), vc("g"), vc("h")];
        assert!(tier.store(&k, &vcs).expect("store"), "fresh write");
        // Idempotent: a second store of the same key is a no-op.
        assert!(!tier.store(&k, &vcs).expect("store2"), "existing record untouched");

        let got = tier.observe_lookup(&k).expect("hit");
        assert_eq!(got.vc_count(), 3, "observation reports only vector length");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn disk_miss_on_absent_and_on_key_mismatch() {
        let (tier, dir) = temp_tier();
        assert!(tier.observe_lookup(&key("never")).is_none(), "absent key misses");

        tier.store(&key("modX"), &[vc("a")]).expect("store");
        // Different semantics under a colliding-ish path still exact-key-misses.
        assert!(
            tier.observe_lookup(&VcArtifactKey::new("modX", "sem=OTHER", 1)).is_none(),
            "different key component misses"
        );
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn disk_content_tampered_record_fails_closed() {
        // Mutating a VC's CONTENT (here a function name) diverges the record
        // from the locally derived compatibility tag, so the observation
        // becomes a miss. This is corruption detection only: the vector is
        // private and verdict production regenerates from the current body
        // regardless. (An unknown field is serde-ignored and does not alter the
        // deserialized compatibility payload.)
        let (tier, dir) = temp_tier();
        let k = key("modTamper");
        tier.store(&k, &[vc("aaa"), vc("bbb")]).expect("store");
        let path = dir.join(format!("{}.json", k.digest()));
        let raw = std::fs::read_to_string(&path).expect("read record");
        let tampered = raw.replace("bbb", "ccc");
        assert_ne!(tampered, raw, "test actually mutated VC content");
        std::fs::write(&path, tampered).expect("write tampered");

        assert!(tier.observe_lookup(&k).is_none(), "content-tampered record must miss");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn disk_corrupted_hmac_tag_fails_closed() {
        // Corrupting just the tag (leaving content intact) must also miss.
        let (tier, dir) = temp_tier();
        let k = key("modTag");
        tier.store(&k, &[vc("a")]).expect("store");
        let path = dir.join(format!("{}.json", k.digest()));
        let raw = std::fs::read_to_string(&path).expect("read");
        // Flip a hex digit inside the hmac field's value.
        let idx = raw.find("\"hmac\":\"").expect("has hmac") + 8;
        let mut bytes = raw.into_bytes();
        bytes[idx] = if bytes[idx] == b'a' { b'b' } else { b'a' };
        std::fs::write(&path, bytes).expect("write");
        assert!(tier.observe_lookup(&k).is_none(), "corrupted HMAC misses");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn disk_empty_hmac_legacy_record_fails_closed() {
        let (tier, dir) = temp_tier();
        let k = key("modLegacy");
        // A record with no HMAC (legacy/foreign) must not be trusted.
        let record = format!(
            r#"{{"version":{VC_ARTIFACT_TIER_VERSION},"key":{{"module_digest":"modLegacy","semantics_key":"sem=L0;wp=true","vcgen_version":1}},"vcs":[],"hmac":""}}"#
        );
        std::fs::write(dir.join(format!("{}.json", k.digest())), record).expect("write");
        assert!(tier.observe_lookup(&k).is_none(), "empty-HMAC record misses");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn disk_wrong_version_fails_closed() {
        let (tier, dir) = temp_tier();
        let k = key("modVer");
        tier.store(&k, &[vc("a")]).expect("store");
        let path = dir.join(format!("{}.json", k.digest()));
        let raw = std::fs::read_to_string(&path).expect("read");
        let bumped =
            raw.replacen(&format!("\"version\":{VC_ARTIFACT_TIER_VERSION}"), "\"version\":999", 1);
        std::fs::write(&path, bumped).expect("write");
        assert!(tier.observe_lookup(&k).is_none(), "unrecognized schema version misses");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn empty_locally_tagged_record_is_observation_only() {
        let (tier, dir) = temp_tier();
        let k = key("modEmpty");
        assert!(tier.store(&k, &[]).expect("store empty vector"));
        assert_eq!(tier.observe_lookup(&k).expect("observe").vc_count(), 0);
        assert!(!VC_ARTIFACT_CACHE_AUTHORITY_CAPABLE);
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn oversized_disk_record_is_rejected_before_json_parsing() {
        let (tier, dir) = temp_tier();
        let k = key("modHuge");
        let path = dir.join(format!("{}.json", k.digest()));
        let file = std::fs::File::create(path).expect("create sparse oversized record");
        file.set_len(MAX_VC_ARTIFACT_RECORD_BYTES + 1).expect("extend sparse record");
        assert!(tier.observe_lookup(&k).is_none());
        std::fs::remove_dir_all(dir).ok();
    }
}
