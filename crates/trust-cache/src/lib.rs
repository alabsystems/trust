//! trust-cache: verification caching for Trust
//!
//! What is actually live in a compile today is the in-process solver result
//! cache (`result_cache`, driven by `trust_router::solver_cache`): the same
//! formula sent to the same solver returns its cached verdict instead of
//! re-solving. Everything below that is either quarantined
//! (`vc_artifact_cache`, explicitly non-authoritative) or unadopted.
//!
//! In particular, [`VerificationCache`] — the per-function content-hash tier
//! this crate is named for — has no consumer. The compiler's verify pass
//! deliberately does not populate a cross-run proof cache: a per-function key
//! cannot capture the whole-program facts a Trust verdict consumes (caller
//! coverage, callee panic-freedom, backing certificates, ...), so replaying a
//! stale `Proved` for a function whose own bytes are unchanged would be a false
//! PROVE. Adopting any tier here requires a whole-program-aware key or a
//! "verification consumed a fact not in the key" tripwire, not an exclusion
//! list. Do not describe this crate as delivering incremental verification
//! until one of those exists.
//!
//! Also provides:
//! - Solver query caching (query_cache.rs) — KLEE-inspired exact-match cache
//! - Constraint independence splitting (independence.rs) — variable-based splitting
//! - Subsumption-based proof caching (query_cache.rs) — stronger proofs subsume weaker
//!
//! ## Module layout
//!
//! - `fingerprint` — content + solver fingerprint helpers ([`compute_content_hash`],
//!   [`compute_solver_fingerprint`]).
//! - `entry` — the on-disk schema: [`CacheEntry`], [`CacheLookup`], and the
//!   `CACHE_VERSION` constant.
//! - `cache` — the [`VerificationCache`] orchestrator and [`CacheError`].
//!
//! Everything historically reached as `trust_cache::Foo` continues to be
//! re-exported from this root.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Register the inert `#[trust::...]` tool namespace used by cache metadata.
#![feature(register_tool)]
#![register_tool(trust)]
// Trust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

pub mod alpha_normalize;
pub(crate) mod cache;
// File-based cache coordination for concurrent compilations.
pub mod coordination;
pub(crate) mod entry;
pub(crate) mod fingerprint;
pub(crate) mod independence;
// HMAC-SHA256 compatibility/corruption-detection tags for cache files on disk.
// Public for sibling cache crates, but explicitly non-authoritative: the key is
// locally derivable and cannot authenticate proof claims from a writable file.
pub mod integrity;
// MIR structural hashing and per-function incremental cache.
pub(crate) mod invalidation;
pub mod invalidation_strategy;
pub(crate) mod mir_hash;
pub mod proof_cache_admission;
pub mod proof_replay;
pub(crate) mod query_cache;
// Solver result caching consolidated from trust-router.
pub mod result_cache;
pub mod spec_aware_cache;
pub mod spec_change_detector;
pub(crate) mod sub_query_splitter;
// QUARANTINED experimental VC-vector container. The compiler may populate it
// and observe hit counts, but its key/value omit parts of the production
// obligation/fresh-context outcome and its public read API cannot return VCs.
// It must not feed verification authority.
pub mod vc_artifact_cache;
// Property-based idempotency and serialization roundtrip tests.
#[cfg(test)]
mod proptest_roundtrip;

// ---- Public API re-exports ---------------------------------------------

// Core cache + entry types live in their own modules but are exposed at the
// crate root for backward compatibility.
// Re-export key types from independence and query_cache for convenience.
pub use alpha_normalize::{SubFormulaCache, alpha_normalize, alpha_normalized_hash};
pub use cache::{CacheError, VerificationCache};
// Re-export cache coordination types.
pub use coordination::{
    CacheLockGuard, CoordinationConfig, CoordinationError, acquire_exclusive_lock,
    acquire_shared_lock, coordinated_read, coordinated_write, file_content_hash,
    try_exclusive_lock, try_shared_lock, validate_content_hash,
};
pub use entry::{CacheEntry, CacheLookup};
pub use fingerprint::{
    SolverBinaryFingerprint, compose_semantics_key, compute_content_hash,
    compute_solver_fingerprint, fingerprint_solver_binary, snapshot_solver_binary,
    whole_program_semantics_segment,
};
pub use independence::{
    ConstraintIndependence, free_variables, partition_constraints, simplify_query,
};
// Re-export MIR hash incremental types.
pub use mir_hash::{
    DependencyGraph, IncrementalCache, MirHash, MirHashCacheError, VerificationResult,
    compute_mir_hash, try_compute_mir_hash,
};
pub use proof_cache_admission::{
    PROOF_QUERY_CACHE_ADMISSION_SCHEMA, PROOF_QUERY_CACHE_ADMISSION_VERSION,
    ProofQueryCacheAdmissionMetrics, ProofQueryCacheAdmissionReport,
    ProofQueryCacheAdmissionStatus, validate_proof_query_cache_admission_json,
    validate_proof_query_cache_admission_str,
};
pub use query_cache::{CacheKey, CacheStats, QueryCache, SubsumptionCache, is_subsumed};
// Re-export solver result cache types.
pub use result_cache::{
    CachePolicy, CacheStats as ResultCacheStats, CachedResult, ResultCache, ResultCacheKey,
    hash_formula,
};
// Spec-aware cache manager — owns the verification cache plus the
// caller->callee dependency graph that would invalidate a caller's proof when a
// transitive callee contract changes. NOT wired to anything: nothing outside
// this crate constructs it, and the compiler verify pass does not consult it.
// The reason is the same one that keeps the incremental proof cache
// unpopulated (`trust_verify.rs`, "the incremental proof cache is NOT populated
// here"): a per-function key cannot capture the whole-program facts a Trust
// verdict consumes, and this graph tracks only the contract-change channel out
// of the several that were found. Treat it as an unadopted design, not a live
// invalidation path. Its lookup path is nonetheless barred from returning a
// proof-bearing entry, so adopting it can never become the vehicle for that
// gap; see `spec_aware_cache`.
pub use spec_aware_cache::{InvalidationEvent, SpecAwareCacheManager};
pub use sub_query_splitter::{
    CachedSubQuery, IndependenceAnalysis, SplitResult, SplitterConfig, SplitterStats, SubQuery,
    SubQuerySplitter, analyze_independence, sub_query_hash,
};
pub use vc_artifact_cache::{
    DEFAULT_VC_ARTIFACT_CACHE_CAP, VC_ARTIFACT_CACHE_AUTHORITY_CAPABLE, VC_ARTIFACT_TIER_VERSION,
    VcArtifactCache, VcArtifactCacheStats, VcArtifactDiskTier, VcArtifactKey,
    VcArtifactObservation,
};
