//! trust-cache: what a compile still uses of Trust's first verification cache
//!
//! No cache tier here is live, and none is left. The in-process solver result
//! cache and the quarantined VC-artifact container went first (plan P4,
//! T4.2/T4.6): a process-wide map filled in demand order makes a verdict depend
//! on which function filled it first, and an observation-only container is an
//! env seam that can never become authority. T11 (2026-10-16, plan P6 of
//! `docs/design/2026-09-29-incremental-deterministic-trust-results.md`) deleted
//! the rest, none of which a compile consumed: the per-function
//! `VerificationCache` and its on-disk entries and integrity tags, the solver
//! query and subsumption caches, constraint independence and sub-query
//! splitting, alpha-normalized formula hashing, the MIR structural hash and its
//! incremental cache, the spec-aware invalidation manager and spec change
//! detector, the proof-replay and proof-cache-admission records. A per-function
//! key cannot capture the whole-program facts a Trust verdict consumes (caller
//! coverage, callee panic-freedom, backing certificates, ...), so replaying a
//! stale `Proved` for a function whose own bytes are unchanged would be a false
//! PROVE. Trust's one result store is STORE-1's, under `{cargo-cache-home}/trust/`.
//!
//! What a compile still uses:
//! - `fingerprint`: [`compose_semantics_key`], which `trust_verify` folds the
//!   whole-program bit into its verification-semantics key with (it stays until
//!   it has a replacement), and [`compute_content_hash`].
//! - `coordination`: the file-coordination primitives trust-router's memory
//!   jobserver locks with (T3 deletes it).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

// File-based cache coordination for concurrent compilations.
pub mod coordination;
pub(crate) mod fingerprint;

pub use coordination::{
    CacheLockGuard, CoordinationConfig, CoordinationError, acquire_exclusive_lock,
    acquire_shared_lock, coordinated_read, coordinated_write, file_content_hash,
    try_exclusive_lock, try_shared_lock, validate_content_hash,
};
pub use fingerprint::{
    compose_semantics_key, compute_content_hash, whole_program_semantics_segment,
};
