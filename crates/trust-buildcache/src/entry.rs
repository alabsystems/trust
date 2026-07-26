//! Cache entry types: what we hand back on a hit, and what callers hand us
//! when storing.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// A materialized artifact candidate. Paths point into the cache directory;
/// no production compiler currently consumes them. Any future consumer must
/// live-revalidate the candidate before copying or linking its artifacts.
#[derive(Debug, Clone)]
pub struct CacheEntry {
    pub rlib: PathBuf,
    pub rmeta: PathBuf,
    pub depfile: PathBuf,
    pub certificate: PathBuf,
    pub metadata: EntryMetadata,
}

/// Per-entry metadata handed back to callers on a cache hit. The fields
/// here are the merged view of two on-disk files:
///
/// - `metadata.json` (HMAC-sealed, immutable post-store): `key_hex`,
///   `stored_at_unix_ms`, `size_bytes`.
/// - `access.txt` (NOT sealed, mutated on every lookup):
///   `last_access_unix_ms`, `hit_count`.
///
/// The split exists so LRU bookkeeping doesn't invalidate the HMAC over
/// the immutable artifacts -- see `storage.rs` for the rationale.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EntryMetadata {
    pub key_hex: String,
    pub stored_at_unix_ms: u64,
    pub last_access_unix_ms: u64,
    pub hit_count: u64,
    pub size_bytes: u64,
}

/// Inputs to [`crate::BuildCache::store`]. Source paths must exist and be
/// readable; the cache copies them into the content-addressed entry dir.
#[derive(Debug, Clone)]
pub struct StoreRequest {
    pub rlib_source: PathBuf,
    pub rmeta_source: PathBuf,
    pub depfile_source: PathBuf,
    pub certificate_source: PathBuf,
}
