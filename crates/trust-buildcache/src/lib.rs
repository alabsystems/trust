//! trust-buildcache: native artifact-candidate cache for the Trust toolchain.
//!
//! Owned alternative to the role sccache plays in generic Rust workflows.
//! Two integrity invariants set this apart from a generic compiler cache:
//!
//! 1. **Experimental keys include verification state.** [`CacheInputs`] hashes the
//!    trustc binary fingerprint, every solver backend version, and the
//!    verification policy in effect, alongside source content and codegen
//!    flags. These inputs distinguish prototype entries, but the schema is not
//!    a complete Cargo/rustc fingerprint and cannot authorize production reuse.
//!
//! 2. **No pure binary candidates.** Every stored entry contains a certificate
//!    artifact stored beside the rlib/rmeta. A lookup that finds artifacts but
//!    no certificate returns `Ok(None)` and treats the entry as corrupt.
//!
//! This crate checks content-addressing and a same-machine integrity tag; it
//! does **not** validate certificate semantics and the locally derived tag is
//! not a security boundary against another process running as the same user.
//! Consequently, a hit is never proof evidence and must be revalidated live
//! before any artifact is consumed. No production compiler path currently
//! consumes this cache.
//!
//! See [`storage::BuildCache`] for the on-disk layout and
//! [`key::CacheKey::compute`] for the hash composition.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod entry;
pub mod error;
pub mod inputs;
pub(crate) mod integrity;
pub mod key;
pub mod storage;

pub use entry::{CacheEntry, EntryMetadata, StoreRequest};
pub use error::{BuildCacheError, Result};
pub use inputs::{fingerprint_binary, hash_file, hash_sources, normalize_versions};
pub use key::{CacheInputs, CacheKey};
pub use storage::{BuildCache, CacheStats, GcReport};
