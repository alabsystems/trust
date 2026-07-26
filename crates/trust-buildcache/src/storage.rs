//! Filesystem-backed [`BuildCache`].
//!
//! Layout under `root/`:
//!
//! ```text
//! root/
//!   objects/<first-byte>/<rest-of-hash>/
//!     rlib
//!     rmeta
//!     depfile
//!     certificate.json
//!     metadata.json       (HMAC-sealed, immutable post-store)
//!     access.txt          (NOT sealed, mutated on every lookup)
//!     hmac.hex
//!   index/
//! ```
//!
//! Cache candidates MUST carry the certificate artifact stored with the build.
//! A lookup that finds artifacts but no `certificate.json` returns
//! `Ok(None)` and (eventually) evicts the corrupt entry. Pure binary hits
//! are never returned. Presence and byte integrity do not validate certificate
//! semantics; callers must revalidate candidates live.
//!
//! ## Sealed vs mutable per-entry state
//!
//! `metadata.json` holds the entry's IMMUTABLE identity: key_hex,
//! stored_at_unix_ms, size_bytes. It's covered by the HMAC seal.
//!
//! `access.txt` holds MUTABLE LRU bookkeeping: last_access_unix_ms and
//! hit_count. It lives outside the seal so concurrent lookups can bump
//! it without invalidating the HMAC over the immutable artifacts.
//! Best-effort: a torn or lost write only loses LRU precision, never
//! integrity. Writes are tempfile + atomic rename so readers see a
//! consistent file.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use crate::entry::{CacheEntry, EntryMetadata, StoreRequest};
use crate::error::{BuildCacheError, Result};
use crate::key::CacheKey;

/// Filesystem-backed, content-addressed artifact-candidate cache.
///
/// Construct with [`BuildCache::open`]. Default cache root is
/// `~/.trust/cache` (override via `TRUST_CACHE_DIR`).
pub struct BuildCache {
    root: PathBuf,
}

#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    pub entries: u64,
    pub total_bytes: u64,
    pub last_gc_unix_ms: Option<u64>,
}

#[derive(Debug, Clone, Default)]
pub struct GcReport {
    pub entries_evicted: u64,
    pub bytes_freed: u64,
}

/// The HMAC-sealed slice of an entry's metadata. Written once at
/// [`BuildCache::store`] time, never mutated again. Lives in
/// `metadata.json` under the HMAC seal.
///
/// Old `metadata.json` files written before the split also carry
/// `last_access_unix_ms` and `hit_count`; serde will silently ignore
/// them when deserializing into this newer schema.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SealedMetadata {
    key_hex: String,
    stored_at_unix_ms: u64,
    size_bytes: u64,
}

/// The MUTABLE slice of an entry's metadata. Written outside the HMAC
/// seal so concurrent lookups can bump it without re-sealing. Lives in
/// `access.txt`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct AccessInfo {
    last_access_unix_ms: u64,
    hit_count: u64,
}

const ACCESS_FILENAME: &str = "access.txt";
const METADATA_FILENAME: &str = "metadata.json";
const LAST_GC_FILENAME: &str = "last_gc_unix_ms";

impl BuildCache {
    /// Open or create the cache at `root`. Creates `objects/` and `index/`
    /// subdirectories. Does not validate existing entries.
    pub fn open(root: impl Into<PathBuf>) -> Result<Self> {
        let root = root.into();
        std::fs::create_dir_all(&root).map_err(|error| BuildCacheError::io(&root, error))?;
        require_real_directory(&root)?;
        for sub in ["objects", "index"] {
            let p = root.join(sub);
            std::fs::create_dir_all(&p).map_err(|error| BuildCacheError::io(&p, error))?;
            require_real_directory(&p)?;
        }
        Ok(Self { root })
    }

    /// Open an already initialized artifact cache without creating files or
    /// directories.
    ///
    /// Returns `Ok(None)` when `root` is absent, or when it exists only as a
    /// shared namespace for another Trust cache (for example native capability
    /// probes) and neither `objects/` nor `index/` exists. A half-initialized
    /// artifact cache is an error rather than a silent empty cache.
    pub fn open_existing(root: impl Into<PathBuf>) -> Result<Option<Self>> {
        let root = root.into();
        match std::fs::symlink_metadata(&root) {
            Ok(_) => require_real_directory(&root)?,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(BuildCacheError::io(&root, error)),
        }

        let objects = root.join("objects");
        let index = root.join("index");
        let objects_exists = path_exists_without_following(&objects)?;
        let index_exists = path_exists_without_following(&index)?;
        match (objects_exists, index_exists) {
            (false, false) => Ok(None),
            (true, true) => {
                require_real_directory(&objects)?;
                require_real_directory(&index)?;
                Ok(Some(Self { root }))
            }
            _ => Err(BuildCacheError::io(
                &root,
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "cache is only partially initialized (objects/ and index/ must both exist)",
                ),
            )),
        }
    }

    /// Default cache root: `$TRUST_CACHE_DIR` if set, else `~/.trust/cache`.
    /// Falls back to `./.trust/cache` if `$HOME` is also unset.
    #[must_use]
    pub fn default_root() -> PathBuf {
        if let Some(dir) = std::env::var_os("TRUST_CACHE_DIR").filter(|dir| !dir.is_empty()) {
            return PathBuf::from(dir);
        }
        let home =
            std::env::var_os("HOME").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
        home.join(".trust").join("cache")
    }

    /// Path to this cache's root.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Look up a cache entry by key.
    ///
    /// Returns `Ok(None)` on:
    /// - cache miss (no object dir)
    /// - corrupt entry (missing `certificate.json` or missing/invalid HMAC)
    /// - unreadable / malformed `metadata.json`
    ///
    /// Never returns a binary candidate without an accompanying certificate
    /// artifact. The certificate has not been semantically validated here.
    /// HMAC verification runs BEFORE LRU bookkeeping, so a tampered entry
    /// is treated as a miss without bumping its access time.
    ///
    /// On hit, bumps `last_access_unix_ms` and `hit_count` in `access.txt`,
    /// which lives outside the HMAC seal. Concurrent lookups on the same
    /// key race on access.txt (last writer wins, occasional lost
    /// increments are acceptable), but never invalidate the seal.
    pub fn lookup(&self, key: &CacheKey) -> Result<Option<CacheEntry>> {
        let _cache_lock = self.lock_cache(false)?;
        self.read_entry(key, true)
    }

    /// Validate and inspect an entry without changing its LRU/access metadata.
    /// This applies the same layout, integrity, and path/key checks as
    /// [`Self::lookup`] and is intended for read-only diagnostics.
    pub fn inspect(&self, key: &CacheKey) -> Result<Option<CacheEntry>> {
        let _cache_lock = self.lock_cache(false)?;
        self.read_entry(key, false)
    }

    fn read_entry(&self, key: &CacheKey, record_access: bool) -> Result<Option<CacheEntry>> {
        let dir = self.object_dir(key);
        if !is_real_directory(&dir) {
            return Ok(None);
        }
        let cert = dir.join("certificate.json");
        if !required_entry_files_are_regular(&dir) {
            return Ok(None);
        }
        // HMAC seal must verify before we touch anything. A failed seal
        // (tampering, partial write, or no seal at all) is treated as a
        // miss; the entry will be cleaned up by the next gc.
        if !crate::integrity::verify_entry(&dir)? {
            return Ok(None);
        }
        let metadata_path = dir.join(METADATA_FILENAME);
        let sealed: SealedMetadata = match std::fs::read(&metadata_path) {
            Ok(bytes) => match serde_json::from_slice(&bytes) {
                Ok(m) => m,
                Err(_) => return Ok(None),
            },
            Err(_) => return Ok(None),
        };
        if sealed.key_hex != key.hex() {
            return Ok(None);
        }

        // Read-modify-write access.txt outside the seal. Concurrent
        // lookups on the same key race here; we accept lost-update
        // semantics on hit_count for LRU bookkeeping.
        let mut access = read_access(&dir).unwrap_or_else(|| AccessInfo {
            last_access_unix_ms: sealed.stored_at_unix_ms,
            hit_count: 0,
        });
        if record_access {
            access.last_access_unix_ms = now_unix_ms();
            access.hit_count = access.hit_count.saturating_add(1);
            // Best-effort: a write failure here doesn't invalidate the hit,
            // but the entry will fall to the bottom of the LRU on next gc.
            let _ = write_access(&dir, &access);
        }

        Ok(Some(CacheEntry {
            rlib: dir.join("rlib"),
            rmeta: dir.join("rmeta"),
            depfile: dir.join("depfile"),
            certificate: cert,
            metadata: EntryMetadata {
                key_hex: sealed.key_hex,
                stored_at_unix_ms: sealed.stored_at_unix_ms,
                last_access_unix_ms: access.last_access_unix_ms,
                hit_count: access.hit_count,
                size_bytes: sealed.size_bytes,
            },
        }))
    }

    /// Store an immutable cache entry under a cross-process shard lock.
    ///
    /// All four artifacts (rlib, rmeta, depfile, certificate) are copied
    /// into the entry directory. The sealed metadata is written and
    /// then HMAC-sealed; the unsealed access.txt is initialized last. Concurrent
    /// writers for one content key serialize: the first completed entry wins,
    /// and later writers accept it without overwriting or mixing its files.
    pub fn store(&self, key: &CacheKey, req: StoreRequest) -> Result<()> {
        let _cache_lock = self.lock_cache(false)?;
        let dir = self.object_dir(key);
        let parent = dir.parent().expect("cache object path has a shard parent");
        std::fs::create_dir_all(parent).map_err(|error| BuildCacheError::io(parent, error))?;
        require_real_directory(parent)?;

        // A lock per content key leaves one permanent inode for every key ever
        // stored: deleting a lock file after unlock is racy because a waiter may
        // still hold the old inode. Serialize at the two-hex shard instead. This
        // preserves same-key exclusion and cross-shard concurrency while bounding
        // persistent coordination files at 256.
        let store_lock_dir = self.root.join("index").join("store-shards");
        std::fs::create_dir_all(&store_lock_dir)
            .map_err(|error| BuildCacheError::io(&store_lock_dir, error))?;
        require_real_directory(&store_lock_dir)?;
        let key_hex = key.hex();
        let lock_path = store_lock_dir.join(format!("{}.lock", &key_hex[..2]));
        let lock = open_regular_lock_file(&lock_path)?;
        fs2::FileExt::lock_exclusive(&lock)
            .map_err(|error| BuildCacheError::io(&lock_path, error))?;

        let result = self.store_locked(&dir, key, req);
        let _ = fs2::FileExt::unlock(&lock);
        result
    }

    fn store_locked(&self, dir: &Path, key: &CacheKey, req: StoreRequest) -> Result<()> {
        match std::fs::create_dir(&dir) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                if is_real_directory(&dir) && existing_entry_matches_key(&dir, key)? {
                    return Ok(());
                }
                return Err(BuildCacheError::IncompleteEntry { key_hex: key.hex() });
            }
            Err(error) => return Err(BuildCacheError::io(&dir, error)),
        }

        let result = self.populate_claimed_entry(&dir, key, req);
        if result.is_err() {
            // Only this writer could have created the claimed directory. A
            // failed population must not strand a permanently occupied key.
            let _ = std::fs::remove_dir_all(&dir);
        }
        result
    }

    fn populate_claimed_entry(&self, dir: &Path, key: &CacheKey, req: StoreRequest) -> Result<()> {
        let now = now_unix_ms();
        let mut size = 0u64;
        for (src, dst_name) in [
            (req.rlib_source.as_path(), "rlib"),
            (req.rmeta_source.as_path(), "rmeta"),
            (req.depfile_source.as_path(), "depfile"),
            (req.certificate_source.as_path(), "certificate.json"),
        ] {
            let dst = dir.join(dst_name);
            std::fs::copy(src, &dst).map_err(|e| BuildCacheError::io(&dst, e))?;
            size += std::fs::metadata(&dst).map_err(|e| BuildCacheError::io(&dst, e))?.len();
        }
        let sealed =
            SealedMetadata { key_hex: key.hex(), stored_at_unix_ms: now, size_bytes: size };
        let metadata_path = dir.join(METADATA_FILENAME);
        let bytes = serde_json::to_vec_pretty(&sealed)?;
        std::fs::write(&metadata_path, bytes)
            .map_err(|e| BuildCacheError::io(&metadata_path, e))?;
        // Seal AFTER writing all artifacts so the HMAC covers the full
        // entry. Without this, lookup treats the entry as a miss.
        crate::integrity::seal_entry(&dir)?;
        // Initialize access.txt OUTSIDE the seal. A failure here is
        // recoverable (lookup falls back to stored_at_unix_ms) so it
        // does not roll back the store.
        let _ = write_access(&dir, &AccessInfo { last_access_unix_ms: now, hit_count: 0 });
        Ok(())
    }

    /// LRU eviction. Removes entries by last-access time until total
    /// cache size is <= `max_size_bytes`. Returns the number of entries
    /// evicted and bytes reclaimed.
    ///
    /// Corrupt entries (invalid layout, seal, metadata, or path/key binding)
    /// are evicted unconditionally before LRU ordering kicks in -- they're
    /// dead weight that can never be returned.
    pub fn gc(&self, max_size_bytes: u64) -> Result<GcReport> {
        let _cache_lock = self.lock_cache(true)?;
        let mut report = GcReport::default();
        // Pre-shard-lock builds left one permanent lock file beside every key.
        // No current writer opens these names, and the cache-wide exclusive lock
        // excludes current stores while they are reclaimed.
        report.bytes_freed = self.remove_legacy_per_key_locks()?;
        let mut entries = self.walk_entries()?;

        // First pass: drop corrupt entries. Deletion failures are surfaced;
        // never claim bytes were freed when the directory is still present.
        let mut valid_entries = Vec::with_capacity(entries.len());
        for entry in entries {
            if !entry.valid {
                std::fs::remove_dir_all(&entry.dir)
                    .map_err(|error| BuildCacheError::io(&entry.dir, error))?;
                report.entries_evicted += 1;
                report.bytes_freed += entry.size_bytes;
            } else {
                valid_entries.push(entry);
            }
        }
        entries = valid_entries;

        let total: u64 = entries.iter().map(|e| e.size_bytes).sum();
        if total <= max_size_bytes {
            self.record_last_gc()?;
            return Ok(report);
        }

        // Sort oldest-first by last_access (falling back to stored_at).
        entries.sort_by_key(|e| e.last_access_unix_ms());

        let mut remaining = total;
        for entry in &entries {
            if remaining <= max_size_bytes {
                break;
            }
            std::fs::remove_dir_all(&entry.dir)
                .map_err(|error| BuildCacheError::io(&entry.dir, error))?;
            report.entries_evicted += 1;
            report.bytes_freed += entry.size_bytes;
            remaining = remaining.saturating_sub(entry.size_bytes);
        }
        self.record_last_gc()?;
        Ok(report)
    }

    /// Cache-wide statistics. Walks the object dir on each call.
    pub fn stats(&self) -> Result<CacheStats> {
        let _cache_lock = self.lock_cache(false)?;
        // Statistics are descriptive, not an integrity decision. HMAC-streaming
        // every rlib/rmeta here made a simple size query O(total cache bytes).
        // Walk names and file metadata only; lookup and GC retain full validation.
        let entry_dirs = self.entry_dirs()?;
        let mut total_bytes = 0u64;
        for dir in &entry_dirs {
            total_bytes = total_bytes.saturating_add(measure_tree_file_bytes(dir)?);
        }
        let last_gc_unix_ms =
            std::fs::read_to_string(self.root.join("index").join(LAST_GC_FILENAME))
                .ok()
                .and_then(|value| value.trim().parse().ok());
        Ok(CacheStats { entries: entry_dirs.len() as u64, total_bytes, last_gc_unix_ms })
    }

    /// Remove every object entry while excluding concurrent stores, lookups,
    /// statistics walks, and garbage collection. The cache root and index stay
    /// in place so the global coordination lock remains valid.
    pub fn clear(&self) -> Result<()> {
        let _cache_lock = self.lock_cache(true)?;
        let objects = self.root.join("objects");
        require_real_directory(&objects)?;
        std::fs::remove_dir_all(&objects).map_err(|error| BuildCacheError::io(&objects, error))?;
        std::fs::create_dir(&objects).map_err(|error| BuildCacheError::io(&objects, error))?;
        Ok(())
    }

    fn lock_cache(&self, exclusive: bool) -> Result<std::fs::File> {
        let lock_path = self.root.join("index").join("cache.lock");
        let lock = open_regular_lock_file(&lock_path)?;
        let lock_result = if exclusive {
            fs2::FileExt::lock_exclusive(&lock)
        } else {
            fs2::FileExt::lock_shared(&lock)
        };
        lock_result.map_err(|error| BuildCacheError::io(&lock_path, error))?;
        Ok(lock)
    }

    fn record_last_gc(&self) -> Result<()> {
        let path = self.root.join("index").join(LAST_GC_FILENAME);
        std::fs::write(&path, now_unix_ms().to_string())
            .map_err(|error| BuildCacheError::io(&path, error))
    }

    /// Walk `objects/` and fully validate one [`WalkedEntry`] per
    /// content-addressed directory. Used by [`Self::gc`].
    fn walk_entries(&self) -> Result<Vec<WalkedEntry>> {
        self.entry_dirs()?.into_iter().map(walked_entry).collect()
    }

    /// Enumerate real content-addressed entry directories without opening or
    /// hashing their artifact payloads.
    fn entry_dirs(&self) -> Result<Vec<PathBuf>> {
        let objects = self.root.join("objects");
        let mut out = Vec::new();
        let shard_iter =
            std::fs::read_dir(&objects).map_err(|error| BuildCacheError::io(&objects, error))?;
        for shard in shard_iter {
            let shard = shard.map_err(|error| BuildCacheError::io(&objects, error))?;
            let shard_path = shard.path();
            if !is_real_directory(&shard_path) {
                continue;
            }
            let inner = std::fs::read_dir(&shard_path)
                .map_err(|error| BuildCacheError::io(&shard_path, error))?;
            for entry in inner {
                let entry = entry.map_err(|error| BuildCacheError::io(&shard_path, error))?;
                let dir = entry.path();
                if !is_real_directory(&dir) {
                    continue;
                }
                out.push(dir);
            }
        }
        Ok(out)
    }

    fn remove_legacy_per_key_locks(&self) -> Result<u64> {
        let objects = self.root.join("objects");
        let mut bytes_freed = 0u64;
        let shards =
            std::fs::read_dir(&objects).map_err(|error| BuildCacheError::io(&objects, error))?;
        for shard in shards {
            let shard = shard.map_err(|error| BuildCacheError::io(&objects, error))?;
            let shard_path = shard.path();
            if !is_real_directory(&shard_path) {
                continue;
            }
            let entries = std::fs::read_dir(&shard_path)
                .map_err(|error| BuildCacheError::io(&shard_path, error))?;
            for entry in entries {
                let entry = entry.map_err(|error| BuildCacheError::io(&shard_path, error))?;
                let path = entry.path();
                let Some(name) = entry.file_name().to_str().map(str::to_owned) else {
                    continue;
                };
                let Some(key_remainder) =
                    name.strip_prefix('.').and_then(|name| name.strip_suffix(".store.lock"))
                else {
                    continue;
                };
                if key_remainder.len() != 62
                    || !key_remainder
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                {
                    continue;
                }
                let metadata = std::fs::symlink_metadata(&path)
                    .map_err(|error| BuildCacheError::io(&path, error))?;
                if !metadata.file_type().is_file() {
                    continue;
                }
                std::fs::remove_file(&path).map_err(|error| BuildCacheError::io(&path, error))?;
                bytes_freed = bytes_freed.saturating_add(metadata.len());
            }
        }
        Ok(bytes_freed)
    }

    fn object_dir(&self, key: &CacheKey) -> PathBuf {
        let hex = key.hex();
        let (head, rest) = hex.split_at(2);
        self.root.join("objects").join(head).join(rest)
    }
}

fn path_exists_without_following(path: &Path) -> Result<bool> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(BuildCacheError::io(path, error)),
    }
}

fn is_real_directory(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_dir())
}

fn require_real_directory(path: &Path) -> Result<()> {
    if is_real_directory(path) {
        return Ok(());
    }
    Err(BuildCacheError::io(
        path,
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "cache path must be a real directory, not a symlink or special file",
        ),
    ))
}

fn open_regular_lock_file(path: &Path) -> Result<std::fs::File> {
    if std::fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_symlink()) {
        return Err(BuildCacheError::io(
            path,
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "cache lock must not be a symlink",
            ),
        ));
    }
    let lock = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(path)
        .map_err(|error| BuildCacheError::io(path, error))?;
    if !lock.metadata().map_err(|error| BuildCacheError::io(path, error))?.file_type().is_file() {
        return Err(BuildCacheError::io(
            path,
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "cache lock is not a regular file",
            ),
        ));
    }
    Ok(lock)
}

fn required_entry_files_are_regular(dir: &Path) -> bool {
    ["rlib", "rmeta", "depfile", "certificate.json", METADATA_FILENAME, "hmac.hex"].iter().all(
        |name| {
            std::fs::symlink_metadata(dir.join(name))
                .is_ok_and(|metadata| metadata.file_type().is_file())
        },
    )
}

fn existing_entry_matches_key(dir: &Path, key: &CacheKey) -> Result<bool> {
    if !required_entry_files_are_regular(dir) || !crate::integrity::verify_entry(dir)? {
        return Ok(false);
    }
    let metadata = match std::fs::read(dir.join(METADATA_FILENAME))
        .ok()
        .and_then(|bytes| serde_json::from_slice::<SealedMetadata>(&bytes).ok())
    {
        Some(metadata) => metadata,
        None => return Ok(false),
    };
    Ok(metadata.key_hex == key.hex())
}

fn now_unix_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as u64).unwrap_or(0)
}

/// Read the unsealed access.txt sidecar. Returns `None` on missing /
/// unreadable / malformed file -- callers fall back to defaults.
fn read_access(dir: &Path) -> Option<AccessInfo> {
    let bytes = std::fs::read(dir.join(ACCESS_FILENAME)).ok()?;
    serde_json::from_slice(&bytes).ok()
}

/// Atomically write access.txt via tempfile + rename. The rename is the
/// commit point: concurrent readers see either the old or new file in
/// full, never a torn write. Returns `Ok(())` on success; errors are
/// best-effort and intentionally not surfaced to callers (LRU is a
/// hint, not a correctness invariant).
fn write_access(dir: &Path, access: &AccessInfo) -> std::io::Result<()> {
    let bytes = serde_json::to_vec(access).map_err(std::io::Error::other)?;
    // Embed PID + nanos to disambiguate concurrent writers' tempfiles.
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let tmp_name = format!(".access.tmp.{}.{}", std::process::id(), nanos);
    let tmp = dir.join(&tmp_name);
    std::fs::write(&tmp, &bytes)?;
    let final_path = dir.join(ACCESS_FILENAME);
    // The platform rename primitive is the commit point. This bookkeeping is
    // explicitly best-effort: filesystems that cannot replace the destination
    // report an error, and callers retain the prior complete sidecar.
    if let Err(e) = std::fs::rename(&tmp, &final_path) {
        let _ = std::fs::remove_file(&tmp);
        return Err(e);
    }
    Ok(())
}

struct WalkedEntry {
    dir: PathBuf,
    sealed: Option<SealedMetadata>,
    access: Option<AccessInfo>,
    valid: bool,
    size_bytes: u64,
}

impl WalkedEntry {
    /// Effective LRU timestamp: access.last_access_unix_ms if present,
    /// else the sealed stored_at_unix_ms, else 0 (oldest).
    fn last_access_unix_ms(&self) -> u64 {
        self.access
            .as_ref()
            .map(|a| a.last_access_unix_ms)
            .or_else(|| self.sealed.as_ref().map(|s| s.stored_at_unix_ms))
            .unwrap_or(0)
    }
}

fn walked_entry(dir: PathBuf) -> Result<WalkedEntry> {
    let sealed = match std::fs::read(dir.join(METADATA_FILENAME)) {
        Ok(bytes) => serde_json::from_slice::<SealedMetadata>(&bytes).ok(),
        Err(_) => None,
    };
    let expected_key_hex = object_path_key_hex(&dir);
    let valid = required_entry_files_are_regular(&dir)
        && crate::integrity::verify_entry(&dir).unwrap_or(false)
        && sealed
            .as_ref()
            .zip(expected_key_hex.as_ref())
            .is_some_and(|(metadata, expected)| metadata.key_hex == *expected);
    let access = read_access(&dir);
    // GC and statistics operate on actual stored file bytes, including seal,
    // metadata, and unexpected corrupt payloads. The sealed `size_bytes` field
    // describes only the four artifact payloads and must not enforce a disk cap.
    let size_bytes = measure_tree_file_bytes(&dir)?;
    Ok(WalkedEntry { dir, sealed, access, valid, size_bytes })
}

fn object_path_key_hex(dir: &Path) -> Option<String> {
    let shard = dir.parent()?.file_name()?.to_str()?;
    let remainder = dir.file_name()?.to_str()?;
    if shard.len() != 2 || remainder.len() != 62 {
        return None;
    }
    let key = format!("{shard}{remainder}");
    key.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)).then_some(key)
}

fn measure_tree_file_bytes(dir: &Path) -> Result<u64> {
    let mut total = 0u64;
    let entries = std::fs::read_dir(dir).map_err(|error| BuildCacheError::io(dir, error))?;
    for entry in entries {
        let entry = entry.map_err(|error| BuildCacheError::io(dir, error))?;
        let path = entry.path();
        let metadata =
            std::fs::symlink_metadata(&path).map_err(|error| BuildCacheError::io(&path, error))?;
        if metadata.file_type().is_file() {
            total = total.saturating_add(metadata.len());
        } else if metadata.file_type().is_dir() {
            total = total.saturating_add(measure_tree_file_bytes(&path)?);
        }
    }
    Ok(total)
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use tempfile::TempDir;

    use super::*;
    use crate::key::CacheInputs;

    fn key_for(label: &str) -> CacheKey {
        let policy = label.to_string();
        let inputs = CacheInputs {
            source_hashes: &[],
            transitive_dep_hashes: &[],
            trustc_fingerprint: "test-fingerprint",
            dmath_versions: &[],
            verification_policy: &policy,
            target_triple: "aarch64-apple-darwin",
            profile: "dev",
            codegen_flags: &[],
            rustc_version: "1.0.0",
            edition: "2024",
        };
        CacheKey::compute(&inputs)
    }

    fn write_artifact(dir: &Path, name: &str, body: &[u8]) -> PathBuf {
        let p = dir.join(name);
        let mut f = std::fs::File::create(&p).expect("create artifact");
        f.write_all(body).expect("write artifact");
        p
    }

    #[test]
    fn round_trip_store_then_lookup() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("policy-A");

        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let req = StoreRequest {
            rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib-bytes"),
            rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta-bytes"),
            depfile_source: write_artifact(&src_dir, "lib.d", b"depfile"),
            certificate_source: write_artifact(&src_dir, "cert.json", b"{\"ok\":true}"),
        };

        cache.store(&key, req).expect("store");

        let entry = cache.lookup(&key).expect("lookup ok").expect("hit");
        assert_eq!(entry.metadata.key_hex, key.hex());
        // First lookup bumps hit_count from 0 to 1.
        assert_eq!(entry.metadata.hit_count, 1);
        assert!(entry.metadata.size_bytes > 0);
        assert!(entry.rlib.is_file());
        assert!(entry.certificate.is_file());

        // Second lookup bumps to 2 -- LRU bookkeeping persists across calls.
        let entry2 = cache.lookup(&key).expect("lookup ok").expect("hit");
        assert_eq!(entry2.metadata.hit_count, 2);
    }

    #[test]
    fn inspect_validates_without_counting_a_hit() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("inspect-key");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        cache
            .store(
                &key,
                StoreRequest {
                    rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
                    rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
                    depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
                    certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
                },
            )
            .expect("store");

        assert_eq!(cache.inspect(&key).unwrap().unwrap().metadata.hit_count, 0);
        assert_eq!(cache.inspect(&key).unwrap().unwrap().metadata.hit_count, 0);
        assert_eq!(cache.lookup(&key).unwrap().unwrap().metadata.hit_count, 1);
    }

    #[test]
    fn clear_removes_entries_and_leaves_a_usable_cache() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("clear-key");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        cache
            .store(
                &key,
                StoreRequest {
                    rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
                    rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
                    depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
                    certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
                },
            )
            .expect("store");

        cache.clear().expect("clear");
        assert!(cache.lookup(&key).expect("lookup").is_none());
        assert_eq!(cache.stats().expect("stats").entries, 0);
        assert!(cache.root().join("objects").is_dir());
    }

    #[test]
    fn stats_records_the_last_successful_gc() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        assert_eq!(cache.stats().unwrap().last_gc_unix_ms, None);
        cache.gc(u64::MAX).expect("gc");
        assert!(cache.stats().unwrap().last_gc_unix_ms.is_some());
    }

    #[test]
    fn immutable_same_key_store_never_mixes_or_overwrites_artifacts() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("immutable-key");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();

        let request = |tag: &str| StoreRequest {
            rlib_source: write_artifact(
                &src_dir,
                &format!("{tag}.rlib"),
                format!("{tag}-rlib").as_bytes(),
            ),
            rmeta_source: write_artifact(
                &src_dir,
                &format!("{tag}.rmeta"),
                format!("{tag}-rmeta").as_bytes(),
            ),
            depfile_source: write_artifact(
                &src_dir,
                &format!("{tag}.d"),
                format!("{tag}-dep").as_bytes(),
            ),
            certificate_source: write_artifact(
                &src_dir,
                &format!("{tag}.json"),
                format!("{{\"tag\":\"{tag}\"}}").as_bytes(),
            ),
        };

        cache.store(&key, request("first")).expect("first store");
        cache.store(&key, request("second")).expect("equivalent key is already populated");
        let entry = cache.lookup(&key).expect("lookup").expect("candidate");
        assert_eq!(std::fs::read(entry.rlib).unwrap(), b"first-rlib");
        assert_eq!(std::fs::read(entry.rmeta).unwrap(), b"first-rmeta");
        assert_eq!(std::fs::read(entry.depfile).unwrap(), b"first-dep");
        assert_eq!(std::fs::read(entry.certificate).unwrap(), br#"{"tag":"first"}"#);
    }

    #[test]
    fn incomplete_existing_key_is_never_overwritten() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("incomplete-key");
        let dir = cache.object_dir(&key);
        std::fs::create_dir_all(&dir).expect("incomplete key dir");
        std::fs::write(dir.join("attacker-marker"), b"preserve").unwrap();

        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let error = cache
            .store(
                &key,
                StoreRequest {
                    rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
                    rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
                    depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
                    certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
                },
            )
            .expect_err("occupied incomplete key must fail closed");
        assert!(matches!(error, BuildCacheError::IncompleteEntry { .. }));
        assert_eq!(std::fs::read(dir.join("attacker-marker")).unwrap(), b"preserve");
        assert!(!dir.join("rlib").exists());
    }

    #[test]
    fn sealed_entry_relocated_under_another_key_is_rejected() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let source_key = key_for("source-key");
        let destination_key = key_for("destination-key");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let request = || StoreRequest {
            rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
            rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
            depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
            certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
        };

        cache.store(&source_key, request()).expect("store source entry");
        let source_dir = cache.object_dir(&source_key);
        let destination_dir = cache.object_dir(&destination_key);
        std::fs::create_dir_all(destination_dir.parent().unwrap()).unwrap();
        std::fs::rename(&source_dir, &destination_dir).expect("relocate sealed entry");

        assert!(
            crate::integrity::verify_entry(&destination_dir).expect("verify seal"),
            "the integrity tag alone does not bind an entry to its path"
        );
        assert!(cache.lookup(&destination_key).expect("lookup").is_none());
        let error = cache
            .store(&destination_key, request())
            .expect_err("a differently keyed sealed entry must not occupy this key");
        assert!(matches!(error, BuildCacheError::IncompleteEntry { .. }));
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_key_directory_is_rejected() {
        use std::os::unix::fs::symlink;

        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("symlink-key");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let request = || StoreRequest {
            rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
            rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
            depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
            certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
        };

        cache.store(&key, request()).expect("store entry");
        let key_dir = cache.object_dir(&key);
        let relocated = tmp.path().join("relocated-entry");
        std::fs::rename(&key_dir, &relocated).expect("relocate entry");
        symlink(&relocated, &key_dir).expect("symlink key path");

        assert!(cache.lookup(&key).expect("lookup").is_none());
        let error = cache
            .store(&key, request())
            .expect_err("a symlink must never satisfy or replace a cache key");
        assert!(matches!(error, BuildCacheError::IncompleteEntry { .. }));
    }

    #[cfg(unix)]
    #[test]
    fn open_rejects_symlinked_cache_root_and_object_directory() {
        use std::os::unix::fs::symlink;

        let tmp = TempDir::new().expect("tempdir");
        let real_root = tmp.path().join("real-root");
        std::fs::create_dir_all(&real_root).unwrap();
        let linked_root = tmp.path().join("linked-root");
        symlink(&real_root, &linked_root).unwrap();
        assert!(BuildCache::open(&linked_root).is_err());

        let cache_root = tmp.path().join("cache");
        let external_objects = tmp.path().join("external-objects");
        std::fs::create_dir_all(&cache_root).unwrap();
        std::fs::create_dir_all(&external_objects).unwrap();
        symlink(&external_objects, cache_root.join("objects")).unwrap();
        assert!(BuildCache::open(&cache_root).is_err());
    }

    #[test]
    fn open_existing_never_initializes_a_missing_or_unrelated_cache() {
        let tmp = TempDir::new().expect("tempdir");
        let missing = tmp.path().join("missing-cache");
        assert!(BuildCache::open_existing(&missing).unwrap().is_none());
        assert!(!missing.exists(), "read-only open must not create the cache root");

        let shared_root = tmp.path().join("shared-cache-root");
        std::fs::create_dir_all(shared_root.join("native-capability-probes")).unwrap();
        assert!(BuildCache::open_existing(&shared_root).unwrap().is_none());
        assert!(!shared_root.join("objects").exists());
        assert!(!shared_root.join("index").exists());

        let initialized = BuildCache::open(&shared_root).unwrap();
        assert_eq!(
            BuildCache::open_existing(&shared_root).unwrap().unwrap().root(),
            initialized.root()
        );
    }

    #[test]
    fn store_coordination_files_are_bounded_by_key_shards() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let request = || StoreRequest {
            rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
            rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
            depfile_source: write_artifact(&src_dir, "lib.d", b"dep"),
            certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
        };

        for index in 0..300 {
            cache.store(&key_for(&format!("shard-lock-{index}")), request()).unwrap();
        }

        let lock_dir = cache.root().join("index/store-shards");
        let lock_files = std::fs::read_dir(&lock_dir).unwrap().count();
        assert!(lock_files <= 256, "one lock per shard bounds persistent coordination state");
        assert!(lock_files > 1, "the fixture should exercise multiple shards");
        for shard in std::fs::read_dir(cache.root().join("objects")).unwrap() {
            for entry in std::fs::read_dir(shard.unwrap().path()).unwrap() {
                assert!(
                    !entry.unwrap().file_name().to_string_lossy().ends_with(".store.lock"),
                    "per-key store locks must not leak into object shards"
                );
            }
        }
    }

    #[test]
    fn gc_removes_legacy_per_key_lock_files() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("legacy-lock");
        let key_hex = key.hex();
        let shard = cache.root().join("objects").join(&key_hex[..2]);
        std::fs::create_dir_all(&shard).unwrap();
        let legacy_lock = shard.join(format!(".{}.store.lock", &key_hex[2..]));
        std::fs::write(&legacy_lock, b"legacy-lock-bytes").unwrap();

        let report = cache.gc(u64::MAX).unwrap();
        assert!(!legacy_lock.exists());
        assert!(report.bytes_freed >= b"legacy-lock-bytes".len() as u64);
        assert_eq!(report.entries_evicted, 0);
    }

    #[test]
    fn lookup_bumps_access_without_invalidating_seal() {
        // Regression: pre-split, lookup rewrote metadata.json inside the
        // HMAC scope and re-sealed. That made concurrent same-key lookups
        // race on the seal. With access.txt outside the seal, bumping
        // access must leave the HMAC intact.
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("seal-stability");

        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        cache
            .store(
                &key,
                StoreRequest {
                    rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
                    rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
                    depfile_source: write_artifact(&src_dir, "lib.d", b"d"),
                    certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
                },
            )
            .expect("store");

        let dir = cache.object_dir(&key);
        // Capture sealed metadata + HMAC tag before any lookup.
        let metadata_before = std::fs::read(dir.join(METADATA_FILENAME)).expect("read meta");
        let hmac_before = std::fs::read(dir.join("hmac.hex")).expect("read hmac");

        // Twenty lookups must not perturb the sealed metadata or HMAC.
        for _ in 0..20 {
            assert!(cache.lookup(&key).expect("lookup ok").is_some());
        }
        let metadata_after = std::fs::read(dir.join(METADATA_FILENAME)).expect("read meta");
        let hmac_after = std::fs::read(dir.join("hmac.hex")).expect("read hmac");

        assert_eq!(metadata_before, metadata_after, "metadata.json must be immutable post-store");
        assert_eq!(hmac_before, hmac_after, "HMAC seal must not be re-sealed by lookup");
    }

    #[test]
    fn gc_evicts_oldest_entries_until_under_cap() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();

        let make_req = |suffix: &str, body_size: usize| {
            let body = vec![0u8; body_size];
            StoreRequest {
                rlib_source: write_artifact(&src_dir, &format!("lib-{suffix}.rlib"), &body),
                rmeta_source: write_artifact(&src_dir, &format!("lib-{suffix}.rmeta"), &body),
                depfile_source: write_artifact(&src_dir, &format!("lib-{suffix}.d"), b"d"),
                certificate_source: write_artifact(
                    &src_dir,
                    &format!("cert-{suffix}.json"),
                    b"{\"ok\":true}",
                ),
            }
        };

        // Three entries, ~1KB each. Store with a small sleep between so
        // last_access_unix_ms ordering is well-defined.
        let k1 = key_for("policy-1");
        cache.store(&k1, make_req("1", 1024)).expect("store 1");
        std::thread::sleep(std::time::Duration::from_millis(5));
        let k2 = key_for("policy-2");
        cache.store(&k2, make_req("2", 1024)).expect("store 2");
        std::thread::sleep(std::time::Duration::from_millis(5));
        let k3 = key_for("policy-3");
        cache.store(&k3, make_req("3", 1024)).expect("store 3");

        // Touch k1 so it's most recently accessed.
        let _ = cache.lookup(&k1).expect("lookup ok");

        let before = cache.stats().expect("stats");
        assert_eq!(before.entries, 3);

        // Set cap small enough to force eviction of one entry. k2 is now
        // the oldest (k3 was touched implicitly by store, k1 by lookup).
        let cap = before.total_bytes / 2;
        let report = cache.gc(cap).expect("gc");
        assert!(report.entries_evicted >= 1);

        // k1 should still be present (most recently accessed).
        assert!(cache.lookup(&k1).expect("lookup ok").is_some());
    }

    #[test]
    fn gc_evicts_corrupt_entries_unconditionally() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("policy-corrupt");

        // Manually create object dir with rlib only (no certificate).
        let dir = cache.root().join("objects").join(&key.hex()[..2]).join(&key.hex()[2..]);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("rlib"), b"rlib-bytes").unwrap();

        // gc with infinite cap still evicts the corrupt entry.
        let report = cache.gc(u64::MAX).expect("gc");
        assert_eq!(report.entries_evicted, 1);
        assert!(!dir.exists());
    }

    #[test]
    fn lookup_miss_returns_none() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("never-stored");
        assert!(cache.lookup(&key).expect("lookup ok").is_none());
    }

    #[test]
    fn missing_certificate_is_treated_as_miss() {
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("policy-B");

        // Manually create the object dir with rlib but no certificate.
        let dir = cache.root().join("objects").join(&key.hex()[..2]).join(&key.hex()[2..]);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("rlib"), b"rlib").unwrap();

        // No certificate.json -> lookup must return None.
        assert!(cache.lookup(&key).expect("lookup ok").is_none());
    }

    #[test]
    fn lookup_falls_back_to_stored_at_when_access_missing() {
        // If access.txt is deleted (older entry pre-dating this split,
        // or a partial write was rolled back) lookup must still succeed
        // -- it just starts hit_count over from zero.
        let tmp = TempDir::new().expect("tempdir");
        let cache = BuildCache::open(tmp.path().join("cache")).expect("open cache");
        let key = key_for("legacy-no-access");

        let src_dir = tmp.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        cache
            .store(
                &key,
                StoreRequest {
                    rlib_source: write_artifact(&src_dir, "lib.rlib", b"rlib"),
                    rmeta_source: write_artifact(&src_dir, "lib.rmeta", b"rmeta"),
                    depfile_source: write_artifact(&src_dir, "lib.d", b"d"),
                    certificate_source: write_artifact(&src_dir, "cert.json", b"{}"),
                },
            )
            .expect("store");

        let dir = cache.object_dir(&key);
        std::fs::remove_file(dir.join(ACCESS_FILENAME)).expect("rm access");

        let entry = cache.lookup(&key).expect("lookup ok").expect("hit");
        assert_eq!(entry.metadata.hit_count, 1);
    }
}
