// trust-cache/src/coordination.rs: File-based cache coordination for concurrent compilations
//
// Provides advisory file locking (flock-style) to prevent cache corruption when
// multiple Trust compilations run concurrently (e.g., parallel agent worktrees).
//
// Key features:
// - Advisory file locks via fs2 for cross-platform flock support
// - Stable lock-file inodes: sentinel files are never unlinked based on age
// - Content-hash-based invalidation: cache files include a content hash so readers
//   can detect writes from other processes without holding a lock
// - Shared (read) and exclusive (write) lock modes
//
// Cache coordination for concurrent trustc compilations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::hash_map::RandomState;
use std::fs::{self, File, OpenOptions};
use std::hash::{BuildHasher, Hash, Hasher};
use std::io::{self, Write};
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

/// Trait alias for fs2 locking to avoid conflict with std's nightly File::try_lock_*.
/// On nightly rustc, `std::fs::File` has built-in `try_lock_shared`/`try_lock_exclusive`
/// that return `Result<(), TryLockError>` -- these shadow fs2's `io::Result<()>` methods.
/// We use fully-qualified syntax to call fs2's version explicitly.
use fs2::FileExt as Fs2FileExt;
use sha2::{Digest, Sha256};
use thiserror::Error;

/// Legacy stale-lock threshold default, retained for API/config compatibility.
///
/// Advisory locks are released automatically when their owning process exits.
/// The sentinel must never be unlinked based on mtime: doing so while its inode
/// is still locked would let a second process lock a new inode at the same path.
const DEFAULT_STALE_LOCK_SECS: u64 = 300;

/// Errors from cache coordination operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CoordinationError {
    #[error("lock I/O error on {path}: {source}")]
    LockIo { path: PathBuf, source: io::Error },
    #[error("lock acquisition timed out on {path} after {timeout_ms}ms")]
    LockTimeout { path: PathBuf, timeout_ms: u64 },
    #[error("content hash mismatch: expected {expected}, found {found}")]
    ContentHashMismatch { expected: String, found: String },
}

/// Configuration for cache coordination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoordinationConfig {
    /// Legacy compatibility setting. It is intentionally ignored.
    ///
    /// The OS releases advisory locks on process exit, while unlinking an old
    /// sentinel can break mutual exclusion if a live process still locks that
    /// inode. Lock sentinel files are therefore safe to leave in place.
    pub stale_lock_threshold_secs: u64,
    /// Whether to enable content-hash validation on cache reads.
    pub validate_content_hash: bool,
}

impl Default for CoordinationConfig {
    fn default() -> Self {
        Self { stale_lock_threshold_secs: DEFAULT_STALE_LOCK_SECS, validate_content_hash: true }
    }
}

/// An advisory file lock guard.
///
/// Holds an flock advisory lock on a `.lock` file adjacent to the cache file.
/// The lock is released when this guard is dropped.
///
/// Uses `fs2::FileExt` for cross-platform flock support (works on macOS, Linux,
/// and Windows). The lock is process-scoped and automatically released if the
/// process crashes.
pub struct CacheLockGuard {
    /// The lock file handle. Lock is released on drop (via fs2).
    _file: File,
    /// Path to the lock file (for diagnostics).
    lock_path: PathBuf,
}

impl CacheLockGuard {
    /// Path to the lock file being held.
    #[must_use]
    pub fn lock_path(&self) -> &Path {
        &self.lock_path
    }
}

impl Drop for CacheLockGuard {
    fn drop(&mut self) {
        // fs2 automatically releases the flock when the File is dropped,
        // but we explicitly unlock for clarity and to handle edge cases.
        let _ = Fs2FileExt::unlock(&self._file);
    }
}

/// Acquire a shared (read) lock on the cache file.
///
/// Multiple readers can hold shared locks simultaneously. A shared lock
/// blocks exclusive lock acquisition but not other shared locks.
///
/// The lock sentinel is never removed based on its age. Its stable inode is the
/// rendezvous point all processes must lock.
pub fn acquire_shared_lock(
    cache_path: &Path,
    _config: &CoordinationConfig,
) -> Result<CacheLockGuard, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    let file = open_lock_file(&lock_path)?;
    Fs2FileExt::lock_shared(&file)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.clone(), source: e })?;
    Ok(CacheLockGuard { _file: file, lock_path })
}

/// Acquire an exclusive (write) lock on the cache file.
///
/// Only one writer can hold an exclusive lock. This blocks all other
/// shared and exclusive lock acquisitions.
///
/// The lock sentinel is never removed based on its age. Its stable inode is the
/// rendezvous point all processes must lock.
pub fn acquire_exclusive_lock(
    cache_path: &Path,
    _config: &CoordinationConfig,
) -> Result<CacheLockGuard, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    let file = open_lock_file(&lock_path)?;
    Fs2FileExt::lock_exclusive(&file)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.clone(), source: e })?;
    Ok(CacheLockGuard { _file: file, lock_path })
}

/// Try to acquire a shared lock without blocking.
///
/// Returns `Ok(Some(guard))` on success, `Ok(None)` if the lock is held
/// exclusively by another process.
pub fn try_shared_lock(
    cache_path: &Path,
    _config: &CoordinationConfig,
) -> Result<Option<CacheLockGuard>, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    let file = open_lock_file(&lock_path)?;
    match Fs2FileExt::try_lock_shared(&file) {
        Ok(()) => Ok(Some(CacheLockGuard { _file: file, lock_path })),
        Err(ref e) if is_would_block(e) => Ok(None),
        Err(e) => Err(CoordinationError::LockIo { path: lock_path, source: e }),
    }
}

/// Try to acquire an exclusive lock without blocking.
///
/// Returns `Ok(Some(guard))` on success, `Ok(None)` if the lock is held
/// by another process.
pub fn try_exclusive_lock(
    cache_path: &Path,
    _config: &CoordinationConfig,
) -> Result<Option<CacheLockGuard>, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    let file = open_lock_file(&lock_path)?;
    match Fs2FileExt::try_lock_exclusive(&file) {
        Ok(()) => Ok(Some(CacheLockGuard { _file: file, lock_path })),
        Err(ref e) if is_would_block(e) => Ok(None),
        Err(e) => Err(CoordinationError::LockIo { path: lock_path, source: e }),
    }
}

/// Compute the SHA-256 content hash of a file on disk.
///
/// Returns the hex-encoded hash, or an empty string if the file does not exist.
/// This hash is used for content-based invalidation: if the hash of the file
/// on disk differs from what we expect, another process has written to it.
#[must_use]
pub fn file_content_hash(path: &Path) -> String {
    match fs::read(path) {
        Ok(bytes) => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            format!("{:x}", hasher.finalize())
        }
        Err(_) => String::new(),
    }
}

/// Validate that a cache file's content hash matches the expected value.
///
/// Returns `Ok(())` if the hashes match or the expected hash is empty
/// (indicating no prior state to validate against). Returns
/// `Err(CoordinationError::ContentHashMismatch)` otherwise.
pub fn validate_content_hash(path: &Path, expected_hash: &str) -> Result<(), CoordinationError> {
    if expected_hash.is_empty() {
        return Ok(());
    }
    let actual = file_content_hash(path);
    if actual.is_empty() {
        // File doesn't exist -- no mismatch
        return Ok(());
    }
    if actual != expected_hash {
        return Err(CoordinationError::ContentHashMismatch {
            expected: expected_hash.to_string(),
            found: actual,
        });
    }
    Ok(())
}

/// Coordinated read: acquire shared lock, read file, validate content hash.
///
/// Returns `(contents, content_hash)` on success. The caller can store the
/// content hash and use it later to detect concurrent writes.
pub fn coordinated_read(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<(String, String, CacheLockGuard), CoordinationError> {
    let guard = acquire_shared_lock(cache_path, config)?;
    let contents = fs::read_to_string(cache_path)
        .map_err(|e| CoordinationError::LockIo { path: cache_path.to_path_buf(), source: e })?;
    let hash = {
        let mut hasher = Sha256::new();
        hasher.update(contents.as_bytes());
        format!("{:x}", hasher.finalize())
    };
    Ok((contents, hash, guard))
}

/// Coordinated write: acquire exclusive lock, write file atomically.
///
/// Writes to a temporary file first, then renames to the target path.
/// This ensures readers never see a partially-written file. Returns
/// the content hash of the written data.
pub fn coordinated_write(
    cache_path: &Path,
    data: &str,
    config: &CoordinationConfig,
) -> Result<(String, CacheLockGuard), CoordinationError> {
    let guard = acquire_exclusive_lock(cache_path, config)?;

    atomic_write_replace(cache_path, data.as_bytes())
        .map_err(|e| CoordinationError::LockIo { path: cache_path.to_path_buf(), source: e })?;

    let hash = {
        let mut hasher = Sha256::new();
        hasher.update(data.as_bytes());
        format!("{:x}", hasher.finalize())
    };
    Ok((hash, guard))
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Check if an I/O error represents a "would block" condition.
///
/// `fs2::try_lock_*` returns a plain `io::Error`. On Unix, the "lock is held"
/// condition is `EWOULDBLOCK` (= `EAGAIN`), which maps to `ErrorKind::WouldBlock`.
fn is_would_block(err: &io::Error) -> bool {
    err.kind() == io::ErrorKind::WouldBlock
        // Some platforms report EAGAIN differently
        || err.raw_os_error() == Some(libc_eagain())
}

/// Platform-specific EAGAIN constant.
fn libc_eagain() -> i32 {
    // EAGAIN is 35 on macOS, 11 on Linux
    #[cfg(target_os = "macos")]
    {
        35
    }
    #[cfg(target_os = "linux")]
    {
        11
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        -1
    } // Will never match, fall back to kind() check
}

/// Compute the lock file path for a given cache file.
///
/// The lock file is `<cache_path>.lock` in the same directory.
fn lock_path_for(cache_path: &Path) -> PathBuf {
    let mut lock_path = cache_path.as_os_str().to_owned();
    lock_path.push(".lock");
    PathBuf::from(lock_path)
}

/// Open (or create) the lock file.
fn open_lock_file(lock_path: &Path) -> Result<File, CoordinationError> {
    if let Some(parent) = lock_path.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| CoordinationError::LockIo { path: lock_path.to_path_buf(), source: e })?;
    }
    OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(lock_path)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.to_path_buf(), source: e })
}

/// Atomically replace `path` without ever opening the destination for writing.
///
/// Bytes are first written and synced through a freshly-created, private temp
/// file in the destination directory. The temp name carries a process-random
/// nonce and is opened with `create_new`, so a pre-created symlink is rejected
/// rather than followed. Renaming the completed file replaces a destination
/// symlink itself on Unix; it never truncates the symlink target.
pub(crate) fn atomic_write_replace(path: &Path, data: &[u8]) -> io::Result<()> {
    ensure_parent_directory(path)?;
    let temporary = write_secure_temporary(path, data)?;
    let cleanup = TemporaryPath::new(temporary.clone());

    replace_path(&temporary, path)?;
    drop(cleanup);
    Ok(())
}

/// Atomically publish `path` only if no directory entry already exists there.
///
/// This is used for immutable content-addressed records. A hard link publishes
/// the fully-written temp inode with create-if-absent semantics; unlike
/// `Path::exists` followed by `rename`, it cannot overwrite a winning writer or
/// an attacker-supplied symlink in the intervening race.
pub(crate) fn atomic_write_create_new(path: &Path, data: &[u8]) -> io::Result<bool> {
    ensure_parent_directory(path)?;

    // Avoid a temp write for the overwhelmingly common idempotent case. This
    // check is only an optimization: if the path is absent here, `hard_link`
    // below still makes the authoritative atomic no-clobber decision.
    match fs::symlink_metadata(path) {
        Ok(_) => return Ok(false),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    let temporary = write_secure_temporary(path, data)?;
    let cleanup = TemporaryPath::new(temporary.clone());

    match fs::hard_link(&temporary, path) {
        Ok(()) => {
            // Publication succeeded. Removing the redundant temp name is only
            // cleanup; failure cannot undo the already-durable destination.
            let _ = fs::remove_file(&temporary);
            drop(cleanup);
            Ok(true)
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Ok(false),
        Err(error) => {
            // Some platforms/filesystems report an existing destination using
            // a less specific error kind. Treat any extant directory entry as
            // the no-clobber outcome, including dangling symlinks.
            match fs::symlink_metadata(path) {
                Ok(_) => Ok(false),
                Err(metadata_error) if metadata_error.kind() == io::ErrorKind::NotFound => {
                    Err(error)
                }
                Err(metadata_error) => Err(metadata_error),
            }
        }
    }
}

static TEMPORARY_SEQUENCE: AtomicU64 = AtomicU64::new(0);
static TEMPORARY_RANDOM_STATE: OnceLock<RandomState> = OnceLock::new();

/// Owns an unpublished temp path and removes it on every exit path.
struct TemporaryPath {
    path: PathBuf,
}

impl TemporaryPath {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }
}

impl Drop for TemporaryPath {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn ensure_parent_directory(path: &Path) -> io::Result<()> {
    fs::create_dir_all(parent_directory(path))
}

fn parent_directory(path: &Path) -> &Path {
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    }
}

fn write_secure_temporary(target: &Path, data: &[u8]) -> io::Result<PathBuf> {
    // A bounded retry handles the fantastically unlikely random collision and
    // deliberately pre-created names without ever following them.
    for _ in 0..128 {
        let temporary = unique_temporary_path(target);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);

        let mut file = match options.open(&temporary) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        };

        let write_result = (|| {
            file.write_all(data)?;
            file.sync_all()
        })();
        drop(file);

        match write_result {
            Ok(()) => return Ok(temporary),
            Err(error) => {
                let _ = fs::remove_file(&temporary);
                return Err(error);
            }
        }
    }

    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "could not allocate a unique trust-cache temporary file",
    ))
}

fn unique_temporary_path(target: &Path) -> PathBuf {
    let sequence = TEMPORARY_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let random_state = TEMPORARY_RANDOM_STATE.get_or_init(RandomState::new);
    let mut hasher = random_state.build_hasher();
    target.hash(&mut hasher);
    std::process::id().hash(&mut hasher);
    sequence.hash(&mut hasher);
    let nonce = hasher.finish();

    parent_directory(target)
        .join(format!(".trust-cache-tmp-{:x}-{sequence:016x}-{nonce:016x}", std::process::id()))
}

#[cfg(not(windows))]
fn replace_path(temporary: &Path, destination: &Path) -> io::Result<()> {
    fs::rename(temporary, destination)
}

#[cfg(windows)]
fn replace_path(temporary: &Path, destination: &Path) -> io::Result<()> {
    use std::os::windows::ffi::OsStrExt;

    const MOVEFILE_REPLACE_EXISTING: u32 = 0x1;

    #[link(name = "kernel32")]
    unsafe extern "system" {
        #[link_name = "MoveFileExW"]
        fn move_file_ex_w(
            existing_file_name: *const u16,
            new_file_name: *const u16,
            flags: u32,
        ) -> i32;
    }

    let temporary_wide: Vec<u16> =
        temporary.as_os_str().encode_wide().chain(std::iter::once(0)).collect();
    let destination_wide: Vec<u16> =
        destination.as_os_str().encode_wide().chain(std::iter::once(0)).collect();

    // SAFETY: both pointers reference live, NUL-terminated UTF-16 buffers for
    // the duration of the call. The temp and destination live in one directory,
    // and MOVEFILE_REPLACE_EXISTING provides the atomic replace operation that
    // `std::fs::rename` lacks on Windows.
    let moved = unsafe {
        move_file_ex_w(
            temporary_wide.as_ptr(),
            destination_wide.as_ptr(),
            MOVEFILE_REPLACE_EXISTING,
        )
    };
    if moved == 0 { Err(io::Error::last_os_error()) } else { Ok(()) }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Barrier};
    use std::thread;

    use super::*;

    fn default_config() -> CoordinationConfig {
        CoordinationConfig::default()
    }

    // -----------------------------------------------------------------------
    // Lock path computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_lock_path_for_appends_dot_lock() {
        let cache = Path::new("/tmp/cache/trust-cache.json");
        let lock = lock_path_for(cache);
        assert_eq!(lock, PathBuf::from("/tmp/cache/trust-cache.json.lock"));
    }

    #[test]
    fn test_lock_path_for_handles_no_extension() {
        let cache = Path::new("/tmp/cache/trust-cache");
        let lock = lock_path_for(cache);
        assert_eq!(lock, PathBuf::from("/tmp/cache/trust-cache.lock"));
    }

    // -----------------------------------------------------------------------
    // Shared lock acquisition
    // -----------------------------------------------------------------------

    #[test]
    fn test_acquire_shared_lock_creates_lock_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard = acquire_shared_lock(&cache_path, &default_config());
        assert!(guard.is_ok());
        let guard = guard.unwrap();
        assert!(guard.lock_path().exists());
        drop(guard);
    }

    #[test]
    fn test_multiple_shared_locks_coexist() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard1 =
            acquire_shared_lock(&cache_path, &default_config()).expect("first shared lock");
        let guard2 = acquire_shared_lock(&cache_path, &default_config())
            .expect("second shared lock should succeed");

        // Both guards exist simultaneously
        assert!(guard1.lock_path().exists());
        assert!(guard2.lock_path().exists());
        drop(guard1);
        drop(guard2);
    }

    // -----------------------------------------------------------------------
    // Exclusive lock acquisition
    // -----------------------------------------------------------------------

    #[test]
    fn test_acquire_exclusive_lock_creates_lock_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard = acquire_exclusive_lock(&cache_path, &default_config());
        assert!(guard.is_ok());
        let guard = guard.unwrap();
        assert!(guard.lock_path().exists());
        drop(guard);
    }

    #[test]
    fn test_try_exclusive_lock_fails_when_held() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let _guard =
            acquire_exclusive_lock(&cache_path, &default_config()).expect("first exclusive lock");

        // Try non-blocking exclusive lock -- should fail
        let result = try_exclusive_lock(&cache_path, &default_config())
            .expect("try_exclusive_lock should not error");
        assert!(result.is_none(), "second exclusive lock should fail (non-blocking)");
    }

    #[test]
    fn test_try_shared_lock_fails_when_exclusive_held() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let _guard =
            acquire_exclusive_lock(&cache_path, &default_config()).expect("exclusive lock");

        // Try non-blocking shared lock -- should fail
        let result = try_shared_lock(&cache_path, &default_config())
            .expect("try_shared_lock should not error");
        assert!(result.is_none(), "shared lock should fail while exclusive held");
    }

    // -----------------------------------------------------------------------
    // Lock release on drop
    // -----------------------------------------------------------------------

    #[test]
    fn test_lock_released_on_drop() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        {
            let _guard =
                acquire_exclusive_lock(&cache_path, &default_config()).expect("exclusive lock");
            // Guard is dropped here
        }

        // Should be able to acquire again
        let guard = acquire_exclusive_lock(&cache_path, &default_config());
        assert!(guard.is_ok(), "should acquire lock after previous guard dropped");
    }

    // -----------------------------------------------------------------------
    // Stable lock inode
    // -----------------------------------------------------------------------

    #[test]
    fn stale_threshold_never_unlinks_an_actively_locked_sentinel() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        let guard = acquire_exclusive_lock(&cache_path, &default_config())
            .expect("acquire the original lock inode");
        let lock_path = guard.lock_path().to_path_buf();
        let before = fs::symlink_metadata(&lock_path).expect("stat original lock inode");

        // The legacy threshold is intentionally ignored. The previous
        // implementation unlinked this still-locked inode at threshold zero,
        // then successfully locked a new inode under the same pathname.
        let config =
            CoordinationConfig { stale_lock_threshold_secs: 0, validate_content_hash: true };
        assert!(
            try_exclusive_lock(&cache_path, &config).expect("try the same lock").is_none(),
            "an age threshold must never split mutual exclusion across two inodes"
        );

        let after = fs::symlink_metadata(&lock_path).expect("lock sentinel must remain");
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            assert_eq!(before.dev(), after.dev(), "lock sentinel device changed");
            assert_eq!(before.ino(), after.ino(), "active lock sentinel inode was replaced");
        }
        #[cfg(not(unix))]
        let _ = (before, after);
        drop(guard);
    }

    // -----------------------------------------------------------------------
    // Content hash computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_file_content_hash_deterministic() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, r#"{"key": "value"}"#).expect("write file");

        let h1 = file_content_hash(&path);
        let h2 = file_content_hash(&path);
        assert_eq!(h1, h2, "content hash must be deterministic");
        assert_eq!(h1.len(), 64, "SHA-256 hex is 64 chars");
    }

    #[test]
    fn test_file_content_hash_nonexistent_returns_empty() {
        let hash = file_content_hash(Path::new("/nonexistent/path/file.json"));
        assert!(hash.is_empty());
    }

    #[test]
    fn test_file_content_hash_changes_with_content() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");

        fs::write(&path, "version 1").expect("write v1");
        let h1 = file_content_hash(&path);

        fs::write(&path, "version 2").expect("write v2");
        let h2 = file_content_hash(&path);

        assert_ne!(h1, h2, "different content must produce different hashes");
    }

    // -----------------------------------------------------------------------
    // Content hash validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_content_hash_match() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        let data = r#"{"entries": {}}"#;
        fs::write(&path, data).expect("write file");

        let hash = file_content_hash(&path);
        let result = validate_content_hash(&path, &hash);
        assert!(result.is_ok(), "matching hash should validate");
    }

    #[test]
    fn test_validate_content_hash_mismatch() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, "original").expect("write file");

        let result = validate_content_hash(
            &path,
            "0000000000000000000000000000000000000000000000000000000000000000",
        );
        assert!(result.is_err(), "mismatched hash should fail");

        let err = result.unwrap_err();
        assert!(
            matches!(err, CoordinationError::ContentHashMismatch { .. }),
            "should be ContentHashMismatch"
        );
    }

    #[test]
    fn test_validate_content_hash_empty_expected_always_ok() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, "anything").expect("write file");

        let result = validate_content_hash(&path, "");
        assert!(result.is_ok(), "empty expected hash should always pass");
    }

    #[test]
    fn test_validate_content_hash_nonexistent_file_ok() {
        let result = validate_content_hash(Path::new("/nonexistent/file.json"), "some_hash");
        assert!(result.is_ok(), "nonexistent file should be ok (no mismatch)");
    }

    // -----------------------------------------------------------------------
    // Coordinated read/write
    // -----------------------------------------------------------------------

    #[test]
    fn test_coordinated_write_and_read_roundtrip() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("coord-test.json");
        let config = default_config();

        let data = r#"{"version": 3, "entries": {}, "hmac": ""}"#;
        let (write_hash, _guard) = coordinated_write(&cache_path, data, &config).expect("write");
        assert_eq!(write_hash.len(), 64);
        drop(_guard);

        let (contents, read_hash, _guard) = coordinated_read(&cache_path, &config).expect("read");
        assert_eq!(contents, data);
        assert_eq!(write_hash, read_hash, "write and read hashes must match");
    }

    #[test]
    fn test_coordinated_write_atomic() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("atomic-test.json");
        let config = default_config();

        // Write initial data
        let (_, _guard) = coordinated_write(&cache_path, "initial", &config).expect("first write");
        drop(_guard);

        // Overwrite with new data
        let (_, _guard) = coordinated_write(&cache_path, "updated", &config).expect("second write");
        drop(_guard);

        let contents = fs::read_to_string(&cache_path).expect("read result");
        assert_eq!(contents, "updated");

        // Secure temp files are cleaned up after publication.
        assert!(
            fs::read_dir(dir.path())
                .expect("list temp directory")
                .filter_map(Result::ok)
                .all(|entry| !entry.file_name().to_string_lossy().starts_with(".trust-cache-tmp-")),
            "atomic publication must not leave a temp file behind"
        );
    }

    #[cfg(unix)]
    #[test]
    fn coordinated_write_never_follows_the_legacy_predictable_temp_symlink() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("cache.json");
        let victim_path = dir.path().join("victim.txt");
        let legacy_temp_path = cache_path.with_extension("tmp");
        fs::write(&victim_path, "do not overwrite").expect("seed victim");
        symlink(&victim_path, &legacy_temp_path).expect("plant legacy temp symlink");

        let (_, guard) = coordinated_write(&cache_path, "safe cache", &default_config())
            .expect("secure write succeeds despite planted legacy path");
        drop(guard);

        assert_eq!(fs::read_to_string(&victim_path).unwrap(), "do not overwrite");
        assert_eq!(fs::read_to_string(&cache_path).unwrap(), "safe cache");
        assert!(
            fs::symlink_metadata(&legacy_temp_path).unwrap().file_type().is_symlink(),
            "the obsolete predictable temp pathname must not be touched"
        );
    }

    #[cfg(unix)]
    #[test]
    fn coordinated_write_replaces_a_destination_symlink_without_touching_its_target() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("cache.json");
        let victim_path = dir.path().join("victim.txt");
        fs::write(&victim_path, "sensitive contents").expect("seed victim");
        symlink(&victim_path, &cache_path).expect("plant destination symlink");

        let (_, guard) = coordinated_write(&cache_path, "new cache", &default_config())
            .expect("atomically replace destination directory entry");
        drop(guard);

        assert_eq!(fs::read_to_string(&victim_path).unwrap(), "sensitive contents");
        assert_eq!(fs::read_to_string(&cache_path).unwrap(), "new cache");
        assert!(
            !fs::symlink_metadata(&cache_path).unwrap().file_type().is_symlink(),
            "the destination symlink itself, not its target, must be replaced"
        );
    }

    // -----------------------------------------------------------------------
    // Concurrent access tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_concurrent_writers_serialize() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("concurrent-write.json");
        let config = default_config();

        // Initialize the file
        fs::write(&cache_path, "").expect("init");

        let num_writers = 8;
        let barrier = Arc::new(Barrier::new(num_writers));
        let path = Arc::new(cache_path.clone());

        let handles: Vec<_> = (0..num_writers)
            .map(|i| {
                let barrier = Arc::clone(&barrier);
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    barrier.wait();
                    let data = format!("writer-{i}");
                    let result = coordinated_write(&path, &data, &config);
                    result.is_ok()
                })
            })
            .collect();

        let results: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert!(results.iter().all(|&r| r), "all writers should succeed");

        // File should contain one of the writer's data (last writer wins)
        let final_contents = fs::read_to_string(&cache_path).expect("read final");
        assert!(
            final_contents.starts_with("writer-"),
            "final contents should be from one writer: got '{final_contents}'"
        );
    }

    #[test]
    fn test_concurrent_readers_dont_block() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("concurrent-read.json");
        let config = default_config();

        // Write initial data
        let data = r#"{"test": "concurrent read"}"#;
        fs::write(&cache_path, data).expect("write initial");

        let num_readers = 8;
        let barrier = Arc::new(Barrier::new(num_readers));
        let path = Arc::new(cache_path.clone());

        let handles: Vec<_> = (0..num_readers)
            .map(|_| {
                let barrier = Arc::clone(&barrier);
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    barrier.wait();
                    let result = coordinated_read(&path, &config);
                    match result {
                        Ok((contents, _, _guard)) => {
                            assert_eq!(contents, data);
                            true
                        }
                        Err(_) => false,
                    }
                })
            })
            .collect();

        let results: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert!(results.iter().all(|&r| r), "all readers should succeed concurrently");
    }

    #[test]
    fn test_reader_writer_interleaving() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("interleave.json");
        let config = default_config();

        // Initialize
        fs::write(&cache_path, "v0").expect("init");

        let path = Arc::new(cache_path.clone());

        // Writer thread
        let writer_path = Arc::clone(&path);
        let writer_config = config.clone();
        let writer = thread::spawn(move || {
            for i in 0..10 {
                let data = format!("v{}", i + 1);
                coordinated_write(&writer_path, &data, &writer_config)
                    .expect("writer should succeed");
            }
        });

        // Reader threads
        let readers: Vec<_> = (0..4)
            .map(|_| {
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    for _ in 0..10 {
                        let result = coordinated_read(&path, &config);
                        assert!(result.is_ok(), "reader should succeed");
                        let (contents, _, _guard) = result.unwrap();
                        // Contents should start with "v" (some version)
                        assert!(contents.starts_with('v'), "unexpected contents: {contents}");
                    }
                })
            })
            .collect();

        writer.join().expect("writer thread panicked");
        for r in readers {
            r.join().expect("reader thread panicked");
        }

        // Final state should be the last writer's value
        let final_contents = fs::read_to_string(&cache_path).expect("read final");
        assert_eq!(final_contents, "v10");
    }

    // -----------------------------------------------------------------------
    // Config tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config() {
        let config = CoordinationConfig::default();
        assert_eq!(config.stale_lock_threshold_secs, DEFAULT_STALE_LOCK_SECS);
        assert!(config.validate_content_hash);
    }

    // -----------------------------------------------------------------------
    // Error display tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_error_display() {
        let err = CoordinationError::ContentHashMismatch {
            expected: "abc".to_string(),
            found: "def".to_string(),
        };
        let msg = format!("{err}");
        assert!(msg.contains("abc"));
        assert!(msg.contains("def"));
    }
}
