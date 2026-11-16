// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Stable, authority-checked local file ownership shared by Trust clients.
//!
//! This crate owns the filesystem checks, OS lock lifetime and Linux namespace
//! binding. It has no daemon protocol, build ID, solver or proof dependency.
//! A lock grants work ownership only; callers still validate actual outputs.
//!
//! Cooperating clients must share a trusted local filesystem and mount view.
//! Owner/mode checks do not authenticate extended ACLs or mount namespaces.
//! The filesystem must honor flock, no-follow opens and stable inode identity.
//! Synchronous filesystem calls are not preempted by a contention deadline.
//! Guards belong to the acquiring process; callers must not transfer them
//! across a fork and treat the inherited descriptor as independent ownership.

#[cfg(unix)]
use std::fs::{File, OpenOptions};
#[cfg(any(target_os = "linux", all(test, unix)))]
use std::io::{Read, Seek, SeekFrom, Write};
#[cfg(unix)]
use std::os::fd::AsRawFd;
#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
#[cfg(not(unix))]
use std::time::SystemTime;
use std::time::{Duration, Instant};

#[cfg(unix)]
const INITIAL_ACQUIRE_BACKOFF: Duration = Duration::from_millis(25);
#[cfg(unix)]
const MAX_ACQUIRE_BACKOFF: Duration = Duration::from_millis(500);

#[derive(Debug, thiserror::Error)]
pub enum AuthorityError {
    #[error("file ownership was not acquired within {deadline_ms}ms")]
    Deadline { deadline_ms: u128 },
    #[error("{0}")]
    Invalid(String),
}

pub type AuthorityResult<T> = Result<T, AuthorityError>;

fn authority_error(message: impl Into<String>) -> AuthorityError {
    AuthorityError::Invalid(message.into())
}

/// One absolute wait budget, retained across lock retries.
#[derive(Clone, Copy)]
#[cfg_attr(not(unix), allow(dead_code))]
pub struct LockDeadline {
    end: Instant,
    timeout_ms: u128,
}

impl LockDeadline {
    pub fn new(timeout: Duration) -> Self {
        let now = Instant::now();
        Self { end: now.checked_add(timeout).unwrap_or(now), timeout_ms: timeout.as_millis() }
    }

    pub fn from_absolute(end: Instant, timeout_ms: u128) -> Self {
        Self { end, timeout_ms }
    }

    #[cfg(unix)]
    fn expired(self) -> bool {
        Instant::now() >= self.end
    }
    #[cfg(unix)]
    fn remaining(self) -> Duration {
        self.end.saturating_duration_since(Instant::now())
    }
    #[cfg(unix)]
    fn timeout_error(self) -> AuthorityError {
        AuthorityError::Deadline { deadline_ms: self.timeout_ms }
    }
}

/// Resolve one absolute, unaliased parent and use only that canonical result
/// thereafter. Rejecting relative paths and any spelling whose parent differs
/// from its canonical path prevents cwd changes or a mutable symlink alias from
/// splitting one configured authority into several independently-full ledgers.
/// The leaf itself must remain a single ordinary filename; it is never
/// canonicalized through an attacker-controlled symlink.
pub fn authoritative_token_path(path: &Path) -> AuthorityResult<PathBuf> {
    #[cfg(not(unix))]
    {
        let _ = path;
        return Err(authority_error(
            "the file memory coordinator is unsupported on this platform because owner/mode, no-follow, and stable-inode authority cannot be established",
        ));
    }

    #[cfg(unix)]
    {
        if !path.is_absolute() {
            return Err(authority_error(format!(
                "token path must be absolute so its authority cannot change with cwd: {}",
                path.display()
            )));
        }
        let file_name = path.file_name().ok_or_else(|| {
            authority_error(format!("token path has no filename: {}", path.display()))
        })?;
        let parent = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent,
            _ => Path::new("."),
        };
        let canonical_parent = std::fs::canonicalize(parent).map_err(|error| {
            authority_error(format!(
                "token parent cannot be resolved (it must already exist): {}: {error}",
                parent.display()
            ))
        })?;
        if canonical_parent.as_os_str() != parent.as_os_str() {
            return Err(authority_error(format!(
                "token parent must already be canonical (no '.', '..', or symlink aliases): configured {}, canonical {}",
                parent.display(),
                canonical_parent.display()
            )));
        }
        validate_authoritative_directory_chain(&canonical_parent)?;
        let authoritative = canonical_parent.join(file_name);
        if authoritative.as_os_str() != path.as_os_str() {
            return Err(authority_error(format!(
                "token path must use one exact canonical spelling: configured {}, authoritative {}",
                path.display(),
                authoritative.display()
            )));
        }
        Ok(authoritative)
    }
}

#[cfg(unix)]
fn validate_authoritative_directory_chain(parent: &Path) -> AuthorityResult<()> {
    #[cfg(unix)]
    let euid = unsafe {
        // SAFETY: `geteuid` has no arguments or memory effects and always returns
        // the effective uid of this process.
        libc::geteuid()
    };

    for (index, directory) in parent.ancestors().enumerate() {
        let metadata = std::fs::symlink_metadata(directory).map_err(|error| {
            authority_error(format!(
                "cannot inspect token ancestor {}: {error}",
                directory.display()
            ))
        })?;
        if !metadata.file_type().is_dir() {
            return Err(authority_error(format!(
                "token ancestor is not a directory: {}",
                directory.display()
            )));
        }

        #[cfg(unix)]
        {
            let mode = metadata.mode() & 0o777;
            if metadata.uid() != 0 && metadata.uid() != euid {
                return Err(authority_error(format!(
                    "token ancestor is foreign-owned: {}",
                    directory.display()
                )));
            }
            if mode & 0o022 != 0 {
                return Err(authority_error(format!(
                    "token ancestor is group/other writable: {}",
                    directory.display()
                )));
            }
            if index == 0 && metadata.uid() != euid {
                return Err(authority_error(format!(
                    "token parent must be owned by effective uid {euid}: {}",
                    directory.display()
                )));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(not(unix))]
    length: u64,
    #[cfg(not(unix))]
    modified: Option<SystemTime>,
}

impl FileIdentity {
    pub fn from_metadata(metadata: &std::fs::Metadata) -> Self {
        Self {
            #[cfg(unix)]
            device: metadata.dev(),
            #[cfg(unix)]
            inode: metadata.ino(),
            #[cfg(not(unix))]
            length: metadata.len(),
            #[cfg(not(unix))]
            modified: metadata.modified().ok(),
        }
    }
}

pub fn validate_private_regular_file(
    metadata: &std::fs::Metadata,
    path: &Path,
    description: &str,
) -> AuthorityResult<FileIdentity> {
    #[cfg(not(unix))]
    {
        let _ = metadata;
        return Err(authority_error(format!(
            "cannot validate private file authority for {description} on this platform: {}",
            path.display()
        )));
    }
    #[cfg(unix)]
    {
        if !metadata.file_type().is_file() {
            return Err(authority_error(format!(
                "{description} is not a regular file: {}",
                path.display()
            )));
        }

        #[cfg(unix)]
        {
            let euid = unsafe {
                // SAFETY: `geteuid` has no arguments or memory effects.
                libc::geteuid()
            };
            if metadata.uid() != euid {
                return Err(authority_error(format!(
                    "{description} is not owned by effective uid {euid}: {}",
                    path.display()
                )));
            }
            if metadata.mode() & 0o077 != 0 {
                return Err(authority_error(format!(
                    "{description} grants group/other permissions: {}",
                    path.display()
                )));
            }
            if metadata.nlink() != 1 {
                return Err(authority_error(format!(
                    "{description} must have exactly one link: {}",
                    path.display()
                )));
            }
        }

        Ok(FileIdentity::from_metadata(metadata))
    }
}

pub fn validate_path_identity(
    path: &Path,
    expected: FileIdentity,
    description: &str,
) -> AuthorityResult<()> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        authority_error(format!("cannot inspect {description} {}: {error}", path.display()))
    })?;
    let actual = validate_private_regular_file(&metadata, path, description)?;
    if actual != expected {
        return Err(authority_error(format!(
            "{description} was replaced during the locked operation: {}",
            path.display()
        )));
    }
    Ok(())
}

pub fn lock_path_for(path: &Path) -> PathBuf {
    let mut lock_path = path.as_os_str().to_owned();
    lock_path.push(".lock");
    PathBuf::from(lock_path)
}

#[cfg(any(target_os = "linux", all(test, unix)))]
const MAX_LOCK_DOMAIN_BYTES: u64 = 128;

#[cfg(target_os = "linux")]
pub fn linux_pid_namespace_marker() -> AuthorityResult<String> {
    let metadata = std::fs::metadata("/proc/self/ns/pid").map_err(|error| {
        authority_error(format!("cannot inspect current Linux PID namespace: {error}"))
    })?;
    Ok(format!("trust-memory-jobserver-lock-v1 pidns={}:{}\n", metadata.dev(), metadata.ino()))
}

#[must_use = "dropping the guard releases file ownership"]
pub struct FileLock {
    #[cfg(unix)]
    file: File,
    path: PathBuf,
    #[cfg(unix)]
    identity: FileIdentity,
}

impl FileLock {
    /// Hold a stable sentinel. Before initializing a Linux PID-namespace marker,
    /// the owner must check that no prior ledger state would be adopted.
    /// `before_bind` runs under the lock, only for an empty namespace marker.
    /// A caller that stores PID-owned state must reject incompatible live state
    /// there; the lock itself knows no ledger format.
    #[cfg(unix)]
    pub fn acquire_with_domain_check(
        token_path: &Path,
        window: LockDeadline,
        before_bind: impl FnOnce(&Path) -> AuthorityResult<()>,
    ) -> AuthorityResult<Self> {
        let token_path = authoritative_token_path(token_path)?;
        let token_path = token_path.as_path();
        let path = lock_path_for(token_path);
        let mut options = OpenOptions::new();
        options
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            // NONBLOCK prevents a pre-existing FIFO/device leaf from wedging
            // before the post-open regular-file validation can reject it.
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK);
        let file = options.open(&path).map_err(|error| {
            authority_error(format!(
                "cannot open private lock sentinel {}: {error}",
                path.display()
            ))
        })?;
        let identity = validate_private_regular_file(
            &file.metadata().map_err(|error| {
                authority_error(format!(
                    "cannot inspect open lock sentinel {}: {error}",
                    path.display()
                ))
            })?,
            &path,
            "memory-jobserver lock sentinel",
        )?;
        validate_path_identity(&path, identity, "memory-jobserver lock sentinel")?;

        let mut backoff = INITIAL_ACQUIRE_BACKOFF;
        loop {
            // SAFETY: `file` owns a live descriptor and `LOCK_EX | LOCK_NB`
            // only changes its advisory lock state. The descriptor remains open
            // in the returned guard. Nonblocking mode keeps the configured
            // admission deadline authoritative even when another holder wedges.
            if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
                break;
            }
            let error = std::io::Error::last_os_error();
            if error.kind() != std::io::ErrorKind::WouldBlock {
                return Err(authority_error(format!(
                    "cannot acquire lock sentinel {}: {error}",
                    path.display()
                )));
            }
            if window.expired() {
                return Err(window.timeout_error());
            }
            std::thread::sleep(backoff.min(window.remaining()));
            backoff = (backoff * 2).min(MAX_ACQUIRE_BACKOFF);
        }
        let mut lock = Self { file, path, identity };
        lock.validate_process_domain(token_path, before_bind)?;
        lock.validate_path()?;
        Ok(lock)
    }

    #[cfg(not(unix))]
    pub fn acquire_with_domain_check(
        _token_path: &Path,
        _window: LockDeadline,
        _before_bind: impl FnOnce(&Path) -> AuthorityResult<()>,
    ) -> AuthorityResult<Self> {
        Err(authority_error("stable file ownership is unsupported on this platform"))
    }

    #[cfg(not(unix))]
    pub fn validate_path(&self) -> AuthorityResult<()> {
        Err(authority_error("stable file ownership is unsupported on this platform"))
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    #[cfg(target_os = "linux")]
    fn validate_process_domain(
        &mut self,
        token_path: &Path,
        before_bind: impl FnOnce(&Path) -> AuthorityResult<()>,
    ) -> AuthorityResult<()> {
        let expected = linux_pid_namespace_marker()?;
        self.validate_domain_marker(token_path, expected, before_bind)
    }

    #[cfg(any(target_os = "linux", all(test, unix)))]
    fn validate_domain_marker(
        &mut self,
        token_path: &Path,
        expected: String,
        before_bind: impl FnOnce(&Path) -> AuthorityResult<()>,
    ) -> AuthorityResult<()> {
        let length = self
            .file
            .metadata()
            .map_err(|error| {
                authority_error(format!(
                    "cannot inspect lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?
            .len();
        if length == 0 {
            // Empty is the legacy/new sentinel state. It may be stamped only
            // while no live rows exist: otherwise a restored lock or a process
            // in another PID namespace could adopt the ledger and mis-prune
            // foreign-but-live PIDs. Parsing/authority errors also fail closed.
            before_bind(token_path)?;
            self.file.seek(SeekFrom::Start(0)).map_err(|error| {
                authority_error(format!(
                    "cannot position new lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?;
            self.file.write_all(expected.as_bytes()).and_then(|()| self.file.sync_all()).map_err(
                |error| {
                    authority_error(format!(
                        "cannot initialize lock-domain marker {}: {error}",
                        self.path.display()
                    ))
                },
            )?;
            return Ok(());
        }
        if length > MAX_LOCK_DOMAIN_BYTES {
            return Err(authority_error(format!(
                "lock-domain marker exceeds {MAX_LOCK_DOMAIN_BYTES} bytes: {}",
                self.path.display()
            )));
        }
        self.file.seek(SeekFrom::Start(0)).map_err(|error| {
            authority_error(format!(
                "cannot position lock-domain marker {}: {error}",
                self.path.display()
            ))
        })?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut self.file)
            .take(MAX_LOCK_DOMAIN_BYTES + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| {
                authority_error(format!(
                    "cannot read lock-domain marker {}: {error}",
                    self.path.display()
                ))
            })?;
        if bytes != expected.as_bytes() {
            return Err(authority_error(format!(
                "lock-domain marker does not match this Linux PID namespace: {}",
                self.path.display()
            )));
        }
        Ok(())
    }

    #[cfg(not(target_os = "linux"))]
    fn validate_process_domain(
        &mut self,
        _token_path: &Path,
        _before_bind: impl FnOnce(&Path) -> AuthorityResult<()>,
    ) -> AuthorityResult<()> {
        Ok(())
    }

    #[cfg(unix)]
    pub fn validate_path(&self) -> AuthorityResult<()> {
        let open_identity = validate_private_regular_file(
            &self.file.metadata().map_err(|error| {
                authority_error(format!(
                    "cannot reinspect open lock sentinel {}: {error}",
                    self.path.display()
                ))
            })?,
            &self.path,
            "memory-jobserver lock sentinel",
        )?;
        if open_identity != self.identity {
            return Err(authority_error(format!(
                "open lock sentinel identity changed: {}",
                self.path.display()
            )));
        }
        validate_path_identity(&self.path, self.identity, "memory-jobserver lock sentinel")
    }
}

#[cfg(test)]
mod tests;

#[cfg(unix)]
impl Drop for FileLock {
    fn drop(&mut self) {
        // SAFETY: this is the same live descriptor locked in `acquire`. Closing
        // would also release it; explicit unlock makes the lifetime obvious.
        let _ = unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}

/// Failure to establish a stable exclusive-work lock. This is distinct from a
/// memory-admission failure: holding this lock reserves no memory and attests
/// neither an output nor a proof.
#[derive(Debug, thiserror::Error)]
#[error("exclusive work lock unavailable: {0}")]
pub struct WorkLockError(String);

/// Ownership of one stable work-lock sentinel. Keep it until publication and
/// call [`Self::validate`] immediately before publishing. The sentinel must not
/// be unlinked or replaced while clients can use this namespace. Process death
/// releases the OS lock; no persisted completion label is involved.
#[must_use = "dropping the guard releases exclusive work ownership"]
pub struct ExclusiveWorkLock {
    lock: FileLock,
}

impl ExclusiveWorkLock {
    /// Reject a replaced pathname or changed file authority before publication.
    pub fn validate(&self) -> Result<(), WorkLockError> {
        self.lock.validate_path().map_err(|error| WorkLockError(error.to_string()))
    }
}

/// Attempt a stable exclusive-work lock without waiting for another owner.
///
/// `path` is the resource name; the stable sentinel is `path` plus `.lock`.
/// The canonical-path, owner, mode, no-follow, regular-file and inode checks are
/// the same ones used by the file memory coordinator. `Ok(None)` means another
/// owner holds the lock. Callers decide their own cancellation/deadline policy
/// and must recheck the actual output after acquiring ownership.
pub fn try_exclusive_work_lock(path: &Path) -> Result<Option<ExclusiveWorkLock>, WorkLockError> {
    match FileLock::acquire_with_domain_check(path, LockDeadline::new(Duration::ZERO), |resource| {
        match std::fs::symlink_metadata(resource) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(authority_error(error.to_string())),
            Ok(metadata) => {
                validate_private_regular_file(&metadata, resource, "work resource")?;
                if metadata.len() == 0 {
                    Ok(())
                } else {
                    Err(authority_error(
                        "nonempty work resource cannot acquire a new namespace marker",
                    ))
                }
            }
        }
    }) {
        Ok(lock) => Ok(Some(ExclusiveWorkLock { lock })),
        Err(AuthorityError::Deadline { .. }) => Ok(None),
        Err(error) => Err(WorkLockError(error.to_string())),
    }
}
