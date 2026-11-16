//! File-locking support.
//!
//! This module defines the [`Filesystem`] type which is an abstraction over a
//! filesystem, ensuring that access to the filesystem is only done through
//! coordinated locks.
//!
//! The [`FileLock`] type represents a locked file, and provides access to the
//! file.

use std::fs::TryLockError;
use std::fs::{File, OpenOptions};
use std::io;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Display, Path, PathBuf};

use crate::util::GlobalContext;
use crate::util::errors::CargoResult;
use crate::util::style;
use anyhow::Context as _;
use cargo_util::paths;

pub(crate) use self::imp::lock_exclusive;
pub(crate) use self::imp::lock_shared;
#[allow(
    unused_imports,
    reason = "non-blocking lock callers vary by target and test profile"
)]
pub(crate) use self::imp::try_lock_exclusive;
#[allow(
    unused_imports,
    reason = "native source-data imports use this on macOS/Linux; other targets may not"
)]
pub(crate) use self::imp::try_lock_shared;
pub(crate) use self::imp::unlock;

/// A locked file.
///
/// This provides access to file while holding a lock on the file. This type
/// implements the [`Read`], [`Write`], and [`Seek`] traits to provide access
/// to the underlying file.
///
/// Locks are either shared (multiple processes can access the file) or
/// exclusive (only one process can access the file).
///
/// This type is created via methods on the [`Filesystem`] type.
///
/// When this value is dropped, the lock will be released.
pub struct FileLock {
    f: Option<File>,
    path: PathBuf,
    // Trust: ordinary guards explicitly unlock. A workload custodian may
    // retain SAME original descriptions across processes, so these guards
    // must instead let only the last description close release the lock.
    unlock_on_drop: bool,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    // LAST: the actual original/duplicate FD closes before its complete fee.
    retained: Option<RetainedLockResources>,
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
struct RetainedLockResources {
    owner: std::sync::Arc<dyn Send + Sync>,
    budget: std::sync::Arc<trust_resource_controller::descriptors::DescriptorBudget>,
    _copy: Option<trust_resource_controller::descriptors::OriginalInputPermit>,
}
impl std::fmt::Debug for FileLock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FileLock")
            .field("f", &self.f)
            .field("path", &self.path)
            .field("unlock_on_drop", &self.unlock_on_drop)
            .finish_non_exhaustive()
    }
}

impl FileLock {
    // Trust: cache recovery can acquire existing native exclusion without
    // creating a file, directory, ticket or compiler-query capture. Unlike
    // ordinary Cargo locking, unsupported locking is a refusal, never success.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn try_existing_exclusive(path: PathBuf) -> CargoResult<Self> {
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};

        anyhow::ensure!(
            !is_on_nfs_mount(&path),
            "cache recovery requires supported original output locks"
        );
        let f = OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(&path)
            .with_context(|| format!("cannot open existing output lock: {}", path.display()))?;
        let held = f.metadata()?;
        let named = std::fs::symlink_metadata(&path)?;
        anyhow::ensure!(
            held.is_file()
                && named.is_file()
                && held.nlink() == 1
                && named.nlink() == 1
                && (held.dev(), held.ino()) == (named.dev(), named.ino()),
            "cache recovery output lock is not its original regular file: {}",
            path.display()
        );
        match imp::try_lock_exclusive(&f) {
            Ok(()) => {}
            Err(TryLockError::WouldBlock) => {
                anyhow::bail!(
                    "output is busy; no cache recovery started: {}",
                    path.display()
                );
            }
            Err(TryLockError::Error(error)) => return Err(error.into()),
        }
        let guard = Self {
            f: Some(f),
            path,
            unlock_on_drop: true,
            retained: None,
        };
        guard.check_existing_backing()?;
        Ok(guard)
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn check_existing_backing(&self) -> CargoResult<()> {
        use std::os::unix::fs::MetadataExt as _;
        let held = self.file().metadata()?;
        let named = std::fs::symlink_metadata(&self.path)?;
        anyhow::ensure!(
            held.is_file()
                && named.is_file()
                && held.nlink() == 1
                && named.nlink() == 1
                && (held.dev(), held.ino()) == (named.dev(), named.ino()),
            "cache recovery output lock changed: {}",
            self.path.display()
        );
        Ok(())
    }

    // Trust: tighten the resident adapter's already owned Shared guard. The
    // ordinary best-effort Cargo path may accept unsupported locking; this
    // closed input owner must establish the real SAME-description kernel lock.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn check_resident_shared(&self) -> CargoResult<()> {
        anyhow::ensure!(
            !is_on_nfs_mount(&self.path),
            "resident inputs refuse unsupported cache locking"
        );
        self.check_existing_backing()?;
        match imp::try_lock_shared(self.file()) {
            Ok(()) => self.check_existing_backing(),
            Err(TryLockError::WouldBlock) => {
                anyhow::bail!("resident input cache exclusion is busy")
            }
            Err(TryLockError::Error(error)) => Err(error.into()),
        }
    }

    /// Retain actual native input/fee ownership with this already held lock.
    /// It grants no CPU/SDK/execution and never opens or locks a pathname.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn retain_original_resources(
        &mut self,
        owner: std::sync::Arc<dyn Send + Sync>,
        budget: std::sync::Arc<trust_resource_controller::descriptors::DescriptorBudget>,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            !self.unlock_on_drop && self.retained.is_none(),
            "native lock resources require an original close-only guard"
        );
        self.retained = Some(RetainedLockResources {
            owner,
            budget,
            _copy: None,
        });
        Ok(())
    }
    /// Adopt ONLY an indexed description in the authenticated coordinator
    /// capsule. The Host supplied SAME original close-only Layout OFDs; this
    /// method neither opens nor locks a matching pathname to invent lineage.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn from_coordinator_original(
        originals: &trust_resource_controller::client::CoordinatorOriginals,
        index: usize,
        deadline: std::time::Instant,
    ) -> CargoResult<Self> {
        use std::os::fd::AsFd as _;
        use std::os::unix::ffi::OsStringExt as _;
        originals.validate(deadline)?;
        let lock = originals
            .observation()
            .outputs
            .locks
            .get(index)
            .context("coordinator output observation is missing")?;
        let source = originals
            .outputs()
            .get(index)
            .context("coordinator original output description is missing")?;
        let f = File::from(source.as_fd().try_clone_to_owned()?);
        let path = PathBuf::from(std::ffi::OsString::from_vec(lock.path.clone()));
        check_coordinator_lock(&f, &path, lock.backing)?;
        originals.validate(deadline)?;
        Ok(Self {
            f: Some(f),
            path,
            unlock_on_drop: false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained: None,
        })
    }
    /// Preserve the original kernel lock through same-description transfers.
    /// Call BEFORE any duplicate/SCM offer; unwinding must never LOCK_UN a
    /// host's still-live copy. Closing the last original still releases it.
    pub(crate) fn close_only_on_drop(&mut self) {
        self.unlock_on_drop = false;
    }
    /// Borrow the SAME original open description after its owner has selected
    /// close-only retirement. This performs no open/flock/acquisition and
    /// grants no permission to schedule concurrent writers.
    pub(crate) fn borrow_close_only(&self) -> CargoResult<Self> {
        anyhow::ensure!(
            !self.unlock_on_drop,
            "original output guard has not entered close-only custody"
        );
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let retained = self
            .retained
            .as_ref()
            .map(|original| {
                // Charge BEFORE the actual FD duplicate. Do not retain an older
                // duplicate's fee after its own FD closes; retain common originals.
                Ok::<_, anyhow::Error>(RetainedLockResources {
                    owner: original.owner.clone(),
                    budget: original.budget.clone(),
                    _copy: Some(original.budget.reserve_original_inputs(1)?),
                })
            })
            .transpose()?;
        Ok(Self {
            f: Some(self.file().try_clone()?),
            path: self.path.clone(),
            unlock_on_drop: false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained,
        })
    }
    /// Returns the underlying file handle of this lock.
    pub fn file(&self) -> &File {
        self.f.as_ref().unwrap()
    }

    /// Returns the underlying path that this lock points to.
    ///
    /// Note that special care must be taken to ensure that the path is not
    /// referenced outside the lifetime of this lock.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the parent path containing this file
    pub fn parent(&self) -> &Path {
        self.path.parent().unwrap()
    }

    /// Removes all sibling files to this locked file.
    ///
    /// This can be useful if a directory is locked with a sentinel file but it
    /// needs to be cleared out as it may be corrupt.
    pub fn remove_siblings(&self) -> CargoResult<()> {
        let path = self.path();
        for entry in path.parent().unwrap().read_dir()? {
            let entry = entry?;
            if Some(&entry.file_name()[..]) == path.file_name() {
                continue;
            }
            let kind = entry.file_type()?;
            if kind.is_dir() {
                paths::remove_dir_all(entry.path())?;
            } else {
                paths::remove_file(entry.path())?;
            }
        }
        Ok(())
    }

    /// Renames the file and updates the internal path.
    ///
    /// This method performs a filesystem rename operation using [`std::fs::rename`]
    /// while keeping the FileLock's internal path synchronized with the actual
    /// file location.
    ///
    /// ## Difference from `std::fs::rename`
    ///
    /// - `std::fs::rename(old, new)` only moves the file on the filesystem
    /// - `FileLock::rename(new)` moves the file AND updates `self.path` to point to the new location
    pub fn rename<P: AsRef<Path>>(&mut self, new_path: P) -> CargoResult<()> {
        let new_path = new_path.as_ref();
        std::fs::rename(&self.path, new_path).with_context(|| {
            format!(
                "failed to rename {} to {}",
                self.path.display(),
                new_path.display()
            )
        })?;
        self.path = new_path.to_path_buf();
        Ok(())
    }
}

/// Native consistency only. Passing this predicate cannot mint a FileLock;
/// only the opaque original-capsule adopter above establishes that lineage.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn check_coordinator_lock(
    f: &File,
    path: &Path,
    backing: trust_resource_controller::FileIdentity,
) -> CargoResult<()> {
    use std::os::fd::AsRawFd as _;
    use std::os::unix::fs::MetadataExt as _;
    let held = f.metadata()?;
    let named = std::fs::symlink_metadata(path)?;
    let access = unsafe { libc::fcntl(f.as_raw_fd(), libc::F_GETFL) };
    let descriptor = unsafe { libc::fcntl(f.as_raw_fd(), libc::F_GETFD) };
    anyhow::ensure!(
        path.canonicalize()? == path
            && held.is_file()
            && named.is_file()
            && !named.file_type().is_symlink()
            && held.nlink() == 1
            && named.nlink() == 1
            && (held.dev(), held.ino()) == (backing.device, backing.inode)
            && (named.dev(), named.ino()) == (held.dev(), held.ino())
            && access >= 0
            && access & libc::O_ACCMODE == libc::O_RDWR
            && descriptor >= 0
            && descriptor & libc::FD_CLOEXEC != 0,
        "coordinator original Layout description or named entry changed"
    );
    Ok(())
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod coordinator_tests {
    use super::*;
    use std::os::unix::fs::MetadataExt as _;

    #[test]
    fn received_output_consistency_refuses_replacement_alias_and_readonly_fd() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let named = root.join(".cargo-lock");
        let held = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&named)
            .unwrap();
        let meta = held.metadata().unwrap();
        let original = trust_resource_controller::FileIdentity {
            device: meta.dev(),
            inode: meta.ino(),
        };
        check_coordinator_lock(&held, &named, original).unwrap();
        let moved = root.join("original");
        std::fs::rename(&named, &moved).unwrap();
        std::fs::write(&named, b"foreign").unwrap();
        assert!(check_coordinator_lock(&held, &named, original).is_err());
        std::fs::remove_file(&named).unwrap();
        std::os::unix::fs::symlink(&moved, &named).unwrap();
        assert!(check_coordinator_lock(&held, &named, original).is_err());
        std::fs::remove_file(&named).unwrap();
        std::fs::rename(&moved, &named).unwrap();
        check_coordinator_lock(&held, &named, original).unwrap();
        let alias = root.join("alias");
        std::fs::hard_link(&named, &alias).unwrap();
        assert!(check_coordinator_lock(&held, &named, original).is_err());
        std::fs::remove_file(alias).unwrap();
        let readonly = File::open(&named).unwrap();
        assert!(check_coordinator_lock(&readonly, &named, original).is_err());
        check_coordinator_lock(&held, &named, original).unwrap();
        // These checks exercise native consistency, never an authenticated
        // Host receiver or output-lock adoption/retirement capability.
    }
}

impl Read for FileLock {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.file().read(buf)
    }
}

impl Seek for FileLock {
    fn seek(&mut self, to: SeekFrom) -> io::Result<u64> {
        self.file().seek(to)
    }
}

impl Write for FileLock {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.file().write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.file().flush()
    }
}

impl Drop for FileLock {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            if self.unlock_on_drop
                && let Err(e) = imp::unlock(&f)
            {
                tracing::warn!("failed to release lock: {e:?}");
            }
        }
    }
}

/// A "filesystem" is intended to be a globally shared, hence locked, resource
/// in Cargo.
///
/// The `Path` of a filesystem cannot be learned unless it's done in a locked
/// fashion, and otherwise functions on this structure are prepared to handle
/// concurrent invocations across multiple instances of Cargo.
///
/// The methods on `Filesystem` that open files return a [`FileLock`] which
/// holds the lock, and that type provides methods for accessing the
/// underlying file.
///
/// If the blocking methods (like [`Filesystem::open_ro_shared`]) detect that
/// they will block, then they will display a message to the user letting them
/// know it is blocked. There are non-blocking variants starting with the
/// `try_` prefix like [`Filesystem::try_open_ro_shared_create`].
///
/// The behavior of locks acquired by the `Filesystem` depend on the operating
/// system. On unix-like system, they are advisory using [`flock`] (or
/// process-scoped `fcntl` locks on Solaris), and thus not enforced against
/// processes which do not try to acquire the lock. On Windows, they are
/// mandatory using [`LockFileEx`], enforced against all processes.
///
/// This **does not** guarantee that a lock is acquired. In some cases, for
/// example on filesystems that don't support locking, it will return a
/// [`FileLock`] even though the filesystem lock was not acquired. This is
/// intended to provide a graceful fallback instead of refusing to work.
/// Usually there aren't multiple processes accessing the same resource. In
/// that case, it is the user's responsibility to not run concurrent
/// processes.
///
/// [`flock`]: https://linux.die.net/man/2/flock
/// [`LockFileEx`]: https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-lockfileex
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Filesystem {
    root: PathBuf,
}

impl Filesystem {
    /// Creates a new filesystem to be rooted at the given path.
    pub fn new(path: PathBuf) -> Filesystem {
        Filesystem { root: path }
    }

    /// Like `Path::join`, creates a new filesystem rooted at this filesystem
    /// joined with the given path.
    pub fn join<T: AsRef<Path>>(&self, other: T) -> Filesystem {
        Filesystem::new(self.root.join(other))
    }

    /// Like `Path::push`, pushes a new path component onto this filesystem.
    pub fn push<T: AsRef<Path>>(&mut self, other: T) {
        self.root.push(other);
    }

    /// Consumes this filesystem and returns the underlying `PathBuf`.
    ///
    /// Note that this is a relatively dangerous operation and should be used
    /// with great caution!.
    pub fn into_path_unlocked(self) -> PathBuf {
        self.root
    }

    /// Returns the underlying `Path`.
    ///
    /// Note that this is a relatively dangerous operation and should be used
    /// with great caution!.
    pub fn as_path_unlocked(&self) -> &Path {
        &self.root
    }

    /// Creates the directory pointed to by this filesystem.
    ///
    /// Handles errors where other Cargo processes are also attempting to
    /// concurrently create this directory.
    pub fn create_dir(&self) -> CargoResult<()> {
        paths::create_dir_all(&self.root)
    }

    /// Returns an adaptor that can be used to print the path of this
    /// filesystem.
    pub fn display(&self) -> Display<'_> {
        self.root.display()
    }

    /// Opens read-write exclusive access to a file, returning the locked
    /// version of a file.
    ///
    /// This function will create a file at `path` if it doesn't already exist
    /// (including intermediate directories), and then it will acquire an
    /// exclusive lock on `path`. If the process must block waiting for the
    /// lock, the `msg` is printed to [`GlobalContext`].
    ///
    /// The returned file can be accessed to look at the path and also has
    /// read/write access to the underlying file.
    pub fn open_rw_exclusive_create<P>(
        &self,
        path: P,
        gctx: &GlobalContext,
        msg: &str,
    ) -> CargoResult<FileLock>
    where
        P: AsRef<Path>,
    {
        let mut opts = OpenOptions::new();
        opts.read(true).write(true).create(true);
        let (path, f) = self.open(path.as_ref(), &opts, true)?;
        acquire(gctx, msg, &path, &|| imp::try_lock_exclusive(&f), &|| {
            imp::lock_exclusive(&f)
        })?;
        Ok(FileLock {
            f: Some(f),
            path,
            unlock_on_drop: true,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained: None,
        })
    }

    /// A non-blocking version of [`Filesystem::open_rw_exclusive_create`].
    ///
    /// Returns `None` if the operation would block due to another process
    /// holding the lock.
    pub fn try_open_rw_exclusive_create<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> CargoResult<Option<FileLock>> {
        let mut opts = OpenOptions::new();
        opts.read(true).write(true).create(true);
        let (path, f) = self.open(path.as_ref(), &opts, true)?;
        if try_acquire(&path, &|| imp::try_lock_exclusive(&f))? {
            Ok(Some(FileLock {
                f: Some(f),
                path,
                unlock_on_drop: true,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                retained: None,
            }))
        } else {
            Ok(None)
        }
    }

    // Trust: reserve a new diagnostic file without ever reopening a prior
    // invocation's file. AlreadyExists is a name collision, not a lock waiter.
    // The returned guard retains the SAME description created atomically here.
    pub(crate) fn create_rw_exclusive_new<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> CargoResult<Option<FileLock>> {
        let path = self.root.join(path);
        let f = match OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(f) => f,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(None),
            Err(error) => {
                return Err(error).with_context(|| format!("failed to create: {}", path.display()));
            }
        };
        anyhow::ensure!(
            try_acquire(&path, &|| imp::try_lock_exclusive(&f))?,
            "new file was locked before its creator acquired it: {}",
            path.display()
        );
        Ok(Some(FileLock {
            f: Some(f),
            path,
            unlock_on_drop: true,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained: None,
        }))
    }

    /// Opens read-only shared access to a file, returning the locked version of a file.
    ///
    /// This function will fail if `path` doesn't already exist, but if it does
    /// then it will acquire a shared lock on `path`. If the process must block
    /// waiting for the lock, the `msg` is printed to [`GlobalContext`].
    ///
    /// The returned file can be accessed to look at the path and also has read
    /// access to the underlying file. Any writes to the file will return an
    /// error.
    pub fn open_ro_shared<P>(
        &self,
        path: P,
        gctx: &GlobalContext,
        msg: &str,
    ) -> CargoResult<FileLock>
    where
        P: AsRef<Path>,
    {
        let (path, f) = self.open(path.as_ref(), &OpenOptions::new().read(true), false)?;
        acquire(gctx, msg, &path, &|| imp::try_lock_shared(&f), &|| {
            imp::lock_shared(&f)
        })?;
        Ok(FileLock {
            f: Some(f),
            path,
            unlock_on_drop: true,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained: None,
        })
    }

    /// Opens read-only shared access to a file, returning the locked version of a file.
    ///
    /// Compared to [`Filesystem::open_ro_shared`], this will create the file
    /// (and any directories in the parent) if the file does not already
    /// exist.
    pub fn open_ro_shared_create<P: AsRef<Path>>(
        &self,
        path: P,
        gctx: &GlobalContext,
        msg: &str,
    ) -> CargoResult<FileLock> {
        let mut opts = OpenOptions::new();
        opts.read(true).write(true).create(true);
        let (path, f) = self.open(path.as_ref(), &opts, true)?;
        acquire(gctx, msg, &path, &|| imp::try_lock_shared(&f), &|| {
            imp::lock_shared(&f)
        })?;
        Ok(FileLock {
            f: Some(f),
            path,
            unlock_on_drop: true,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained: None,
        })
    }

    /// A non-blocking version of [`Filesystem::open_ro_shared_create`].
    ///
    /// Returns `None` if the operation would block due to another process
    /// holding the lock.
    pub fn try_open_ro_shared_create<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> CargoResult<Option<FileLock>> {
        let mut opts = OpenOptions::new();
        opts.read(true).write(true).create(true);
        let (path, f) = self.open(path.as_ref(), &opts, true)?;
        if try_acquire(&path, &|| imp::try_lock_shared(&f))? {
            Ok(Some(FileLock {
                f: Some(f),
                path,
                unlock_on_drop: true,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                retained: None,
            }))
        } else {
            Ok(None)
        }
    }

    fn open(&self, path: &Path, opts: &OpenOptions, create: bool) -> CargoResult<(PathBuf, File)> {
        let path = self.root.join(path);
        let f = opts
            .open(&path)
            .or_else(|e| {
                // If we were requested to create this file, and there was a
                // NotFound error, then that was likely due to missing
                // intermediate directories. Try creating them and try again.
                if e.kind() == io::ErrorKind::NotFound && create {
                    paths::create_dir_all(path.parent().unwrap())?;
                    Ok(opts.open(&path)?)
                } else {
                    Err(anyhow::Error::from(e))
                }
            })
            .with_context(|| format!("failed to open: {}", path.display()))?;
        Ok((path, f))
    }
}

impl PartialEq<Path> for Filesystem {
    fn eq(&self, other: &Path) -> bool {
        self.root == other
    }
}

impl PartialEq<Filesystem> for Path {
    fn eq(&self, other: &Filesystem) -> bool {
        self == other.root
    }
}

fn try_acquire(path: &Path, lock_try: &dyn Fn() -> Result<(), TryLockError>) -> CargoResult<bool> {
    // File locking on Unix is currently implemented via `flock`, which is known
    // to be broken on NFS. We could in theory just ignore errors that happen on
    // NFS, but apparently the failure mode [1] for `flock` on NFS is **blocking
    // forever**, even if the "non-blocking" flag is passed!
    //
    // As a result, we just skip all file locks entirely on NFS mounts. That
    // should avoid calling any `flock` functions at all, and it wouldn't work
    // there anyway.
    //
    // [1]: https://github.com/rust-lang/cargo/issues/2615
    if is_on_nfs_mount(path) {
        tracing::debug!("{path:?} appears to be an NFS mount, not trying to lock");
        return Ok(true);
    }

    match lock_try() {
        Ok(()) => Ok(true),

        // In addition to ignoring NFS which is commonly not working we also
        // just ignore locking on filesystems that look like they don't
        // implement file locking.
        Err(TryLockError::Error(e)) if error_unsupported(&e) => Ok(true),

        Err(TryLockError::Error(e)) => {
            let e = anyhow::Error::from(e);
            let cx = format!("failed to lock file: {}", path.display());
            Err(e.context(cx))
        }

        Err(TryLockError::WouldBlock) => Ok(false),
    }
}

/// Acquires a lock on a file in a "nice" manner.
///
/// Almost all long-running blocking actions in Cargo have a status message
/// associated with them as we're not sure how long they'll take. Whenever a
/// conflicted file lock happens, this is the case (we're not sure when the lock
/// will be released).
///
/// This function will acquire the lock on a `path`, printing out a nice message
/// to the console if we have to wait for it. It will first attempt to use `try`
/// to acquire a lock on the crate, and in the case of contention it will emit a
/// status message based on `msg` to [`GlobalContext`]'s shell, and then use `block` to
/// block waiting to acquire a lock.
///
/// Returns an error if the lock could not be acquired or if any error other
/// than a contention error happens.
fn acquire(
    gctx: &GlobalContext,
    msg: &str,
    path: &Path,
    lock_try: &dyn Fn() -> Result<(), TryLockError>,
    lock_block: &dyn Fn() -> io::Result<()>,
) -> CargoResult<()> {
    // Ensure `shell` is not already in use,
    // regardless of whether we hit contention or not
    gctx.debug_assert_shell_not_borrowed();
    if try_acquire(path, lock_try)? {
        return Ok(());
    }

    let msg = if gctx.extra_verbose() {
        format!("waiting for file lock on {} ({})", msg, path.display())
    } else {
        format!("waiting for file lock on {}", msg)
    };

    gctx.shell()
        .status_with_color("Blocking", &msg, &style::NOTE)?;

    lock_block().with_context(|| format!("failed to lock file: {}", path.display()))?;
    Ok(())
}

#[cfg(all(target_os = "linux", not(target_env = "musl")))]
pub fn is_on_nfs_mount(path: &Path) -> bool {
    use std::ffi::CString;
    use std::mem;
    use std::os::unix::prelude::*;

    let Ok(path) = CString::new(path.as_os_str().as_bytes()) else {
        return false;
    };

    unsafe {
        let mut buf: libc::statfs = mem::zeroed();
        let r = libc::statfs(path.as_ptr(), &mut buf);

        r == 0 && buf.f_type as u32 == libc::NFS_SUPER_MAGIC as u32
    }
}

#[cfg(any(not(target_os = "linux"), target_env = "musl"))]
pub fn is_on_nfs_mount(_path: &Path) -> bool {
    false
}

#[cfg(unix)]
fn error_unsupported(err: &std::io::Error) -> bool {
    match err.raw_os_error() {
        // Unfortunately, depending on the target, these may or may not be the same.
        // For targets in which they are the same, the duplicate pattern causes a warning.
        #[allow(unreachable_patterns)]
        Some(libc::ENOTSUP | libc::EOPNOTSUPP) => true,
        Some(libc::ENOSYS) => true,
        _ => err.kind() == std::io::ErrorKind::Unsupported,
    }
}

#[cfg(windows)]
fn error_unsupported(err: &std::io::Error) -> bool {
    use windows_sys::Win32::Foundation::ERROR_INVALID_FUNCTION;
    match err.raw_os_error() {
        Some(code) if code == ERROR_INVALID_FUNCTION as i32 => true,
        _ => err.kind() == std::io::ErrorKind::Unsupported,
    }
}

// This is the one place allowed to call `std::fs::File` lock methods.
// Everything else goes through this shim.
#[cfg(not(target_os = "solaris"))]
#[expect(
    clippy::disallowed_methods,
    reason = "the OS doesn't need the fcntl shim"
)]
mod imp {
    use super::*;

    pub fn try_lock_exclusive(file: &File) -> Result<(), TryLockError> {
        file.try_lock()
    }

    pub fn lock_exclusive(file: &File) -> io::Result<()> {
        file.lock()
    }

    pub fn try_lock_shared(file: &File) -> Result<(), TryLockError> {
        file.try_lock_shared()
    }

    pub fn lock_shared(file: &File) -> io::Result<()> {
        file.lock_shared()
    }

    pub fn unlock(file: &File) -> io::Result<()> {
        file.unlock()
    }
}

#[cfg(target_os = "solaris")]
mod imp {
    use super::*;
    use std::mem;
    use std::os::unix::io::AsRawFd;

    pub fn try_lock_exclusive(file: &File) -> Result<(), TryLockError> {
        match fcntl_lock(file, libc::F_WRLCK, libc::F_SETLK) {
            Ok(()) => Ok(()),
            Err(e) if is_would_block(&e) => Err(TryLockError::WouldBlock),
            Err(e) => Err(TryLockError::Error(e)),
        }
    }

    pub fn lock_exclusive(file: &File) -> io::Result<()> {
        fcntl_lock(file, libc::F_WRLCK, libc::F_SETLKW)
    }

    pub fn try_lock_shared(file: &File) -> Result<(), TryLockError> {
        match fcntl_lock(file, libc::F_RDLCK, libc::F_SETLK) {
            Ok(()) => Ok(()),
            Err(e) if is_would_block(&e) => Err(TryLockError::WouldBlock),
            Err(e) => Err(TryLockError::Error(e)),
        }
    }

    pub fn lock_shared(file: &File) -> io::Result<()> {
        fcntl_lock(file, libc::F_RDLCK, libc::F_SETLKW)
    }

    pub fn unlock(file: &File) -> io::Result<()> {
        fcntl_lock_raw(file, libc::F_UNLCK, libc::F_SETLK)
    }

    fn fcntl_lock(file: &File, lock_type: libc::c_short, cmd: libc::c_int) -> io::Result<()> {
        fcntl_lock_raw(file, lock_type, cmd)
    }

    fn fcntl_lock_raw(file: &File, lock_type: libc::c_short, cmd: libc::c_int) -> io::Result<()> {
        let mut lock = flock_for_whole_file(lock_type);
        loop {
            let result = unsafe { libc::fcntl(file.as_raw_fd(), cmd, &mut lock) };
            if result != -1 {
                return Ok(());
            }

            let error = io::Error::last_os_error();
            if cmd == libc::F_SETLKW && error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
    }

    fn flock_for_whole_file(lock_type: libc::c_short) -> libc::flock {
        let mut lock = unsafe { mem::zeroed::<libc::flock>() };
        lock.l_type = lock_type;
        lock.l_whence = libc::SEEK_SET as libc::c_short;
        lock.l_start = 0;
        lock.l_len = 0;
        lock
    }

    fn is_would_block(error: &io::Error) -> bool {
        matches!(error.raw_os_error(), Some(libc::EACCES | libc::EAGAIN))
            || error.kind() == io::ErrorKind::WouldBlock
    }
}
