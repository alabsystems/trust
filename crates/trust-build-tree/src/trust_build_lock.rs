//! The build/measurement holder namespace mutex, shared by every current actor.
//!
//! This regular file is persistent: never unlink or rename it. Its flock covers
//! only a holder metadata transaction, never a build, owner wait or background
//! job. The readable holder/token remains the durable resource ownership record.

use std::fs::File;
use std::io;
use std::path::Path;

pub const GUARD_NAME: &str = ".trust-build-lock.guard";

pub struct NamespaceGuard {
    // Closing the final reference releases flock. Do NOT explicitly unlock:
    // the legacy facade retains the same open description across helper exit.
    _file: File,
}

impl NamespaceGuard {
    pub fn acquire(root: &Path) -> io::Result<Self> {
        #[cfg(unix)]
        {
            use std::fs::OpenOptions;
            use std::os::unix::fs::OpenOptionsExt;
            let path = root.canonicalize()?.join(GUARD_NAME);
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
                .open(&path)?;
            lock(&file, &path)?;
            Ok(Self { _file: file })
        }
        #[cfg(not(unix))]
        {
            let _ = root;
            Err(io::Error::new(io::ErrorKind::Unsupported, "build namespace flock requires Unix"))
        }
    }
}

/// Lock a descriptor inherited from the facade. The duplicate is the SAME open
/// description, so helper exit leaves its lock held by the facade's descriptor.
/// This is a capability check, not an inherited boolean claiming ownership.
#[cfg(unix)]
pub fn lock_inherited(root: &Path, fd: std::os::fd::RawFd) -> io::Result<()> {
    use std::os::fd::FromRawFd;
    if fd < 3 {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "invalid guard descriptor"));
    }
    // SAFETY: fcntl validates the numeric descriptor, returning EBADF rather
    // than manufacturing a Rust borrowed/owned descriptor from an invalid CLI
    // number. A successful duplicate is ours and shares the open description.
    let duplicate = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if duplicate < 0 {
        return Err(io::Error::last_os_error());
    }
    let file = unsafe { File::from_raw_fd(duplicate) };
    lock(&file, &root.canonicalize()?.join(GUARD_NAME))
}

#[cfg(unix)]
fn lock(file: &File, path: &Path) -> io::Result<()> {
    use std::fs::TryLockError;
    use std::time::{Duration, Instant};
    validate(file, path)?;
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        match file.try_lock() {
            Ok(()) => break,
            Err(TryLockError::WouldBlock) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(TryLockError::WouldBlock) => {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "build namespace guard is busy",
                ));
            }
            Err(TryLockError::Error(error)) => return Err(error),
        }
    }
    validate(file, path)
}

#[cfg(unix)]
fn validate(file: &File, path: &Path) -> io::Result<()> {
    use std::os::unix::fs::MetadataExt;
    let opened = file.metadata()?;
    let named = std::fs::symlink_metadata(path)?;
    if !opened.is_file()
        || !named.is_file()
        || named.file_type().is_symlink()
        || opened.dev() != named.dev()
        || opened.ino() != named.ino()
        || opened.nlink() != 1
        || named.nlink() != 1
        || opened.uid() != unsafe { libc::geteuid() }
        || opened.mode() & 0o022 != 0
        || opened.len() != 0
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "build namespace guard must be the persistent owned regular inode",
        ));
    }
    Ok(())
}
