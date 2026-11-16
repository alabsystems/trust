//! Trust: ownership of bootstrap's existing output-directory lock.
//!
//! This guard excludes cooperating output writers and cleanup actors for its
//! live-process lifetime. The named `lock` inode and physical output directory
//! must be preserved by those actors. It neither freezes source bytes nor
//! survives process death. PID text is diagnostic only.

#[cfg(unix)]
use std::fs::{self, File, Metadata, OpenOptions, TryLockError};
use std::io;
#[cfg(unix)]
use std::io::{Read, Seek, SeekFrom, Write};
#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
#[cfg(unix)]
use std::path::PathBuf;

/// Actual exclusive ownership of the existing `output/lock` inode.
///
/// Keep this value until all protected work has settled. It cannot be cloned or
/// reconstructed from a PID, pathname, or description. Drop only closes owned
/// descriptors; it does not unlink the sentinel or explicitly unlock a shared
/// open-file description. Moving it to another thread is supported; inheriting
/// it across fork does not establish independent ownership.
#[must_use = "dropping the guard releases output ownership"]
pub struct OutputLock {
    #[cfg(unix)]
    state: State,
    #[cfg(not(unix))]
    _unsupported: (),
}

/// Borrowed originals from one actual close-only output guard. No file/path
/// constructor exists; these descriptions neither acquire nor release a lock.
#[cfg(unix)]
pub struct OriginalOutputDescriptions<'a> {
    root: &'a Path,
    directory: std::os::fd::BorrowedFd<'a>,
    lock: std::os::fd::BorrowedFd<'a>,
}

#[cfg(unix)]
impl<'a> OriginalOutputDescriptions<'a> {
    pub fn root(&self) -> &'a Path {
        self.root
    }
    pub fn directory(&self) -> std::os::fd::BorrowedFd<'a> {
        self.directory
    }
    pub fn lock(&self) -> std::os::fd::BorrowedFd<'a> {
        self.lock
    }
}

#[cfg(unix)]
struct State {
    file: File,
    root_file: File,
    logical: PathBuf,
    physical: PathBuf,
    logical_identity: Identity,
    root_identity: Identity,
    lock_identity: Identity,
}

#[cfg(unix)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct Identity {
    device: u64,
    inode: u64,
    kind: fs::FileType,
}

#[cfg(unix)]
impl Identity {
    fn of(metadata: &Metadata) -> Self {
        Self { device: metadata.dev(), inode: metadata.ino(), kind: metadata.file_type() }
    }
}

impl OutputLock {
    /// Borrow the SAME original physical output directory for no-follow,
    /// descriptor-relative observations. This exposes no lock description and
    /// creates no ownership. Enumerators must open an independent directory
    /// description rather than change this original description's cursor.
    #[cfg(unix)]
    pub fn original_directory(&self) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        use std::os::fd::AsFd as _;
        self.check_current()?;
        Ok(self.state.root_file.as_fd())
    }

    /// Checked name observation of this same held physical directory. A name
    /// never creates or reconstructs an output guard.
    #[cfg(unix)]
    pub fn original_root(&self) -> io::Result<&Path> {
        self.check_current()?;
        Ok(&self.state.physical)
    }

    /// Borrow the SAME original physical root and held lock descriptions for
    /// authenticated original-root input retention. No reopen or lock call.
    ///
    /// # Safety
    /// The recipient and every transferred duplicate must be close-only: never
    /// unlock, change flags/cursors or mutate/close an original descriptor.
    /// Retain this actual guard through original Host custody/settlement; an
    /// acknowledgement or record is not release authority.
    #[cfg(unix)]
    pub unsafe fn original_descriptions(&self) -> io::Result<OriginalOutputDescriptions<'_>> {
        use std::os::fd::AsFd as _;
        self.check_current()?;
        Ok(OriginalOutputDescriptions {
            root: &self.state.physical,
            directory: self.state.root_file.as_fd(),
            lock: self.state.file.as_fd(),
        })
    }

    /// Try once without waiting for another output owner. Missing output
    /// directories are created before their identities are captured. A logical
    /// root symlink is supported when it resolves to an existing directory;
    /// the lock leaf itself may never be a symlink.
    pub fn try_acquire(out: &Path) -> io::Result<Option<Self>> {
        Self::try_acquire_with(out, true)
    }

    /// Try an already existing output directory and lock leaf. Unlike
    /// [`Self::try_acquire`], this never creates donor state. Missing paths are
    /// errors; contention alone returns `Ok(None)`.
    pub fn try_acquire_existing(out: &Path) -> io::Result<Option<Self>> {
        Self::try_acquire_with(out, false)
    }

    fn try_acquire_with(out: &Path, create: bool) -> io::Result<Option<Self>> {
        #[cfg(unix)]
        {
            let mut state = State::open(out, create)?;
            match state.file.try_lock() {
                Ok(()) => {
                    state.acquired()?;
                    Ok(Some(Self { state }))
                }
                Err(TryLockError::WouldBlock) => {
                    state.check_current()?;
                    Ok(None)
                }
                Err(TryLockError::Error(error)) => Err(error),
            }
        }
        #[cfg(not(unix))]
        {
            let _ = (out, create);
            Err(unsupported())
        }
    }

    /// Acquire ownership, reporting contention once before the single blocking
    /// OS-lock wait. The optional PID is untrusted diagnostic text and never
    /// establishes liveness or release authority. Filesystem calls and the
    /// blocking lock wait have no finite deadline.
    pub fn acquire(out: &Path, on_busy: impl FnOnce(Option<u32>)) -> io::Result<Self> {
        #[cfg(unix)]
        {
            let mut state = State::open(out, true)?;
            match state.file.try_lock() {
                Ok(()) => {}
                Err(TryLockError::WouldBlock) => {
                    state.check_current()?;
                    on_busy(state.diagnostic_pid());
                    state.check_current()?;
                    state.file.lock()?;
                }
                Err(TryLockError::Error(error)) => return Err(error),
            }
            state.acquired()?;
            Ok(Self { state })
        }
        #[cfg(not(unix))]
        {
            let _ = (out, on_busy);
            Err(unsupported())
        }
    }

    /// Recheck the original logical mapping and named root/lock identities.
    /// This is replacement detection, not protection against arbitrary actors
    /// deleting or changing paths outside the cooperating cleanup protocol.
    pub fn check_current(&self) -> io::Result<()> {
        #[cfg(unix)]
        {
            self.state.check_current()
        }
        #[cfg(not(unix))]
        {
            Err(unsupported())
        }
    }

    /// Check that the requested output is the SAME original held root. This
    /// observes identity only; it acquires no lock and creates no ownership.
    pub fn check_root(&self, output: &Path) -> io::Result<()> {
        self.check_current()?;
        #[cfg(unix)]
        {
            if fs::canonicalize(output)? != self.state.physical
                || Identity::of(&fs::metadata(output)?) != self.state.root_identity
            {
                return Err(invalid("requested output is not the original held root"));
            }
            self.check_current()
        }
        #[cfg(not(unix))]
        {
            let _ = output;
            Err(unsupported())
        }
    }
}

#[cfg(not(unix))]
fn unsupported() -> io::Error {
    io::Error::new(io::ErrorKind::Unsupported, "checked output-lock identity requires Unix")
}

#[cfg(unix)]
fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(unix)]
impl State {
    fn open(out: &Path, create: bool) -> io::Result<Self> {
        let logical =
            if out.is_absolute() { out.to_owned() } else { std::env::current_dir()?.join(out) };
        if create {
            fs::create_dir_all(&logical)?;
        }
        let logical_metadata = fs::symlink_metadata(&logical)?;
        if !logical_metadata.is_dir() && !logical_metadata.file_type().is_symlink() {
            return Err(invalid("output root must resolve to a directory"));
        }
        let physical = fs::canonicalize(&logical)?;
        let root_file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_DIRECTORY)
            .open(&physical)?;
        let root_metadata = root_file.metadata()?;
        if !root_metadata.is_dir() {
            return Err(invalid("physical output root is not a directory"));
        }
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(create)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(physical.join("lock"))?;
        let lock_identity = Identity::of(&file.metadata()?);
        let state = Self {
            file,
            root_file,
            logical,
            physical,
            logical_identity: Identity::of(&logical_metadata),
            root_identity: Identity::of(&root_metadata),
            lock_identity,
        };
        state.check_current()?;
        Ok(state)
    }

    fn check_current(&self) -> io::Result<()> {
        let logical = fs::symlink_metadata(&self.logical)?;
        let physical = fs::symlink_metadata(&self.physical)?;
        if Identity::of(&logical) != self.logical_identity
            || fs::canonicalize(&self.logical)? != self.physical
            || !physical.is_dir()
            || physical.file_type().is_symlink()
            || Identity::of(&physical) != self.root_identity
            || Identity::of(&self.root_file.metadata()?) != self.root_identity
        {
            return Err(invalid("output root or its logical mapping changed"));
        }
        let opened = self.file.metadata()?;
        let named = fs::symlink_metadata(self.physical.join("lock"))?;
        for metadata in [&opened, &named] {
            if !metadata.is_file()
                || metadata.file_type().is_symlink()
                || metadata.nlink() != 1
                || metadata.uid() != unsafe { libc::geteuid() }
                || metadata.mode() & 0o022 != 0
                || Identity::of(metadata) != self.lock_identity
            {
                return Err(invalid(
                    "output lock must remain the same owned regular single-link inode",
                ));
            }
        }
        Ok(())
    }

    fn acquired(&mut self) -> io::Result<()> {
        self.check_current()?;
        self.file.set_len(0)?;
        self.file.seek(SeekFrom::Start(0))?;
        write!(&mut self.file, "{}", std::process::id())?;
        self.check_current()
    }

    fn diagnostic_pid(&mut self) -> Option<u32> {
        let mut text = String::new();
        self.file.seek(SeekFrom::Start(0)).ok()?;
        (&self.file).take(32).read_to_string(&mut text).ok()?;
        text.parse::<u32>().ok().filter(|pid| *pid != 0)
    }
}

#[cfg(all(test, unix))]
pub(crate) mod tests;
