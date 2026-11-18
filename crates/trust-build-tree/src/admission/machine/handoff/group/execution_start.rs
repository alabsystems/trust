//! The existing execution-start pipe reports lifecycle DATA only. The actual
//! native group owner calls this at its validated-loaded to GO transition.

use std::ffi::OsStr;
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;
use std::time::Instant;

type Identity = (u64, u64, u32);

#[cfg(test)]
thread_local! {
    pub(super) static AFTER_CHECK_MODE: std::cell::RefCell<Option<File>> = const { std::cell::RefCell::new(None) };
}

fn identity(file: &File) -> io::Result<Identity> {
    let meta = file.metadata()?;
    Ok((meta.dev(), meta.ino(), meta.mode()))
}

fn refused(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

/// The original lifecycle pipe only: no admission, GO or execution capability.
/// Hold it while queued; only the native group owner can arm and notify it.
pub struct ExecutionStartPipe {
    file: File,
    original: Identity,
    flags: libc::c_int,
}

impl ExecutionStartPipe {
    /// Retain the caller's original descriptor as a fresh owned description.
    /// The advertised number is routing DATA; every type/flag check is on the
    /// actual duplicate. The caller's descriptor is never adopted or closed.
    pub fn from_descriptor(raw: &OsStr) -> io::Result<Self> {
        let raw = raw
            .to_str()
            .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|text| text.parse::<i32>().ok())
            .filter(|fd| *fd >= 3)
            .ok_or_else(|| refused("invalid original execution-start descriptor"))?;
        // SAFETY: fcntl atomically duplicates a live descriptor or refuses;
        // it borrows no Rust owner and never takes ownership of the advertised slot.
        let copy = unsafe { libc::fcntl(raw, libc::F_DUPFD_CLOEXEC, 3) };
        if copy < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful fcntl returned this fresh, uniquely owned slot.
        Self::from_owned_writer(unsafe { File::from_raw_fd(copy) })
    }

    pub fn from_owned_writer(file: File) -> io::Result<Self> {
        let fd = file.as_raw_fd();
        let original = identity(&file)?;
        // SAFETY: observe this owned original descriptor without changing it.
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if fd < 3
            || original.2 & libc::S_IFMT as u32 != libc::S_IFIFO as u32
            || flags & libc::O_ACCMODE != libc::O_WRONLY
            || flags & libc::O_NONBLOCK == 0
        {
            return Err(refused("execution-start needs its original nonblocking pipe writer"));
        }
        Ok(Self { file, original, flags })
    }

    fn check(&self) -> io::Result<()> {
        // SAFETY: observe the same owned original's open-file-description flags.
        let flags = unsafe { libc::fcntl(self.file.as_raw_fd(), libc::F_GETFL) };
        if identity(&self.file)? != self.original || flags != self.flags {
            return Err(refused("original execution-start pipe changed"));
        }
        Ok(())
    }
}

pub(crate) struct ExecutionStart {
    file: File,
    original: Identity,
    flags: libc::c_int,
}

impl ExecutionStart {
    pub(crate) fn capture(
        input: ExecutionStartPipe,
        resources: impl IntoIterator<Item = i32>,
    ) -> io::Result<Self> {
        input.check()?;
        #[cfg(test)]
        AFTER_CHECK_MODE.with(|fault| {
            if let Some(file) = fault.borrow_mut().take() {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(std::fs::Permissions::from_mode(0o400)).unwrap();
            }
        });
        let ExecutionStartPipe { file, original, flags } = input;
        let fd = file.as_raw_fd();
        for resource in resources {
            let mut observed = std::mem::MaybeUninit::<libc::stat>::uninit();
            // SAFETY: borrowed actual resource descriptor and writable stat.
            if unsafe { libc::fstat(resource, observed.as_mut_ptr()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: successful fstat initialized the complete value.
            let observed = unsafe { observed.assume_init() };
            // Permission mode belongs to currency checks, not object identity:
            // changing it cannot turn the SAME original inode into a nonalias.
            if (original.0, original.1) == (observed.st_dev as u64, observed.st_ino) {
                return Err(refused("execution-start pipe aliases original scheduling transport"));
            }
        }
        // Apple's public sys/fcntl.h declares these descriptor operations as
        // 73 and 74. Apply them ONLY after rejecting every original-resource
        // alias: no process-wide signal handler or scheduling pipe is changed.
        const SET_NO_SIGPIPE: libc::c_int = 73;
        const GET_NO_SIGPIPE: libc::c_int = 74;
        // SAFETY: this is the independently owned lifecycle pipe, not a grant.
        if unsafe { libc::fcntl(fd, SET_NO_SIGPIPE, 1) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: read back this descriptor's actual native setting.
        if unsafe { libc::fcntl(fd, GET_NO_SIGPIPE) } != 1 {
            return Err(refused("execution-start pipe cannot suppress its own EPIPE signal"));
        }
        Ok(Self { file, original, flags })
    }

    pub(crate) fn notify(self, pid: u32, deadline: Instant) -> io::Result<()> {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        if identity(&self.file)? != self.original {
            return Err(refused("original execution-start pipe changed"));
        }
        // SAFETY: recheck the same original's finite nonblocking behavior;
        // an earlier observation cannot authorize a later blocking write.
        if unsafe { libc::fcntl(self.file.as_raw_fd(), libc::F_GETFL) } != self.flags {
            return Err(refused("original execution-start pipe flags changed"));
        }
        let mut now = std::mem::MaybeUninit::<libc::timespec>::uninit();
        // SAFETY: writable native timespec; this is the same monotonic clock
        // used by the existing build-slot lifecycle codec and its consumers.
        if unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, now.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: clock_gettime succeeded and initialized the complete value.
        let now = unsafe { now.assume_init() };
        let micros = u64::try_from(now.tv_sec)
            .ok()
            .and_then(|seconds| seconds.checked_mul(1_000_000))
            .and_then(|seconds| {
                u64::try_from(now.tv_nsec)
                    .ok()
                    .filter(|nanos| *nanos < 1_000_000_000)
                    .and_then(|nanos| seconds.checked_add(nanos / 1000))
            })
            .ok_or_else(|| refused("execution-start monotonic time exceeds codec bounds"))?;
        let mut message = [0; 17];
        message[0] = b'S';
        message[1..9].copy_from_slice(&u64::from(pid).to_be_bytes());
        message[9..].copy_from_slice(&micros.to_be_bytes());
        loop {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            // SAFETY: the same held nonblocking private writer and exactly
            // 17 initialized bytes. Its own NOSIGPIPE setting preserves EPIPE
            // as an error even under the process's default SIGPIPE action.
            let written = unsafe {
                libc::write(self.file.as_raw_fd(), message.as_ptr().cast(), message.len())
            };
            if written == message.len() as isize {
                return Ok(());
            }
            if written < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            return Err(refused("incomplete execution-start notification"));
        }
    }
}
