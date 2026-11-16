// Trust: kernel process identity for scheduling-only descendant handoff.
// No executable, source, compiler-unit or proof authority is granted here.

use std::io;
use std::mem::size_of;
use std::os::fd::AsRawFd;
#[cfg(target_os = "linux")]
use std::os::fd::{FromRawFd, OwnedFd};
use std::os::unix::net::UnixStream;
#[cfg(target_os = "linux")]
use std::sync::Arc;

fn refused(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Identity {
    pid: u32,
    parent: u32,
    birth: u64,
    #[cfg(target_os = "macos")]
    parent_birth: u64,
    #[cfg(target_os = "macos")]
    version: u32,
}

#[derive(Clone, Debug)]
pub(super) struct Process {
    identity: Identity,
    #[cfg(target_os = "linux")]
    lifetime: Arc<OwnedFd>,
}

impl Process {
    pub(super) fn capture(pid: u32) -> io::Result<Self> {
        let identity = read_identity(pid)?;
        #[cfg(target_os = "linux")]
        let lifetime = {
            // SAFETY: pidfd_open creates a new CLOEXEC descriptor or returns -1.
            let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) };
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: this successful syscall returned one newly owned fd.
            Arc::new(unsafe { OwnedFd::from_raw_fd(fd as libc::c_int) })
        };
        let process = Self {
            identity,
            #[cfg(target_os = "linux")]
            lifetime,
        };
        process.ensure_unchanged()?;
        Ok(process)
    }

    pub(super) fn direct_child(pid: u32) -> io::Result<Self> {
        let parent = Self::current()?;
        let child = Self::capture(pid)?;
        if child.identity.parent != parent.pid() {
            return Err(refused("scoped handoff member is not our direct child"));
        }
        #[cfg(target_os = "macos")]
        if child.identity.parent_birth != parent.birth() {
            return Err(refused("scoped handoff member has a replaced parent"));
        }
        child.ensure_unchanged()?;
        parent.ensure_unchanged()?;
        Ok(child)
    }

    pub(super) fn current() -> io::Result<Self> {
        Self::capture(std::process::id())
    }

    pub(super) fn pid(&self) -> u32 {
        self.identity.pid
    }

    pub(super) fn birth(&self) -> u64 {
        self.identity.birth
    }

    /// A registered member may exec after its stopped launch was bound.
    /// Preserve lifetime and parent identity, then capture its CURRENT image's
    /// peer version. Owner endpoints and in-flight chains never use this path.
    pub(super) fn refresh_registered_member(&self) -> io::Result<Self> {
        self.ensure_alive()?;
        let current = Self::capture(self.pid())?;
        if current.identity.birth != self.identity.birth
            || current.identity.parent != self.identity.parent
        {
            return Err(refused("registered member changed lifetime or parent"));
        }
        #[cfg(target_os = "macos")]
        if current.identity.parent_birth != self.identity.parent_birth {
            return Err(refused("registered member parent was replaced"));
        }
        current.ensure_unchanged()?;
        self.ensure_alive()?;
        Ok(current)
    }

    fn ensure_alive(&self) -> io::Result<()> {
        #[cfg(target_os = "linux")]
        {
            let mut descriptor =
                libc::pollfd { fd: self.lifetime.as_raw_fd(), events: libc::POLLIN, revents: 0 };
            // SAFETY: one initialized pollfd is writable for this call.
            if unsafe { libc::poll(&mut descriptor, 1, 0) } != 0 {
                return Err(refused("jobserver peer exited during handoff"));
            }
        }
        Ok(())
    }

    pub(super) fn ensure_unchanged(&self) -> io::Result<()> {
        self.ensure_alive()?;
        if read_identity(self.pid())? != self.identity {
            return Err(refused("jobserver peer changed identity or parent during handoff"));
        }
        Ok(())
    }

    pub(super) fn peer(stream: &UnixStream) -> io::Result<Self> {
        #[cfg(target_os = "linux")]
        let (pid, uid) = {
            let mut credentials = std::mem::MaybeUninit::<libc::ucred>::uninit();
            let mut length = size_of::<libc::ucred>() as libc::socklen_t;
            // SAFETY: the buffer is read only after the exact-size check.
            if unsafe {
                libc::getsockopt(
                    stream.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_PEERCRED,
                    credentials.as_mut_ptr().cast(),
                    &mut length,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            if length as usize != size_of::<libc::ucred>() {
                return Err(refused("malformed jobserver peer credentials"));
            }
            // SAFETY: getsockopt initialized this exact-sized buffer.
            let credentials = unsafe { credentials.assume_init() };
            (u32::try_from(credentials.pid).unwrap_or(0), credentials.uid)
        };
        #[cfg(target_os = "macos")]
        let token = {
            let mut token = [0_u32; 8];
            let mut length = size_of::<[u32; 8]>() as libc::socklen_t;
            // SAFETY: audit_token_t consists of eight words. It is used only
            // after the kernel returns the complete token, as in Targo's
            // existing process_authority/macos_broker.rs owner.
            if unsafe {
                libc::getsockopt(
                    stream.as_raw_fd(),
                    libc::SOL_LOCAL,
                    libc::LOCAL_PEERTOKEN,
                    token.as_mut_ptr().cast(),
                    &mut length,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            if length as usize != size_of::<[u32; 8]>() {
                return Err(refused("malformed jobserver peer audit token"));
            }
            token
        };
        #[cfg(target_os = "macos")]
        let (pid, uid) = (token[5], token[1]);
        // SAFETY: geteuid has no preconditions.
        if pid == 0 || uid != unsafe { libc::geteuid() } {
            return Err(refused("jobserver peer is not a live same-user process"));
        }
        let process = Self::capture(pid)?;
        #[cfg(target_os = "macos")]
        if token[7] != process.identity.version {
            return Err(refused("jobserver socket peer process was replaced"));
        }
        Ok(process)
    }
}

/// Bind a bounded client-to-owner parent chain to process birth identities.
/// A sibling, stale PID or reparented descendant is never a substitute owner.
pub(super) fn ancestry(owner: &Process, requester: &Process) -> io::Result<Vec<Process>> {
    if owner.pid() == requester.pid() {
        return Err(refused("jobserver endpoint owner is not an ancestor"));
    }
    let mut chain = vec![requester.clone()];
    for _ in 0..256 {
        let child = chain.last().unwrap();
        if child.identity.parent <= 1 {
            break;
        }
        let parent = Process::capture(child.identity.parent)?;
        #[cfg(target_os = "macos")]
        if child.identity.parent_birth != parent.birth() {
            return Err(refused("jobserver ancestor process was replaced"));
        }
        if parent.pid() == owner.pid() {
            if parent.birth() != owner.birth() {
                return Err(refused("jobserver endpoint owner PID was reused"));
            }
            chain.push(parent);
            ensure_chain(&chain)?;
            owner.ensure_unchanged()?;
            return Ok(chain);
        }
        chain.push(parent);
    }
    Err(refused("jobserver endpoint owner is not a bounded live ancestor"))
}

pub(super) fn ensure_chain(chain: &[Process]) -> io::Result<()> {
    chain.iter().try_for_each(Process::ensure_unchanged)
}

#[cfg(target_os = "linux")]
fn read_identity(pid: u32) -> io::Result<Identity> {
    fn read(pid: u32) -> io::Result<Identity> {
        let text = std::fs::read_to_string(format!("/proc/{pid}/stat"))?;
        let (_, fields) = text.rsplit_once(')').ok_or_else(|| refused("invalid process stat"))?;
        let fields = fields.split_whitespace().collect::<Vec<_>>();
        let parent = fields.get(1).and_then(|s| s.parse().ok());
        let birth = fields.get(19).and_then(|s| s.parse().ok());
        match (parent, birth) {
            (Some(parent), Some(birth)) => Ok(Identity { pid, parent, birth }),
            _ => Err(refused("incomplete process stat")),
        }
    }
    let before = read(pid)?;
    if read(pid)? != before {
        return Err(refused("process changed while reading its identity"));
    }
    Ok(before)
}

/// Trust: a record `proc_pidinfo` writes whole.
///
/// # Safety
///
/// Every bit pattern, all-zero included, must be a valid value of the type:
/// `read_record` hands back the zeroed buffer as the kernel left it.
#[cfg(target_os = "macos")]
unsafe trait ProcRecord: Copy {}

// SAFETY: integers and `c_char` arrays only.
#[cfg(target_os = "macos")]
unsafe impl ProcRecord for libc::proc_bsdinfo {}

/// Trust: the `proc_pidinfo` a reader calls, `native_info` or a test's
/// stand-in. Any `unsafe fn` of this shape coerces to it, whatever its own
/// contract, so the safe-looking readers that call one (`read_record`,
/// `read_identity_with`) are `unsafe fn` and their callers vouch for it.
#[cfg(target_os = "macos")]
type ProcInfo = unsafe fn(libc::c_int, libc::c_int, *mut libc::c_void, libc::c_int) -> libc::c_int;

/// # Safety
///
/// `size` must be non-negative and `buffer` must be `size` writable bytes.
#[cfg(target_os = "macos")]
unsafe fn native_info(
    pid: libc::c_int,
    flavor: libc::c_int,
    buffer: *mut libc::c_void,
    size: libc::c_int,
) -> libc::c_int {
    // SAFETY: the caller hands `size` writable bytes, which bounds the write.
    unsafe { libc::proc_pidinfo(pid, flavor, 0, buffer, size) }
}

/// Trust: one fixed-size `proc_pidinfo` record. The call returns the bytes it
/// wrote, or 0 with errno set. A short positive count sets no errno, so it is
/// its own error: reading errno then would report whatever an earlier call
/// left there.
///
/// # Safety
///
/// `info` must be safe to call with a non-negative `size` and a buffer of
/// `size` writable bytes, and must write at most `size` bytes into it.
#[cfg(target_os = "macos")]
unsafe fn read_record<T: ProcRecord>(
    pid: u32,
    flavor: libc::c_int,
    info: ProcInfo,
) -> io::Result<T> {
    let pid = libc::c_int::try_from(pid).map_err(|_| refused("invalid process PID"))?;
    const { assert!(size_of::<T>() <= libc::c_int::MAX as usize) };
    let mut output = std::mem::MaybeUninit::<T>::zeroed();
    let size = size_of::<T>() as libc::c_int;
    // SAFETY: `output` is exactly `size` writable bytes, `size` is
    // non-negative (the assertion above), and the caller vouches for `info`.
    let count = unsafe { info(pid, flavor, output.as_mut_ptr().cast(), size) };
    if count <= 0 {
        return Err(io::Error::last_os_error());
    }
    if count != size {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "incomplete native process identity record",
        ));
    }
    // SAFETY: every bit pattern is a valid T (`ProcRecord`), and the
    // exact-size count says the kernel wrote the whole record.
    Ok(unsafe { output.assume_init() })
}

#[cfg(target_os = "macos")]
fn read_identity(pid: u32) -> io::Result<Identity> {
    // SAFETY: native_info meets read_identity_with's contract: it hands
    // proc_pidinfo the caller's buffer and size, and the kernel writes at most
    // `size` bytes.
    unsafe { read_identity_with(pid, native_info) }
}

/// # Safety
///
/// The same contract as `read_record`'s, for `info`.
#[cfg(target_os = "macos")]
unsafe fn read_identity_with(pid: u32, info: ProcInfo) -> io::Result<Identity> {
    // Same pinned proc_uniqidentifierinfo ABI used by Targo's existing broker.
    #[repr(C)]
    #[derive(Clone, Copy, Default)]
    struct Unique {
        uuid: [u8; 16],
        birth: u64,
        parent_birth: u64,
        version: i32,
        parent_version: i32,
        reserved: [u64; 2],
    }
    // SAFETY: a byte array and integers only.
    unsafe impl ProcRecord for Unique {}
    // SAFETY: the caller vouches for `info`, as read_record requires.
    let before: Unique = unsafe { read_record(pid, 17, info) }?;
    // SAFETY: the caller vouches for `info`, as read_record requires.
    let bsd: libc::proc_bsdinfo = unsafe { read_record(pid, libc::PROC_PIDTBSDINFO, info) }?;
    // SAFETY: the caller vouches for `info`, as read_record requires.
    let after: Unique = unsafe { read_record(pid, 17, info) }?;
    if before.birth != after.birth
        || before.parent_birth != after.parent_birth
        || before.version != after.version
        || bsd.pbi_pid != pid
    {
        return Err(refused("process changed while reading its unique identity"));
    }
    Ok(Identity {
        pid,
        parent: bsd.pbi_ppid,
        birth: after.birth,
        parent_birth: after.parent_birth,
        version: after.version as u32,
    })
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "tests/handoff_process.rs"]
mod tests;
