//! A process asking the kernel about itself (X3a, design §2.6): the
//! descriptor listing `proc_pidinfo(getpid(), PROC_PIDLISTFDS, …)` and the
//! integer sysctl `kern.maxfilesperproc`. aterm's descriptor strip
//! (`aterm-uds` `spawnfd::InheritStrip`: `descriptor_bound` in the parent,
//! `darwin_strip::mark_listed` in the forked child) is built from exactly
//! these two calls. Neither changes the host.
//!
//! MEASURED (Darwin 25.6, 2026-10-01; re-checked by every run of
//! `tests/conformance_darwin.rs`):
//!
//! * `PROC_PIDLISTFDS` lists the caller's open descriptors in ASCENDING
//!   order, `struct proc_fdinfo { int32 fd; uint32 type }` (8 bytes) each,
//!   and a buffer of `n` slots holds the LOWEST `n` of them; the return is
//!   the byte count written. Kqueues are listed (type 5), so are descriptors
//!   above a lowered soft `RLIMIT_NOFILE`; close-on-exec plays no part. A
//!   non-NULL buffer smaller than one entry is `ENOMEM` (libproc then
//!   returns 0); a size that is not a multiple of 8 is rounded down; the
//!   `arg` operand is ignored; a NEGATIVE size is read as a ~4 GiB buffer
//!   (the kernel wrote all ten entries of a ten-descriptor table into a
//!   four-entry buffer) — refused here, since no program has that buffer.
//! * `sysctlbyname("kern.maxfilesperproc", old, &oldlen, NULL, 0)` writes the
//!   `int` (92160 here) and sets `oldlen` to 4 for any `oldlen >= 4`; an
//!   `oldlen` below 4 (0 included) is `ENOMEM` with `oldlen` set to 0; a
//!   write (`new` non-NULL) by an unprivileged process is `EPERM`; an unknown
//!   name is `ENOENT`.

use crate::call::{Refusal, Ret, SysResult};
use crate::darwin::Errno;
use crate::host::{Host, OfdKind, Pid};

/// `PROC_PIDLISTFDS` (`sys/proc_info.h`): the `proc_pidinfo` flavor that
/// lists a process's descriptors.
pub const PROC_PIDLISTFDS: i32 = 1;

/// `sizeof(struct proc_fdinfo)` (`sys/proc_info.h`): `int32_t proc_fd;
/// uint32_t proc_fdtype;`. MEASURED: 8.
pub const PROC_FDINFO_SIZE: i32 = 8;

/// `proc_fdtype` values (`sys/proc_info.h`, `PROX_FDTYPE_*`) for the kinds
/// the model has. MEASURED: `/dev/null` and `/` list as a vnode, a pipe end
/// as a pipe, an `AF_UNIX` socket as a socket, a kqueue as a kqueue.
pub const PROX_FDTYPE_VNODE: u32 = 1;
pub const PROX_FDTYPE_SOCKET: u32 = 2;
pub const PROX_FDTYPE_KQUEUE: u32 = 5;
pub const PROX_FDTYPE_PIPE: u32 = 6;

/// The one sysctl name the model answers.
pub const SYSCTL_MAXFILESPERPROC: &str = "kern.maxfilesperproc";

/// One `struct proc_fdinfo` of a listing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ListedFd {
    pub fd: i32,
    /// `proc_fdtype`; `None` for a description whose kind RL-INIT left
    /// unknown ([`OfdKind::Opaque`]: the listing has SOME type for it, the
    /// model does not know which).
    pub fdtype: Option<u32>,
}

/// The `proc_fdtype` the kernel lists for a description of `kind`.
#[must_use]
pub fn fdtype(kind: OfdKind) -> Option<u32> {
    match kind {
        OfdKind::PipeRead | OfdKind::PipeWrite => Some(PROX_FDTYPE_PIPE),
        OfdKind::Socket { .. } => Some(PROX_FDTYPE_SOCKET),
        OfdKind::Kqueue => Some(PROX_FDTYPE_KQUEUE),
        OfdKind::File => Some(PROX_FDTYPE_VNODE),
        OfdKind::Opaque => None,
    }
}

/// What `proc_pidinfo(getpid(), PROC_PIDLISTFDS, _, buf, bytes)` writes into
/// a non-NULL `buf` when `pid` calls it in `host` (the state BEFORE the call):
/// the lowest `bytes / 8` open descriptors, ascending, or `ENOMEM` when
/// `bytes < 8`.
///
/// Refused by name:
/// * a negative `bytes` (the kernel reads it as a ~4 GiB buffer and writes
///   the whole table, whatever the program allocated);
/// * a caller with more than one thread: XNU lists without a snapshot (the
///   torn-copy class [`crate::clauses::step_torn`] measures for `fork`), so a
///   slot another thread is `dup2`-ing onto may be missing. The listing is
///   exact for a single-threaded caller — aterm's is a fork child before its
///   exec, which nothing else can touch.
pub fn listing(host: &Host, pid: Pid, bytes: i32) -> Result<Result<Vec<ListedFd>, Errno>, Refusal> {
    let proc = host.proc(pid).ok_or(Refusal::NoSuchProcess(pid))?;
    if !proc.is_live() {
        return Err(Refusal::NotLive(pid));
    }
    if bytes < 0 {
        return Err(Refusal::Unmodeled {
            symbol: "proc_pidinfo",
            detail: format!(
                "PROC_PIDLISTFDS with buffer size {bytes}: the kernel reads it as {} bytes and \
                 may write past any buffer the program has",
                bytes.cast_unsigned()
            ),
        });
    }
    if proc.threads > 1 {
        return Err(Refusal::Unmodeled {
            symbol: "proc_pidinfo",
            detail: format!(
                "PROC_PIDLISTFDS in a process running {} threads: a listing that races another \
                 thread's dup2/close is not modeled (only a single-threaded caller is)",
                proc.threads
            ),
        });
    }
    if bytes < PROC_FDINFO_SIZE {
        return Ok(Err(Errno::ENOMEM));
    }
    let slots = usize::try_from(bytes / PROC_FDINFO_SIZE).unwrap_or(0);
    Ok(Ok(proc
        .table
        .iter()
        .take(slots)
        .map(|(fd, e)| ListedFd { fd: *fd, fdtype: host.ofd(e.ofd).and_then(|o| fdtype(o.kind)) })
        .collect()))
}

/// The [`crate::Call::ListOwnFds`] clause: the byte count the listing wrote.
pub(crate) fn list_own_fds(h: &Host, pid: Pid, bytes: i32) -> Result<SysResult, Refusal> {
    Ok(listing(h, pid, bytes)?.map(|l| {
        let n = i64::try_from(l.len()).unwrap_or(i64::MAX);
        Ret::Int(n.saturating_mul(i64::from(PROC_FDINFO_SIZE)))
    }))
}

/// Integer sysctls a refusal can say more about than "not modeled".
const SYSCTL_NAMED: &[(&str, &str)] = &[
    (
        "kern.maxfiles",
        "the system-wide file table size: the model has no system table (ENFILE is an oracle \
         choice)",
    ),
    ("kern.num_files", "the system-wide open-file count is not modeled"),
    ("kern.maxproc", "process-count limits are not modeled"),
    ("kern.maxprocperuid", "process-count limits are not modeled"),
];

/// The [`crate::Call::Sysctl`] clause: a read of `name` into an `oldlen`-byte
/// buffer. Only `kern.maxfilesperproc` — the host's
/// [`Host::max_files_per_proc`], which the model holds constant (root alone
/// can change it; premise P-MAXFILES) — is answered; any other name is
/// refused by name.
pub(crate) fn sysctl(h: &Host, name: &str, oldlen: u64) -> Result<SysResult, Refusal> {
    if name != SYSCTL_MAXFILESPERPROC {
        let why = SYSCTL_NAMED
            .iter()
            .find(|(n, _)| *n == name)
            .map_or("only kern.maxfilesperproc is modeled", |(_, why)| why);
        return Err(Refusal::Unmodeled {
            symbol: "sysctlbyname",
            detail: format!("{name}: {why}"),
        });
    }
    if oldlen < 4 {
        return Ok(Err(Errno::ENOMEM));
    }
    let v = i32::try_from(h.max_files_per_proc()).map_err(|_| Refusal::Unmodeled {
        symbol: "sysctlbyname",
        detail: format!(
            "kern.maxfilesperproc = {} does not fit the int the sysctl returns",
            h.max_files_per_proc()
        ),
    })?;
    Ok(Ok(Ret::Int(i64::from(v))))
}
