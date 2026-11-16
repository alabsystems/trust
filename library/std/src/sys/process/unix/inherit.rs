// Trust: this whole module is Trust-only (docs/DECISION_QUEUE.md, SP-1).
//! A spawned child inherits its stdio and NOTHING ELSE, unless asked.
//!
//! Upstream `Command` hands a child every descriptor this process holds
//! without `FD_CLOEXEC` at the instant of the spawn. std opens its own
//! descriptors close-on-exec, but that still leaves every descriptor another
//! thread is creating (Darwin has no `SOCK_CLOEXEC`: a `socketpair` end is
//! unflagged until its `F_SETFD`), every one this process inherited from its
//! own parent, and every one a C library opened without the flag. Each rides
//! into every child for the child's whole life. MEASURED (aterm, 2026-10-01):
//! a plain `Command` racing another thread's `UnixStream::pair()` carried a
//! pair end into 17-27 of 200 children.
//!
//! Trust's std hands a spawned child exactly
//!
//! * fds 0, 1 and 2 as the `Command` configures them (null, inherited, piped,
//!   or a given descriptor), and
//! * the descriptors `CommandExt::inherit_fd` names, at their own numbers;
//!
//! `CommandExt::inherit_all_fds` restores upstream's behaviour, and a
//! `pre_exec` hook can still hand anything over (it runs after the strip, and
//! `dup2` clears `FD_CLOEXEC` on its target). `CommandExt::exec` replaces this
//! process rather than starting a child and keeps upstream's behaviour.
//!
//! Two mechanisms, both reused from aterm's `crates/aterm-uds/src/spawnfd.rs`,
//! which implements and tests each of them:
//!
//! * The `posix_spawn` path. Darwin: `POSIX_SPAWN_CLOEXEC_DEFAULT`, so the
//!   kernel closes every descriptor no file action names. Facts MEASURED on
//!   Darwin 25 (aterm, 2026-09-30): only a descriptor a file action names AND
//!   that is not close-on-exec at the exec survives; `adddup2(fd, fd)` KEEPS
//!   `FD_CLOEXEC` (a source sitting on its own target would arrive closed)
//!   while `addinherit_np(fd)` clears it; libc refuses a file action naming
//!   any number >= 10 240 (`OPEN_MAX`) with `EBADF` at add time; kqueue
//!   descriptors never cross; the table copy is not atomic, but a concurrent
//!   change can only DROP a slot from the child, never add one. Elsewhere:
//!   `posix_spawn_file_actions_addclosefrom_np(3)` where libc has it (glibc
//!   2.34+, FreeBSD 13.1+, illumos); a spawn that cannot be expressed takes
//!   the fork path instead.
//! * The fork path (a `pre_exec` hook, or a spawn `posix_spawn` cannot
//!   express): [`FdStrip`]. In the child, after std has placed stdio and
//!   before the first `pre_exec` hook, every descriptor from 3 up is MARKED
//!   close-on-exec (never closed: std's own exec-status pipe is already
//!   close-on-exec and must stay open until the exec, to report a failure).
//!   The strip lists the child's own table, which no other thread can change:
//!   `close_range(3, ~0, CLOSE_RANGE_CLOEXEC)` or `/proc/self/fd` on Linux,
//!   `proc_pidinfo(PROC_PIDLISTFDS)` on Darwin; where a listing fails or is
//!   cut short it probes every number up to [`descriptor_bound`], read before
//!   the fork.

// tvOS and watchOS never fork (`Command::do_exec` is a stub there).
#![cfg_attr(any(target_os = "tvos", target_os = "watchos"), allow(dead_code))]

use libc::c_int;

use crate::io;

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests;

/// The first descriptor number the strip touches: everything above stdio.
const FIRST_STRIPPED: c_int = 3;

/// The bound used when the kernel's own cannot be read.
const FALLBACK_BOUND: c_int = 1 << 20;

/// Darwin's libc answers `EBADF` at add time for a file action naming any
/// descriptor at `OPEN_MAX` (10 240) or above: a spawn that would need one
/// takes the fork path.
#[cfg(target_vendor = "apple")]
pub(crate) const ACTION_FD_LIMIT: c_int = 10_240;

/// The lowest number std's exec-status descriptor may sit on in a fork whose
/// `pre_exec` hooks run: above 0..=9, the numbers a hook conventionally
/// places descriptors on (shell redirections, jobserver and `LISTEN_FDS`
/// hand-offs). A hook that `dup2`s onto the status descriptor replaces it in
/// the child, and a failed `exec` then reads as a started child.
pub(crate) const STATUS_FD_FLOOR: c_int = 10;

#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    /// `<spawn.h>`: hand `fd` to the child at its own number, clearing its
    /// `FD_CLOEXEC` there (unlike `adddup2(fd, fd)`).
    pub(crate) fn posix_spawn_file_actions_addinherit_np(
        actions: *mut libc::posix_spawn_file_actions_t,
        fd: c_int,
    ) -> c_int;
}

/// Whether this process holds `fd` open WITHOUT close-on-exec: whether a
/// plain `exec` would hand it on.
#[cfg(target_vendor = "apple")]
pub(crate) fn passes_exec(fd: c_int) -> bool {
    // SAFETY: `F_GETFD` reads one descriptor's flags; a closed number is -1.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    flags >= 0 && flags & libc::FD_CLOEXEC == 0
}

/// Set `FD_CLOEXEC` on `fd` if it is open and not already flagged, keeping
/// any other descriptor flag. Async-signal-safe: two `fcntl`s on integers.
fn mark_cloexec(fd: c_int) {
    // SAFETY: integer arguments only; an unused number is a harmless `EBADF`.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFD);
        if flags >= 0 && flags & libc::FD_CLOEXEC == 0 {
            libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC);
        }
    }
}

/// Clear `FD_CLOEXEC` on `fd`, which must be open: `inherit_fd`'s hand-over
/// on the fork path. Async-signal-safe (the error is `last_os_error`, which
/// allocates nothing).
pub(crate) fn clear_cloexec(fd: c_int) -> io::Result<()> {
    // SAFETY: integer arguments only.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFD);
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::FD_CLOEXEC != 0
            && libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
        {
            return Err(io::Error::last_os_error());
        }
    }
    Ok(())
}

/// Whether `inherit_fd`'s numbers name any of `own`: descriptors std opened
/// for this spawn, which a number the caller never opened can land on.
pub(crate) fn names_any(inherit: &[c_int], own: &[Option<c_int>]) -> bool {
    inherit.iter().any(|fd| own.contains(&Some(*fd)))
}

/// A close-on-exec copy of `fd` at [`STATUS_FD_FLOOR`] or above, or `None`
/// when none can be made (no free number there below the soft limit): the
/// caller then keeps `fd` where it is.
pub(crate) fn dup_above_conventional(fd: c_int) -> Option<c_int> {
    if fd >= STATUS_FD_FLOOR {
        return None;
    }
    // SAFETY: `F_DUPFD_CLOEXEC` reads one descriptor number and returns a
    // fresh descriptor or -1; it touches no memory.
    let copy = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, STATUS_FD_FLOOR) };
    (copy >= 0).then_some(copy)
}

/// THE STRIP for a spawn that forks. [`FdStrip::prepare`] in the parent,
/// before the fork; [`FdStrip::apply`] in the child, between the fork and the
/// exec: every descriptor above stdio is then close-on-exec, and what the
/// child places afterwards (`dup2`, or `inherit_fd`'s `clear_cloexec`) is
/// not.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FdStrip {
    /// One past the highest number this process can hold, read before the
    /// fork ([`descriptor_bound`]).
    bound: c_int,
}

impl FdStrip {
    /// Read [`descriptor_bound`] — in the parent, before the fork.
    pub(crate) fn prepare() -> FdStrip {
        FdStrip { bound: descriptor_bound() }
    }

    /// MARK EVERY DESCRIPTOR FROM 3 UP CLOSE-ON-EXEC.
    ///
    /// The descriptors are LISTED wherever the kernel can list them (this
    /// process's own table, which nothing else changes while a forked child
    /// runs): Linux `close_range(3, ~0, CLOSE_RANGE_CLOEXEC)` (5.11+), else
    /// `/proc/self/fd` read with `getdents64` into a stack buffer; Darwin
    /// `proc_pidinfo(PROC_PIDLISTFDS)` into a stack buffer, probing only what
    /// a full listing cannot vouch for. The last resort, where a listing
    /// fails: one `fcntl` per number below the bound.
    ///
    /// ASYNC-SIGNAL-SAFE by construction: raw system calls and integer
    /// arithmetic; no allocation, no lock, no panic path.
    ///
    /// # Safety
    ///
    /// Only in a forked child before its `exec`: anywhere else it strips
    /// descriptors this process means to keep handing on.
    pub(crate) unsafe fn apply(self) {
        #[cfg(any(target_os = "linux", target_os = "android"))]
        if linux::close_range_cloexec() || linux::mark_proc_self_fd() {
            return;
        }
        #[cfg(target_vendor = "apple")]
        let rest = darwin::mark_listed(self.bound);
        #[cfg(not(target_vendor = "apple"))]
        let rest = FIRST_STRIPPED..self.bound;
        for fd in rest {
            mark_cloexec(fd);
        }
    }
}

/// ONE MORE THAN THE HIGHEST DESCRIPTOR NUMBER THIS PROCESS CAN EVER HOLD, by
/// a limit no thread of an unprivileged process can raise, so a number read
/// before a fork still bounds the child's whole table.
///
/// Darwin: `kern.maxfilesperproc` (Darwin hands out numbers up to it whenever
/// the soft `RLIMIT_NOFILE` is higher, so the soft limit bounds nothing).
/// Elsewhere: the HARD `RLIMIT_NOFILE`, which bounds every soft limit a number
/// is allocated under (though not a number opened before the limit was
/// lowered, which is why the strip lists the table first). Infinite, too
/// large, or unreadable: 2^20.
fn descriptor_bound() -> c_int {
    #[cfg(target_vendor = "apple")]
    {
        let mut value: c_int = 0;
        let mut len = size_of::<c_int>();
        // SAFETY: a NUL-terminated name and a live `c_int` with its size; the
        // call writes at most `len` bytes and sets nothing.
        let rc = unsafe {
            libc::sysctlbyname(
                c"kern.maxfilesperproc".as_ptr(),
                (&raw mut value).cast(),
                &mut len,
                crate::ptr::null_mut(),
                0,
            )
        };
        if rc == 0 && len == size_of::<c_int>() && value > 0 { value } else { FALLBACK_BOUND }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        // SAFETY: `limit` is a live `struct rlimit`, which `getrlimit` fills
        // and does not retain.
        if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) } != 0
            || limit.rlim_max == libc::RLIM_INFINITY
            || limit.rlim_max > FALLBACK_BOUND as libc::rlim_t
        {
            FALLBACK_BOUND
        } else {
            limit.rlim_max as c_int
        }
    }
}

/// Darwin's listing tier of [`FdStrip::apply`].
#[cfg(target_vendor = "apple")]
mod darwin {
    use core::ops::Range;

    use libc::c_int;

    use super::{FIRST_STRIPPED, mark_cloexec};

    /// How many descriptors one listing holds: `struct proc_fdinfo` is 8
    /// bytes, so 8 KiB of the forking thread's stack.
    const SLOTS: usize = 1024;

    /// The listing buffer's size in bytes, as `proc_pidinfo` takes it.
    const LISTING_BYTES: c_int = (SLOTS * size_of::<libc::proc_fdinfo>()) as c_int;

    /// Mark every descriptor from 3 up that this process's table lists, and
    /// return the numbers the listing does NOT vouch for, which the caller
    /// probes.
    ///
    /// What a listing vouches for depends on the kernel: XNU 8019 and later
    /// list the first `SLOTS` OPEN descriptors in ascending order, earlier
    /// kernels the open ones among the first `SLOTS` NUMBERS. So a short
    /// listing vouches for every number below `SLOTS`, and a full one for
    /// every number up to its last entry; either way the rest, up to the end
    /// of the table ([`table_end`]), is probed. In a forked child the table
    /// ends just past its highest open number (MEASURED, aterm 2026-10-01:
    /// 2 170 slots for 2 103), so for a table of fewer than `SLOTS` numbers
    /// nothing is probed. A failed listing vouches for nothing.
    pub(super) fn mark_listed(bound: c_int) -> Range<c_int> {
        let mut listed = [libc::proc_fdinfo { proc_fd: -1, proc_fdtype: 0 }; SLOTS];
        // SAFETY: `listed` is `LISTING_BYTES` writable bytes of
        // `proc_fdinfo` slots, which the kernel fills and does not retain;
        // `getpid` takes nothing.
        let got = unsafe {
            libc::proc_pidinfo(
                libc::getpid(),
                libc::PROC_PIDLISTFDS,
                0,
                listed.as_mut_ptr().cast(),
                LISTING_BYTES,
            )
        };
        // 0 is libproc's failure answer (and that of a table with nothing in it).
        let count = match usize::try_from(got) {
            Ok(bytes) => (bytes / size_of::<libc::proc_fdinfo>()).min(SLOTS),
            Err(_) => 0,
        };
        if count == 0 {
            return FIRST_STRIPPED..bound;
        }
        let mut last: c_int = -1;
        for entry in listed.iter().take(count) {
            if entry.proc_fd >= FIRST_STRIPPED {
                mark_cloexec(entry.proc_fd);
            }
            last = last.max(entry.proc_fd);
        }
        let vouched = if count < SLOTS { SLOTS as c_int } else { last.saturating_add(1) };
        vouched.max(FIRST_STRIPPED)..table_end(bound)
    }

    /// One past the highest number this process's table can hold open, at
    /// most `bound`: a listing with no buffer answers the table's size in
    /// `proc_fdinfo` slots (its allocated length plus 20), and no open number
    /// reaches past it. `bound` when it cannot answer.
    fn table_end(bound: c_int) -> c_int {
        // SAFETY: a null buffer of size 0 asks for the size alone; nothing is
        // written. `getpid` takes nothing.
        let got = unsafe {
            libc::proc_pidinfo(libc::getpid(), libc::PROC_PIDLISTFDS, 0, crate::ptr::null_mut(), 0)
        };
        match usize::try_from(got) {
            Ok(bytes) if bytes > 0 => c_int::try_from(bytes / size_of::<libc::proc_fdinfo>())
                .map_or(bound, |end| end.min(bound)),
            _ => bound,
        }
    }
}

/// The Linux strip's two listing tiers. Each answers whether it marked the
/// whole table; `false` sends [`FdStrip::apply`] on to the next.
#[cfg(any(target_os = "linux", target_os = "android"))]
mod linux {
    use libc::{c_int, c_long};

    use super::{FIRST_STRIPPED, mark_cloexec};

    /// `<linux/close_range.h>`.
    const CLOSE_RANGE_CLOEXEC: c_long = 1 << 2;

    /// `close_range(3, ~0U, CLOSE_RANGE_CLOEXEC)`: Linux 5.11+, one system
    /// call, no ceiling.
    pub(super) fn close_range_cloexec() -> bool {
        // SAFETY: three integer arguments; the kernel touches no memory of ours.
        unsafe {
            libc::syscall(
                libc::SYS_close_range,
                FIRST_STRIPPED as c_long,
                c_long::from(u32::MAX),
                CLOSE_RANGE_CLOEXEC,
            ) == 0
        }
    }

    /// Mark every number `/proc/self/fd` lists (but the listing's own
    /// directory descriptor), read with raw `getdents64` into a stack buffer,
    /// as CPython's `_posixsubprocess` does in the same place. `false` when
    /// the directory cannot be opened or read to its end.
    pub(super) fn mark_proc_self_fd() -> bool {
        /// `struct linux_dirent64`: `d_reclen` at 16, `d_name` at 19.
        const RECLEN_AT: usize = 16;
        const NAME_AT: usize = 19;
        // SAFETY: a C string literal; the result is a fresh descriptor or -1.
        let dir = unsafe {
            libc::open(
                c"/proc/self/fd".as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
            )
        };
        if dir < 0 {
            return false;
        }
        let mut buf = [0u8; 4096];
        let complete = loop {
            // SAFETY: `buf` is a live, writable buffer of the length passed.
            let n = unsafe {
                libc::syscall(
                    libc::SYS_getdents64,
                    dir as c_long,
                    buf.as_mut_ptr(),
                    buf.len() as c_long,
                )
            };
            if n <= 0 {
                break n == 0;
            }
            let end = usize::try_from(n).unwrap_or(0).min(buf.len());
            let mut at = 0;
            while at + NAME_AT < end {
                let (Some(&lo), Some(&hi)) = (buf.get(at + RECLEN_AT), buf.get(at + RECLEN_AT + 1))
                else {
                    break;
                };
                let reclen = usize::from(u16::from_ne_bytes([lo, hi]));
                if reclen == 0 {
                    break;
                }
                let mut fd: c_int = 0;
                let mut digits = 0;
                let mut i = at + NAME_AT;
                while i < end && i < at + reclen {
                    let Some(&b) = buf.get(i) else { break };
                    if b == 0 {
                        break;
                    }
                    if !b.is_ascii_digit() {
                        digits = 0;
                        break;
                    }
                    fd = fd.saturating_mul(10).saturating_add(c_int::from(b - b'0'));
                    digits += 1;
                    i += 1;
                }
                if digits > 0 && fd >= FIRST_STRIPPED && fd != dir {
                    mark_cloexec(fd);
                }
                at += reclen;
            }
        };
        // SAFETY: the directory descriptor opened above, closed once.
        unsafe {
            libc::close(dir);
        }
        complete
    }
}
