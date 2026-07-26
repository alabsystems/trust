// T6 regression (demand-free fd summaries, report addendum to
// reports/ffi-name-collision-over-refutation-2026-07-06.md): the pty/process
// management seam — dup + close + fcntl(F_GETFL/F_SETFL) + guarded killpg +
// waitpid(&mut status) through real `extern "C"` libc declarations — must
// PROVE (exit 0). Every call here is fd/pid/flag plumbing whose failure mode
// is errno (EBADF/ESRCH/ECHILD), never UB, so the summaries impose NO caller
// demands: the old fd-range demands ([0, i128::MAX]) plus the
// always-SAT WritesGlobal / backwards return-contract obligations refuted
// every such call site. waitpid's status out-pointer is `&mut i32` — valid
// by construction, and NULLABLE in the summary, so no demand fires. Flips
// RED if any fd demand, informational side-effect obligation, or
// return-contract assertion re-enters the FFI lane.
#![crate_type = "lib"]

unsafe extern "C" {
    fn dup(fd: i32) -> i32;
    fn close(fd: i32) -> i32;
    fn fcntl(fd: i32, cmd: i32, arg: i32) -> i32;
    fn killpg(pgrp: i32, sig: i32) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
}

const F_GETFL: i32 = 3;
const F_SETFL: i32 = 4;
const O_NONBLOCK: i32 = 0x0004;
const SIGTERM: i32 = 15;

/// Duplicate a pty fd and mark the duplicate non-blocking, returning the new
/// fd or -1. Checked at every step; the fds themselves carry no proof
/// obligations (EBADF is errno, not UB).
pub fn dup_nonblocking(fd: i32) -> i32 {
    // SAFETY: dup/fcntl/close take only integer fd/flag arguments; an
    // invalid fd is reported via errno (EBADF), never UB.
    unsafe {
        let dup_fd = dup(fd);
        if dup_fd < 0 {
            return -1;
        }
        let flags = fcntl(dup_fd, F_GETFL, 0);
        if flags < 0 {
            let _ = close(dup_fd);
            return -1;
        }
        if fcntl(dup_fd, F_SETFL, flags | O_NONBLOCK) < 0 {
            let _ = close(dup_fd);
            return -1;
        }
        dup_fd
    }
}

/// Terminate a child's process group (guarded: only a real pgrp id — 0/-1
/// broadcast forms are refused) and reap the child, returning the raw wait
/// status or -1.
pub fn shutdown_child(pid: i32, pgrp: i32) -> i32 {
    // SAFETY: killpg takes only integer pgrp/signal arguments (ESRCH/EPERM
    // are errno); waitpid writes through `status`, which is a `&mut i32` —
    // non-null and writable by construction (NULL would also be legal per
    // the summary's nullable status contract).
    unsafe {
        if pgrp > 0 {
            let _ = killpg(pgrp, SIGTERM);
        }
        let mut status: i32 = 0;
        if waitpid(pid, &mut status, 0) < 0 {
            return -1;
        }
        status
    }
}
