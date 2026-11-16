// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! A concurrent spawn caught before its exec, for the tests that check that a
//! lock is released by its unlock and not only by its final close. The lib's
//! unit tests and the recovery_material test binary both compile this file,
//! each with its own `KernelFixture` and `kernel_fixture` in the parent module.

use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;
use std::path::Path;

use super::KernelFixture;

/// This process's descriptor table copied by fork and held until dropped: a
/// concurrent spawn caught before its exec. The copy never execs, so it holds
/// every descriptor this process had at the fork, slot files and the test
/// harness's output pipes included. It must not outlive this process: it
/// blocks reading a close-on-exec pipe whose write end this process keeps,
/// and exits once that read returns. The kernel closes the end when this
/// process ends, however it ends (a harness timeout, an abort, SIGKILL), and
/// the drop closes it first. A later copy holds the write ends of the copies
/// before it, never the reverse, and only a kernel fixture holder copies, so
/// the copies end one after another and no two wait on each other.
pub(crate) struct Unexecuted {
    child: Option<libc::pid_t>,
    parent_end: Option<io::PipeWriter>,
}

impl Unexecuted {
    pub(crate) fn copy(_fixture: &KernelFixture) -> Self {
        // Close-on-exec, so no child that execs keeps the copy alive.
        let (copy_end, parent_end) = io::pipe().expect("pipe for a descriptor copy");
        let (read, write) = (copy_end.as_raw_fd(), parent_end.as_raw_fd());
        // SAFETY: the child calls only close, read and _exit, each
        // async-signal-safe, on descriptors opened before the fork, and reads
        // errno; it touches no lock, allocation or other state copied from
        // the parent. Nothing is written to the pipe, so the read returns
        // only at end of file, once every copy of the write end has closed.
        match unsafe { libc::fork() } {
            -1 => panic!("fork: {}", io::Error::last_os_error()),
            0 => unsafe {
                libc::close(write);
                let mut byte = 0_u8;
                while libc::read(read, (&raw mut byte).cast(), 1) < 0 && interrupted() {}
                libc::_exit(0)
            },
            child => {
                drop(copy_end);
                Self { child: Some(child), parent_end: Some(parent_end) }
            }
        }
    }

    /// Close this process's end without killing the copy, as this process's
    /// death would, and hand back the child that the caller must reap.
    fn orphan(mut self) -> libc::pid_t {
        drop(self.parent_end.take());
        self.child.take().expect("only orphan or drop takes the child")
    }
}

impl Drop for Unexecuted {
    fn drop(&mut self) {
        drop(self.parent_end.take());
        if let Some(child) = self.child.take() {
            // SAFETY: child is this test's own, reaped exactly once here.
            unsafe { libc::kill(child, libc::SIGKILL) };
            reap(child);
        }
    }
}

/// Whether the last call failed with EINTR. Reads errno only.
fn interrupted() -> bool {
    io::Error::last_os_error().raw_os_error() == Some(libc::EINTR)
}

/// Wait for `child` to end, with no deadline, and return its wait status.
fn reap(child: libc::pid_t) -> i32 {
    let mut status = 0;
    loop {
        // SAFETY: child is the caller's own unreaped child; status is live.
        let reaped = unsafe { libc::waitpid(child, &raw mut status, 0) };
        if reaped == child {
            return status;
        }
        assert!(reaped < 0 && interrupted(), "waitpid: {}", io::Error::last_os_error());
    }
}

/// Whether an independent open description can lock `path` exclusively now.
pub(crate) fn relockable(path: &Path) -> bool {
    let file = File::open(path).unwrap();
    let locked = file.try_lock().is_ok();
    if locked {
        file.unlock().unwrap();
    }
    locked
}

#[test]
fn a_copy_exits_on_its_own_once_this_process_end_closes() {
    let fixture = super::kernel_fixture();
    let child = Unexecuted::copy(&fixture).orphan();
    // No kill and no deadline: only the copy's own exit ends this wait, so a
    // copy that outlives its parent hangs this test.
    let status = reap(child);
    drop(fixture);
    assert!(
        libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0,
        "the copy did not exit by itself once its parent's end closed: wait status {status}"
    );
}
