//! Trust: lifecycle ownership for platform-authenticated isolated children.
//!
//! Image authentication remains with the launcher. This module only shares the
//! streaming executor's signal epoch, cancellation, nonreaping observation and
//! process-group cleanup. It never launches a program by pathname.

use std::io;
use std::process::{Child, ExitStatus};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use super::{
    StreamingProcessScope, StreamingSignals, ensure_streaming_wait_ownership,
    observe_streaming_child_exit_with_poll, pending_streaming_signal,
};

/// A signal/cancellation epoch established before a platform child is spawned.
/// Preparation neither creates a child nor supplies executable-image authority.
pub struct PreparedIsolatedChild {
    signals: StreamingSignals,
    execution_cancel: Arc<AtomicBool>,
}

impl PreparedIsolatedChild {
    /// Refuse incompatible SIGCHLD handling or pending cancellation before the
    /// launcher creates a child. Keep a signal lease through ownership transfer.
    pub fn prepare(scope: &StreamingProcessScope) -> io::Result<Self> {
        Self::prepare_with_cancel(Some(Arc::clone(&scope.cancel)))
    }

    pub(super) fn prepare_with_cancel(cancel: Option<Arc<AtomicBool>>) -> io::Result<Self> {
        ensure_streaming_wait_ownership()?;
        let prepared = Self {
            signals: StreamingSignals::install(true)?.expect("enabled isolated-child signals"),
            execution_cancel: cancel.unwrap_or_else(|| Arc::new(AtomicBool::new(false))),
        };
        prepared.check_cancelled()?;
        Ok(prepared)
    }

    /// Recheck immediately before launch; preparation cannot reserve immunity
    /// from cancellation which arrived while the image was being authenticated.
    pub fn check_cancelled(&self) -> io::Result<()> {
        check_cancelled(&self.execution_cancel)
    }

    /// Transfer ownership of an isolated direct child returned by a native
    /// platform spawn API. No further caller may wait for or reap that child.
    ///
    /// # Safety
    /// `pid` must be positive and name the caller's own direct, unreaped child.
    /// The launcher must have created a new process group with PGID equal to
    /// `pid` at spawn time. No independent waiter or reaper may own it.
    pub unsafe fn adopt(self, pid: libc::pid_t) -> OwnedIsolatedChild {
        OwnedIsolatedChild::new(self, Reaper::Native(pid))
    }

    /// Transfer an isolated `Command::spawn` child without reconstructing a
    /// standard-library child handle from a reusable numeric PID.
    ///
    /// # Safety
    /// The command must have created a new process group with PGID equal to its
    /// child PID at spawn time. No independent waiter or reaper may own it.
    pub unsafe fn adopt_std(self, child: Child) -> OwnedIsolatedChild {
        OwnedIsolatedChild::new(self, Reaper::Standard(child))
    }
}

enum Reaper {
    Standard(Child),
    Native(libc::pid_t),
}

impl Reaper {
    fn pid(&self) -> libc::pid_t {
        match self {
            Self::Standard(child) => child.id() as libc::pid_t,
            Self::Native(pid) => *pid,
        }
    }

    fn wait(&mut self) -> io::Result<ExitStatus> {
        match self {
            Self::Standard(child) => child.wait(),
            Self::Native(pid) => {
                use std::os::unix::process::ExitStatusExt;
                loop {
                    let mut status = 0;
                    // SAFETY: this guard alone owns the direct child and the
                    // common observer confirmed exit without reaping it.
                    let waited = unsafe { libc::waitpid(*pid, &mut status, 0) };
                    if waited == *pid {
                        return Ok(ExitStatus::from_raw(status));
                    }
                    let error = io::Error::last_os_error();
                    if waited < 0 && error.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(error);
                }
            }
        }
    }
}

/// Sole owner of an already-spawned isolated direct child and its cancellation
/// epoch. Drop stops its process group and reaps only after successful WNOWAIT
/// observation. Loss of wait custody never falls back to signalling a PID.
pub struct OwnedIsolatedChild {
    prepared: PreparedIsolatedChild,
    reaper: Reaper,
    finished: bool,
}

impl OwnedIsolatedChild {
    fn new(prepared: PreparedIsolatedChild, reaper: Reaper) -> Self {
        Self {
            prepared,
            reaper,
            finished: false,
        }
    }

    /// Check before resuming a suspended authenticated image. A refusal leaves
    /// this guard responsible for stopping and reaping the suspended child.
    pub fn check_cancelled(&self) -> io::Result<()> {
        self.prepared.check_cancelled()
    }

    /// Wait for exit, stop inherited-group descendants while the leader is
    /// unreaped, then perform the sole reap. External cancellation is reported
    /// even if the child raced it and exited successfully.
    pub fn wait(self) -> io::Result<ExitStatus> {
        self.wait_with_cancel(|| false)
    }

    /// Poll an existing authenticated root-control channel while waiting. A
    /// cancellation becomes sticky in this execution epoch, even if the child
    /// already exited successfully when the next observation runs. Polling
    /// must be bounded and nonblocking; this API creates no control authority.
    pub fn wait_with_cancel(
        mut self,
        mut poll_cancel: impl FnMut() -> bool,
    ) -> io::Result<ExitStatus> {
        self.finish_with_poll(false, &mut poll_cancel)
    }

    /// Stop and reap after authentication/setup failure. Deliberate cleanup is
    /// not itself an interruption, but a pending scope/signal cancellation is.
    pub fn cancel_and_wait(mut self) -> io::Result<ExitStatus> {
        self.finish(true)
    }

    fn finish(&mut self, cancel: bool) -> io::Result<ExitStatus> {
        self.finish_with_poll(cancel, &mut || false)
    }

    fn finish_with_poll(
        &mut self,
        cancel: bool,
        poll_cancel: &mut dyn FnMut() -> bool,
    ) -> io::Result<ExitStatus> {
        let local_cancel = AtomicBool::new(cancel);
        let observed = observe_streaming_child_exit_with_poll(
            self.reaper.pid(),
            &local_cancel,
            Some(&self.prepared.execution_cancel),
            || {
                let cancelled = poll_cancel();
                if cancelled {
                    self.prepared
                        .execution_cancel
                        .store(true, Ordering::Release);
                }
                cancelled
            },
        );
        // The observer owns the last process-group signal. Neither this guard's
        // Drop nor a caller can signal this identity after its sole reap.
        self.finished = true;
        let result = if observed.exited {
            let waited = self.reaper.wait();
            match observed.error {
                Some(error) => waited.and_then(|_| Err(error)),
                None => waited,
            }
        } else {
            Err(observed
                .error
                .unwrap_or_else(|| io::Error::other("isolated child custody was lost")))
        };
        let cancelled = self.prepared.check_cancelled();
        let restored = self.prepared.signals.restore();
        // Lifecycle errors retain precedence: interruption must not hide lost
        // custody or failed cleanup. A clean successful wait is still never a
        // successful execution when its allocation was cancelled.
        result.and_then(|status| {
            cancelled?;
            restored?;
            Ok(status)
        })
    }
}

impl Drop for OwnedIsolatedChild {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.finish(true);
        }
    }
}

fn check_cancelled(cancel: &AtomicBool) -> io::Result<()> {
    if pending_streaming_signal() != 0 || cancel.load(Ordering::Acquire) {
        return Err(io::Error::new(
            io::ErrorKind::Interrupted,
            "isolated child execution cancelled",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
