//! Exclusive legacy or cgroup-at-birth custody. Neither kind is release authority.
use std::os::fd::{AsRawFd, OwnedFd};

use trust_process_isolation::Budget;

use super::child::Child;
use super::tree::Tree;
use super::{checked, contract};
use crate::{Error, system};

#[derive(Debug)]
pub(super) enum Custody {
    Legacy(Child),
    Tree { pid: libc::pid_t, pidfd: OwnedFd, reaped: bool, tree: Tree, budget: Budget },
}
impl Custody {
    /// Move the sole direct-child guard into the native pair monitor. A tree
    /// guard cannot be downgraded; an erroneous caller retains normal cleanup.
    pub(crate) fn into_legacy(self) -> Result<Child, Error> {
        if !matches!(self, Self::Legacy(_)) {
            return Err(contract("native direct-child custody"));
        }
        let held = std::mem::ManuallyDrop::new(self);
        let Self::Legacy(child) = &*held else { unreachable!() };
        // SAFETY: the checked Legacy variant owns only this Child. Disable the
        // wrapper's Drop and move the guard exactly once; no alias is returned.
        Ok(unsafe { std::ptr::read(child) })
    }
    pub(super) fn pid(&self) -> libc::pid_t {
        match self {
            Self::Legacy(child) => child.pid,
            Self::Tree { pid, .. } => *pid,
        }
    }
    pub(super) fn used_pidfd(&self) -> bool {
        match self {
            Self::Legacy(child) => child.pidfd.is_some(),
            Self::Tree { .. } => true,
        }
    }
    pub(super) fn reaped(&self) -> bool {
        match self {
            Self::Legacy(child) => child.reaped,
            Self::Tree { reaped, .. } => *reaped,
        }
    }
    pub(super) fn exited(&mut self) -> Result<bool, Error> {
        match self {
            Self::Legacy(child) => child.exited(),
            Self::Tree { pid, pidfd, budget, tree, .. } => {
                tree.check_active()?;
                checked(budget)?;
                budget
                    .charge(trust_process_isolation::Charge { work: 128, ..Default::default() })
                    .map_err(Error::Budget)?;
                let result = observe(pidfd, *pid, libc::WNOHANG | libc::WNOWAIT, budget)?;
                checked(budget)?;
                Ok(result.is_some())
            }
        }
    }
    pub(super) fn stop_and_reap(&mut self) -> Result<i32, Error> {
        match self {
            Self::Legacy(child) => child.stop_and_reap(),
            Self::Tree { pid, pidfd, reaped, tree, budget } => {
                if *reaped {
                    return Err(contract("tree leader already reaped"));
                }
                tree.stop()?;
                loop {
                    tree.cleanup_poll()?;
                    if observe(pidfd, *pid, libc::WNOHANG | libc::WNOWAIT, budget)?.is_some() {
                        break;
                    }
                    tree.pause();
                }
                // Reap only the held terminal child, without an opaque blocking
                // wait or numerical-PID reacquisition. The earlier status was
                // WNOWAIT and keeps this original identity reserved.
                let status = observe(pidfd, *pid, libc::WNOHANG, budget)?
                    .ok_or_else(|| contract("tree terminal status absent"))?;
                *reaped = true;
                // Whole recursive cgroup absence is a separate observation
                // from direct-child wait. No new deadline or cleanup grace.
                tree.finish()?;
                Ok(status)
            }
        }
    }
}
impl Drop for Custody {
    fn drop(&mut self) {
        if let Self::Tree { budget, reaped, .. } = self {
            if !*reaped {
                budget.cancel();
                // Callback unwind/partial setup uses the same prepaid bounded
                // original-endpoint retirement, never a renewed cleanup grace.
                let _ = self.stop_and_reap();
            }
        }
        if let Self::Tree { pid, pidfd, reaped, tree, budget } = self {
            if !*reaped {
                let _ = tree.stop();
                // SAFETY: exclusive birth pidfd identifies the same leader;
                // this final request has no numerical PID/path fallback.
                unsafe {
                    libc::syscall(
                        libc::SYS_pidfd_send_signal,
                        pidfd.as_raw_fd(),
                        libc::SIGKILL,
                        std::ptr::null::<libc::siginfo_t>(),
                        0u32,
                    );
                }
                if matches!(observe(pidfd, *pid, libc::WNOHANG, budget), Ok(Some(_))) {
                    *reaped = true;
                }
            }
            // Incomplete cleanup never creates a receipt. Tree::drop requests
            // recursive kill again through its original FD. The caller's hard
            // outside owner remains mandatory after an expired endpoint or an
            // opaque/failed kernel operation; dropping this guard is no seal.
        }
    }
}

fn observe(
    pidfd: &OwnedFd,
    expected_pid: libc::pid_t,
    flags: libc::c_int,
    budget: &Budget,
) -> Result<Option<i32>, Error> {
    if std::time::Instant::now() >= budget.deadline() {
        budget.refuse(trust_process_isolation::Error::Deadline);
        return Err(contract("original leader wait deadline"));
    }
    let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
    // SAFETY: the exclusively owned birth pidfd remains open. waitid writes
    // one initialized siginfo_t and can reap only that same original child.
    // Every call is nonblocking; no opaque wait or hidden EINTR retry exists.
    let rc = unsafe {
        libc::waitid(
            libc::P_PIDFD,
            pidfd.as_raw_fd() as libc::id_t,
            info.as_mut_ptr(),
            libc::WEXITED | flags,
        )
    };
    if rc != 0 {
        return Err(system("tree leader waitid"));
    }
    // SAFETY: successful waitid initialized the complete output; zero pid is
    // the documented WNOHANG result, never a success exit synthesized on ECHILD.
    let info = unsafe { info.assume_init() };
    // SAFETY: successful WEXITED waitid selects the initialized child-status
    // variant of this siginfo_t; si_pid reads that variant's process identity.
    let pid = unsafe { info.si_pid() };
    if pid == 0 && flags & libc::WNOHANG != 0 {
        return Ok(None);
    }
    if pid != expected_pid {
        return Err(contract("tree terminal identity"));
    }
    // SAFETY: WEXITED selects the child-status variant of siginfo_t.
    let status = unsafe { info.si_status() };
    Ok(Some(raw_status(info.si_code, status)?))
}
fn raw_status(code: libc::c_int, status: libc::c_int) -> Result<i32, Error> {
    match (code, status) {
        (libc::CLD_EXITED, 0..=255) => Ok(status << 8),
        (libc::CLD_KILLED, 1..=64) => Ok(status),
        (libc::CLD_DUMPED, 1..=64) => Ok(status | 0x80),
        _ => Err(contract("tree terminal status grammar")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn authentic_terminal_status_preserves_normal_signal_and_core_distinction() {
        assert_eq!(raw_status(libc::CLD_EXITED, 0).unwrap(), 0);
        assert_eq!(libc::WEXITSTATUS(raw_status(libc::CLD_EXITED, 127).unwrap()), 127);
        assert_eq!(
            libc::WTERMSIG(raw_status(libc::CLD_KILLED, libc::SIGKILL).unwrap()),
            libc::SIGKILL
        );
        assert!(libc::WCOREDUMP(raw_status(libc::CLD_DUMPED, libc::SIGABRT).unwrap()));
        for (code, status) in [
            (libc::CLD_STOPPED, 0),
            (libc::CLD_EXITED, 256),
            (libc::CLD_KILLED, 0),
            (libc::CLD_KILLED, 65),
        ] {
            assert!(raw_status(code, status).is_err());
        }
    }
}
