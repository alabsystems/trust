// Trust: a child retains only the credits assigned to its own command.
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::sync::Arc;

use trust_build_cpu::{Lease, LegacyFence};

use super::{Acquired, Client};

#[derive(Clone)]
pub struct ChildResources {
    leases: Vec<Arc<Lease>>,
    fence: Arc<LegacyFence>,
}

impl Client {
    pub fn child_resources(&self, extra: &[Acquired]) -> Option<ChildResources> {
        let global = self.global.as_ref()?;
        let fence = Arc::clone(global.fence()?);
        let mut leases = vec![Arc::clone(global.implicit())];
        leases.extend(extra.iter().filter_map(|credit| match credit {
            Acquired::Global(credit) => Some(Arc::clone(credit.cpu())),
            Acquired::Local(_) | Acquired::BootstrapFixed(_) => None, // Trust: private Fixed has no cooperative Lease.
        }));
        Some(ChildResources { leases, fence })
    }
}

impl ChildResources {
    pub fn output(
        &self,
        command: &mut std::process::Command,
    ) -> std::io::Result<std::process::Output> {
        self.configure(command);
        let child = command
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;
        self.wait_with_output(child)
    }

    /// Attribute these retained credits to the actual, still-owned child while
    /// it executes. Sampling its kernel birth avoids guessing descendant CPU
    /// from a parent PID or treating every reserved credit as a busy core.
    pub fn wait_with_output(
        &self,
        child: std::process::Child,
    ) -> std::io::Result<std::process::Output> {
        let parent = trust_build_cpu::process_cpu::read(std::process::id());
        let executing = owned_child_usage(child.id());
        if let Some(executing) = executing {
            for lease in &self.leases {
                // Attribution is advisory. A failed/partial diagnostic write
                // reports unknown usage; it never releases the actual lease.
                let _ = lease.report_owner(executing.owner);
            }
        }
        let result = child.wait_with_output();
        // Only a completed wait proves that this child no longer executes.
        // On uncertainty leave its identity in place and retain normal FD
        // custody; sampled parent absence is never release authority.
        if result.is_ok()
            && let Some(parent) = parent
        {
            for lease in &self.leases {
                let _ = lease.report_owner(parent.owner);
            }
        }
        result
    }

    pub fn configure(&self, command: &mut std::process::Command) {
        let resources = self.clone();
        // SAFETY: only async-signal-safe fcntl calls run after fork. The owned
        // descriptions stay alive in the closure until spawn has completed.
        unsafe {
            command.pre_exec(move || {
                let fds = resources
                    .leases
                    .iter()
                    .map(|lease| lease.as_raw_fd())
                    .chain(resources.fence.files().iter().map(|file| file.as_raw_fd()));
                for fd in fds {
                    let flags = libc::fcntl(fd, libc::F_GETFD);
                    if flags == -1
                        || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) == -1
                    {
                        return Err(std::io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
    }
}

fn owned_child_usage(pid: u32) -> Option<trust_build_cpu::process_cpu::ProcessCpu> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        let before = trust_build_cpu::process_cpu::read(pid)?;
        // SAFETY: waitid writes this initialized siginfo, examines only our
        // specified child, and WNOWAIT prevents consuming its exit status.
        let owned = unsafe {
            let mut status: libc::siginfo_t = std::mem::zeroed();
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                &mut status,
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if owned != 0 {
            return None;
        }
        let after = trust_build_cpu::process_cpu::read(pid)?;
        (before.owner == after.owner).then_some(after)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = pid;
        None
    }
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
#[path = "child/tests.rs"]
mod tests;
