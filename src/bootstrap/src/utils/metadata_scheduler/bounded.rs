//! Bounded observation of the constructor's known, no-fork compiler query.
//! The caller retains the original scheduler mutex throughout this function.
//! This does not authorize an arbitrary executable or escaped descendants.

use std::io::{self, Read as _, Seek as _};
use std::os::unix::process::CommandExt as _;
use std::process::{Child, Command, Output};
use std::time::Instant;

use trust_resource_provenance::process::{
    observe_owned_group_exit, stop_owned_group, unreaped_child_exit,
};

struct Owned(Option<Child>);

fn require_wait_ownership(action: &libc::sigaction) -> io::Result<()> {
    if action.sa_sigaction != libc::SIG_DFL || action.sa_flags & libc::SA_NOCLDWAIT != 0 {
        return Err(io::Error::other("bounded query requires exclusive child wait ownership"));
    }
    Ok(())
}

impl Drop for Owned {
    fn drop(&mut self) {
        let Some(child) = self.0.as_mut() else { return };
        let pid = child.id() as libc::pid_t;
        // SAFETY: exclusively owned direct child, spawned with group ID=PID;
        // no wait/try_wait has consumed its status and SIGCHLD is default.
        let cleanup = unsafe {
            unreaped_child_exit(pid)
                .and_then(|_| stop_owned_group(pid))
                .and_then(|_| {
                    child.kill().or_else(|error| {
                        if error.raw_os_error() == Some(libc::ESRCH) { Ok(()) } else { Err(error) }
                    })
                })
                .and_then(|_| child.wait().map(|_| ()))
        };
        if cleanup.is_err() {
            // Never release the implicit borrower on unresolved child custody.
            std::process::abort();
        }
    }
}

pub(super) fn run(command: &mut Command, deadline: Instant, bytes: u64) -> io::Result<Output> {
    if bytes == 0 || bytes > 64 * 1024 || Instant::now() >= deadline {
        return Err(io::Error::other("invalid bounded compiler query limits"));
    }
    // Refuse automatic/competing SIGCHLD reaping before creating the child.
    // SAFETY: initialized output; a null new-action pointer only observes.
    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
    if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut action) } != 0 {
        return Err(io::Error::last_os_error());
    }
    require_wait_ownership(&action)?;
    command.process_group(0);
    let mut out = super::capture(command, true, true)?
        .ok_or_else(|| io::Error::other("compiler stdout capture absent"))?;
    let mut err = super::capture(command, true, false)?
        .ok_or_else(|| io::Error::other("compiler stderr capture absent"))?;
    let mut owned = Owned(Some(command.spawn()?));
    let child =
        owned.0.as_mut().ok_or_else(|| io::Error::other("compiler child custody absent"))?;
    drop(child.stdin.take());
    let mut refusal = None;
    // SAFETY: original direct Child remains exclusively owned and unreaped;
    // process_group(0) created its group, and callback never waits or signals.
    let observed = unsafe {
        observe_owned_group_exit(child.id() as libc::pid_t, || {
            if refusal.is_none() {
                refusal = if Instant::now() >= deadline {
                    Some(io::Error::new(io::ErrorKind::TimedOut, "compiler discovery deadline"))
                } else {
                    match out.metadata().and_then(|left| {
                        err.metadata().map(|right| left.len() > bytes || right.len() > bytes)
                    }) {
                        Ok(false) => None,
                        Ok(true) => Some(io::Error::other("compiler discovery output bound")),
                        Err(error) => Some(error),
                    }
                };
            }
            refusal.is_some()
        })
    };
    if let Some(error) = observed.error {
        return Err(error);
    }
    if !observed.exited {
        return Err(io::Error::other("compiler discovery custody unresolved"));
    }
    let status = child.wait()?;
    owned.0 = None; // sole reap completed; no numeric group control after here
    if let Some(error) = refusal {
        return Err(error);
    }
    let read = |file: &mut std::fs::File| -> io::Result<Vec<u8>> {
        file.rewind()?;
        let mut result = Vec::new();
        file.take(bytes + 1).read_to_end(&mut result)?;
        if result.len() as u64 > bytes {
            return Err(io::Error::other("compiler discovery output bound"));
        }
        Ok(result)
    };
    Ok(Output { status, stdout: read(&mut out)?, stderr: read(&mut err)? })
}

#[cfg(test)]
mod tests;
