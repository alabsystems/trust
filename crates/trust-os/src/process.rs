//! Deadline-bounded child processes that cannot outlive their deadline.
//!
//! Every verifier backend that shells out to a solver needs the same three
//! things, and getting any of them wrong leaks a runaway solver into the
//! machine: put the child somewhere killable, poll until it exits or the
//! deadline passes, and on the deadline kill *everything it started*.
//!
//! The last part is the one that is easy to get wrong. `Child::kill` signals
//! the direct child only. A solver that forked — or a `cargo` that spawned
//! `rustc` — leaves its descendants running, and because those descendants
//! still hold the inherited stdout/stderr write ends, the caller's own reader
//! threads then block forever on a pipe nobody will close. The timeout becomes
//! a hang. Spawning into a fresh process group and signalling the group is what
//! makes the deadline real, so both halves live here together: a caller cannot
//! pick up the wait without also getting the group.

use std::io;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

/// Poll interval while waiting for a bounded child.
///
/// Short enough that the kill lands promptly after the deadline, long enough
/// that a multi-second solve does not burn a core spinning on `try_wait`.
const POLL_INTERVAL: Duration = Duration::from_millis(10);

/// Outcome of [`wait_bounded`].
#[derive(Debug)]
pub struct BoundedWait {
    /// Exit status, reaped in both the completed and killed cases so no
    /// zombie survives the call.
    pub status: std::process::ExitStatus,
    /// Whether the deadline — not the child — ended the run.
    pub timed_out: bool,
}

/// Spawn `command` as the leader of a fresh process group.
///
/// The group is what makes [`kill_process_group`] able to reach descendants.
/// On platforms without process groups this is an ordinary spawn, and the
/// timeout degrades to killing the direct child only.
pub fn spawn_in_own_process_group(command: &mut Command) -> io::Result<Child> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        // `process_group` is the safe std spelling of `setpgid(0, 0)` in the
        // pre-exec window; no hand-rolled `pre_exec` closure is needed, and it
        // is honored by `posix_spawn` rather than forcing the fork path.
        command.process_group(0);
    }
    command.spawn()
}

/// SIGKILL the child's whole process group, falling back to the direct child.
///
/// The fallback matters: if the child already exited, its group may be gone
/// (`ESRCH`) while a descendant still runs under a reparented group we can no
/// longer name — killing the child directly is then the only remaining lever,
/// and reporting success on `ESRCH` keeps "already dead" from reading as a
/// cleanup failure.
pub fn kill_process_group(child: &mut Child) -> io::Result<()> {
    #[cfg(unix)]
    {
        let pid = i32::try_from(child.id()).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("child pid {} does not fit in platform pid_t", child.id()),
            )
        })?;
        // SAFETY: `kill` is async-signal-safe and takes no pointers; a negative
        // pid addresses the process group, which this child leads because it
        // was spawned through `spawn_in_own_process_group`.
        let result = unsafe { libc::kill(-pid, libc::SIGKILL) };
        if result == 0 {
            return Ok(());
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::ESRCH) {
            return Ok(());
        }
        child.kill().map_err(|child_error| {
            io::Error::new(
                child_error.kind(),
                format!(
                    "failed to kill process group: {error}; failed to kill child: {child_error}"
                ),
            )
        })
    }
    #[cfg(not(unix))]
    {
        child.kill()
    }
}

/// Wait for `child` for at most `timeout`, killing its process group if the
/// deadline passes first.
///
/// Returns only after the child has been reaped, so the caller may join reader
/// threads immediately: once the group is gone, every inherited pipe write end
/// is closed and a blocked `read_to_end` returns.
pub fn wait_bounded(child: &mut Child, timeout: Duration) -> io::Result<BoundedWait> {
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(BoundedWait { status, timed_out: false });
        }
        let elapsed = start.elapsed();
        if elapsed >= timeout {
            kill_process_group(child)?;
            // A child that raced us to exit between `try_wait` and the kill is
            // not a timeout: report what actually happened rather than
            // manufacturing one.
            let raced_to_exit = child.try_wait()?;
            let status = match raced_to_exit {
                Some(status) => status,
                None => child.wait()?,
            };
            return Ok(BoundedWait { status, timed_out: raced_to_exit.is_none() });
        }
        std::thread::sleep(POLL_INTERVAL.min(timeout - elapsed));
    }
}

#[cfg(test)]
mod tests {
    use std::process::Stdio;

    use super::*;

    #[cfg(unix)]
    #[test]
    fn a_child_that_finishes_first_is_not_reported_as_timed_out() {
        let mut command = Command::new("true");
        command.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
        let mut child = spawn_in_own_process_group(&mut command).expect("spawn");
        let wait = wait_bounded(&mut child, Duration::from_secs(30)).expect("wait");
        assert!(!wait.timed_out);
        assert!(wait.status.success());
    }

    #[cfg(unix)]
    #[test]
    fn the_deadline_reaches_a_grandchild_holding_the_pipe() {
        // The regression this module exists for: a shell that backgrounds a
        // long sleep and exits leaves the sleep holding the inherited stdout.
        // Killing only the direct child would leave `read_to_end` blocked on
        // that pipe long past the deadline; killing the group unblocks it.
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg("sleep 600 & sleep 600")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());
        let mut child = spawn_in_own_process_group(&mut command).expect("spawn");
        let mut stdout = child.stdout.take().expect("piped stdout");
        let reader = std::thread::spawn(move || {
            use std::io::Read as _;
            let mut buffer = Vec::new();
            stdout.read_to_end(&mut buffer).map(|_| buffer)
        });

        let start = Instant::now();
        let wait = wait_bounded(&mut child, Duration::from_millis(200)).expect("wait");
        assert!(wait.timed_out);
        // The reader must complete promptly; before the group kill it would
        // stay blocked on the backgrounded sleep's copy of the write end.
        let drained = reader.join().expect("reader thread").expect("drain");
        assert!(drained.is_empty());
        assert!(start.elapsed() < Duration::from_secs(30), "group kill did not release the pipe");
    }
}
