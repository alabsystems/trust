//! One child of a gate verb: run to its end or to a bound, with no stdin and
//! its stdout and stderr together in a log.
//!
//! `targo trust gate corpus-delta` runs a compiler this way and `targo trust
//! land --check` a row's command. The child is owned (`process_lifecycle`): a
//! signal to the verb stops it, and what is left of its process group when its
//! leader exits is stopped before the leader is reaped.

use std::fs::File;
use std::path::Path;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use crate::bounded_process;
use crate::process_lifecycle::{self, StopCause};

/// How one child ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ChildExit {
    Exited(i32),
    /// Ended by this signal (no exit status).
    Signalled(i32),
    /// Still running at its bound, and stopped.
    PastBound,
    /// Could not be started, or waited for.
    Failed(String),
}

/// Run `command` to its end or to `bound`, with no stdin and its stdout and
/// stderr in `log`. `what` names the child in a failure ("the compiler").
pub(crate) fn run_logged(
    command: &mut Command,
    log: &Path,
    bound: Duration,
    what: &str,
) -> ChildExit {
    let streams = File::create(log).and_then(|out| Ok((out.try_clone()?, out)));
    let (stdout, stderr) = match streams {
        Ok(streams) => streams,
        Err(error) => {
            return ChildExit::Failed(format!("cannot create {}: {error}", log.display()));
        }
    };
    command.stdin(Stdio::null()).stdout(stdout).stderr(stderr);
    let (mut child, ownership) = match process_lifecycle::spawn_owned(command) {
        Ok(owned) => owned,
        Err(error) => {
            return ChildExit::Failed(format!(
                "cannot start {}: {error}",
                Path::new(command.get_program()).display()
            ));
        }
    };
    let exit = wait_within(&mut child, bound, what);
    drop(ownership);
    exit
}

/// `stability::legs::wait_then_sweep` with a bound: wait for the leader
/// without reaping it, stop what is left of its group while the unreaped
/// leader still reserves the group's id, then reap it. A leader still running
/// at `bound` is stopped with its group and has no exit.
fn wait_within(child: &mut Child, bound: Duration, what: &str) -> ChildExit {
    const LONGEST_POLL: Duration = Duration::from_millis(50);
    // A bound past the end of the clock is a time that never comes: there is
    // no deadline, and the caller's number is never an overflow.
    let deadline = Instant::now().checked_add(bound);
    let mut poll = Duration::from_millis(1);
    loop {
        match bounded_process::exited_without_reaping(child) {
            Ok(true) => break,
            Ok(false) if deadline.is_none_or(|deadline| Instant::now() < deadline) => {
                std::thread::sleep(poll);
                poll = (poll * 2).min(LONGEST_POLL);
            }
            Ok(false) => {
                let _ = process_lifecycle::stop_child(child, StopCause::Bound);
                let _ = child.wait();
                return ChildExit::PastBound;
            }
            Err(error) => {
                let _ = process_lifecycle::stop_child(child, StopCause::Error);
                let _ = child.wait();
                return ChildExit::Failed(format!("cannot wait for {what}: {error}"));
            }
        }
    }
    // A signal that stopped the verb may be why the child exited: its exit is
    // no verdict, and the stop owns the run's exit.
    process_lifecycle::signals::hold_if_interrupted();
    #[cfg(unix)]
    let _ = process_lifecycle::stop_tree(child.id(), StopCause::LeaderExited);
    match child.wait() {
        Ok(status) => exit_of(status, what),
        Err(error) => ChildExit::Failed(format!("cannot wait for {what}: {error}")),
    }
}

fn exit_of(status: ExitStatus, what: &str) -> ChildExit {
    if let Some(code) = status.code() {
        return ChildExit::Exited(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;
        if let Some(signal) = status.signal() {
            return ChildExit::Signalled(signal);
        }
    }
    ChildExit::Failed(format!("{what} ended with neither a status nor a signal: {status}"))
}
