//! Shared original-child observation and signal-before-reap implementation.
//! Extracted unchanged from Cargo's streaming executor so native harnesses use
//! the same Darwin zombie/EPERM handling and cancellation order. This grants
//! no scheduling, image or detached-descendant authority.

use std::io;
#[cfg(target_os = "macos")]
use std::process::Command;
use std::time::Duration;

pub struct OwnedGroupExit {
    pub exited: bool,
    pub error: Option<io::Error>,
}

/// Trust: observe only the original child. WNOWAIT leaves its PID allocated
/// until the owning caller has decided whether group cleanup is required.
#[cfg(unix)]
/// # Safety
/// `pid` is the caller's exclusively owned, unreaped direct child. No other
/// waiter or SIGCHLD handler may reap it throughout this observation.
pub unsafe fn unreaped_child_exit(pid: libc::pid_t) -> io::Result<bool> {
    // SAFETY: initialized output and a specific original child PID. No status
    // is consumed, so the caller retains its original Child wait ownership.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            pid as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    #[cfg(target_os = "macos")]
    return Ok(info.si_pid == pid);
    #[cfg(target_os = "linux")]
    return Ok(unsafe { info.si_pid() } == pid);
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    // POSIX waitid(P_PID) can report only this selected child. No event leaves
    // the initialized si_signo zero; a reported exit sets it to SIGCHLD.
    Ok(info.si_signo == libc::SIGCHLD)
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
/// Observe and stop the original group before its caller performs the sole
/// reap. `cancelled` must be bounded and must not reap or replace the child.
/// # Safety
/// `pid` is an exclusively owned, unreaped direct child, originally spawned
/// with its own process group whose ID equals `pid`. No competing reaper exists.
pub unsafe fn observe_owned_group_exit(
    pid: libc::pid_t,
    mut cancelled: impl FnMut() -> bool,
) -> OwnedGroupExit {
    let mut killed = false;
    loop {
        // Trust: a hosted native launcher can poll its already-authenticated
        // root control without replacing this observer's wait/group custody.
        let is_cancelled = cancelled();
        let exited = match unsafe { unreaped_child_exit(pid) } {
            Ok(exited) => exited,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => {
                return OwnedGroupExit { exited: false, error: Some(error) };
            }
        };
        if exited {
            return OwnedGroupExit { exited: true, error: unsafe { stop_owned_group(pid) }.err() };
        }
        if !killed && is_cancelled {
            if let Err(error) = unsafe { stop_owned_group(pid) } {
                return OwnedGroupExit { exited: false, error: Some(error) };
            }
            // A program may have moved its own group. Its unreaped PID is
            // still owned and must terminate too before the observer can join.
            if unsafe { libc::kill(pid, libc::SIGKILL) } != 0 {
                let error = io::Error::last_os_error();
                if error.raw_os_error() != Some(libc::ESRCH) {
                    // Darwin can reject signalling a newly exited zombie.
                    // Re-observe without reaping before deciding this is loss
                    // of cleanup authority; never guess from EPERM alone.
                    let mut after: libc::siginfo_t = unsafe { std::mem::zeroed() };
                    let checked = unsafe {
                        libc::waitid(
                            libc::P_PID,
                            pid as libc::id_t,
                            &mut after,
                            libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
                        )
                    };
                    #[cfg(target_os = "macos")]
                    let now_exited = checked == 0 && after.si_pid == pid;
                    #[cfg(target_os = "linux")]
                    let now_exited = checked == 0 && unsafe { after.si_pid() } == pid;
                    if now_exited {
                        continue;
                    }
                    return OwnedGroupExit { exited: false, error: Some(error) };
                }
            }
            killed = true;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[cfg(unix)]
/// # Safety
/// The caller still exclusively owns the original unreaped group leader `pid`.
/// A saved PID or a previously reaped child never satisfies this requirement.
pub unsafe fn stop_owned_group(pid: libc::pid_t) -> io::Result<()> {
    // SAFETY: the observer has not reaped the owned group leader.
    if unsafe { libc::kill(-pid, libc::SIGKILL) } == 0 {
        return Ok(());
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::ESRCH) {
        return Ok(());
    }
    #[cfg(target_os = "macos")]
    if error.raw_os_error() == Some(libc::EPERM) {
        // Darwin sometimes reports EPERM for a group containing only zombies.
        // Accept only an actual successful, nonempty all-zombie census.
        let census = Command::new("/bin/ps").args(["-axo", "pgid=,stat="]).output()?;
        if census.status.success() {
            let text = String::from_utf8(census.stdout).map_err(io::Error::other)?;
            let states = text
                .lines()
                .filter_map(|line| {
                    let mut fields = line.split_whitespace();
                    (fields.next()?.parse::<libc::pid_t>().ok()? == pid)
                        .then(|| fields.next())
                        .flatten()
                })
                .collect::<Vec<_>>();
            if !states.is_empty() && states.iter().all(|state| state.starts_with('Z')) {
                return Ok(());
            }
        }
    }
    Err(error)
}
