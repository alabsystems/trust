//! Actual original child/group ownership at the deadline/exit boundary.
#![cfg(any(target_os = "linux", target_os = "macos"))]

use super::super::{wait_for_streaming_child, wait_for_streaming_child_with_exit_check};
use super::CHILD_EXIT_TEST_LOCK;
use std::io::{self, Read as _, Write as _};
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

const ROLE: &str = "CARGO_TEST_DEADLINE_CUSTODY_CHILD";

#[test]
fn controlled_child() {
    if std::env::var_os(ROLE).is_none() {
        return;
    }
    io::stdin().read_exact(&mut [0]).unwrap();
    std::process::exit(0);
}

struct Running(Child);
impl Running {
    fn spawn(group: Option<u32>) -> Self {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "--exact",
                "process_builder::tests::deadline_custody::controlled_child",
                "--nocapture",
                "--quiet",
            ])
            .env(ROLE, "controlled")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .process_group(group.map_or(0, |pid| i32::try_from(pid).unwrap()));
        let running = Self(command.spawn().unwrap());
        let pid = libc::pid_t::try_from(running.0.id()).unwrap();
        // SAFETY: this is our newly spawned, unreaped child, blocked on its
        // owned stdin until release. This reads its actual group membership.
        let actual_group = unsafe { libc::getpgid(pid) };
        assert_eq!(
            actual_group,
            group.map_or(pid, |value| value as libc::pid_t)
        );
        running
    }

    fn release(&mut self) {
        self.0.stdin.take().unwrap().write_all(b"g").unwrap();
    }

    fn wait(&mut self) -> ExitStatus {
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(status) = self.0.try_wait().unwrap() {
                return status;
            }
            if Instant::now() >= until {
                self.0.stdin.take();
                let _ = self.0.kill();
                let status = self.0.wait();
                panic!("owned test child did not terminate: {status:?}");
            }
            thread::sleep(Duration::from_millis(1));
        }
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        // Both processes are direct children. Cleanup never signals a cached
        // reap or uses the already-finished leader's numeric group identifier.
        self.0.stdin.take();
        if matches!(self.0.try_wait(), Ok(None)) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
}

fn unreaped_exit(pid: u32) -> io::Result<bool> {
    // SAFETY: zero initializes the output; the wait below selects only an
    // originally owned child and deliberately leaves its status unreaped.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    // SAFETY: output is valid and WNOWAIT retains the original child owner.
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
    let actual = info.si_pid;
    #[cfg(target_os = "linux")]
    let actual = unsafe { info.si_pid() };
    Ok(actual == pid as libc::pid_t)
}

fn await_unreaped_exit(pid: u32) {
    let until = Instant::now() + Duration::from_secs(5);
    while !unreaped_exit(pid).unwrap() {
        assert!(Instant::now() < until, "original leader did not exit");
        thread::sleep(Duration::from_millis(1));
    }
}

#[test]
fn deadline_crossing_keeps_original_leader_unreaped_through_group_cleanup() {
    let _serial = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut leader = Running::spawn(None);
    let mut peer = Running::spawn(Some(leader.0.id()));
    let leader_pid = leader.0.id();
    let peer_pid = peer.0.id();
    leader.release();
    await_unreaped_exit(leader_pid);
    let deadline = Instant::now() + Duration::from_millis(30);
    let mut anchored = None;
    let result =
        wait_for_streaming_child_with_exit_check(&mut leader.0, Some(deadline), true, |pid| {
            anchored = Some(unreaped_exit(pid).map_err(|e| e.raw_os_error()));
            thread::sleep(deadline.saturating_duration_since(Instant::now()));
            while Instant::now() < deadline {
                thread::yield_now();
            }
        });
    // Always retire our own peer before asserting, including the expected RED
    // baseline. Its retained membership keeps this test's PGID occupied even
    // on the buggy implementation; no unrelated recycled group is targeted.
    let peer_status = peer.wait();
    let leader_status = leader.wait();
    eprintln!(
        "deadline crossing: leader={leader_pid} peer={peer_pid} anchored={anchored:?} result={result:?} leader_status={leader_status:?} peer_status={peer_status:?}"
    );
    assert_eq!(
        anchored,
        Some(Ok(true)),
        "exit observation must not reap the leader"
    );
    assert_eq!(result.unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert_eq!(leader_status.code(), Some(0));
    assert_eq!(peer_status.signal(), Some(libc::SIGKILL));
}

#[test]
fn predeadline_exit_reaps_without_killing_original_group_peer() {
    let _serial = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut leader = Running::spawn(None);
    let mut peer = Running::spawn(Some(leader.0.id()));
    leader.release();
    await_unreaped_exit(leader.0.id());
    let status = wait_for_streaming_child(
        &mut leader.0,
        Some(Instant::now() + Duration::from_secs(5)),
        true,
    )
    .unwrap();
    assert_eq!(status.code(), Some(0));
    assert!(
        peer.0.try_wait().unwrap().is_none(),
        "normal exit must preserve existing group policy"
    );
    peer.release();
    assert_eq!(peer.wait().code(), Some(0));
}

#[test]
fn expired_deadline_stops_and_reaps_both_original_live_children() {
    let _serial = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut leader = Running::spawn(None);
    let mut peer = Running::spawn(Some(leader.0.id()));
    let result = wait_for_streaming_child(
        &mut leader.0,
        Some(Instant::now() - Duration::from_millis(1)),
        true,
    );
    assert_eq!(result.unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert_eq!(leader.wait().signal(), Some(libc::SIGKILL));
    assert_eq!(peer.wait().signal(), Some(libc::SIGKILL));
}

#[test]
fn lost_leader_custody_never_signals_its_still_owned_group_peer() {
    let _serial = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut leader = Running::spawn(None);
    let mut peer = Running::spawn(Some(leader.0.id()));
    leader.release();
    assert_eq!(leader.wait().code(), Some(0));
    let result = wait_for_streaming_child(
        &mut leader.0,
        Some(Instant::now() - Duration::from_millis(1)),
        true,
    );
    let peer_pending = peer.0.try_wait().unwrap().is_none();
    if peer_pending {
        peer.release();
    }
    let peer_status = peer.wait();
    eprintln!(
        "lost custody: result={result:?} peer_pending={peer_pending} peer_status={peer_status:?}"
    );
    assert_eq!(result.unwrap_err().raw_os_error(), Some(libc::ECHILD));
    assert!(
        peer_pending,
        "known lost custody cannot authorize a numeric group signal"
    );
    assert_eq!(peer_status.code(), Some(0));
}
