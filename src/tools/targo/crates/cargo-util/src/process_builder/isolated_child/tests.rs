use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use super::*;

fn spawn(script: &str) -> Child {
    Command::new("/bin/sh")
        .args(["-c", script])
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap()
}

fn assert_reaped(pid: libc::pid_t) {
    let mut status = 0;
    // SAFETY: only query our own former child. No signal or blocking wait is
    // issued, and a recycled PID belonging to another process cannot be reaped.
    assert_eq!(
        unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) },
        -1
    );
    assert_eq!(
        io::Error::last_os_error().raw_os_error(),
        Some(libc::ECHILD)
    );
}

fn assert_not_running(pid: libc::pid_t) {
    let deadline = Instant::now() + Duration::from_secs(3);
    loop {
        let output = Command::new("/bin/ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .unwrap();
        let text = std::str::from_utf8(&output.stdout).unwrap().trim();
        if text.is_empty() || text.starts_with('Z') {
            return;
        }
        assert!(
            Instant::now() < deadline,
            "descendant {pid} still running: {text}"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn standard_child_exit_stops_closed_stdio_descendant_before_reap() {
    let scope = StreamingProcessScope::new().unwrap();
    let prepared = PreparedIsolatedChild::prepare(&scope).unwrap();
    let root = tempfile::tempdir().unwrap();
    let marker = root.path().join("descendant-pid");
    // Pass the marker through argv rather than interpolate a shell pathname.
    let child = Command::new("/bin/sh")
        .args(["-c", "sleep 60 & echo $! > \"$1\"; exit 0", "fixture"])
        .arg(&marker)
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let pid = child.id() as libc::pid_t;
    // SAFETY: spawn created a fresh group, and this transfer leaves no other
    // handle or waiter for the direct child.
    let owned = unsafe { prepared.adopt_std(child) };
    assert!(owned.wait().unwrap().success());
    let descendant = std::fs::read_to_string(marker)
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    assert_not_running(descendant);
    assert_reaped(pid);
    scope.finish().unwrap();
}

#[test]
fn native_child_drop_stops_and_reaps_after_launch() {
    let scope = StreamingProcessScope::new().unwrap();
    let prepared = PreparedIsolatedChild::prepare(&scope).unwrap();
    let child = spawn("trap '' TERM INT; sleep 60");
    let pid = child.id() as libc::pid_t;
    // Std Child's Drop does not wait or signal. This test transfers sole native
    // PID ownership exactly as a successful posix_spawn caller does.
    drop(child);
    // SAFETY: child is our own unreaped isolated group leader; no waiter exists.
    let owned = unsafe { prepared.adopt(pid) };
    drop(owned);
    assert_reaped(pid);
    scope.finish().unwrap();
}

#[test]
fn scope_cancellation_does_not_affect_an_independent_child() {
    let first = StreamingProcessScope::new().unwrap();
    let second = StreamingProcessScope::new().unwrap();
    let a = PreparedIsolatedChild::prepare(&first).unwrap();
    let b = PreparedIsolatedChild::prepare(&second).unwrap();
    let child = spawn("trap '' TERM INT; sleep 60");
    let pid = child.id() as libc::pid_t;
    // SAFETY: both fresh isolated children have one exclusive waiter.
    let owned = unsafe { a.adopt_std(child) };
    let survivor = unsafe { b.adopt_std(spawn("exit 0")) };
    first.cancel();
    assert_eq!(owned.wait().unwrap_err().kind(), io::ErrorKind::Interrupted);
    assert_reaped(pid);
    assert!(survivor.wait().unwrap().success());
    first.finish().unwrap();
    second.finish().unwrap();
}

#[test]
fn cancelled_epoch_refuses_prepare_and_rechecks_before_resume() {
    let scope = StreamingProcessScope::new().unwrap();
    let prepared = PreparedIsolatedChild::prepare(&scope).unwrap();
    scope.cancel();
    assert_eq!(
        prepared.check_cancelled().unwrap_err().kind(),
        io::ErrorKind::Interrupted
    );
    assert!(PreparedIsolatedChild::prepare(&scope).is_err());
    // An already-exited successful child cannot erase the epoch cancellation.
    let child = spawn("exit 0");
    let pid = child.id() as libc::pid_t;
    // SAFETY: the direct child was spawned into its own group and is unreaped.
    let owned = unsafe { prepared.adopt_std(child) };
    let deadline = Instant::now() + Duration::from_secs(3);
    loop {
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        // SAFETY: inspect our own child without consuming the guard's sole
        // reap. No concurrent observer is running until owned.wait below.
        assert_eq!(
            unsafe {
                libc::waitid(
                    libc::P_PID,
                    pid as libc::id_t,
                    &mut info,
                    libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
                )
            },
            0
        );
        #[cfg(target_os = "macos")]
        let exited = info.si_pid == pid;
        #[cfg(target_os = "linux")]
        let exited = unsafe { info.si_pid() } == pid;
        if exited {
            #[cfg(target_os = "macos")]
            assert_eq!(info.si_status, 0);
            #[cfg(target_os = "linux")]
            assert_eq!(unsafe { info.si_status() }, 0);
            break;
        }
        assert!(
            Instant::now() < deadline,
            "fixture did not exit successfully"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
    assert_eq!(
        owned.check_cancelled().unwrap_err().kind(),
        io::ErrorKind::Interrupted
    );
    assert_eq!(owned.wait().unwrap_err().kind(), io::ErrorKind::Interrupted);
    assert_reaped(pid);
    scope.finish().unwrap();
}

#[test]
fn intentional_cleanup_does_not_manufacture_external_cancellation() {
    let command = super::super::ProcessBuilder::new("unused-before-platform-spawn");
    let prepared = command.prepare_isolated_child().unwrap();
    let child = spawn("sleep 60");
    let pid = child.id() as libc::pid_t;
    // SAFETY: the direct child was spawned into its own group and is unreaped.
    let owned = unsafe { prepared.adopt_std(child) };
    assert!(!owned.cancel_and_wait().unwrap().success());
    assert_reaped(pid);
}

#[test]
fn polled_root_cancellation_stops_the_live_child_and_remains_sticky() {
    let scope = StreamingProcessScope::new().unwrap();
    let prepared = PreparedIsolatedChild::prepare(&scope).unwrap();
    let root = tempfile::tempdir().unwrap();
    let marker = root.path().join("running");
    let child = Command::new("/bin/sh")
        .args([
            "-c",
            "echo running > \"$1\"; trap '' TERM INT; sleep 60",
            "fixture",
        ])
        .arg(&marker)
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let pid = child.id() as libc::pid_t;
    // SAFETY: fresh direct child, isolated group and exclusive reap ownership.
    let owned = unsafe { prepared.adopt_std(child) };
    let deadline = Instant::now() + Duration::from_secs(3);
    let mut saw_marker = false;
    let result = owned.wait_with_cancel(|| {
        saw_marker |= marker.exists();
        saw_marker || Instant::now() >= deadline
    });
    assert!(saw_marker, "fixture never became live before cancellation");
    assert_eq!(result.unwrap_err().kind(), io::ErrorKind::Interrupted);
    assert!(
        scope.interrupted(),
        "a consumed control message must cancel later harnesses"
    );
    assert_reaped(pid);
    assert!(PreparedIsolatedChild::prepare(&scope).is_err());
    scope.finish().unwrap();
}

#[test]
fn panicked_root_poll_still_drops_and_reaps_the_owned_child() {
    let scope = StreamingProcessScope::new().unwrap();
    let prepared = PreparedIsolatedChild::prepare(&scope).unwrap();
    let child = spawn("sleep 60");
    let pid = child.id() as libc::pid_t;
    // SAFETY: fresh direct child, isolated group and exclusive reap ownership.
    let owned = unsafe { prepared.adopt_std(child) };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = owned.wait_with_cancel(|| panic!("poll fixture"));
    }));
    assert!(result.is_err());
    assert_reaped(pid);
    scope.finish().unwrap();
}
