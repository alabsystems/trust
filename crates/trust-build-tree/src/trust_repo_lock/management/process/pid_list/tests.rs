use super::*;

#[test]
fn actual_public_libproc_zero_with_errno_must_not_be_empty_data() {
    let mut buffer = [17_i32];
    // A real writable pointer with zero declared bytes requests no writes and
    // is rejected by the public kernel ABI with ENOMEM. Observe the installed
    // libproc wrapper directly before testing our own adapter.
    unsafe {
        *libc::__error() = 0;
    }
    let raw =
        unsafe { libc::proc_listpids(2, libc::getpgrp() as u32, buffer.as_mut_ptr().cast(), 0) };
    let errno = unsafe { *libc::__error() };
    assert_eq!(raw, 0, "installed libproc zero-on-error convention");
    assert_eq!(errno, libc::ENOMEM);
    assert_eq!(buffer, [17]);
    let error =
        read_pid_bytes(2, unsafe { libc::getpgrp() as u32 }, Some(&mut buffer[..0])).unwrap_err();
    assert_eq!(error.raw_os_error(), Some(libc::ENOMEM));
    assert_eq!(buffer, [17]);
}

#[test]
fn sizing_and_population_zero_with_errno_are_errors_for_each_selector() {
    for (selector, argument, observer) in [
        (4, unsafe { libc::geteuid() }, true),
        (1, 0, true),
        (2, unsafe { libc::getpgrp() as u32 }, false),
    ] {
        for skip in [0, 1] {
            let _fault = FaultGuard::install(skip, 1, 0, libc::EPERM);
            let error = list_selected_pids(selector, argument, observer).unwrap_err();
            assert_eq!(
                error.raw_os_error(),
                Some(libc::EPERM),
                "selector{selector}/phase{skip}: {error}"
            );
        }
    }
}

#[test]
fn genuine_empty_and_missing_observer_have_distinct_results_despite_stale_errno() {
    // No process has the reserved uid_t(-1). This is an actual successful
    // empty native selection, not a fault standing in for a real empty group.
    unsafe {
        *libc::__error() = libc::EACCES;
    }
    assert!(list_selected_pids(4, u32::MAX, false).unwrap().is_empty());
    let _fault = FaultGuard::install(1, 1, 0, 0);
    let error = list_selected_pids(4, unsafe { libc::geteuid() }, true).unwrap_err();
    assert!(error.to_string().contains("omitted the observer"));
}

#[test]
fn actual_current_account_and_system_populations_keep_observer() {
    let pid = std::process::id();
    let account = list_selected_pids(4, unsafe { libc::geteuid() }, true).unwrap();
    assert!(account.contains(&pid));
    let system = list_selected_pids(1, 0, true).unwrap();
    assert!(system.contains(&pid));
    let group = list_selected_pids(2, unsafe { libc::getpgrp() as u32 }, false).unwrap();
    assert!(group.contains(&pid));
}

#[test]
fn caller_errno_is_cleared_without_touching_another_live_threads_errno() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let ready = AtomicBool::new(false);
    let finish = AtomicBool::new(false);
    struct Finish<'a>(&'a AtomicBool);
    impl Drop for Finish<'_> {
        fn drop(&mut self) {
            self.0.store(true, Ordering::Release);
        }
    }
    std::thread::scope(|scope| {
        let finish_guard = Finish(&finish);
        let worker = scope.spawn(|| {
            let pointer = unsafe { libc::__error() };
            unsafe {
                *pointer = libc::EBUSY;
            }
            ready.store(true, Ordering::Release);
            // Only atomic loads and a CPU hint occur in this interval; a
            // barrier's own native waits could legitimately change errno.
            while !finish.load(Ordering::Acquire) {
                std::hint::spin_loop();
            }
            assert_eq!(unsafe { *pointer }, libc::EBUSY);
            pointer as usize
        });
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while !ready.load(Ordering::Acquire) {
            assert!(std::time::Instant::now() < deadline, "native errno worker did not start");
            std::hint::spin_loop();
        }
        let pointer = unsafe { libc::__error() };
        unsafe {
            *pointer = libc::EACCES;
        }
        assert!(list_selected_pids(4, u32::MAX, false).unwrap().is_empty());
        assert_eq!(unsafe { *pointer }, 0);
        drop(finish_guard);
        assert_ne!(worker.join().unwrap(), pointer as usize);
    });
}

#[test]
fn malformed_counts_and_native_census_population_bound_refuse() {
    {
        let _fault = FaultGuard::install(1, 1, 3, 0);
        assert!(
            list_selected_pids(4, unsafe { libc::geteuid() }, true)
                .unwrap_err()
                .to_string()
                .contains("incomplete native PID element")
        );
    }
    {
        let _fault = FaultGuard::install(0, 1, 4_000_004, 0);
        assert!(
            list_selected_pids(4, unsafe { libc::geteuid() }, true)
                .unwrap_err()
                .to_string()
                .contains("exceeds its bound")
        );
    }
}

const ACTOR: &str =
    "trust_repo_lock::management::process::pid_list::tests::actual_group_change_actor";
const MODE: &str = "TRUST_NATIVE_PID_LIST_GROUP_ACTOR";

#[test]
fn actual_group_change_actor() {
    if std::env::var_os(MODE).is_none() {
        return;
    }
    use std::io::{Read, Write};
    println!("ACTUAL-GROUP-BEFORE {}", std::process::id());
    std::io::stdout().flush().unwrap();
    let mut byte = [0];
    std::io::stdin().read_exact(&mut byte).unwrap();
    assert_eq!(byte, [1]);
    assert_eq!(unsafe { libc::setsid() }, std::process::id() as i32);
    println!("ACTUAL-GROUP-AFTER {}", std::process::id());
    std::io::stdout().flush().unwrap();
    std::io::stdin().read_exact(&mut byte).unwrap();
    assert_eq!(byte, [2]);
}

struct Owned(std::process::Child);
impl Drop for Owned {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn await_marker(
    output: &mut std::process::ChildStdout,
    expected: &str,
    deadline: std::time::Instant,
) {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    loop {
        let mut row = Vec::new();
        loop {
            let remaining = deadline.saturating_duration_since(std::time::Instant::now());
            assert!(!remaining.is_zero(), "actual PID actor marker deadline");
            let mut poll =
                libc::pollfd { fd: output.as_raw_fd(), events: libc::POLLIN, revents: 0 };
            let ready = unsafe { libc::poll(&mut poll, 1, remaining.as_millis().min(1000) as i32) };
            if ready < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            assert!(ready >= 0, "actual PID actor poll failed");
            if ready == 0 {
                continue;
            }
            let mut byte = [0];
            output.read_exact(&mut byte).expect("actual PID actor exited before marker");
            if byte == *b"\n" {
                break;
            }
            row.push(byte[0]);
            assert!(row.len() <= 4096, "bounded actual PID actor row");
        }
        if String::from_utf8(row).unwrap().ends_with(expected) {
            return;
        }
    }
}

#[test]
fn actual_group_change_keeps_birth_and_unreaped_member_then_actual_reap_is_empty() {
    use std::io::Write;
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut child = Owned(
        Command::new(std::env::current_exe().unwrap())
            .args(["--exact", ACTOR, "--nocapture"])
            .env(MODE, "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let pid = child.0.id();
    let mut input = child.0.stdin.take().unwrap();
    let mut output = child.0.stdout.take().unwrap();
    await_marker(&mut output, &format!("ACTUAL-GROUP-BEFORE {pid}"), deadline);
    let before = super::super::read(pid).unwrap();
    assert_ne!(before.group, pid, "native actor must begin in inherited actual group");
    assert!(list_selected_pids(2, before.group, false).unwrap().contains(&pid));
    input.write_all(&[1]).unwrap();
    await_marker(&mut output, &format!("ACTUAL-GROUP-AFTER {pid}"), deadline);
    let after = super::super::read(pid).unwrap();
    assert_eq!((after.pid, after.birth, after.uid), (before.pid, before.birth, before.uid));
    assert_eq!(after.group, pid);
    assert!(
        super::super::writer_recheck(&before, &super::super::CensusSettle::new()).is_err(),
        "changed group is not original identity"
    );
    assert!(!list_selected_pids(2, before.group, false).unwrap().contains(&pid));
    assert!(list_selected_pids(2, after.group, false).unwrap().contains(&pid));
    input.write_all(&[2]).unwrap();
    while !super::super::writer_gone(pid).unwrap() {
        assert!(Instant::now() < deadline, "actual actor never reached native exit observation");
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(super::super::present(pid).unwrap(), "no census may reap the original child");
    assert!(
        list_selected_pids(2, after.group, false).unwrap().contains(&pid),
        "unreaped original remains in kernel population"
    );
    assert!(child.0.wait().unwrap().success());
    assert!(list_selected_pids(2, after.group, false).unwrap().is_empty());
    assert!(!super::super::writer_recheck(&after, &super::super::CensusSettle::new()).unwrap());
    assert!(Instant::now() < deadline);
}

#[test]
fn failed_native_census_cannot_release_or_erase_the_actual_original_holder() {
    use std::os::unix::fs::MetadataExt;

    use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager, Release};
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native census exclusion control".into(),
        contract: "original actual holder survives unavailable observations".into(),
        wait: std::time::Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("new native fixture is held"),
    };
    let manager = Manager::open(root.path()).unwrap();
    let token = manager.status().unwrap().holder.unwrap().token;
    let path = root.path().join(".trust-build-lock/info");
    let bytes = std::fs::read(&path).unwrap();
    let inode = std::fs::metadata(&path).unwrap().ino();
    {
        let _fault = FaultGuard::install(0, usize::MAX, 0, libc::EPERM);
        let error = manager.release(&token).unwrap_err();
        assert_eq!(error.raw_os_error(), Some(libc::EPERM));
        lease.check_current().unwrap();
        drop(lease); // Unavailable census also refuses the ordinary Drop release.
        assert_eq!(std::fs::read(&path).unwrap(), bytes);
        assert_eq!(std::fs::metadata(&path).unwrap().ino(), inode);
    }
    assert!(!manager.status().unwrap().is_free());
    assert_eq!(manager.release(&token).unwrap(), Release::Released);
}
