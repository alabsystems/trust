use std::os::fd::FromRawFd;
use std::sync::{Arc, mpsc};
use std::time::{Duration, Instant};

use super::*;

/// Runs `body` alone, in a fresh process of this test binary that runs nothing
/// else. Every check here reads state the whole process shares: descriptor
/// numbers, a file lock that each child of this process holds a copy of until
/// it execs, and the count of forks that reached the prepare handler. A
/// sibling test that opens a file, forks or spawns changes all three.
fn alone(test: &str, body: impl FnOnce()) {
    crate::handoff::tests::isolated_assertions(&format!("fork_custody::tests::{test}"), body);
}

fn native_null() -> io::Result<OwnedFd> {
    // SAFETY: immutable NUL-terminated path; successful open returns one new
    // exclusively owned close-on-exec descriptor. No allocator is involved.
    let raw = unsafe { libc::open(c"/dev/null".as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: fresh original returned by open, adopted exactly once.
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}

fn fork_probe(fd: RawFd, closed: bool) {
    // SAFETY: child executes only async-signal-safe fcntl/_exit. Parent owns
    // the actual returned child through unreaped waitpid, never a saved PID.
    let pid = unsafe { libc::fork() };
    assert!(pid >= 0);
    if pid == 0 {
        // SAFETY: observation only; no Rust I/O, allocator or destructor runs.
        let observed = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        let correct = (observed < 0) == closed;
        // SAFETY: no inherited Rust owner is touched after fork.
        unsafe { libc::_exit(if correct { 0 } else { 31 }) };
    }
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        let mut status = 0;
        // SAFETY: pid is this exact unreaped child and status is initialized.
        let waited = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        if waited == pid {
            assert_eq!(status, 0);
            return;
        }
        assert!(waited >= 0 || io::Error::last_os_error().kind() == io::ErrorKind::Interrupted);
        if Instant::now() >= deadline {
            // SAFETY: only this exact still-unreaped owned child is signaled.
            unsafe {
                libc::kill(pid, libc::SIGKILL);
                libc::waitpid(pid, &mut status, 0);
            }
            panic!("owned native fork child did not finish");
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

#[test]
fn protected_original_is_closed_in_actual_fork_but_stays_held_in_parent() {
    alone("protected_original_is_closed_in_actual_fork_but_stays_held_in_parent", || {
        let owner =
            ProtectedOriginals::<1>::capture(Instant::now() + Duration::from_secs(30), |fds| {
                fds.push(native_null()?)
            })
            .unwrap();
        let fd = owner.get(0).unwrap().as_raw_fd();
        fork_probe(fd, true);
        // SAFETY: parent still owns this live descriptor.
        assert!(unsafe { libc::fcntl(fd, libc::F_GETFD) } >= 0);
    });
}

#[test]
fn actual_fork_waits_for_creation_and_cannot_copy_an_unregistered_original() {
    alone("actual_fork_waits_for_creation_and_cannot_copy_an_unregistered_original", || {
        let (created, ready) = mpsc::sync_channel(0);
        let (release, resume) = mpsc::sync_channel(0);
        let (close, finished) = mpsc::sync_channel(0);
        let maker = std::thread::spawn(move || {
            let owner =
                ProtectedOriginals::<1>::capture(Instant::now() + Duration::from_secs(30), |fds| {
                    let original = native_null()?;
                    let fd = original.as_raw_fd();
                    fds.push(original)?;
                    // Deliberately hold the real creation interval for the concurrent
                    // fork. This test seam is not used by production native receivers.
                    created.send(fd).unwrap();
                    resume.recv().unwrap();
                    Ok(())
                })
                .unwrap();
            finished.recv().unwrap();
            drop(owner);
        });
        let fd = ready.recv().unwrap();
        let before = PREPARE_ATTEMPTS.load(Ordering::SeqCst);
        let forker = std::thread::spawn(move || fork_probe(fd, true));
        let deadline = Instant::now() + Duration::from_secs(30);
        while PREPARE_ATTEMPTS.load(Ordering::SeqCst) == before && Instant::now() < deadline {
            std::thread::yield_now();
        }
        let attempted = PREPARE_ATTEMPTS.load(Ordering::SeqCst) != before;
        release.send(()).unwrap();
        forker.join().unwrap();
        close.send(()).unwrap();
        maker.join().unwrap();
        assert!(attempted, "actual prepare handler must meet the held creation interval");
    });
}

#[test]
fn dropped_registration_cannot_close_an_unrelated_reused_descriptor() {
    alone("dropped_registration_cannot_close_an_unrelated_reused_descriptor", || {
        let owner =
            ProtectedOriginals::<1>::capture(Instant::now() + Duration::from_secs(30), |fds| {
                fds.push(native_null()?)
            })
            .unwrap();
        let slot = owner.get(0).unwrap().as_raw_fd();
        drop(owner);
        let replacement = native_null().unwrap();
        let duplicate = if replacement.as_raw_fd() != slot {
            // SAFETY: slot was closed above and this test owns its replacement;
            // duplicate is adopted exactly once and remains live through fork.
            assert_eq!(unsafe { libc::dup2(replacement.as_raw_fd(), slot) }, slot);
            // SAFETY: successful dup2 created a new owned slot distinct from source.
            Some(unsafe { OwnedFd::from_raw_fd(slot) })
        } else {
            None
        };
        fork_probe(slot, false);
        drop((replacement, duplicate));
    });
}

#[test]
fn capture_unwind_closes_partial_originals_before_releasing_exclusion() {
    alone("capture_unwind_closes_partial_originals_before_releasing_exclusion", || {
        let raw = Arc::new(std::sync::atomic::AtomicI32::new(-1));
        let observed = raw.clone();
        let outcome = std::panic::catch_unwind(move || {
            let _ =
                ProtectedOriginals::<2>::capture(Instant::now() + Duration::from_secs(30), |fds| {
                    let original = native_null()?;
                    observed.store(original.as_raw_fd(), Ordering::SeqCst);
                    fds.push(original)?;
                    panic!("actual partial native capture unwinds");
                });
        });
        assert!(outcome.is_err());
        let fd = raw.load(Ordering::SeqCst);
        // SAFETY: observing the actual captured slot after owner cleanup.
        assert!(unsafe { libc::fcntl(fd, libc::F_GETFD) } < 0);
        let next =
            ProtectedOriginals::<1>::capture(Instant::now() + Duration::from_secs(30), |fds| {
                fds.push(native_null()?)
            })
            .unwrap();
        fork_probe(next.get(0).unwrap().as_raw_fd(), true);
    });
}

#[test]
fn concurrent_normal_std_spawn_cannot_retain_the_pending_original_lock() {
    alone("concurrent_normal_std_spawn_cannot_retain_the_pending_original_lock", || {
        use std::os::unix::ffi::OsStrExt as _;
        use std::process::{Command, Stdio};
        let scratch = tempfile::tempdir().unwrap();
        let path = scratch.path().join("pending-lock");
        std::fs::write(&path, b"actual original").unwrap();
        let native_path = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (created, ready) = mpsc::sync_channel(0);
        let (release, resume) = mpsc::sync_channel(0);
        let (owners, owner) = mpsc::sync_channel(1);
        let maker = std::thread::spawn(move || {
            let captured = ProtectedOriginals::<1>::capture(deadline, |fds| {
                // SAFETY: valid owned test path. Deliberately omit O_CLOEXEC to
                // exercise the actual capture producer's own descriptor marking.
                let raw = unsafe { libc::open(native_path.as_ptr(), libc::O_RDWR) };
                if raw < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: adopt this successful native open exactly once.
                let original = unsafe { OwnedFd::from_raw_fd(raw) };
                // SAFETY: acquire only this actual owned fixture's exclusive OFD.
                if unsafe { libc::flock(raw, libc::LOCK_EX | libc::LOCK_NB) } != 0 {
                    return Err(io::Error::last_os_error());
                }
                fds.push(original)?;
                // SAFETY: inspect the same live descriptor after capture marking.
                assert_ne!(unsafe { libc::fcntl(raw, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
                created.send(()).unwrap();
                resume.recv().unwrap();
                Ok(())
            })
            .unwrap();
            owners.send(captured).unwrap();
        });
        ready.recv_timeout(deadline.saturating_duration_since(Instant::now())).unwrap();
        let before = PREPARE_ATTEMPTS.load(Ordering::SeqCst);
        let (started, start) = mpsc::sync_channel(1);
        let spawner = std::thread::spawn(move || {
            // No pre_exec/inherit_all_fds or arbitrary descriptor handover: this
            // exercises the real ordinary Trust std Command spawn path.
            let child = Command::new("/bin/cat")
                .stdin(Stdio::piped())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn();
            started.send(child).unwrap();
        });
        let mut started_child = None;
        while Instant::now() < deadline {
            if let Ok(child) = start.try_recv() {
                started_child = Some(child);
                break;
            }
            if PREPARE_ATTEMPTS.load(Ordering::SeqCst) != before {
                break; // A real fallback fork is waiting on the held exclusion.
            }
            std::thread::yield_now();
        }
        release.send(()).unwrap();
        let captured =
            owner.recv_timeout(deadline.saturating_duration_since(Instant::now())).unwrap();
        let mut child = started_child
            .unwrap_or_else(|| {
                start.recv_timeout(deadline.saturating_duration_since(Instant::now())).unwrap()
            })
            .unwrap();
        maker.join().unwrap();
        spawner.join().unwrap();
        assert!(
            child.try_wait().unwrap().is_none(),
            "actual child must remain alive for the lock test"
        );
        drop(captured);
        let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
        let released = probe.try_lock();
        // Closing our actual stdin writer lets the owned child finish, with no
        // writes/SIGPIPE, saved-PID signaling or guessed process observation.
        drop(child.stdin.take());
        loop {
            if let Some(status) = child.try_wait().unwrap() {
                assert!(status.success());
                break;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("actual ordinary std child did not finish");
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        released.unwrap();
    });
}
