use super::*;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn bounded_waiter_deadline_does_not_borrow_or_replenish() {
    use std::time::{Duration, Instant};
    let original = Jobserver::new(2).unwrap();
    let owner = scheduler(Some(original.clone()));
    let held = owner.state.lock().unwrap();
    let waiting = owner.clone();
    let worker = std::thread::spawn(move || {
        waiting.bounded_output(
            &mut Command::new("/this-program-must-not-start"),
            Instant::now() + Duration::from_millis(50),
            1024,
        )
    });
    // Keep the real borrower locked until the waiter has returned. No release/
    // reacquire gap or scheduler marker substitutes for this exclusion.
    let error = worker.join().unwrap().unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert_eq!(original.client().available().unwrap(), 2);
    drop(held);
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn bounded_queries_preserve_the_original_token_inventory_after_refusal() {
    use std::time::{Duration, Instant};
    let original = Jobserver::new(2).unwrap();
    let held = original.client().acquire().unwrap();
    let owner = scheduler(Some(original.clone()));
    assert!(
        owner
            .bounded_output(
                &mut Command::new("/usr/bin/true"),
                Instant::now() + Duration::from_secs(2),
                1024
            )
            .unwrap()
            .status
            .success()
    );
    assert_eq!(original.client().available().unwrap(), 1);
    let refused = owner
        .bounded_output(
            Command::new("/bin/sleep").arg("30"),
            Instant::now() + Duration::from_millis(50),
            1024,
        )
        .unwrap_err();
    assert_eq!(refused.kind(), io::ErrorKind::TimedOut);
    assert_eq!(original.client().available().unwrap(), 1);
    assert!(
        owner
            .bounded_output(
                &mut Command::new("/usr/bin/true"),
                Instant::now() + Duration::from_secs(2),
                1024
            )
            .unwrap()
            .status
            .success()
    );
    drop(owner);
    assert_eq!(original.client().available().unwrap(), 1);
    drop(held);
    assert_eq!(original.client().available().unwrap(), 2);
}

#[test]
fn in_process_install_keeps_the_actual_original_pipe_and_refuses_a_second_owner() {
    const ROLE: &str = "TRUST_BOOTSTRAP_EMBEDDED_SCHEDULER_ACTOR";
    if std::env::var_os(ROLE).as_deref() != Some(std::ffi::OsStr::new("1")) {
        let output = crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", "utils::metadata_scheduler::tests::in_process_install_keeps_the_actual_original_pipe_and_refuses_a_second_owner", "--nocapture"])
            .env(ROLE, "1").output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            output
                .stdout
                .windows(b"original-scheduler-installed".len())
                .any(|bytes| bytes == b"original-scheduler-installed")
        );
        return;
    }
    let original = Jobserver::new(2).unwrap();
    let held = original.client().acquire().unwrap();
    install_test_original(original.clone()).unwrap();
    assert!(install_test_original(original.clone()).is_err());
    let selected = selected().unwrap();
    let mut command = Command::new("/usr/bin/true");
    assert!(selected.output(&mut command, true, true).unwrap().status.success());
    assert_eq!(original.client().available().unwrap(), 1);
    assert_eq!(
        selected.state.lock().unwrap().server.as_ref().unwrap().client().available().unwrap(),
        1
    );
    #[cfg(unix)]
    {
        use std::os::fd::AsRawFd;
        let identity = |fd: i32| {
            let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
            assert_eq!(unsafe { libc::fstat(fd, stat.as_mut_ptr()) }, 0);
            let stat = unsafe { stat.assume_init() };
            (stat.st_dev, stat.st_ino)
        };
        let state = selected.state.lock().unwrap();
        for (left, right) in original
            .pipe_descriptors()
            .unwrap()
            .iter()
            .zip(state.server.as_ref().unwrap().pipe_descriptors().unwrap())
        {
            assert_eq!(identity(left.as_raw_fd()), identity(right.as_raw_fd()));
        }
    }
    drop(held);
    assert_eq!(original.client().available().unwrap(), 2);
    println!("original-scheduler-installed");
}

#[test]
fn a_test_build_refuses_without_an_owner_and_dispatches_through_the_test_owner() {
    // Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): fd53debc5b routed
    // Session::new's startup queries through `selected()`, which the lib-test
    // process never captured, and every test that built a Session panicked.
    // Run alone in a fresh process, so no other test installed an owner first.
    const ROLE: &str = "TRUST_BOOTSTRAP_TEST_OWNER_ACTOR";
    const NAME: &str = "utils::metadata_scheduler::tests::a_test_build_refuses_without_an_owner_and_dispatches_through_the_test_owner";
    if std::env::var_os(ROLE).as_deref() != Some(std::ffi::OsStr::new("1")) {
        let output =
            crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
                .args(["--exact", NAME, "--nocapture"])
                .env(ROLE, "1")
                .output()
                .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            output
                .stdout
                .windows(b"test-owner-dispatched".len())
                .any(|bytes| bytes == b"test-owner-dispatched")
        );
        return;
    }
    // No Session: the production refusal still holds in a test build.
    assert!(CAPTURED.get().is_none());
    let refused = output(&mut Command::new("/usr/bin/true"), true, true).unwrap_err();
    assert!(refused.to_string().contains("requires native early scheduler capture"), "{refused}");
    assert!(CAPTURED.get().is_none());
    install_test_owner();
    {
        let state = selected().unwrap().state.lock().unwrap();
        assert!(!state.embedded_original);
        assert!(!state.producer_failed);
        // The empty owner is born only when a query is dispatched.
        assert!(state.server.is_none());
    }
    assert!(output(&mut Command::new("/usr/bin/true"), true, true).unwrap().status.success());
    {
        let state = selected().unwrap().state.lock().unwrap();
        assert_eq!(state.server.as_ref().unwrap().client().available().unwrap(), 0);
    }
    // A second install keeps the same owner, and an embedding cannot follow it.
    let first = Arc::as_ptr(selected().unwrap());
    install_test_owner();
    assert_eq!(Arc::as_ptr(selected().unwrap()), first);
    assert!(install_test_original(Jobserver::new(1).unwrap()).is_err());
    println!("test-owner-dispatched");
}

#[test]
fn a_test_session_dispatches_its_startup_queries_through_the_test_owner() {
    // Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): guards the cfg(test) call in
    // Session::new_with_shims itself. Alone in a fresh process, a dry-run
    // Session's run_in_dry_run startup queries must find the test owner.
    const ROLE: &str = "TRUST_BOOTSTRAP_TEST_SESSION_OWNER_ACTOR";
    const NAME: &str = "utils::metadata_scheduler::tests::a_test_session_dispatches_its_startup_queries_through_the_test_owner";
    if std::env::var_os(ROLE).as_deref() != Some(std::ffi::OsStr::new("1")) {
        let output =
            crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
                .args(["--exact", NAME, "--nocapture"])
                .env(ROLE, "1")
                .output()
                .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            output
                .stdout
                .windows(b"test-session-owner-dispatched".len())
                .any(|bytes| bytes == b"test-session-owner-dispatched")
        );
        return;
    }
    assert!(CAPTURED.get().is_none());
    install_test_owner();
    let config = crate::utils::tests::TestCtx::new().config("build").create_config();
    let _session = crate::core::session::Session::new(config);
    let state = selected().unwrap().state.lock().unwrap();
    assert!(!state.embedded_original);
    assert!(!state.producer_failed);
    // The startup queries were dispatched through it, so its owner was born.
    assert!(state.server.is_some());
    drop(state);
    println!("test-session-owner-dispatched");
}

fn scheduler(server: Option<Jobserver>) -> Arc<Scheduler> {
    Arc::new(Scheduler {
        state: Mutex::new(State {
            original_transport_present: server.is_some(),
            sdk_present: false,
            server,
            embedded_original: false,
            producer_failed: false,
        }),
    })
}

#[test]
fn zero_extra_transport_retains_its_owner_and_exact_output() {
    let owner = scheduler(None);
    let mut cmd = Command::new("/bin/sh");
    cmd.env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS");
    cmd.args(["-c", "printf '%s' \"$CARGO_MAKEFLAGS\"; printf error >&2; exit 7"]);
    let output = owner.output(&mut cmd, true, true).unwrap();
    assert_eq!(output.status.code(), Some(7));
    let flags = String::from_utf8(output.stdout).unwrap();
    assert_eq!(flags.contains("--jobserver-auth="), scheduler_transport_supported());
    assert_eq!(output.stderr, b"error");
    let state = owner.state.lock().unwrap();
    if scheduler_transport_supported() {
        assert_eq!(state.server.as_ref().unwrap().client().available().unwrap(), 0);
    } else {
        assert!(state.server.is_none());
    }
}

#[test]
fn actual_inherited_pool_capacity_is_not_replaced_or_replenished() {
    let original = Jobserver::new(2).unwrap();
    let owner = scheduler(Some(original.clone()));
    let credit = original.client().acquire().unwrap();
    let mut cmd = Command::new("/bin/sh");
    cmd.args(["-c", "exit 0"]);
    assert!(owner.output(&mut cmd, true, true).unwrap().status.success());
    assert_eq!(original.client().available().unwrap(), 1);
    assert_eq!(
        owner.state.lock().unwrap().server.as_ref().unwrap().client().available().unwrap(),
        1
    );
    drop(credit);
    assert_eq!(original.client().available().unwrap(), 2);
}

#[test]
fn metadata_child_inherits_same_original_gnu_in_all_aliases() {
    use std::os::fd::AsRawFd;

    const NAME: &str = "utils::metadata_scheduler::tests::metadata_child_inherits_same_original_gnu_in_all_aliases";
    const ROLE: &str = "TRUST_BOOTSTRAP_METADATA_GNU_ACTOR";
    let identity = |fd| {
        let mut value = std::mem::MaybeUninit::<libc::stat>::uninit();
        assert_eq!(unsafe { libc::fstat(fd, value.as_mut_ptr()) }, 0);
        let value = unsafe { value.assume_init() };
        assert_eq!(value.st_mode & libc::S_IFMT, libc::S_IFIFO);
        format!("{}:{}", value.st_dev, value.st_ino)
    };
    if std::env::var_os(ROLE).is_some() {
        let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
        assert_eq!(std::env::var("MAKEFLAGS").unwrap(), flags);
        assert_eq!(std::env::var("MFLAGS").unwrap(), flags);
        let pair = flags
            .split_ascii_whitespace()
            .find_map(|word| word.strip_prefix("--jobserver-auth="))
            .unwrap();
        let actual = pair
            .split(',')
            .map(|number| identity(number.parse().unwrap()))
            .collect::<Vec<_>>()
            .join(",");
        assert_eq!(actual, std::env::var(ROLE).unwrap());
        println!("same-original-metadata-gnu");
        return;
    }
    let original = Jobserver::new(2).unwrap();
    let paid = original.client().acquire().unwrap();
    let descriptors = original.pipe_descriptors().unwrap();
    let flags: Vec<_> = descriptors
        .iter()
        .map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) })
        .collect();
    let expected =
        descriptors.iter().map(|fd| identity(fd.as_raw_fd())).collect::<Vec<_>>().join(",");
    let owner = scheduler(Some(original.clone()));
    let mut child =
        crate::test_entry::synthetic_observer(Command::new(std::env::current_exe().unwrap()));
    child
        .args(["--exact", NAME, "--nocapture"])
        .env(ROLE, expected)
        .env("MAKEFLAGS", "--jobserver-auth=999998,999999 -j")
        .env("MFLAGS", "--jobserver-auth=999998,999999 -j");
    let output = owner.output(&mut child, true, true).unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("same-original-metadata-gnu"));
    assert_eq!(original.client().available().unwrap(), 1);
    for (fd, before) in descriptors.iter().zip(flags) {
        assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) }, before);
    }
    drop(paid);
    assert_eq!(original.client().available().unwrap(), 2);
}

#[test]
fn concurrent_queries_cannot_execute_with_two_implicit_borrowers() {
    let directory = tempfile::tempdir().unwrap();
    let active = directory.path().join("active");
    let owner = scheduler(None);
    let barrier = Arc::new(std::sync::Barrier::new(2));
    let handles: Vec<_> = (0..2)
        .map(|_| {
            let owner = Arc::clone(&owner);
            let barrier = Arc::clone(&barrier);
            let active = active.clone();
            std::thread::spawn(move || {
                let mut command = Command::new("/bin/sh");
                command.args(["-c", "mkdir \"$1\" || exit 9; sleep 0.1; rmdir \"$1\"", "sh"]);
                command.arg(active);
                barrier.wait();
                owner.output(&mut command, true, true).unwrap()
            })
        })
        .collect();
    for handle in handles {
        let output = handle.join().unwrap();
        assert!(output.status.success(), "{output:?}");
    }
    assert!(!active.exists());
}

#[test]
fn spawn_error_releases_borrow_without_forging_success() {
    let owner = scheduler(None);
    assert!(owner.output(&mut Command::new("/no/such/metadata-executable"), true, true).is_err());
    let output = owner.output(&mut Command::new("/usr/bin/true"), true, true).unwrap();
    assert!(output.status.success());
}

#[test]
fn capture_drains_both_streams_without_pipe_deadlock() {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "i=0; while [ $i -lt 2048 ]; do printf a; printf b >&2; i=$((i+1)); done"]);
    let output = scheduler(None).output(&mut command, true, true).unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, vec![b'a'; 2048]);
    assert_eq!(output.stderr, vec![b'b'; 2048]);
}

#[test]
fn unwinding_retains_and_reaps_the_actual_owned_child() {
    let (send, receive) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let child = Command::new("/bin/sleep").arg("30").spawn().unwrap();
        send.send(child.id()).unwrap();
        let _running = Running(child);
        panic!("exercise actual child cleanup during unwinding");
    });
    let pid = receive.recv().unwrap();
    assert!(worker.join().is_err());
    #[cfg(unix)]
    {
        let mut status = 0;
        // SAFETY: waitpid reads only this scalar PID and writes our status.
        let result = unsafe { libc::waitpid(pid as libc::pid_t, &mut status, libc::WNOHANG) };
        assert_eq!(result, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    }
}

#[test]
fn poisoned_borrower_refuses_a_new_dispatch() {
    let owner = scheduler(None);
    let other = Arc::clone(&owner);
    assert!(
        std::thread::spawn(move || {
            let _guard = other.state.lock().unwrap();
            panic!("poison execution custody");
        })
        .join()
        .is_err()
    );
    assert!(owner.output(&mut Command::new("/usr/bin/true"), true, true).is_err());
}

#[test]
fn raw_command_cache_does_not_impersonate_metadata_transport() {
    use crate::utils::exec::{ExecutionContext, OutputMode, command};
    let mut raw = command("/usr/bin/true");
    let mut protected = command("/usr/bin/true");
    protected.metadata_scheduler();
    assert_ne!(raw.fingerprint(), protected.fingerprint());
    raw.mark_as_executed();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ExecutionContext::new(0, true).stream(
            &mut protected,
            OutputMode::Capture,
            OutputMode::Capture,
        )
    }));
    assert!(result.is_err(), "asynchronous metadata must refuse before spawn");
}

fn completed_within_deadline(child: &mut Child) -> Option<std::process::ExitStatus> {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Some(status),
            Err(_) => return None,
            Ok(None) => {}
        }
        if std::time::Instant::now() >= deadline {
            return None;
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

fn run_actor_with_deadline(name: &str, role: &str, mode: &str) {
    let mut out = tempfile::tempfile().unwrap();
    let mut err = tempfile::tempfile().unwrap();
    let mut actor = Running(
        crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", name, "--nocapture"])
            .env(role, mode)
            .stdout(out.try_clone().unwrap())
            .stderr(err.try_clone().unwrap())
            .spawn()
            .unwrap(),
    );
    let status = completed_within_deadline(&mut actor.0);
    drop(actor); // settle exact owned actor before every assertion
    out.rewind().unwrap();
    err.rewind().unwrap();
    let mut stdout = String::new();
    let mut stderr = String::new();
    out.read_to_string(&mut stdout).unwrap();
    err.read_to_string(&mut stderr).unwrap();
    assert!(
        status.is_some_and(|status| status.success()),
        "actor {mode}: {status:?} stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn ordinary_streaming_borrow_preserves_output_and_poison_after_unwind() {
    const NAME: &str = "utils::metadata_scheduler::tests::ordinary_streaming_borrow_preserves_output_and_poison_after_unwind";
    const ROLE: &str = "TRUST_BOOTSTRAP_STREAM_BORROW_ACTOR";
    if std::env::var_os(ROLE).is_none() {
        for mode in ["drop", "unwind"] {
            run_actor_with_deadline(NAME, ROLE, mode);
        }
        return;
    }
    // Synthetic original scheduler, with explicit absent SDK. No admission.
    install_test_original(Jobserver::new(0).unwrap()).unwrap();
    if !scheduler_transport_supported() {
        assert!(stream_original(&mut Command::new("/no/such/managed-child")).is_err());
        return;
    }
    let mut print = Command::new("/usr/bin/printf");
    print.args(["%s", "ordinary streaming query transport"]);
    print.stdout(std::process::Stdio::piped());
    let mut child = stream_original(&mut print).unwrap();
    let mut text = String::new();
    child.take_stdout().unwrap().read_to_string(&mut text).unwrap();
    assert!(child.wait().unwrap().success());
    assert_eq!(text, "ordinary streaming query transport");
    let mut command = Command::new("/bin/sleep");
    command.arg("30");
    let actual = stream_original(&mut command).unwrap();
    let pid = actual.child.id() as libc::pid_t;
    let unwind = std::env::var(ROLE).unwrap() == "unwind";
    if unwind {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _actual = actual;
            panic!("exercise owning streaming cleanup");
        }));
        assert!(result.is_err());
    } else {
        drop(actual);
    }
    let mut status = 0;
    let observed = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
    let error = io::Error::last_os_error();
    if observed == 0 {
        // Regressions still settle ONLY this fixture's own original child
        // before assertions; no keeper or foreign process is signalled.
        unsafe {
            libc::kill(pid, libc::SIGKILL);
            libc::waitpid(pid, &mut status, 0);
        }
    }
    assert_eq!(observed, -1, "own child was not reaped by cleanup");
    assert_eq!(error.raw_os_error(), Some(libc::ECHILD));
    // Local child retirement does NOT return descendant authority or restore
    // a reusable original borrower after abnormal drop/unwind.
    if unwind {
        assert!(selected().unwrap().state.lock().is_err());
    } else {
        assert!(selected().unwrap().state.lock().unwrap().producer_failed);
    }
    assert!(stream_original(&mut Command::new("/usr/bin/true")).is_err());
}

#[test]
fn stock_absent_stream_preserves_absence_across_two_exec_hops() {
    if scheduler_transport_supported() {
        return;
    } // stock-compatibility branch only
    const NAME: &str = "utils::metadata_scheduler::tests::stock_absent_stream_preserves_absence_across_two_exec_hops";
    const ROLE: &str = "TRUST_BOOTSTRAP_STOCK_ABSENCE_ACTOR";
    let role = std::env::var(ROLE).unwrap_or_default();
    if role.is_empty() {
        run_actor_with_deadline(NAME, ROLE, "owner");
        return;
    }
    if role == "child" {
        for key in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
            assert!(
                std::env::var_os(key).is_none(),
                "synthetic GNU advertisement at first hop: {key}"
            );
        }
        let mut child = Running(
            Command::new("/bin/sh")
                .args(["-c", "test -z \"$CARGO_MAKEFLAGS$MAKEFLAGS$MFLAGS\""])
                .spawn()
                .unwrap(),
        );
        let status = completed_within_deadline(&mut child.0);
        drop(child);
        assert!(
            status.is_some_and(|status| status.success()),
            "synthetic GNU advertisement or timeout at second hop"
        );
        return;
    }
    // Explicit synthetic original absence: no descriptor import/admission.
    CAPTURED.set(Ok(scheduler(None))).ok().expect("isolated absence owner");
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args(["--exact", NAME, "--nocapture"]).env(ROLE, "child");
    command.env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS");
    let mut child = stream_original(&mut command).unwrap();
    let status = completed_within_deadline(&mut child.child);
    let waited = if status.is_some() {
        Some(child.wait().unwrap())
    } else {
        drop(child);
        None
    };
    assert!(waited.is_some_and(|status| status.success()), "first stock hop failed or timed out");
    assert!(selected().unwrap().state.lock().unwrap().server.is_none());
}
