use std::io::Write;
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, Ordering};

use super::*;
use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};

fn original() -> (tempfile::TempDir, Arc<WithheldLease>) {
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "actual local protected-scope controls".into(),
        contract: "local joins only; no Host/release authority".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    (root, Arc::new(lease.into_withheld().unwrap()))
}

const ACTOR: &str =
    "trust_repo_lock::management::lease::withholding::protected_scope::tests::native_child_actor";
fn actor(mode: &str, pipes: bool) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args(["--exact", ACTOR, "--nocapture"]);
    command.env("TRUST_LOCAL_SCOPE_ACTOR", mode);
    if pipes {
        command.stdout(Stdio::piped()).stderr(Stdio::piped());
    } else {
        command.stdout(Stdio::null()).stderr(Stdio::null());
    }
    command
}

#[test]
fn native_child_actor() {
    let Ok(mode) = std::env::var("TRUST_LOCAL_SCOPE_ACTOR") else {
        return;
    };
    match mode.as_str() {
        "pipes" => {
            std::io::stdout().write_all(&vec![b'a'; 128 * 1024]).unwrap();
            std::io::stderr().write_all(&vec![b'b'; 128 * 1024]).unwrap();
            std::process::exit(7);
        }
        "delay" => thread::sleep(Duration::from_millis(80)),
        _ => panic!("unknown actor"),
    }
}

#[test]
fn real_child_both_full_pipes_and_nonzero_status_have_actual_local_bookends() {
    let (root, original) = original();
    let scope = ProtectedWorkScope::new(original.clone(), Instant::now() + Duration::from_secs(20))
        .unwrap();
    let identity = scope.identity().clone();
    let output = scope
        .dispatcher()
        .register_launch()
        .unwrap()
        .spawn(&mut actor("pipes", true))
        .unwrap()
        .wait_with_output()
        .unwrap();
    assert_eq!(output.status.code(), Some(7));
    assert!(output.stdout.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'a')));
    assert!(output.stderr.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'b')));
    let joined = scope.seal().join().unwrap();
    assert_eq!(joined.identity(), &identity);
    joined.check_current().unwrap();
    drop(joined);
    drop(original);
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn completed_output_survives_rejected_original_bookend() {
    let (root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(60)).unwrap();
    let dispatch = scope.dispatcher();
    let child = dispatch.register_launch().unwrap().spawn(&mut actor("pipes", true)).unwrap();
    let slot = child.slot.clone();
    // Hold the actual original reader census: the waiter can drain and reap,
    // but cannot finish its bookend until this same guard is released.
    let readers = slot.readers.lock().unwrap();
    let waiter = thread::spawn(move || child.wait_with_output_observed());
    let until = Instant::now() + Duration::from_secs(60);
    loop {
        let reaped = matches!(*slot.child.lock().unwrap(), ChildState::Reaped(_));
        let eof = readers.iter().all(|reader| reader.reader.lock().unwrap().eof);
        if reaped && eof {
            break;
        }
        assert!(Instant::now() < until, "actual child did not reap and drain");
        thread::sleep(Duration::from_millis(2));
    }
    dispatch.record_failure("actual completed child lost scope acceptance");
    drop(readers);
    let (output, joined) = waiter.join().unwrap().expect("observed output must survive refusal");
    assert_eq!(output.status.code(), Some(7));
    assert!(output.stdout.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'a')));
    assert!(output.stderr.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'b')));
    assert!(joined.is_err(), "rejected original scope grants no local bookend");
    assert!(scope.seal().join().is_err());
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn seal_refuses_further_dispatch_and_actually_joins_registered_child_and_worker() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let dispatch = scope.dispatcher();
    let child = dispatch.register_launch().unwrap().spawn(&mut actor("delay", false)).unwrap();
    drop(child); // registry still owns actual Child; seal joins it
    let finished = Arc::new(AtomicBool::new(false));
    let flag = finished.clone();
    let registration = dispatch.register_worker().unwrap();
    let worker = registration
        .spawn(thread::Builder::new(), move || {
            thread::sleep(Duration::from_millis(80));
            flag.store(true, Ordering::Release);
            42
        })
        .unwrap();
    let sealed = scope.seal();
    assert!(dispatch.register_launch().is_err());
    assert!(dispatch.register_worker().is_err());
    let joined = sealed.join().unwrap();
    assert!(finished.load(Ordering::Acquire));
    assert_eq!(worker.join().unwrap(), 42);
    joined.check_current().unwrap();
}

#[test]
fn actual_leader_exit_cannot_replace_original_reader_eof() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let mut command = actor("delay", true);
    let mut child = scope.dispatcher().register_launch().unwrap().spawn(&mut command).unwrap();
    assert!(child.wait().unwrap().success());
    let failure = scope.seal().join().err().expect("unread pipes must refuse local closure");
    assert!(failure.error().to_string().contains("actual EOF"));
}

#[test]
fn abandoned_or_panicking_original_owners_permanently_refuse_local_join() {
    for panic_worker in [false, true] {
        let (_root, original) = original();
        let scope =
            ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
        if panic_worker {
            let registration = scope.dispatcher().register_worker().unwrap();
            drop(
                registration
                    .spawn(thread::Builder::new(), || panic!("actual worker panic"))
                    .unwrap(),
            );
        } else {
            drop(scope.dispatcher().register_launch().unwrap());
        }
        assert!(scope.seal().join().is_err());
    }
}

/// A deadline far enough ahead that a scope's construction and its first
/// checks finish before it on a loaded machine. Each takes the namespace guard,
/// whose description another test's spawn can still hold just after a release.
const LOADED_SPAN: Duration = Duration::from_secs(5);

/// Sleeps until `deadline`, past it only by the sleep's wake-up latency, so a
/// grace longer than that latency fails the test.
fn reach(deadline: Instant) {
    while Instant::now() < deadline {
        thread::sleep(deadline.saturating_duration_since(Instant::now()));
    }
}

#[test]
fn exact_guard_binds_once_and_original_deadline_is_never_renewed() {
    let (_root, original) = original();
    assert!(ProtectedWorkScope::new(original.clone(), Instant::now()).is_err());
    // The span leaves new() room on a loaded machine (it takes the namespace
    // guard twice); the test then sleeps until the deadline, not a fixed time.
    let deadline = Instant::now() + LOADED_SPAN;
    let scope = ProtectedWorkScope::new(original.clone(), deadline).unwrap();
    assert!(ProtectedWorkScope::new(original, deadline + Duration::from_secs(5)).is_err());
    let dispatch = scope.dispatcher();
    assert_eq!(dispatch.deadline(), deadline);
    reach(deadline);
    assert!(dispatch.register_launch().is_err());
    assert!(scope.seal().join().is_err());
}

#[test]
fn seal_after_registration_refuses_actual_late_delivery() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let registration = scope.dispatcher().register_launch().unwrap();
    let sealed = scope.seal();
    let result = registration.spawn(&mut actor("delay", false));
    assert!(result.is_err(), "an earlier registration must not deliver after permanent seal");
    assert!(sealed.join().is_err(), "abandoned pending launch remains incomplete");
}

#[test]
fn actual_child_bookend_requires_all_original_eof_and_is_one_use() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let registration = scope.dispatcher().register_launch().unwrap();
    let identity = registration.identity().clone();
    let mut child = registration.spawn(&mut actor("delay", true)).unwrap();
    let mut stdout = child.take_stdout().unwrap();
    let mut stderr = child.take_stderr().unwrap();
    assert!(child.joined().is_err());
    child.wait().unwrap();
    assert!(child.joined().is_err(), "leader exit cannot certify unread pipes");
    stdout.read_to_end(&mut Vec::new()).unwrap();
    stderr.read_to_end(&mut Vec::new()).unwrap();
    let joined = child.joined().unwrap();
    assert_eq!(joined.identity(), &identity);
    assert!(child.joined().is_err(), "same actual child cannot emit a second bookend");
    let _joined = scope.seal().join().unwrap();
}

#[test]
fn private_capture_is_retained_before_launch_and_read_after_original_wait() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let registration = scope.dispatcher().register_launch().unwrap();
    let out = tempfile::tempfile().unwrap();
    let err = tempfile::tempfile().unwrap();
    let mut command = actor("pipes", false);
    command.stdout(Stdio::from(out.try_clone().unwrap()));
    command.stderr(Stdio::from(err.try_clone().unwrap()));
    let stdout = registration.capture_file(out).unwrap();
    let stderr = registration.capture_file(err).unwrap();
    let mut child = registration.spawn(&mut command).unwrap();
    assert_eq!(child.wait().unwrap().code(), Some(7));
    assert!(child.joined().is_err(), "private captures must be fully read too");
    let stdout = stdout.read_after_wait().unwrap();
    let stderr = stderr.read_after_wait().unwrap();
    assert!(stdout.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'a')));
    assert!(stderr.windows(128 * 1024).any(|w| w.iter().all(|&b| b == b'b')));
    child.joined().unwrap();
    let _joined = scope.seal().join().unwrap();
}

#[test]
fn weak_installed_restriction_cannot_keep_or_reconstruct_original_custody() {
    let (_root, original) = original();
    let scope = ProtectedWorkScope::new(original.clone(), Instant::now() + Duration::from_secs(20))
        .unwrap();
    let weak = scope.dispatcher().downgrade();
    drop(weak.upgrade().unwrap());
    let joined = scope.seal().join().unwrap();
    assert!(weak.upgrade().is_err());
    assert_eq!(Arc::strong_count(&original), 2);
    drop(joined);
    assert_eq!(
        Arc::strong_count(&original),
        1,
        "inert installed locator must not prevent final owner uniqueness"
    );
    assert!(weak.upgrade().is_err());
}

#[test]
fn poisoned_registry_drop_retains_actual_original_pipe_description() {
    const NAME: &str = "trust_repo_lock::management::lease::withholding::protected_scope::tests::poisoned_registry_drop_retains_actual_original_pipe_description";
    if std::env::var_os("TRUST_SCOPE_POISON_ISOLATED").is_none() {
        assert!(
            Command::new(std::env::current_exe().unwrap())
                .args(["--exact", NAME, "--nocapture"])
                .env("TRUST_SCOPE_POISON_ISOLATED", "1")
                .status()
                .unwrap()
                .success()
        );
        return;
    }
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let child =
        scope.dispatcher().register_launch().unwrap().spawn(&mut actor("delay", true)).unwrap();
    let fd = child.stdout.as_ref().unwrap().reader.lock().unwrap().pipe.as_ref().unwrap().fd();
    let mut before: libc::stat = unsafe { std::mem::zeroed() };
    assert_eq!(unsafe { libc::fstat(fd, &mut before) }, 0);
    drop(child); // the original registry is now its only actual reader owner
    let inner = scope.inner.clone();
    assert!(
        thread::spawn(move || {
            let _state = inner.state.lock().unwrap();
            panic!("actual scope mutex poison");
        })
        .join()
        .is_err()
    );
    assert!(scope.seal().join().is_err()); // dropping failure retains originals
    let mut after: libc::stat = unsafe { std::mem::zeroed() };
    assert_eq!(unsafe { libc::fstat(fd, &mut after) }, 0, "poison must not drop original reader");
    assert_eq!((before.st_dev, before.st_ino), (after.st_dev, after.st_ino));
}

#[test]
fn actual_borrowed_thread_scope_joins_original_workers_before_return() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let mut borrowed = [0, 0];
    scope
        .dispatcher()
        .scoped_threads(|threads| {
            let (first, second) = borrowed.split_at_mut(1);
            drop(
                threads
                    .spawn(move || {
                        thread::sleep(Duration::from_millis(30));
                        first[0] = 17;
                    })
                    .unwrap(),
            ); // actual std Scope retains and joins this handle
            let second = threads
                .spawn(move || {
                    second[0] = 23;
                    42
                })
                .unwrap();
            assert_eq!(second.join().unwrap(), 42);
        })
        .unwrap();
    assert_eq!(borrowed, [17, 23]);
    let _joined = scope.seal().join().unwrap();
}

#[test]
fn active_native_scope_and_late_native_spawn_cannot_mint_local_join() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let dispatch = scope.dispatcher();
    let ran = Arc::new(AtomicBool::new(false));
    let flag = ran.clone();
    let result = dispatch.scoped_threads(move |threads| {
        let sealed = scope.seal();
        assert!(threads.spawn(move || flag.store(true, Ordering::Release)).is_err());
        assert!(sealed.join().is_err(), "actual native scope is still active");
    });
    assert!(result.is_err());
    assert!(!ran.load(Ordering::Acquire));
}

#[test]
fn handled_native_worker_panic_still_permanently_refuses_scope_completion() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let result = scope.dispatcher().scoped_threads(|threads| {
        assert!(threads.spawn(|| panic!("actual borrowed worker panic")).unwrap().join().is_err());
    });
    assert!(result.is_err(), "caller handling a panic cannot clear original failure");
    assert!(scope.seal().join().is_err());
}

#[test]
fn original_native_scope_join_cannot_renew_expired_deadline() {
    let (_root, original) = original();
    let deadline = Instant::now() + LOADED_SPAN;
    let scope = ProtectedWorkScope::new(original, deadline).unwrap();
    let completed = Arc::new(AtomicBool::new(false));
    let flag = completed.clone();
    let result = scope.dispatcher().scoped_threads(|threads| {
        drop(
            threads
                .spawn(move || {
                    reach(deadline);
                    flag.store(true, Ordering::Release);
                })
                .unwrap(),
        );
    });
    assert!(completed.load(Ordering::Acquire), "actual lexical owner joined original worker");
    assert!(result.is_err());
    assert!(scope.seal().join().is_err());
}

#[test]
fn dropping_original_scope_owner_seals_every_retained_dispatcher() {
    let (_root, original) = original();
    let scope =
        ProtectedWorkScope::new(original, Instant::now() + Duration::from_secs(20)).unwrap();
    let dispatch = scope.dispatcher();
    let weak = dispatch.downgrade();
    drop(scope);
    assert!(
        dispatch.register_launch().is_err(),
        "lost coordinator cannot leave child delivery open"
    );
    assert!(dispatch.register_worker().is_err());
    assert!(weak.upgrade().is_err());
}
