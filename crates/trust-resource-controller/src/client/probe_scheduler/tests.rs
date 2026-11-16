#[cfg(trust_std)]
use std::io::{BufRead, BufReader, Write};
#[cfg(trust_std)]
use std::sync::{Arc, mpsc};

use super::*;

#[cfg(trust_std)]
fn owner() -> ProbeScheduler {
    ProbeScheduler {
        server: Mutex::new(Some(Jobserver::new(0).unwrap())),
        original_transport_present: true,
        inherited_server_present: true,
        interrupted: std::sync::atomic::AtomicBool::new(false),
        lock_rendezvous: None,
        sdk_present: false,
    }
}

#[test]
fn producing_child_cannot_promote_a_query_only_scheduler() {
    let owner = ProbeScheduler {
        server: Mutex::new(Some(Jobserver::new(0).unwrap())),
        original_transport_present: true,
        inherited_server_present: false,
        interrupted: std::sync::atomic::AtomicBool::new(false),
        lock_rendezvous: None,
        sdk_present: false,
    };
    // Even an already-created query pipe cannot supply missing entry custody.
    let error =
        owner.run_inherited_child(&mut Command::new("/must/not/execute"), |_| Ok(())).unwrap_err();
    // A std without Trust's descriptor inheritance cannot forward the transport
    // this owner holds, and that refusal comes before the custody check.
    let (kind, cause) = if cfg!(trust_std) {
        (io::ErrorKind::PermissionDenied, "no original inherited GNU")
    } else {
        (io::ErrorKind::Unsupported, "inherited command transport requires Trust std")
    };
    assert_eq!(error.kind(), kind, "{error}");
    assert!(error.to_string().contains(cause), "{error}");
}

#[cfg(trust_std)]
#[test]
fn query_and_case_share_one_serial_borrow() {
    let _epoch = super::inherited_child::shared_signal_epoch();
    let owner = Arc::new(owner());
    let directory = tempfile::tempdir().unwrap();
    let guard = directory.path().join("active");
    let log = directory.path().join("log");
    let (entered_tx, entered_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let case_owner = Arc::clone(&owner);
    let case_guard = guard.clone();
    let case_log = log.clone();
    let case = std::thread::spawn(move || {
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "mkdir \"$1\" || exit 91; echo case >> \"$2\"; read ready; rmdir \"$1\""])
            .arg("case")
            .arg(case_guard)
            .arg(case_log)
            .stdin(Stdio::piped());
        case_owner
            .run_inherited_child(&mut command, |child| {
                entered_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                writeln!(child.take_stdin().unwrap(), "ready")?;
                assert!(child.wait()?.success());
                Ok(())
            })
            .unwrap();
    });
    entered_rx.recv().unwrap();
    let query_owner = Arc::clone(&owner);
    let query = std::thread::spawn(move || {
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "mkdir \"$1\" || exit 92; echo query >> \"$2\"; rmdir \"$1\""])
            .arg("query")
            .arg(guard)
            .arg(&log);
        assert!(query_owner.output(&mut command).unwrap().status.success());
        std::fs::read_to_string(log).unwrap()
    });
    release_tx.send(()).unwrap();
    case.join().unwrap();
    assert_eq!(query.join().unwrap(), "case\nquery\n");
}

#[cfg(trust_std)]
#[test]
fn reader_error_retires_child_and_inherited_group_before_reuse() {
    let _epoch = super::inherited_child::shared_signal_epoch();
    let owner = owner();
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "sleep 30 & echo $!; wait"]).stdout(Stdio::piped());
    let mut descendant = 0;
    let error = owner
        .run_inherited_child(&mut command, |child| {
            let mut line = String::new();
            BufReader::new(child.take_stdout().unwrap()).read_line(&mut line)?;
            descendant = line.trim().parse::<i32>().unwrap();
            Err::<(), _>(io::Error::other("intentional reader failure"))
        })
        .unwrap_err();
    assert!(error.to_string().contains("intentional reader failure"));
    assert!(descendant > 0);
    // Completion requires actual post-reap group absence, not a saved status.
    assert!(
        owner
            .run_inherited_child(&mut Command::new("/usr/bin/true"), |child| {
                child.wait().map(|status| status.success())
            })
            .unwrap()
    );
}

#[cfg(trust_std)]
#[test]
fn panic_retires_group_and_poisoned_borrow_never_reexecutes() {
    let _epoch = super::inherited_child::shared_signal_epoch();
    let owner = owner();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        owner
            .run_inherited_child(Command::new("/bin/sleep").arg("30"), |_| -> io::Result<()> {
                panic!("intentional consumer panic");
            })
            .unwrap();
    }));
    assert!(result.is_err());
    let error =
        owner.run_inherited_child(&mut Command::new("/must/not/execute"), |_| Ok(())).unwrap_err();
    assert!(error.to_string().contains("poisoned serial"));
}

#[cfg(trust_std)]
#[test]
fn external_signal_retires_the_child_and_blocks_later_borrowers() {
    const ISOLATED: &str = "TRUST_PROBE_SIGNAL_COMPLETION";
    let completion = std::env::var_os(ISOLATED);
    if completion.is_none() {
        // Cancellation belongs to the whole process. Exercise it in a fresh
        // process so parallel positive controls keep their own signal epoch.
        let directory = tempfile::tempdir().unwrap();
        let marker = directory.path().join("completed");
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "client::probe_scheduler::inherited_tests::external_signal_retires_the_child_and_blocks_later_borrowers",
                "--nocapture",
            ])
            .env(ISOLATED, &marker)
            .stdout(Stdio::null())
            .spawn()
            .unwrap();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) if std::time::Instant::now() < deadline => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                Ok(None) => {
                    // Only this original, still-unreaped Child is controlled.
                    child.kill().unwrap();
                    child.wait().unwrap();
                    panic!("isolated signal control exceeded its hang detector");
                }
                Err(error) => panic!("isolated signal control lost owning wait: {error}"),
            }
        };
        assert!(status.success(), "isolated signal control failed: {status}");
        assert_eq!(std::fs::read(marker).unwrap(), b"retired");
        return;
    }
    // The raise below reaches every leaseholder in this process; hold the epoch alone.
    let _epoch = super::inherited_child::SIGNAL_EPOCH
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let owner = owner();
    let started = std::time::Instant::now();
    let error = owner
        .run_inherited_child(Command::new("/bin/sleep").arg("30"), |child| {
            // The installed shared handler records cancellation. The watcher must
            // stop/reap our actual group before returning an Interrupted result.
            assert_eq!(unsafe { libc::raise(libc::SIGTERM) }, 0);
            child.wait().map(|_| ())
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::Interrupted);
    assert!(
        started.elapsed() < std::time::Duration::from_secs(5),
        "signal cancellation waited for the original 30-second child"
    );
    let error =
        owner.run_inherited_child(&mut Command::new("/must/not/execute"), |_| Ok(())).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::Interrupted);
    assert_eq!(
        owner.output(&mut Command::new("/must/not/execute")).unwrap_err().kind(),
        io::ErrorKind::Interrupted
    );
    std::fs::write(completion.unwrap(), b"retired").unwrap();
}

#[cfg(trust_std)]
#[test]
fn queued_query_and_case_recheck_interruption_under_the_serial_lock() {
    let (arrived, receivers) = mpsc::channel();
    let mut selected = owner();
    selected.lock_rendezvous = Some(Arc::new(move || arrived.send(()).unwrap()));
    let selected = Arc::new(selected);
    let held = selected.server.lock().unwrap();
    let query_owner = Arc::clone(&selected);
    let query =
        std::thread::spawn(move || query_owner.output(&mut Command::new("/must/not/execute")));
    let case_owner = Arc::clone(&selected);
    let case = std::thread::spawn(move || {
        case_owner.run_inherited_child(&mut Command::new("/must/not/execute"), |_| Ok(()))
    });
    // Both callers have passed their initial check before the current borrower
    // publishes cancellation. The missing program distinguishes a bad launch
    // (NotFound) from the required Interrupted refusal, without another child.
    for _ in 0..2 {
        receivers.recv_timeout(std::time::Duration::from_secs(5)).unwrap();
    }
    selected.interrupted.store(true, std::sync::atomic::Ordering::Release);
    drop(held);
    assert_eq!(query.join().unwrap().unwrap_err().kind(), io::ErrorKind::Interrupted);
    assert_eq!(case.join().unwrap().unwrap_err().kind(), io::ErrorKind::Interrupted);
}
