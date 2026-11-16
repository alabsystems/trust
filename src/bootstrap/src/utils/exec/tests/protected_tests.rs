//! Actual executor consumers. Each permanent installer runs in its own process
//! so normal parallel Bootstrap tests keep their original standalone state.

use std::os::fd::AsRawFd;

use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};
use jobserver_utils::Jobserver;

use super::*;

const NAME: &str = "utils::exec::protected_tests::actual_protected_execution_paths";
const ROLE: &str = "TRUST_PROTECTED_EXEC_TEST_ROLE";

fn identity(fd: i32) -> String {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    assert_eq!(unsafe { libc::fstat(fd, stat.as_mut_ptr()) }, 0);
    let stat = unsafe { stat.assume_init() };
    assert_eq!(stat.st_mode & libc::S_IFMT, libc::S_IFIFO);
    format!("{}:{}", stat.st_dev, stat.st_ino)
}

fn work(deadline: Instant) -> (tempfile::TempDir, ProtectedWorkScope) {
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "actual protected Bootstrap executor controls".into(),
        contract: "native local child/scheduler only, no Host/SDK/release authority".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    (root, ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), deadline).unwrap())
}

fn command(server: &Jobserver) -> BootstrapCommand {
    let mut command = BootstrapCommand::new(std::env::current_exe().unwrap());
    command.args(["--exact", NAME, "--nocapture"]);
    command.env(ROLE, "leaf");
    let expected = server
        .pipe_descriptors()
        .unwrap()
        .iter()
        .map(|fd| identity(fd.as_raw_fd()))
        .collect::<Vec<_>>()
        .join(",");
    command.env("TRUST_PROTECTED_EXEC_EXPECTED_FDS", expected);
    // Mirror actual Cargo's environment processing; only the SAME captured
    // owner may restore these aliases after this point.
    command.env_remove("MAKEFLAGS").env_remove("MFLAGS").env_remove("CARGO_MAKEFLAGS");
    command
}

fn prefix(output: &CommandOutput) {
    assert!(output.is_failure(), "local exit must not claim resource completion");
    assert!(output.status().is_none());
    assert!(output.observed_child_status().unwrap().success());
    assert!(output.stdout.as_ref().unwrap().windows(3).any(|s| s == [0, 255, 10]));
    assert!(output.stderr.as_ref().unwrap().windows(3).any(|s| s == [9, 254, 10]));
}

fn isolated(role: &str) {
    isolated_at(role, NAME);
}

fn isolated_at(role: &str, name: &str) {
    let mut stdout = tempfile::tempfile().unwrap();
    let mut stderr = tempfile::tempfile().unwrap();
    let mut child =
        crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", name, "--nocapture"])
            .env(ROLE, role)
            .stdout(stdout.try_clone().unwrap())
            .stderr(stderr.try_clone().unwrap())
            .spawn()
            .unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            // This original unreaped Child anchors its PID. There is one wait
            // owner; no numeric signal follows a successful reap.
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("original one-minute native actor deadline: {role}");
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    use std::io::Seek;
    stdout.rewind().unwrap();
    stderr.rewind().unwrap();
    let mut out = Vec::new();
    let mut err = Vec::new();
    stdout.read_to_end(&mut out).unwrap();
    stderr.read_to_end(&mut err).unwrap();
    assert!(status.success(), "actor {role}: stdout={out:?}, stderr={err:?}");
}

#[test]
fn actual_protected_execution_paths() {
    let Ok(role) = std::env::var(ROLE) else {
        isolated("complete");
        isolated("reentrant");
        isolated("streaming");
        return;
    };
    if role == "leaf" {
        let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
        assert_eq!(std::env::var("MAKEFLAGS").unwrap(), flags);
        assert_eq!(std::env::var("MFLAGS").unwrap(), flags);
        let pair = flags
            .split_ascii_whitespace()
            .find_map(|word| word.strip_prefix("--jobserver-auth="))
            .unwrap();
        let actual =
            pair.split(',').map(|n| identity(n.parse().unwrap())).collect::<Vec<_>>().join(",");
        assert_eq!(actual, std::env::var("TRUST_PROTECTED_EXEC_EXPECTED_FDS").unwrap());
        std::io::stdout().write_all(&[0, 255, 10]).unwrap();
        std::io::stderr().write_all(&[9, 254, 10]).unwrap();
        return;
    }
    // A deliberately owned component fixture, not machine/SDK admission.
    let server = Jobserver::new(2).unwrap();
    let _paid = server.client().acquire().unwrap();
    super::super::metadata_scheduler::install_test_original(server.clone()).unwrap();
    // This ctx intentionally predates installation, as Config.exec_ctx does.
    let old = ExecutionContext::new(0, false);
    let deadline = Instant::now()
        + if role == "reentrant" { Duration::from_secs(1) } else { Duration::from_secs(20) };
    let (_root, work) = work(deadline);
    install_protected_scope(work.dispatcher()).unwrap();
    if role == "streaming" {
        let mut streaming = command(&server);
        let mut stream =
            old.stream(&mut streaming, OutputMode::Capture, OutputMode::Capture).unwrap();
        let mut stdout = stream.stdout.take().unwrap();
        let mut stderr = stream.stderr.take().unwrap();
        let dispatch = work.dispatcher();
        let out = dispatch
            .register_worker()
            .unwrap()
            .spawn(std::thread::Builder::new(), move || {
                let mut bytes = Vec::new();
                stdout.read_to_end(&mut bytes).unwrap();
                bytes
            })
            .unwrap();
        let err = dispatch
            .register_worker()
            .unwrap()
            .spawn(std::thread::Builder::new(), move || {
                let mut bytes = Vec::new();
                stderr.read_to_end(&mut bytes).unwrap();
                bytes
            })
            .unwrap();
        assert!(out.join().unwrap().windows(3).any(|s| s == [0, 255, 10]));
        assert!(err.join().unwrap().windows(3).any(|s| s == [9, 254, 10]));
        assert!(
            stream.wait(&old).is_err(),
            "stream EOF cannot return execution without retirement"
        );
        assert!(work.seal().join().is_err());
        assert_eq!(server.client().available().unwrap(), 1);
        return;
    }
    if role == "reentrant" {
        let mut streaming = command(&server);
        let stream = old.stream(&mut streaming, OutputMode::Capture, OutputMode::Capture).unwrap();
        let mut query = command(&server).allow_failure();
        query.metadata_scheduler();
        let result = query.run_capture(&old);
        assert!(
            result.status().is_none(),
            "reentrant metadata must refuse without another implicit borrower"
        );
        assert!(stream.wait(&old).is_err());
        assert!(work.seal().join().is_err());
        return;
    }
    let mut first = command(&server).allow_failure();
    first.cached();
    let mut second = command(&server).allow_failure();
    let first_data = first.start_capture(&old);
    // The first retains actual child output but cannot return implicit
    // execution. The second must refuse before delivery, without self-blocking.
    let second_data = second.start_capture(&old);
    prefix(&first_data.wait_for_output(&old));
    let second = second_data.wait_for_output(&old);
    assert!(second.is_failure());
    assert!(second.observed_child_status().is_none());
    let mut query = command(&server).allow_failure();
    query.metadata_scheduler();
    let query = query.run_capture(&old);
    assert!(query.is_failure());
    assert!(query.observed_child_status().is_none());
    assert_eq!(
        server.client().available().unwrap(),
        1,
        "original extras were not replenished or acquired"
    );
    assert!(work.seal().join().is_err(), "unresolved execution cannot close the graph");
    first = first.allow_failure();
    assert!(
        first.run_capture(&old).status().is_none(),
        "cached output must not bypass the permanent seal"
    );
    let mut fresh = command(&server).allow_failure();
    assert!(fresh.run_capture(ExecutionContext::new(0, false)).status().is_none());
}

// A local owning wait and both stream EOFs deliberately remain weaker than
// original protected-work retirement. This must never return the implicit CPU.
#[test]
fn actual_live_descendant_cannot_return_producer() {
    use std::fs::{File, OpenOptions};
    use std::os::fd::FromRawFd;

    const DESCENDANT: &str =
        "utils::exec::protected_tests::actual_live_descendant_cannot_return_producer";
    let Ok(role) = std::env::var(ROLE) else {
        isolated_at("descendant-controller", DESCENDANT);
        return;
    };
    if role == "live-descendant" {
        let held = OpenOptions::new()
            .read(true)
            .write(true)
            .open(std::env::var_os("TRUST_PROTECTED_DESCENDANT_LOCK").unwrap())
            .unwrap();
        assert_eq!(unsafe { libc::flock(held.as_raw_fd(), libc::LOCK_EX) }, 0);
        let mut input = [0; 16];
        loop {
            let count = std::io::stdin().read(&mut input).unwrap();
            if count == 0 {
                break;
            }
            let mut value = 0u64;
            for item in 0..100_000u64 {
                value = std::hint::black_box(value.wrapping_add(item));
            }
            std::hint::black_box(value);
        }
        // Only fixture cleanup: no native Host/root/CPU authority comes from
        // this flock or the stop pipe. No PID is signalled or imported.
        drop(held);
        return;
    }
    if role == "descendant-leader" {
        // This escaped fixture observes only its local lock/pipe lifecycle; it
        // does not borrow the leader's imported query transport.
        let descendant =
            crate::test_entry::synthetic_observer(Command::new(std::env::current_exe().unwrap()))
                .args(["--exact", DESCENDANT, "--nocapture"])
                .env(ROLE, "live-descendant")
                .stdin(Stdio::inherit())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .unwrap();
        drop(descendant); // ordinary allowed process behavior; it stays alive
        return;
    }
    assert_eq!(role, "descendant-controller");
    let original = Jobserver::new(2).unwrap();
    super::super::metadata_scheduler::install_test_original(original).unwrap();
    let (_root, work) = work(Instant::now() + Duration::from_secs(20));
    install_protected_scope(work.dispatcher()).unwrap();
    let lock = tempfile::NamedTempFile::new().unwrap();
    let mut fds = [-1; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    for fd in fds {
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
    }
    let read = unsafe { File::from_raw_fd(fds[0]) };
    let mut stop = unsafe { File::from_raw_fd(fds[1]) };
    let mut leader = BootstrapCommand::new(std::env::current_exe().unwrap()).allow_failure();
    leader
        .args(["--exact", DESCENDANT, "--nocapture"])
        .env(ROLE, "descendant-leader")
        .env("TRUST_PROTECTED_DESCENDANT_LOCK", lock.path())
        .stdin(Stdio::from(read));
    let result = leader.run_capture(ExecutionContext::new(0, false));
    let busy = || {
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
            assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) }, 0);
            false
        } else {
            assert_eq!(io::Error::last_os_error().kind(), io::ErrorKind::WouldBlock);
            true
        }
    };
    let readiness = Instant::now() + Duration::from_secs(10);
    while !busy() {
        assert!(Instant::now() < readiness, "actual descendant never retained its fixture guard");
        std::thread::sleep(Duration::from_millis(2));
    }
    stop.write_all(b"work").unwrap();
    assert!(busy(), "descendant must remain live after direct-child wait and EOF");
    let mut next = BootstrapCommand::new("/usr/bin/true").allow_failure();
    let next = next.run_capture(ExecutionContext::new(0, false));
    let local = work.seal().join();
    assert!(busy(), "local waits cannot retire a live descendant");
    let incorrectly_returned = result.is_success();
    // End the actual fixture through its original input description. Closing
    // this writer cannot release any production loan/custody/withheld record.
    drop(stop);
    let cleanup = Instant::now() + Duration::from_secs(10);
    while busy() {
        assert!(Instant::now() < cleanup, "actual descendant did not finish fixture cleanup");
        std::thread::sleep(Duration::from_millis(2));
    }
    assert!(local.is_err(), "missing original retirement must poison graph completion");
    assert!(next.observed_child_status().is_none(), "no next implicit child may execute");
    assert!(result.observed_child_status().unwrap().success(), "retain actual child exit data");
    assert!(
        !incorrectly_returned,
        "GNU producer returned from local child reap/EOF while a closed-stream descendant remained live"
    );
}
