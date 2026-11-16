use std::os::fd::{AsFd, IntoRawFd};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;

#[test]
fn protected_keeper_receive_keeps_original_lock_and_closes_all_malformed_rights() {
    const TEST: &str = "client::workload::tests::protected_keeper_receive_keeps_original_lock_and_closes_all_malformed_rights";
    if isolated_process(TEST) {
        return;
    }
    for marker in [host::keeper::ORIGINALS_MARKER, host::keeper::ORIGINALS_MARKER ^ 1] {
        let root = root();
        let path = root.join("pending-original");
        let original = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        original.lock().unwrap();
        let (sender, receiver) = UnixStream::pair().unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        jobserver_utils::descriptor_transfer::send(&sender, &[original.as_fd()], marker, deadline)
            .unwrap();
        let received = receive_protected_marked::<1>(
            &Channel::new(receiver).unwrap(),
            host::keeper::ORIGINALS_MARKER,
            deadline,
        );
        let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
        drop(original);
        if marker == host::keeper::ORIGINALS_MARKER {
            let received = received.unwrap();
            assert!(probe.try_lock().is_err());
            assert_eq!(
                identity(received.get(0).unwrap().as_raw_fd()).unwrap(),
                identity(probe.as_raw_fd()).unwrap()
            );
            drop(received);
        } else {
            assert!(received.is_err());
        }
        probe.try_lock().unwrap();
        drop(probe);
        std::fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn phase_transport_requires_actual_matching_original_fifo_access_modes() {
    // ResourceRuntime's ONE original PrivateFifo is a named FIFO. Darwin
    // anonymous pipe ends have distinct inode observations and cannot satisfy
    // this closed profile merely because both descriptors are FIFO-shaped.
    let root = root();
    let path = root.join("original-fifo");
    use std::os::unix::ffi::OsStrExt as _;
    let cpath = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(cpath.as_ptr(), 0o600) }, 0);
    let read =
        std::fs::OpenOptions::new().read(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
    let write =
        std::fs::OpenOptions::new().write(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
    let observed = fifo_identity(read.as_fd(), libc::O_RDONLY).unwrap();
    assert_eq!(fifo_identity(write.as_fd(), libc::O_WRONLY).unwrap(), observed);
    assert!(fifo_identity(read.as_fd(), libc::O_WRONLY).is_err());
    assert!(fifo_identity(write.as_fd(), libc::O_RDONLY).is_err());
    let (other, _) = std::io::pipe().unwrap();
    assert_ne!(fifo_identity(other.as_fd(), libc::O_RDONLY).unwrap(), observed);
    assert!(
        fifo_identity(std::fs::File::open("/dev/null").unwrap().as_fd(), libc::O_RDONLY).is_err()
    );
    drop((read, write));
    std::fs::remove_dir_all(root).unwrap();
}

pub(super) fn root() -> std::path::PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "workload-originals-{}-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
    root
}

pub(super) fn isolated_process(test: &str) -> bool {
    const ROLE: &str = "TRUST_WORKLOAD_ORIGINAL_FD_TEST";
    if std::env::var(ROLE).as_deref() == Ok(test) {
        return false;
    }
    // These controls assert final close and numeric-fd nonreuse inside ONE
    // process. A parallel SIGPIPE fork/exec control can temporarily inherit a
    // description between Darwin recvmsg and CLOEXEC, or before kernel exec
    // closes it. Run the unchanged real SCM/lock assertions after that child
    // has executed, with no unrelated descriptor births in its test process.
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture"])
        .env(ROLE, test)
        .output()
        .unwrap();
    assert!(output.status.success(), "original native FD control failed: {output:?}");
    true
}

#[test]
fn received_original_keeps_actual_guard_when_independent_offered_file_is_unlocked() {
    if isolated_process(
        "client::workload::tests::received_original_keeps_actual_guard_when_independent_offered_file_is_unlocked",
    ) {
        return;
    }
    let root = root();
    let path = root.join("slot");
    let original = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&path)
        .unwrap();
    original.lock().unwrap();
    let offered = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
    // SAFETY: duplicate this owned independent file into the real bootstrap
    // range; a unit-test runner can initially allocate its file below fd6.
    let raw = unsafe { libc::fcntl(offered.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 6) };
    assert!(raw >= 6);
    // SAFETY: exactly the fresh successful syscall result becomes owned here.
    let mapped = unsafe { OwnedFd::from_raw_fd(raw) };
    drop(offered);
    let raw = mapped.into_raw_fd(); // Transfer the actual mapped slot, once.
    let pending = snapshot(&raw.to_string()).unwrap();
    // SAFETY: the test owns every descriptor and runs no intervening importer.
    let early = unsafe { take_owned_cpu_set(pending) }.unwrap();
    let (sender, receiver) = UnixStream::pair().unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    jobserver_utils::descriptor_transfer::send(
        &sender,
        &[original.as_fd()],
        host::CPU_SET_MARKER,
        deadline,
    )
    .unwrap();
    let actual = receive(&Channel::new(receiver).unwrap(), 1, deadline).unwrap();
    drop(early);
    // SAFETY: an observation only; no opens run after early ownership closes.
    assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFD) }, -1);
    drop(original);
    let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
    assert!(matches!(probe.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    drop(actual);
    probe.try_lock().unwrap();
    drop(probe);
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn rejected_original_transfer_closes_received_rights_and_never_acquires_offered_file() {
    if isolated_process(
        "client::workload::tests::rejected_original_transfer_closes_received_rights_and_never_acquires_offered_file",
    ) {
        return;
    }
    for (marker, count) in [(host::CPU_SET_MARKER ^ 1, 1), (host::CPU_SET_MARKER, 2)] {
        let root = root();
        let path = root.join("slot");
        let original = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        original.lock().unwrap();
        let (sender, receiver) = UnixStream::pair().unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        jobserver_utils::descriptor_transfer::send(&sender, &[original.as_fd()], marker, deadline)
            .unwrap();
        drop(original);
        assert!(receive(&Channel::new(receiver).unwrap(), count, deadline).is_err());
        let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
        probe.try_lock().unwrap();
        drop(probe);
        std::fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn early_locator_is_bounded_unique_canonical_and_never_an_original_lease_constructor() {
    for bad in ["", "5", "06", "-1", "999999999999999999999999", "6,6", "6,"] {
        assert!(snapshot(bad).is_err(), "{bad}");
    }
    assert!(snapshot(&"6,".repeat(host::MAX_CPU_SET + 1)).is_err());
    let (sender, receiver) = UnixStream::pair().unwrap();
    drop(sender);
    assert!(
        receive(&Channel::new(receiver).unwrap(), 1, Instant::now() + Duration::from_secs(60))
            .is_err()
    );
}
