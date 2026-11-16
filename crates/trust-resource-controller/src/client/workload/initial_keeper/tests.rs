use std::os::fd::AsFd as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::time::Duration;

use super::*;

#[test]
fn expired_initial_capture_closes_both_originals_without_importing_them() {
    const TEST: &str = "client::workload::initial_keeper::tests::expired_initial_capture_closes_both_originals_without_importing_them";
    if super::super::tests::isolated_process(TEST) {
        return;
    }
    use std::os::fd::IntoRawFd as _;
    let root = super::super::tests::root();
    let paths = ["expired-shadow", "expired-memory"].map(|name| root.join(name));
    let files = paths.map(|path| {
        std::fs::OpenOptions::new()
            .create_new(true)
            .read(true)
            .write(true)
            .mode(0o600)
            .open(path)
            .unwrap()
    });
    let originals = files.map(|file| {
        let expected = identity(file.as_raw_fd()).unwrap();
        (file.into_raw_fd(), expected)
    });
    let descriptors = originals.map(|(fd, _)| fd);
    let pending = PendingInitialKeeper { native: FileIdentity { device: 1, inode: 1 }, originals };
    // SAFETY: this isolated, single-threaded process transfers both actual
    // owned descriptions; no importer, callback or thread can reuse them.
    assert!(
        unsafe { capture_initial_keeper(pending, Instant::now() - Duration::from_secs(1)) }
            .is_err()
    );
    for descriptor in descriptors {
        // SAFETY: observing a numeric descriptor cannot create ownership.
        assert_eq!(unsafe { libc::fcntl(descriptor, libc::F_GETFD) }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EBADF));
    }
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn initial_keeper_retains_real_originals_and_rejects_wrong_identity_and_memory_access() {
    const TEST: &str = "client::workload::initial_keeper::tests::initial_keeper_retains_real_originals_and_rejects_wrong_identity_and_memory_access";
    if super::super::tests::isolated_process(TEST) {
        return;
    }
    let root = super::super::tests::root();
    let paths = ["native", "shadow", "memory"].map(|name| root.join(name));
    for path in &paths {
        std::fs::OpenOptions::new().create_new(true).write(true).mode(0o600).open(path).unwrap();
    }
    let native = File::open(&paths[0]).unwrap();
    let shadow = File::open(&paths[1]).unwrap();
    let memory = File::open(&paths[2]).unwrap();
    shadow.lock().unwrap();
    memory.lock().unwrap();
    let binding = host::keeper::Request {
        root_attempt: [1; 16],
        invocation_sha256: [2; 32],
        phase: [3; 16],
        nonce: [4; 16],
        native_slot: 0,
        native: identity(native.as_raw_fd()).unwrap(),
        shadow: identity(shadow.as_raw_fd()).unwrap(),
        memory_guard: identity(memory.as_raw_fd()).unwrap(),
        memory_epoch: [5; 16],
        memory_scope_sha256: [6; 32],
    };
    let deadline = Instant::now() + Duration::from_secs(30);
    let originals = ProtectedOriginals::capture(deadline, |capture| {
        capture.push(shadow.as_fd().try_clone_to_owned()?)?;
        capture.push(memory.as_fd().try_clone_to_owned()?)
    })
    .unwrap();
    let early = EarlyInitialKeeper { native: binding.native, originals };
    early.check_binding(&binding).unwrap();
    let mut foreign = binding;
    foreign.memory_guard.inode += 1;
    assert!(early.check_binding(&foreign).is_err());
    foreign = binding;
    foreign.native.inode += 1;
    assert!(early.check_binding(&foreign).is_err());
    let writable = std::fs::OpenOptions::new().read(true).write(true).open(&paths[2]).unwrap();
    assert!(readonly_memory(writable.as_raw_fd()).is_err());
    drop((shadow, memory));
    let shadow_probe = File::open(&paths[1]).unwrap();
    let memory_probe = File::open(&paths[2]).unwrap();
    assert!(shadow_probe.try_lock().is_err());
    assert!(memory_probe.try_lock().is_err());
    drop(early);
    shadow_probe.try_lock().unwrap();
    memory_probe.try_lock().unwrap();
    drop((native, writable, shadow_probe, memory_probe));
    std::fs::remove_dir_all(root).unwrap();
}
