//! Real descriptor/SCM controls; no fake original scope or Host is constructed.
use std::fs::{self, File, OpenOptions};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
struct Inputs {
    path: PathBuf,
    root: File,
    file: File,
    request: Request,
}
impl Inputs {
    fn new() -> Self {
        // Parallel tests can read one clock microsecond; the sequence keeps each fixture its own.
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "object-source-{}-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        fs::create_dir_all(path.join("src/bootstrap")).unwrap();
        let path = fs::canonicalize(path).unwrap();
        fs::write(path.join("src/bootstrap/native_object.rs"), SOURCE_BYTES).unwrap();
        let root = File::open(&path).unwrap();
        let file = File::open(path.join("src/bootstrap/native_object.rs")).unwrap();
        let mut request = super::super::tests::request();
        request.source_root = path.as_os_str().as_bytes().to_vec();
        request.source_directory = inspect(root.as_fd()).unwrap().identity;
        request.source.path =
            path.join("src/bootstrap/native_object.rs").as_os_str().as_bytes().to_vec();
        let source = file.metadata().unwrap();
        request.source.device = source.dev();
        request.source.inode = source.ino();
        Self { path, root, file, request }
    }
    fn fds(&self) -> [BorrowedFd<'_>; 2] {
        [self.root.as_fd(), self.file.as_fd()]
    }
}
impl Drop for Inputs {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.path).unwrap();
    }
}
#[test]
fn exact_original_source_survives_transfer_without_cursor_or_configuration_mutation() {
    let inputs = Inputs::new();
    assert_eq!(unsafe { libc::lseek(inputs.file.as_raw_fd(), 7, libc::SEEK_SET) }, 7);
    let flags = unsafe { libc::fcntl(inputs.file.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(inputs.file.as_raw_fd(), libc::F_GETFD) };
    let (sender, receiver) = UnixStream::pair().unwrap();
    let mut sender = Channel::new(sender).unwrap();
    let mut receiver = Channel::new(receiver).unwrap();
    send_source(&mut sender, &inputs.request, &inputs.fds(), deadline(), || Ok(())).unwrap();
    let held = receive_source(&mut receiver, &inputs.request, deadline(), || Ok(())).unwrap();
    check_source(&inputs.request, &held.each_ref().map(|fd| fd.as_fd()), deadline()).unwrap();
    assert_eq!(unsafe { libc::lseek(inputs.file.as_raw_fd(), 0, libc::SEEK_CUR) }, 7);
    let mask = libc::O_ACCMODE | libc::O_NONBLOCK | libc::O_APPEND | libc::O_ASYNC;
    assert_eq!(unsafe { libc::fcntl(inputs.file.as_raw_fd(), libc::F_GETFL) } & mask, flags & mask);
    assert_eq!(unsafe { libc::fcntl(inputs.file.as_raw_fd(), libc::F_GETFD) }, local);
}
#[test]
fn changed_bytes_same_size_swapped_file_parent_alias_and_writable_offer_refuse() {
    let inputs = Inputs::new();
    check_source(&inputs.request, &inputs.fds(), deadline()).unwrap();
    let path = inputs.path.join("src/bootstrap/native_object.rs");
    let writable = OpenOptions::new().read(true).write(true).open(&path).unwrap();
    assert!(
        check_source(&inputs.request, &[inputs.root.as_fd(), writable.as_fd()], deadline())
            .is_err()
    );
    assert!(
        check_source(&inputs.request, &[inputs.root.as_fd(), inputs.root.as_fd()], deadline())
            .is_err()
    );
    let mut changed = SOURCE_BYTES.to_vec();
    changed[0] ^= 1;
    fs::write(&path, &changed).unwrap();
    assert!(check_source(&inputs.request, &inputs.fds(), deadline()).is_err());
    fs::write(&path, SOURCE_BYTES).unwrap();
    fs::rename(&path, inputs.path.join("saved.rs")).unwrap();
    fs::write(&path, SOURCE_BYTES).unwrap();
    assert!(check_source(&inputs.request, &inputs.fds(), deadline()).is_err());
    fs::remove_file(&path).unwrap();
    fs::rename(inputs.path.join("saved.rs"), &path).unwrap();
    let bootstrap = inputs.path.join("src/bootstrap");
    fs::rename(&bootstrap, inputs.path.join("saved-bootstrap")).unwrap();
    std::os::unix::fs::symlink(inputs.path.join("saved-bootstrap"), &bootstrap).unwrap();
    assert!(check_source(&inputs.request, &inputs.fds(), deadline()).is_err());
}
#[test]
fn failed_final_check_and_malformed_rights_close_actual_received_flock_prefix() {
    for malformed in [false, true] {
        let inputs = Inputs::new();
        inputs.file.lock().unwrap();
        let competitor = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC)
            .open(inputs.path.join("src/bootstrap/native_object.rs"))
            .unwrap();
        let (sender, receiver) = UnixStream::pair().unwrap();
        let mut receiver = Channel::new(receiver).unwrap();
        jobserver_utils::descriptor_transfer::send(
            &sender,
            &inputs.fds(),
            if malformed { SOURCE_MARKER ^ 1 } else { SOURCE_MARKER },
            deadline(),
        )
        .unwrap();
        let mut calls = 0;
        assert!(
            receive_source(&mut receiver, &inputs.request, deadline(), || {
                calls += 1;
                if calls == 2 {
                    Err(io::Error::other("lost actual original owner"))
                } else {
                    Ok(())
                }
            })
            .is_err()
        );
        assert!(receiver.poisoned());
        let path = inputs.path.clone();
        drop((sender, receiver));
        drop(inputs);
        let until = deadline();
        loop {
            match competitor.try_lock() {
                Ok(()) => break,
                Err(std::fs::TryLockError::WouldBlock) => {
                    assert!(
                        Instant::now() < until,
                        "received source prefix retained flock after failure at {path:?}"
                    );
                    std::thread::sleep(Duration::from_millis(2));
                }
                result => panic!("actual lock observation failed: {result:?}"),
            }
        }
    }
}
#[test]
fn final_native_callback_cannot_extend_original_deadline() {
    let inputs = Inputs::new();
    let (sender, receiver) = UnixStream::pair().unwrap();
    let mut sender = Channel::new(sender).unwrap();
    let mut receiver = Channel::new(receiver).unwrap();
    send_source(&mut sender, &inputs.request, &inputs.fds(), deadline(), || Ok(())).unwrap();
    let until = Instant::now() + Duration::from_millis(20);
    let mut calls = 0;
    let error = receive_source(&mut receiver, &inputs.request, until, || {
        calls += 1;
        if calls == 2 {
            std::thread::sleep(
                until.saturating_duration_since(Instant::now()) + Duration::from_millis(1),
            );
        }
        Ok(())
    })
    .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(receiver.poisoned());
}
