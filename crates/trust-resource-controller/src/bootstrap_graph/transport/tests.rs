//! Actual SCM/description controls; these private pipes/locks grant no Job,
//! protected scope, SDK, producing admission or backend retirement authority.
use std::fs::{self, File, OpenOptions};
use std::io::{Read as _, Write as _};
use std::os::fd::FromRawFd as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
fn channels() -> (Channel, Channel) {
    let (left, right) = UnixStream::pair().unwrap();
    (Channel::new(left).unwrap(), Channel::new(right).unwrap())
}
fn pipe() -> [OwnedFd; 2] {
    let mut fds = [-1; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    let fds = fds.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
    for fd in &fds {
        assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
    }
    fds
}
fn identity(fd: BorrowedFd<'_>) -> FileIdentity {
    inspect(fd).unwrap().0
}
fn request(fds: &[OwnedFd; 2]) -> Enrollment {
    let mut value = super::super::tests::enrollment();
    value.gnu = GnuIdentity::NumericPipe {
        read: identity(fds[0].as_fd()),
        write: identity(fds[1].as_fd()),
    };
    value
}
fn configuration(fd: BorrowedFd<'_>) -> (i32, i32) {
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    assert!(flags >= 0 && local >= 0);
    // Explicit persistent modes, not Darwin's unrelated rights-GC/write bits.
    (flags & (libc::O_ACCMODE | libc::O_NONBLOCK | libc::O_APPEND | libc::O_ASYNC), local)
}
fn actual_eof(read: OwnedFd) {
    let until = deadline();
    loop {
        let mut p = libc::pollfd { fd: read.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        let result = unsafe { libc::poll(&mut p, 1, 10) };
        if result > 0 {
            let mut byte = 0u8;
            assert_eq!(
                unsafe { libc::read(read.as_raw_fd(), (&mut byte as *mut u8).cast(), 1) },
                0
            );
            break;
        }
        assert!(result >= 0 || io::Error::last_os_error().kind() == io::ErrorKind::Interrupted);
        assert!(Instant::now() < until, "rejected actual rights retained a writer");
    }
}

#[test]
fn actual_numeric_pair_conserves_one_inventory_and_preserves_source_configuration() {
    let originals = pipe();
    let request = request(&originals);
    let before = originals.each_ref().map(|fd| configuration(fd.as_fd()));
    let (mut sender, mut receiver) = channels();
    send_gnu(&mut sender, &request, &originals.each_ref().map(AsFd::as_fd), deadline(), || Ok(()))
        .unwrap();
    let received = receive_gnu(&mut receiver, &request, deadline(), || Ok(())).unwrap();
    assert_eq!(before, originals.each_ref().map(|fd| configuration(fd.as_fd())));
    assert_eq!(identity(received[0].as_fd()), identity(originals[0].as_fd()));
    assert_eq!(identity(received[1].as_fd()), identity(originals[1].as_fd()));
    let mut source_write = File::from(originals[1].try_clone().unwrap());
    source_write.write_all(b"T").unwrap();
    let mut received_read = File::from(received[0].try_clone().unwrap());
    let mut byte = [0];
    received_read.read_exact(&mut byte).unwrap();
    assert_eq!(byte, *b"T");
    let mut received_write = File::from(received[1].try_clone().unwrap());
    received_write.write_all(&byte).unwrap();
    File::from(originals[0].try_clone().unwrap()).read_exact(&mut byte).unwrap();
    assert_eq!(byte, *b"T");
    // The same control channel remains live for output/operation attachment.
    sender.send(b"still original", deadline()).unwrap();
    assert_eq!(receiver.receive(deadline()).unwrap(), b"still original");
}

#[test]
fn source_swap_and_duplicate_descriptions_refuse_without_changing_the_pipe() {
    let originals = pipe();
    let value = request(&originals);
    let before = originals.each_ref().map(|fd| configuration(fd.as_fd()));
    assert!(check_gnu(&value, &[originals[1].as_fd(), originals[0].as_fd()]).is_err());
    assert!(check_gnu(&value, &[originals[0].as_fd(), originals[0].as_fd()]).is_err());
    assert_eq!(before, originals.each_ref().map(|fd| configuration(fd.as_fd())));
}

#[test]
fn malformed_marker_and_full_wrong_count_close_every_actual_received_writer() {
    for (count, marker) in
        [(2, OUTPUT_RIGHTS_MARKER), (1, GNU_RIGHTS_MARKER), (3, GNU_RIGHTS_MARKER)]
    {
        let originals = pipe();
        let value = request(&originals);
        let (sender, receiver) = UnixStream::pair().unwrap();
        let fds = (0..count).map(|_| originals[1].as_fd()).collect::<Vec<_>>();
        jobserver_utils::descriptor_transfer::send(&sender, &fds, marker, deadline()).unwrap();
        let mut receiver = Channel::new(receiver).unwrap();
        assert!(receive_gnu(&mut receiver, &value, deadline(), || Ok(())).is_err());
        assert!(receiver.poisoned());
        drop((sender, receiver));
        let [read, write] = originals;
        drop(write);
        actual_eof(read);
    }
}

#[test]
fn failed_final_native_revalidation_closes_received_prefix_and_poison_is_permanent() {
    let originals = pipe();
    let value = request(&originals);
    let (mut sender, mut receiver) = channels();
    send_gnu(&mut sender, &value, &originals.each_ref().map(AsFd::as_fd), deadline(), || Ok(()))
        .unwrap();
    let mut calls = 0;
    let error = receive_gnu(&mut receiver, &value, deadline(), || {
        calls += 1;
        if calls == 2 { Err(io::Error::other("actual original owner unavailable")) } else { Ok(()) }
    })
    .unwrap_err();
    assert!(error.to_string().contains("original owner"));
    assert!(receiver.poisoned());
    assert!(receiver.receive(deadline()).is_err());
    drop((sender, receiver));
    let [read, write] = originals;
    drop(write);
    actual_eof(read);
}

#[test]
fn original_deadline_is_sampled_after_the_last_native_callback() {
    let originals = pipe();
    let value = request(&originals);
    let (mut sender, mut receiver) = channels();
    send_gnu(&mut sender, &value, &originals.each_ref().map(AsFd::as_fd), deadline(), || Ok(()))
        .unwrap();
    let until = Instant::now() + Duration::from_millis(20);
    let mut calls = 0;
    let error = receive_gnu(&mut receiver, &value, until, || {
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

#[test]
fn original_output_lock_stays_held_through_received_copies_without_cursor_changes() {
    let root = std::env::temp_dir().join(format!(
        "bootstrap-output-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
    ));
    fs::create_dir(&root).unwrap();
    let root = fs::canonicalize(root).unwrap();
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    let _cleanup = Cleanup(root.clone());
    let path = root.join("lock");
    let root_file = File::open(&root).unwrap();
    let lock =
        OpenOptions::new().read(true).write(true).create_new(true).mode(0o600).open(&path).unwrap();
    lock.lock().unwrap();
    assert_eq!(unsafe { libc::lseek(lock.as_raw_fd(), 7, libc::SEEK_SET) }, 7);
    let value = OutputAttachment {
        key: super::super::tests::key(),
        root: identity(root_file.as_fd()),
        lock: identity(lock.as_fd()),
    };
    let (mut sender, mut receiver) = channels();
    send_output(&mut sender, &value, &[root_file.as_fd(), lock.as_fd()], deadline(), || Ok(()))
        .unwrap();
    let held = receive_output(&mut receiver, &value, deadline(), || Ok(())).unwrap();
    assert_eq!(unsafe { libc::lseek(lock.as_raw_fd(), 0, libc::SEEK_CUR) }, 7);
    assert!(check_output(&value, &[lock.as_fd(), root_file.as_fd()]).is_err());
    let competitor = OpenOptions::new().read(true).write(true).open(path).unwrap();
    assert!(matches!(competitor.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    drop((root_file, lock));
    assert!(matches!(competitor.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    drop(held);
    let until = deadline();
    loop {
        match competitor.try_lock() {
            Ok(()) => break,
            Err(std::fs::TryLockError::WouldBlock) => {
                assert!(Instant::now() < until, "final actual copy stayed held");
                std::thread::sleep(Duration::from_millis(1));
            }
            error => panic!("actual lock observation failed: {error:?}"),
        }
    }
}

#[test]
fn actual_named_fifo_retains_original_descriptions_but_refuses_a_replaced_namespace() {
    let directory = std::env::temp_dir().join(format!(
        "bootstrap-gnu-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
    ));
    fs::create_dir(&directory).unwrap();
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    let _cleanup = Cleanup(directory.clone());
    let path = directory.join("gnu");
    let encoded = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(encoded.as_ptr(), 0o600) }, 0);
    let control = OpenOptions::new()
        .read(true)
        .write(true)
        .custom_flags(libc::O_NONBLOCK)
        .open(&path)
        .unwrap();
    let read = OpenOptions::new().read(true).open(&path).unwrap();
    let mut write = OpenOptions::new().write(true).open(&path).unwrap();
    assert_eq!(unsafe { libc::fcntl(read.as_raw_fd(), libc::F_GETFL) } & libc::O_NONBLOCK, 0);
    assert_eq!(unsafe { libc::fcntl(write.as_raw_fd(), libc::F_GETFL) } & libc::O_NONBLOCK, 0);
    assert_ne!(unsafe { libc::fcntl(control.as_raw_fd(), libc::F_GETFL) } & libc::O_NONBLOCK, 0);
    let backing = identity(read.as_fd());
    let mut value = super::super::tests::enrollment();
    value.gnu = GnuIdentity::NamedFifo { path: path.as_os_str().as_bytes().to_vec(), backing };
    let before = [configuration(read.as_fd()), configuration(write.as_fd())];
    let (mut sender, mut receiver) = channels();
    send_gnu(&mut sender, &value, &[read.as_fd(), write.as_fd()], deadline(), || Ok(())).unwrap();
    let held = receive_gnu(&mut receiver, &value, deadline(), || Ok(())).unwrap();
    assert_eq!(before, [configuration(read.as_fd()), configuration(write.as_fd())]);
    write.write_all(b"N").unwrap();
    let mut byte = [0];
    File::from(held[0].try_clone().unwrap()).read_exact(&mut byte).unwrap();
    assert_eq!(byte, *b"N");
    fs::rename(&path, directory.join("original-gnu")).unwrap();
    fs::write(&path, b"replacement is not scheduling transport").unwrap();
    assert!(check_gnu(&value, &held.each_ref().map(AsFd::as_fd)).is_err());
    assert_eq!(identity(held[0].as_fd()), backing);
    assert_eq!(identity(read.as_fd()), backing);
}
