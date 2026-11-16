//! Real Unix SCM and caller checks of the production exchange helper. Packet
//! fixtures are DATA; no live Root, Host, protected Graph, Seed or SDK is made.
use std::fs::{self, File, OpenOptions};
use std::os::fd::{AsFd, AsRawFd};
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;
use crate::FileIdentity;

struct Files {
    directory: File,
    lock: File,
    root: PathBuf,
}
impl Drop for Files {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}
fn files() -> Files {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "preparation-output-{}-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    fs::create_dir(&root).unwrap();
    let directory = File::open(&root).unwrap();
    let lock =
        OpenOptions::new().create_new(true).read(true).write(true).open(root.join("lock")).unwrap();
    lock.lock().unwrap();
    Files { directory, lock, root }
}
fn request(files: &Files) -> PreparationOutputAttachment {
    let id = |file: &File| {
        let m = file.metadata().unwrap();
        FileIdentity { device: m.dev(), inode: m.ino() }
    };
    PreparationOutputAttachment {
        key: crate::bootstrap_graph::query::tests::request().key,
        root: id(&files.directory),
        lock: id(&files.lock),
    }
}
fn reply(
    request: &PreparationOutputAttachment,
    context: &ContextReply,
    prepared: bool,
    remaining_input_ns: u64,
) -> Vec<u8> {
    let attachment_sha256 = Sha256::digest(request.binding_preimage().unwrap()).into();
    if prepared {
        PreparationOutputReply::Prepared {
            request: request.clone(),
            attachment_sha256,
            remaining_input_ns,
            context: context.clone(),
        }
    } else {
        PreparationOutputReply::Custodied {
            request: request.clone(),
            attachment_sha256,
            remaining_input_ns,
            context: context.clone(),
        }
    }
    .encode()
    .unwrap()
}

#[test]
fn actual_output_scm_keeps_lock_cursor_and_same_source_channel_after_custody() {
    let files = files();
    let request = request(&files);
    let context = crate::bootstrap_graph::test_context();
    let (client, server) = UnixStream::pair().unwrap();
    let until = Instant::now() + Duration::from_secs(60);
    let (release, retain) = std::sync::mpsc::sync_channel(0);
    let observed = request.clone();
    let expected = context.clone();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        assert!(
            PreparationOutputAttachment::decode(&channel.receive(until).unwrap()).unwrap()
                == observed
        );
        channel.send(&reply(&observed, &expected, true, 50_000_000_000), until).unwrap();
        let delivered =
            transport::receive_preparation_output_delivery(&mut channel, until).unwrap();
        let mut held = Vec::new();
        assert!(delivered.into_parts(&mut held));
        transport::check_output(&observed.physical_binding(), &[held[0].as_fd(), held[1].as_fd()])
            .unwrap();
        channel.send(&reply(&observed, &expected, false, 40_000_000_000), until).unwrap();
        assert_eq!(channel.receive(until).unwrap(), b"next source/configuration message");
        channel.send(b"same handler retained", until).unwrap();
        retain.recv().unwrap(); // actual received lock remains held until explicit fixture teardown
    });
    let mut channel = Channel::new(client).unwrap();
    let mut attempt = Attempt::new(request, until).unwrap();
    let flags = unsafe { libc::fcntl(files.lock.as_raw_fd(), libc::F_GETFL) };
    assert_eq!(unsafe { libc::lseek(files.lock.as_raw_fd(), 7, libc::SEEK_SET) }, 7);
    let mut calls = 0;
    exchange(
        &mut channel,
        &mut attempt,
        &context,
        &[files.directory.as_fd(), files.lock.as_fd()],
        |_| {
            calls += 1;
            Ok(())
        },
    )
    .unwrap();
    assert!(calls >= 5);
    assert!(attempt.deadline < until);
    assert_eq!(unsafe { libc::fcntl(files.lock.as_raw_fd(), libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::lseek(files.lock.as_raw_fd(), 0, libc::SEEK_CUR) }, 7);
    let competitor =
        OpenOptions::new().read(true).write(true).open(files.root.join("lock")).unwrap();
    assert!(matches!(competitor.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    channel.send(b"next source/configuration message", attempt.deadline).unwrap();
    assert_eq!(channel.receive(attempt.deadline).unwrap(), b"same handler retained");
    release.send(()).unwrap();
    peer.join().unwrap();
    assert!(
        exchange(
            &mut channel,
            &mut attempt,
            &context,
            &[files.directory.as_fd(), files.lock.as_fd()],
            |_| Ok(())
        )
        .is_err(),
        "custody is one-use"
    );
}

#[test]
fn observed_context_operation_order_and_deadline_refusals_are_sticky() {
    let files = files();
    let original = request(&files);
    let context = crate::bootstrap_graph::test_context();
    for wrong in 0..4 {
        let until = Instant::now() + Duration::from_secs(60);
        let mut attempt = Attempt::new(original.clone(), until).unwrap();
        let mut request = original.clone();
        let mut observed = context.clone();
        if wrong == 0 {
            request.key.operation[0] ^= 1;
        }
        if wrong == 1 {
            observed.context.host.push_str("-changed");
        }
        if wrong == 3 {
            attempt.started = Instant::now() - Duration::from_secs(2);
        }
        let bytes =
            reply(&request, &observed, wrong != 2, if wrong == 3 { 1 } else { 1_000_000_000 });
        assert!(attempt.observe(&bytes, &context).is_err());
        assert!(
            attempt.observe(&reply(&original, &context, true, 30_000_000_000), &context).is_err()
        );
        assert!(attempt.check(until).is_err());
    }
}

#[test]
fn failed_actual_caller_check_poison_keeps_original_lock_and_prohibits_resend() {
    let files = files();
    let request = request(&files);
    let context = crate::bootstrap_graph::test_context();
    let until = Instant::now() + Duration::from_secs(60);
    let (client, server) = UnixStream::pair().unwrap();
    let mut channel = Channel::new(client).unwrap();
    let mut attempt = Attempt::new(request, until).unwrap();
    let result = exchange(
        &mut channel,
        &mut attempt,
        &context,
        &[files.directory.as_fd(), files.lock.as_fd()],
        |_| Err(io::Error::other("actual caller revoked")),
    );
    assert!(result.unwrap_err().to_string().contains("caller revoked"));
    assert!(channel.poisoned());
    assert!(attempt.check(until).is_err());
    let competitor =
        OpenOptions::new().read(true).write(true).open(files.root.join("lock")).unwrap();
    assert!(matches!(competitor.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    drop(server);
}
