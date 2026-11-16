//! Actual directory SCM and canonical packet controls, not an authenticated
//! Root, native cache lock, configured bundle, Seed or SDK fixture.
use std::fs;
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;
use crate::descriptors::DescriptorBudget;

struct Directory {
    home: Arc<AdmittedDirectory>,
    path: PathBuf,
}
impl Drop for Directory {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.path).unwrap();
    }
}
fn directory(end: Instant) -> Directory {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "preparation-home-{}-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
    let home = budget.capture_directory(&path, end).unwrap();
    Directory { home, path }
}
fn request(home: &AdmittedDirectory) -> Request {
    let mut request = crate::bootstrap_graph::offline_preparation::test_request();
    request.cargo_home = home.path().as_os_str().as_bytes().to_vec();
    request.budget_ns = 50_000_000_000;
    request
}
fn reply(
    request: &Request,
    context: &ContextReply,
    prepared: bool,
    remaining_input_ns: u64,
) -> Vec<u8> {
    let request_sha256 = Sha256::digest(request.binding_preimage().unwrap()).into();
    if prepared {
        PreparationCacheReply::Prepared {
            request: request.clone(),
            request_sha256,
            remaining_input_ns,
            context: context.clone(),
        }
    } else {
        PreparationCacheReply::Custodied {
            request: request.clone(),
            request_sha256,
            remaining_input_ns,
            context: context.clone(),
        }
    }
    .encode()
    .unwrap()
}

#[test]
fn actual_original_directory_crosses_once_and_same_source_channel_continues() {
    let end = Instant::now() + Duration::from_secs(60);
    let directory = directory(end);
    let request = request(&directory.home);
    let context = crate::bootstrap_graph::test_context();
    let expected = request.clone();
    let observed_context = context.clone();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        assert!(Request::decode(&channel.receive(end).unwrap()).unwrap() == expected);
        channel.send(&reply(&expected, &observed_context, true, 40_000_000_000), end).unwrap();
        let delivered = transport::receive_preparation_cache_directory(&mut channel, end).unwrap();
        let mut originals = Vec::new();
        assert!(delivered.into_parts(&mut originals));
        assert_eq!(originals.len(), 1);
        let file = fs::File::from(originals.pop().unwrap());
        let meta = file.metadata().unwrap();
        let named = fs::metadata(std::ffi::OsStr::from_bytes(&expected.cargo_home)).unwrap();
        assert!(meta.is_dir());
        assert_eq!((meta.dev(), meta.ino()), (named.dev(), named.ino()));
        channel.send(&reply(&expected, &observed_context, false, 30_000_000_000), end).unwrap();
        assert_eq!(channel.receive(end).unwrap(), b"first later Configuration message");
        channel.send(b"same source handler", end).unwrap();
        file // physical original only, never converted to a cache-lock owner
    });
    let fd = directory.home.descriptor(end).unwrap();
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let cursor = unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_CUR) };
    let mut attempt = Attempt::retain(Arc::clone(&directory.home), end);
    attempt.freeze(request).unwrap();
    let mut channel = Channel::new(client).unwrap();
    exchange(&mut channel, &mut attempt, &context, |_| Ok(())).unwrap();
    assert!(attempt.end < end);
    assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_CUR) }, cursor);
    channel.send(b"first later Configuration message", attempt.end).unwrap();
    assert_eq!(channel.receive(attempt.end).unwrap(), b"same source handler");
    let received = peer.join().unwrap();
    assert!(received.metadata().unwrap().is_dir());
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    assert!(channel.poisoned());
}

#[test]
fn whole_request_context_order_and_expired_bounds_cannot_be_repaired_by_later_reply() {
    let end = Instant::now() + Duration::from_secs(60);
    let directory = directory(end);
    let original = request(&directory.home);
    let context = crate::bootstrap_graph::test_context();
    for kind in 0..4 {
        let mut attempt = Attempt::retain(Arc::clone(&directory.home), end);
        attempt.freeze(original.clone()).unwrap();
        let mut request = original.clone();
        let mut observed = context.clone();
        if kind == 0 {
            request.configured_targo.extend(b"-retargeted");
        }
        if kind == 1 {
            observed.context.host.push_str("-foreign");
        }
        if kind == 3 {
            attempt.started = Instant::now() - Duration::from_secs(2);
        }
        assert!(
            attempt
                .observe(
                    &reply(
                        &request,
                        &observed,
                        kind != 2,
                        if kind == 3 { 1 } else { 20_000_000_000 }
                    ),
                    &context
                )
                .is_err()
        );
        assert!(
            attempt.observe(&reply(&original, &context, true, 20_000_000_000), &context).is_err()
        );
        assert!(attempt.check(end).is_err());
        if kind == 3 {
            assert!(attempt.end < Instant::now());
        }
    }
}

#[test]
fn actual_runtime_veto_leaves_original_retained() {
    let end = Instant::now() + Duration::from_secs(60);
    let directory = directory(end);
    let original = request(&directory.home);
    let context = crate::bootstrap_graph::test_context();
    let mut attempt = Attempt::retain(Arc::clone(&directory.home), end);
    attempt.freeze(original).unwrap();
    let (client, server) = UnixStream::pair().unwrap();
    let mut channel = Channel::new(client).unwrap();
    assert!(
        exchange(&mut channel, &mut attempt, &context, |_| Err(io::Error::other(
            "actual context changed"
        )))
        .is_err()
    );
    assert!(channel.poisoned());
    assert!(attempt.check(end).is_err());
    assert!(directory.home.descriptor(end).is_ok());
    drop(server);
}

#[test]
fn observed_directory_replacement_stays_revoked_after_restoring_its_path() {
    let end = Instant::now() + Duration::from_secs(60);
    let directory = directory(end);
    let original = request(&directory.home);
    let context = crate::bootstrap_graph::test_context();
    let raw = directory.home.descriptor(end).unwrap().as_raw_fd();
    let mut attempt = Attempt::retain(Arc::clone(&directory.home), end);
    attempt.freeze(original.clone()).unwrap();
    let held = directory.path.with_extension("held-original");
    fs::rename(&directory.path, &held).unwrap();
    fs::create_dir(&directory.path).unwrap();
    assert!(attempt.observe(&reply(&original, &context, true, 20_000_000_000), &context).is_err());
    fs::remove_dir(&directory.path).unwrap();
    fs::rename(held, &directory.path).unwrap();
    assert!(directory.home.validate(end).is_err());
    assert!(attempt.observe(&reply(&original, &context, true, 20_000_000_000), &context).is_err());
    assert!(
        unsafe { libc::fcntl(raw, libc::F_GETFD) } >= 0,
        "retained descriptor was not disposed by refusal"
    );
}
