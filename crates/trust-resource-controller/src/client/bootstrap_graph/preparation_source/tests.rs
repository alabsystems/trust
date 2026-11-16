//! Actual sockets/physical directories and canonical equality DATA only. No
//! Host, Root, admitted Graph, semantic source/Seed or native closure fixture.
use std::fs;
use std::os::fd::AsRawFd as _;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use super::*;
use crate::descriptors::DescriptorBudget;

struct Directory {
    path: PathBuf,
    original: Arc<AdmittedDirectory>,
}
impl Drop for Directory {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.path).unwrap();
    }
}
fn directory(end: Instant) -> Directory {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "preparation-source-{}-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    let original =
        DescriptorBudget::for_preparation(1, 0).unwrap().capture_directory(&path, end).unwrap();
    Directory { path, original }
}
fn candidates() -> Vec<ArchiveCandidate> {
    vec![ArchiveCandidate {
        relative: b"bootstrap/trust-stage0/dist/day/seed.tar.xz".to_vec(),
        sha256: [7; 32],
    }]
}
fn attempt(directory: &Directory, end: Instant) -> Attempt {
    use std::os::unix::ffi::OsStrExt as _;
    let mut request = crate::bootstrap_graph::offline_preparation::test_request();
    request.cargo_home = directory.path.as_os_str().as_bytes().to_vec();
    let mut attempt = Attempt::retain(candidates(), end);
    attempt.bind(request, Arc::clone(&directory.original), end).unwrap();
    attempt
}
fn accepted(selection: &SourceCapture, context: &ContextReply, remaining: u64) -> Vec<u8> {
    SourceCaptureAccepted {
        selection_sha256: Sha256::digest(selection.encode().unwrap()).into(),
        remaining_input_ns: remaining,
        context: context.clone(),
    }
    .encode(selection)
    .unwrap()
}

#[test]
fn accepted_pending_work_keeps_the_original_carrier_and_cannot_enable_configuration() {
    let end = Instant::now() + Duration::from_secs(20);
    let original = directory(end);
    let mut attempt = attempt(&original, end);
    let selection = attempt.selection.as_ref().unwrap().clone();
    let context = crate::bootstrap_graph::test_context();
    let peer_context = context.clone();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        assert!(SourceCapture::decode(&channel.receive(end).unwrap()).unwrap() == selection);
        channel.send(&accepted(&selection, &peer_context, 10_000_000_000), end).unwrap();
        assert_eq!(channel.receive(end).unwrap(), b"pending work; same carrier");
        channel.send(b"still pending; no completion", end).unwrap();
    });
    let mut channel = Channel::new(client).unwrap();
    exchange(&mut channel, &mut attempt, &context, |_| Ok(())).unwrap();
    attempt.check(attempt.end).unwrap();
    assert!(attempt.configuration_ready().is_err());
    assert!(Arc::ptr_eq(attempt.home.as_ref().unwrap(), &original.original));
    channel.send(b"pending work; same carrier", attempt.end).unwrap();
    assert_eq!(channel.receive(attempt.end).unwrap(), b"still pending; no completion");
    peer.join().unwrap();
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    assert!(channel.poisoned());
    assert!(attempt.check(attempt.end).is_err());
}

#[test]
fn full_request_population_context_and_digest_refusals_poison_the_same_socket() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    for kind in 0..4 {
        let mut attempt = attempt(&directory, end);
        let context = crate::bootstrap_graph::test_context();
        let peer_context = context.clone();
        let (client, server) = UnixStream::pair().unwrap();
        let peer = std::thread::spawn(move || {
            let mut channel = Channel::new(server).unwrap();
            let mut selection = SourceCapture::decode(&channel.receive(end).unwrap()).unwrap();
            let mut context = peer_context;
            if kind == 0 {
                selection.request.configured_targo.extend(b"-retargeted");
            }
            if kind == 1 {
                selection.candidates[0].sha256[0] ^= 1;
            }
            if kind == 2 {
                context.context.host.push_str("-foreign");
            }
            let mut bytes = accepted(&selection, &context, 10_000_000_000);
            if kind == 3 {
                let mut reply = SourceCaptureAccepted::decode(
                    &bytes,
                    &selection,
                    Sha256::digest(selection.encode().unwrap()).into(),
                )
                .unwrap();
                reply.selection_sha256[0] ^= 1;
                bytes = reply.encode(&selection).unwrap();
            }
            channel.send(&bytes, end).unwrap();
        });
        let mut channel = Channel::new(client).unwrap();
        assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
        assert!(channel.poisoned());
        assert!(attempt.check(end).is_err());
        assert!(Arc::ptr_eq(attempt.home.as_ref().unwrap(), &directory.original));
        assert!(directory.original.descriptor(end).is_ok());
        peer.join().unwrap();
    }
}

#[test]
fn remaining_is_anchored_before_the_first_send_and_never_renews_the_cache_end() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    let mut attempt = attempt(&directory, end);
    let hard_end = Instant::now() + Duration::from_secs(5);
    attempt.end = hard_end;
    let context = crate::bootstrap_graph::test_context();
    let peer_context = context.clone();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        let selection = SourceCapture::decode(&channel.receive(end).unwrap()).unwrap();
        std::thread::sleep(Duration::from_millis(2));
        channel.send(&accepted(&selection, &peer_context, 1), end).unwrap();
    });
    let mut channel = Channel::new(client).unwrap();
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    assert!(attempt.end <= hard_end);
    assert_eq!(attempt.end, attempt.first_send.unwrap() + Duration::from_nanos(1));
    assert!(attempt.end < Instant::now());
    assert!(channel.poisoned());
    peer.join().unwrap();
}

#[test]
fn actual_directory_drift_then_restore_is_permanently_refused_with_original_fd_held() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    let mut attempt = attempt(&directory, end);
    let raw = directory.original.descriptor(end).unwrap().as_raw_fd();
    let path = directory.path.clone();
    let held = path.with_extension("held-original");
    let context = crate::bootstrap_graph::test_context();
    let peer_context = context.clone();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        let selection = SourceCapture::decode(&channel.receive(end).unwrap()).unwrap();
        fs::rename(&path, &held).unwrap();
        fs::create_dir(&path).unwrap();
        channel.send(&accepted(&selection, &peer_context, 10_000_000_000), end).unwrap();
        (path, held)
    });
    let mut channel = Channel::new(client).unwrap();
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    let (path, held) = peer.join().unwrap();
    fs::remove_dir(path).unwrap();
    fs::rename(held, &directory.path).unwrap();
    assert!(directory.original.validate(end).is_err());
    assert!(attempt.check(end).is_err());
    assert!(unsafe { libc::fcntl(raw, libc::F_GETFD) } >= 0);
    assert!(channel.poisoned());
}

#[test]
fn unwind_after_acceptance_poison_retains_original_directory_and_attempt() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    let mut attempt = attempt(&directory, end);
    let context = crate::bootstrap_graph::test_context();
    let peer_context = context.clone();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        let selection = SourceCapture::decode(&channel.receive(end).unwrap()).unwrap();
        channel.send(&accepted(&selection, &peer_context, 10_000_000_000), end).unwrap();
    });
    let mut channel = Channel::new(client).unwrap();
    let mut checks = 0;
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = exchange(&mut channel, &mut attempt, &context, |_| {
                checks += 1;
                if checks == 2 {
                    panic!("actual owning postcheck panicked");
                }
                Ok(())
            });
        }))
        .is_err()
    );
    peer.join().unwrap();
    assert!(channel.poisoned());
    assert!(attempt.check(end).is_err());
    assert!(Arc::ptr_eq(attempt.home.as_ref().unwrap(), &directory.original));
    assert!(directory.original.descriptor(end).is_ok());
}

#[test]
fn lost_acceptance_does_not_create_a_retry_or_release_the_original() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    let mut attempt = attempt(&directory, end);
    let context = crate::bootstrap_graph::test_context();
    let (client, server) = UnixStream::pair().unwrap();
    let peer = std::thread::spawn(move || {
        let mut channel = Channel::new(server).unwrap();
        SourceCapture::decode(&channel.receive(end).unwrap()).unwrap();
        // Original receive can have effects; deliberately lose the reply.
    });
    let mut channel = Channel::new(client).unwrap();
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    peer.join().unwrap();
    assert!(channel.poisoned());
    assert!(exchange(&mut channel, &mut attempt, &context, |_| Ok(())).is_err());
    assert!(attempt.selection.is_some());
    assert!(directory.original.descriptor(end).is_ok());
}

#[test]
fn malformed_population_is_retained_and_refusal_cannot_rebind_the_attempt() {
    let end = Instant::now() + Duration::from_secs(20);
    let directory = directory(end);
    let request = crate::bootstrap_graph::offline_preparation::test_request();
    let mut population = candidates();
    population.push(population[0].clone());
    let mut attempt = Attempt::retain(population, end);
    assert!(attempt.bind(request.clone(), Arc::clone(&directory.original), end).is_err());
    assert_eq!(attempt.selection.as_ref().unwrap().candidates.len(), 2);
    assert!(attempt.bind(request, Arc::clone(&directory.original), end).is_err());
    assert!(Arc::ptr_eq(attempt.home.as_ref().unwrap(), &directory.original));
    assert!(directory.original.descriptor(end).is_ok());
}
