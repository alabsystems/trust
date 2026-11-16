//! Actual pipes and framed observations; no fake host, loan, SDK or CPU grant.
use std::io::Write;

use super::*;
use crate::StatusFrame;
use crate::linker::tests as fixture;

fn streams() -> (MetadataStreams, Channel, io::PipeWriter, io::PipeWriter) {
    let (events, target) = UnixStream::pair().unwrap();
    let (output, stdout, stderr) = Capture::with_limit(crate::linker::MAX_OUTPUT).unwrap();
    (
        MetadataStreams {
            events: Channel::new(events).unwrap(),
            output,
            state: Lifecycle::default(),
            observed: ObservedEvents::default(),
            cancel_sent: false,
            failed: false,
        },
        Channel::new(target).unwrap(),
        stdout,
        stderr,
    )
}
fn status(status: Status) -> Vec<u8> {
    StatusFrame { root_attempt: [1; 16], member_attempt: [3; 16], status }.encode().unwrap()
}
fn prepared() -> crate::linker::Prepared {
    let mut p = fixture::prepared(&fixture::request());
    let (host, boot) = process::host_boot().unwrap();
    p.host = host;
    p.boot = boot;
    p.policy = program::RUNTIME_POLICY.into();
    p.scope = program::INPUT_SCOPE.into();
    p
}
fn prefix(target: &mut Channel, deadline: Instant) -> Vec<u8> {
    let p = prepared();
    let frames = [
        status(Status::Attached),
        p.encode().unwrap(),
        status(Status::Started(Started { identity: p.identity, monotonic_ns: 10, unix_ns: 11 })),
    ];
    let mut original = Vec::new();
    for frame in frames {
        original.extend((frame.len() as u32).to_be_bytes());
        original.extend(&frame);
        target.send(&frame, deadline).unwrap();
    }
    original
}
#[test]
fn direct_linker_orders_the_exact_actual_cpu_description_without_gnu() {
    use std::os::fd::{AsRawFd as _, FromRawFd as _};
    let (read, write) = std::io::pipe().unwrap();
    // An actual native transport description, not a CPU lease constructor.
    let raw = unsafe { libc::fcntl(read.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5) };
    assert!(raw >= 5);
    let original = unsafe { std::os::fd::OwnedFd::from_raw_fd(raw) };
    let flags = unsafe { libc::fcntl(raw, libc::F_GETFD) };
    let mut request = fixture::request();
    request.member.delegations.cpu.as_mut().unwrap().source = raw as u32;
    request.validate().unwrap();
    let ordered =
        super::super::ordered(&NativeQueryRequest::Linker(request), vec![original]).unwrap();
    assert_eq!(ordered.len(), 1);
    assert_eq!(ordered[0].as_raw_fd(), raw, "the actual description must not be reopened/replaced");
    assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFD) }, flags);
    assert_ne!(flags & libc::FD_CLOEXEC, 0);
    drop((ordered, read, write));
}
#[test]
fn direct_linker_actual_streams_require_distinct_retirement_and_both_output_eofs() {
    let request = NativeQueryRequest::Linker(fixture::request());
    let (mut streams, mut target, mut stdout, stderr) = streams();
    let deadline = Instant::now() + Duration::from_secs(5);
    let _ = prefix(&mut target, deadline);
    let completion = fixture::completion(&fixture::request());
    target.send(&completion.encode().unwrap(), deadline).unwrap();
    stdout.write_all(b"actual\0\xfflinker bytes").unwrap();
    drop(target);
    assert!(matches!(streams.poll(&request, deadline).unwrap(), StreamReady::Pending));
    assert_eq!(streams.state.accounting, Some(completion.observation));
    drop((stdout, stderr));
    // Nonblocking polling may still observe Pending while another test's
    // concurrent process birth temporarily retains a writer before exec.
    // Require actual physical EOF within the original bound, never synthesize
    // closure from the completed event or our local writer drops.
    while !matches!(streams.poll(&request, deadline).unwrap(), StreamReady::Completed) {
        assert!(Instant::now() < deadline, "actual linker streams did not reach EOF");
        std::thread::yield_now();
    }
    assert_eq!(streams.output.bytes[0], b"actual\0\xfflinker bytes");
    assert!(streams.state.prepared.is_none());
    assert!(streams.state.produced.is_none());
    assert!(streams.state.linker.is_some());
}
#[test]
fn direct_linker_rejects_legacy_terminal_and_wrong_suspended_child() {
    let request = NativeQueryRequest::Linker(fixture::request());
    for wrong_identity in [false, true] {
        let (mut streams, mut target, stdout, stderr) = streams();
        let deadline = Instant::now() + Duration::from_secs(5);
        if wrong_identity {
            target.send(&status(Status::Attached), deadline).unwrap();
            target.send(&prepared().encode().unwrap(), deadline).unwrap();
            let mut identity = prepared().identity;
            identity.birth += 1;
            target
                .send(
                    &status(Status::Started(Started { identity, monotonic_ns: 10, unix_ns: 11 })),
                    deadline,
                )
                .unwrap();
        } else {
            let _ = prefix(&mut target, deadline);
            target
                .send(
                    &fixture::completion(&fixture::request()).completed.encode().unwrap(),
                    deadline,
                )
                .unwrap();
        }
        drop((target, stdout, stderr));
        assert!(streams.poll(&request, deadline).is_err());
        assert!(streams.state.completed.is_none());
    }
}
#[test]
fn direct_linker_eof_before_retirement_keeps_actual_failed_prefix() {
    let request = NativeQueryRequest::Linker(fixture::request());
    let (mut streams, mut target, mut stdout, stderr) = streams();
    let deadline = Instant::now() + Duration::from_secs(60);
    let original_events = prefix(&mut target, deadline);
    stdout.write_all(b"failed\0\xffprefix").unwrap();
    // An actual duplicate retains the SAME event peer, as a concurrent birth
    // can retain it before exec closes descriptors. Local Drop is not EOF.
    let retained_event_peer = target.as_fd().try_clone_to_owned().unwrap();
    drop((target, stdout, stderr));
    assert!(matches!(streams.poll(&request, deadline).unwrap(), StreamReady::Pending));
    assert!(streams.state.started.is_some());
    assert!(streams.state.completed.is_none());
    drop(retained_event_peer);
    // SAME streams, no reexecution: another process birth may still retain an
    // original writer until exec. Pending cannot stand in for physical EOF.
    loop {
        match streams.poll(&request, deadline) {
            Ok(StreamReady::Pending) => {
                assert!(Instant::now() < deadline, "actual negative event EOF was not observed");
                std::thread::sleep(Duration::from_millis(1));
            }
            Err(error) => {
                assert_eq!(error.kind(), io::ErrorKind::InvalidData, "{error}");
                assert!(streams.events.at_eof().unwrap(), "a polling error is not physical EOF");
                break;
            }
            Ok(StreamReady::Completed) => panic!("event EOF cannot become Completed"),
            Ok(StreamReady::Refused) => panic!("event EOF cannot become Refused"),
        }
    }
    while !streams.output.eof.iter().all(|eof| *eof) {
        assert!(Instant::now() < deadline, "actual output EOFs were not observed");
        streams.output.drain().unwrap();
        std::thread::sleep(Duration::from_millis(1));
    }
    let observed = streams.take_failure_observation(&request);
    assert_eq!(observed.stdout, b"failed\0\xffprefix");
    assert!(observed.stderr.is_empty());
    assert!(observed.stdout_eof && observed.stderr_eof);
    assert_eq!(observed.event_prefix, original_events);
    assert_eq!(observed.event_bytes_seen, original_events.len() as u64);
    assert!(!observed.event_prefix_truncated());
    assert!(streams.state.completed.is_none());
    assert!(streams.state.linker_completed.is_none());
}
#[test]
fn direct_linker_capture_does_not_change_existing_query_limits() {
    let request = NativeQueryRequest::Linker(fixture::request());
    assert_eq!(request.output_limit(), 8 << 20);
    assert_eq!(METADATA_MAX_OUTPUT, 64 << 10);
    assert!(Capture::with_limit(8 << 20).is_ok());
    assert!(Capture::with_limit(8 << 20 | 1).is_err());
    assert_eq!(crate::workload::host::produced::MAX_OUTPUT_BYTES, 64 << 20);
}
