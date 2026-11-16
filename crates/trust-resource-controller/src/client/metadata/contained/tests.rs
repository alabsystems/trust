//! Raw stream controls are DATA-only. They cannot construct a live pinned
//! member, CompletedProducedOperation, registered output or retirement owner.
use std::io::Write;

use sha2::{Digest, Sha256};

use super::*;
use crate::workload::host::contained::tests as fixtures;
use crate::workload::host::produced::tests as outputs;

#[test]
fn consumed_control_requires_actual_eof_refuses_trailing_data_and_keeps_original_deadline() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (reader, writer) = UnixStream::pair().unwrap();
    let channel = Channel::new(reader).unwrap();
    assert!(!control_finished(&channel, deadline).unwrap());
    writer.shutdown(std::net::Shutdown::Write).unwrap();
    assert!(control_finished(&channel, deadline).unwrap());
    assert!(control_finished(&channel, Instant::now()).is_err());
    drop(writer);
    let (reader, mut writer) = UnixStream::pair().unwrap();
    let channel = Channel::new(reader).unwrap();
    writer.write_all(b"trailing-original-control").unwrap();
    writer.shutdown(std::net::Shutdown::Write).unwrap();
    assert!(control_finished(&channel, deadline).is_err());
    assert!(!channel.at_eof().unwrap(), "checking never consumes or hides the bytes");
}

fn request() -> NativeQueryRequest {
    NativeQueryRequest::ContainedProduced(
        fixtures::request(),
        crate::workload::host::produced::RegistrationAck {
            key: fixtures::request().produced.key,
            executable: outputs::prepared().executable,
        },
    )
}
fn terminal() -> contained::Completion {
    let mut completion = fixtures::completion();
    completion.request_sha256 =
        Sha256::digest(fixtures::request().binding_preimage().unwrap()).into();
    completion
}
fn streams() -> (MetadataStreams, Channel, io::PipeWriter, io::PipeWriter) {
    let (events, target) = UnixStream::pair().unwrap();
    let (output, stdout, stderr) =
        Capture::with_limit(crate::workload::host::produced::MAX_OUTPUT_BYTES).unwrap();
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
fn prefix(target: &mut Channel, deadline: Instant) {
    let status = |status| {
        crate::StatusFrame { root_attempt: [1; 16], member_attempt: [8; 16], status }
            .encode()
            .unwrap()
    };
    target.send(&status(Status::Attached), deadline).unwrap();
    let mut prepared = outputs::prepared();
    (prepared.host, prepared.boot) = process::host_boot().unwrap();
    target.send(&prepared.encode().unwrap(), deadline).unwrap();
    target
        .send(
            &status(Status::Started(Started {
                identity: prepared.identity,
                monotonic_ns: 10,
                unix_ns: 11,
            })),
            deadline,
        )
        .unwrap();
}
#[test]
fn contained_terminal_requires_the_actual_full_stream_denominator() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (mut streams, mut target, mut stdout, stderr) = streams();
    stdout.write_all(b"actual\0prefix\xff").unwrap();
    prefix(&mut target, deadline);
    target.send(&terminal().encode().unwrap(), deadline).unwrap();
    assert!(matches!(streams.poll(&request(), deadline).unwrap(), StreamReady::Pending));
    drop((target, stdout, stderr));
    loop {
        if matches!(streams.poll(&request(), deadline).unwrap(), StreamReady::Completed) {
            break;
        }
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(2));
    }
    assert_eq!(streams.output.bytes[0], b"actual\0prefix\xff");
    assert_eq!(streams.state.contained.as_ref().unwrap(), &terminal());
}
#[test]
fn old_workload_retirement_cannot_complete_a_contained_operation() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (mut streams, mut target, stdout, stderr) = streams();
    prefix(&mut target, deadline);
    target.send(&terminal().completion.encode().unwrap(), deadline).unwrap();
    drop((target, stdout, stderr));
    assert!(streams.poll(&request(), deadline).is_err());
    assert!(streams.failed && streams.state.contained.is_none());
}
#[test]
fn wrong_operation_hash_and_gnu_poison_the_original_stream_without_retry() {
    for which in 0..3 {
        let deadline = Instant::now() + Duration::from_secs(60);
        let (mut streams, mut target, mut stdout, stderr) = streams();
        stdout.write_all(b"failed-prefix").unwrap();
        prefix(&mut target, deadline);
        let mut wrong = terminal();
        match which {
            0 => wrong.operation[0] ^= 1,
            1 => wrong.request_sha256[0] ^= 1,
            _ => wrong.gnu.inode += 1,
        }
        target.send(&wrong.encode().unwrap(), deadline).unwrap();
        drop((target, stdout, stderr));
        assert!(streams.poll(&request(), deadline).is_err());
        assert!(streams.poll(&request(), deadline).is_err());
        assert!(streams.state.contained.is_none());
        let failed = streams.take_failure_observation(&request());
        assert_eq!(failed.stdout, b"failed-prefix");
        assert!(failed.event_bytes_seen > 0);
    }
}
#[test]
fn duplicate_contained_terminal_is_not_a_second_completion() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (mut streams, mut target, stdout, stderr) = streams();
    prefix(&mut target, deadline);
    let bytes = terminal().encode().unwrap();
    target.send(&bytes, deadline).unwrap();
    target.send(&bytes, deadline).unwrap();
    drop((target, stdout, stderr));
    assert!(streams.poll(&request(), deadline).is_err());
    assert!(streams.failed);
}
#[test]
fn lost_contained_owner_preserves_observed_bytes_without_retirement() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (mut streams, mut target, mut stdout, stderr) = streams();
    stdout.write_all(b"actual-failed-work").unwrap();
    prefix(&mut target, deadline);
    drop((target, stdout, stderr));
    loop {
        if streams.poll(&request(), deadline).is_err() {
            break;
        }
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(2));
    }
    assert!(streams.state.contained.is_none());
    let failed = streams.take_failure_observation(&request());
    assert_eq!(failed.stdout, b"actual-failed-work");
    assert!(failed.stdout_eof && failed.stderr_eof);
}
