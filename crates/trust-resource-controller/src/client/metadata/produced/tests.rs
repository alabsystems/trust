//! Actual pipe/event-owner controls. These saved protocol observations do not
//! construct a pinned host, registered output, managed SDK or execution grant.
use std::io::Write;

use super::*;
use crate::workload::host::produced::tests as fixtures;
use crate::workload::host::{Completion, MemberKind};
use crate::{CompletionCause, Outcome, StatusFrame};

fn request() -> NativeQueryRequest {
    let request = fixtures::request();
    let ack = crate::workload::host::produced::RegistrationAck {
        key: request.key.clone(),
        executable: fixtures::prepared().executable,
    };
    NativeQueryRequest::Produced(request, ack)
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
fn prepared() -> ProducedPrepared {
    let mut prepared = fixtures::prepared();
    let (host, boot) = process::host_boot().unwrap();
    prepared.host = host;
    prepared.boot = boot;
    prepared
}
fn status(status: Status) -> Vec<u8> {
    StatusFrame { root_attempt: [1; 16], member_attempt: [8; 16], status }.encode().unwrap()
}
fn completed() -> Completion {
    Completion {
        phase: 3,
        kind: MemberKind::Inventory,
        completed: MetadataCompletion {
            finished: StatusFrame {
                root_attempt: [1; 16],
                member_attempt: [8; 16],
                status: Status::Finished {
                    outcome: Outcome::Exit(0),
                    cause: CompletionCause::Exited,
                    runtime_ns: 17,
                },
            },
            inputs_unchanged: Ok(()),
        },
        observation: crate::accounting::Observation {
            scope: crate::accounting::Scope::ChildAndWaitedDescendantsV1,
            cpu_times: Some(crate::accounting::CpuTimes { user_ns: 0, system_ns: 7 }),
            peak_rss_bytes: None,
        },
    }
}
fn prefix(target: &mut Channel, deadline: Instant) {
    target.send(&status(Status::Attached), deadline).unwrap();
    let prepared = prepared();
    target.send(&prepared.encode().unwrap(), deadline).unwrap();
    target
        .send(
            &status(Status::Started(crate::Started {
                identity: prepared.identity,
                monotonic_ns: 10,
                unix_ns: 11,
            })),
            deadline,
        )
        .unwrap();
}

#[test]
fn producing_stream_requires_mixed_preparation_accounted_completion_and_all_actual_eofs() {
    let deadline = Instant::now() + Duration::from_secs(3);
    let (mut member, mut target, mut stdout, stderr) = streams();
    stdout.write_all(b"actual\0binary\xff").unwrap();
    prefix(&mut target, deadline);
    target.send(&completed().encode().unwrap(), deadline).unwrap();
    assert!(
        matches!(member.poll(&request(), deadline).unwrap(), StreamReady::Pending),
        "leader terminal cannot stand in for real stream closure"
    );
    drop((stdout, stderr, target));
    while !matches!(member.poll(&request(), deadline).unwrap(), StreamReady::Completed) {
        // Require physical EOF under the original finite bound; another
        // parallel process birth may transiently retain an inherited writer.
        assert!(Instant::now() < deadline, "actual produced streams did not reach EOF");
        std::thread::yield_now();
    }
    assert_eq!(member.output.bytes[0], b"actual\0binary\xff");
    assert_eq!(member.state.accounting, Some(completed().observation));
    assert!(member.state.prepared.is_none(), "no forged single-SDK preparation");
    assert_eq!(member.state.produced.unwrap().identity, prepared().identity);
}

#[test]
fn producing_stream_refuses_legacy_terminal_wrong_phase_kind_and_another_child_identity() {
    for changed in 0..4 {
        let deadline = Instant::now() + Duration::from_secs(3);
        let (mut member, mut target, stdout, stderr) = streams();
        if changed == 3 {
            target.send(&status(Status::Attached), deadline).unwrap();
            let prepared = prepared();
            target.send(&prepared.encode().unwrap(), deadline).unwrap();
            let mut identity = prepared.identity;
            identity.birth += 1;
            target
                .send(
                    &status(Status::Started(crate::Started {
                        identity,
                        monotonic_ns: 10,
                        unix_ns: 11,
                    })),
                    deadline,
                )
                .unwrap();
        } else {
            prefix(&mut target, deadline);
            let mut complete = completed();
            let bytes = match changed {
                0 => complete.completed.encode().unwrap(),
                1 => {
                    complete.phase += 1;
                    complete.encode().unwrap()
                }
                _ => {
                    complete.kind = MemberKind::Sample;
                    complete.encode().unwrap()
                }
            };
            target.send(&bytes, deadline).unwrap();
        }
        drop((stdout, stderr, target));
        assert!(member.poll(&request(), deadline).is_err(), "changed{changed}");
    }
}

#[test]
fn observer_failure_keeps_actual_binary_prefix_and_never_reads_or_finishes_again() {
    let (mut output, mut stdout, stderr) =
        Capture::with_limit(crate::workload::host::produced::MAX_OUTPUT_BYTES).unwrap();
    stdout.write_all(b"received\0\xff").unwrap();
    drop((stdout, stderr));
    let mut observed = Vec::new();
    let mut observe = |stream, bytes: &[u8]| {
        assert_eq!(stream, MetadataOutputStream::Stdout);
        observed.extend_from_slice(bytes);
        Err(io::Error::other("original durable sink refused"))
    };
    assert!(output.drain_observed(&mut Some(&mut observe)).is_err());
    assert_eq!(output.bytes[0], observed);
    assert_eq!(observed, b"received\0\xff");
    assert!(output.drain_observed(&mut None).is_err());
    assert!(!output.eof.iter().all(|closed| *closed), "callback failure cannot fabricate EOF");
}

#[test]
fn producing_limit_is_distinct_and_does_not_widen_old_metadata_query_captures() {
    for limit in [METADATA_MAX_OUTPUT, crate::workload::host::produced::MAX_OUTPUT_BYTES] {
        let (mut output, mut stdout, stderr) = Capture::with_limit(limit).unwrap();
        let payload: Vec<u8> = (0..METADATA_MAX_OUTPUT + 4096).map(|n| n as u8).collect();
        let deadline = Instant::now() + Duration::from_secs(3);
        std::thread::scope(|scope| {
            let bytes = &payload;
            let writer = scope.spawn(move || {
                stdout.write_all(bytes).unwrap();
                drop((stdout, stderr));
            });
            while !output.eof.iter().all(|closed| *closed) {
                assert!(Instant::now() < deadline);
                output.drain_observed(&mut None).unwrap();
                std::thread::sleep(Duration::from_millis(1));
            }
            writer.join().unwrap();
        });
        let retained = payload.len().min(limit);
        assert_eq!(output.bytes[0], payload[..retained]);
        assert_eq!(output.exceeded, payload.len() > limit);
    }
}
