//! Real pipe/event predicates only. These controls do not construct a pinned
//! production host, registered output, managed SDK or execution grant.
use std::cell::Cell;
use std::io::Write as _;

use super::*;
use crate::{CommandSpec, Delegations, Descriptor, GnuTransport, JobBinding, Role};

fn request() -> NativeQueryRequest {
    NativeQueryRequest::Workload(crate::workload::host::CompilerQuery {
        member: crate::Request {
            binding: JobBinding {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            member_attempt: [3; 16],
            role: Role::WorkloadQuery,
            command: CommandSpec {
                program: b"/sdk/bin/trustc".to_vec(),
                arg0: None,
                args: vec![b"-vV".to_vec()],
                cwd: b"/source".to_vec(),
                environment: vec![
                    (b"LANG".to_vec(), b"C".to_vec()),
                    (b"LC_ALL".to_vec(), b"C".to_vec()),
                    (b"CARGO".to_vec(), b"/sdk/bin/targo".to_vec()),
                    (b"RUSTC".to_vec(), b"/sdk/bin/trustc".to_vec()),
                    (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
                    (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
                ],
            },
            delegations: Delegations {
                cpu: Some(Descriptor { source: 8, target: 6 }),
                gnu: GnuTransport::None,
                fences: Vec::new(),
            },
            timeout_ns: Some(crate::workload::host::MAX_QUERY_NS),
        },
        root: b"/sdk".to_vec(),
        program_sha256: [4; 32],
    })
}
fn streams() -> (MetadataStreams, Channel, io::PipeWriter, io::PipeWriter) {
    let (events, peer) = UnixStream::pair().unwrap();
    let (output, stdout, stderr) = Capture::new().unwrap();
    (
        MetadataStreams {
            events: Channel::new(events).unwrap(),
            output,
            state: Lifecycle::default(),
            observed: ObservedEvents::default(),
            cancel_sent: false,
            failed: false,
        },
        Channel::new(peer).unwrap(),
        stdout,
        stderr,
    )
}
fn refusal(request: &NativeQueryRequest) -> StatusFrame {
    StatusFrame {
        root_attempt: request.member().binding.root_attempt,
        member_attempt: request.member().member_attempt,
        status: Status::Refused { reason: "actual native pre-execution refusal".into() },
    }
}
fn settle(streams: &mut MetadataStreams, request: &NativeQueryRequest, deadline: Instant) {
    loop {
        match streams.poll_inner(request, deadline, &mut None).unwrap() {
            StreamReady::Refused => break,
            StreamReady::Pending => {
                assert!(Instant::now() < deadline, "actual refusal streams never closed");
                std::thread::yield_now();
            }
            StreamReady::Completed => panic!("refusal became completion"),
        }
    }
}

#[test]
fn retained_bound_refusal_waits_actual_output_and_event_eof_and_rechecks_the_original_pin() {
    let request = request();
    request.validate_request().unwrap();
    let (mut streams, mut peer, mut stdout, mut stderr) = streams();
    let deadline = Instant::now() + Duration::from_secs(10);
    let frame = refusal(&request);
    peer.send(&MetadataEvent::Status(frame.clone()).encode().unwrap(), deadline).unwrap();
    stdout.write_all(b"actual refused stdout\0\xff").unwrap();
    stderr.write_all(b"actual refused stderr\xfe").unwrap();
    assert!(matches!(
        streams.poll_inner(&request, deadline, &mut None).unwrap(),
        StreamReady::Pending
    ));
    assert_eq!(streams.state.refused_frame, Some(frame.clone()));
    assert!(observe(&streams, &request, true, || panic!("not complete")).unwrap().is_none());
    drop((stdout, stderr));
    assert!(
        observe(&streams, &request, true, || panic!("event EOF still missing")).unwrap().is_none()
    );
    drop(peer);
    settle(&mut streams, &request, deadline);
    assert!(
        observe(&streams, &request, false, || panic!("no positive owner finalization"))
            .unwrap()
            .is_none(),
        "cached frame and EOF cannot supply owner finalization"
    );
    let checked = Cell::new(false);
    assert_eq!(
        observe(&streams, &request, true, || {
            checked.set(true);
            Ok(())
        })
        .unwrap(),
        Some(&frame)
    );
    assert!(checked.get());
    assert_eq!(streams.output.bytes[0], b"actual refused stdout\0\xff");
    assert_eq!(streams.output.bytes[1], b"actual refused stderr\xfe");
    // The SAME error kind can mean a lost original pin. It never becomes a
    // positive refusal simply because poll also uses PermissionDenied.
    assert!(
        observe(&streams, &request, true, || Err(io::ErrorKind::PermissionDenied.into())).is_err()
    );
    assert!(streams.state.started.is_none() && streams.state.completed.is_none());
}

#[test]
fn wrong_binding_contradictory_status_or_failed_observer_never_supplies_known_refusal() {
    let request = request();
    let (mut streams, mut peer, stdout, stderr) = streams();
    let deadline = Instant::now() + Duration::from_secs(10);
    peer.send(&MetadataEvent::Status(refusal(&request)).encode().unwrap(), deadline).unwrap();
    drop((peer, stdout, stderr));
    settle(&mut streams, &request, deadline);
    streams.state.refused_frame.as_mut().unwrap().member_attempt[0] ^= 1;
    assert!(observe(&streams, &request, true, || Ok(())).is_err());
    streams.state.refused_frame = Some(refusal(&request));
    streams.output.observer_failed = true;
    assert!(observe(&streams, &request, true, || Ok(())).is_err());
    streams.output.observer_failed = false;
    streams.state.started = Some(Started {
        identity: crate::Identity {
            pid: 42,
            birth: 1,
            birth_kind: crate::BirthKind::MacosWallMicroseconds,
        },
        monotonic_ns: 1,
        unix_ns: 1,
    });
    assert!(observe(&streams, &request, true, || Ok(())).is_err());
    streams.state.started = None;
    streams.state.refused_frame.as_mut().unwrap().status = Status::Attached;
    assert!(observe(&streams, &request, true, || Ok(())).is_err());
}

#[test]
fn trailing_protocol_error_after_refused_is_never_a_positive_refusal() {
    let request = request();
    let (mut streams, mut peer, stdout, stderr) = streams();
    let deadline = Instant::now() + Duration::from_secs(10);
    let encoded = MetadataEvent::Status(refusal(&request)).encode().unwrap();
    peer.send(&encoded, deadline).unwrap();
    peer.send(&encoded, deadline).unwrap();
    drop((peer, stdout, stderr));
    assert!(
        streams.poll_inner(&request, deadline, &mut None).is_err(),
        "duplicate actual terminal must be rejected"
    );
    while !streams.output.eof.iter().all(|eof| *eof) && Instant::now() < deadline {
        streams.output.drain().unwrap();
        std::thread::yield_now();
    }
    assert!(streams.output.eof.iter().all(|eof| *eof));
    assert!(streams.events.at_eof().unwrap());
    assert!(streams.state.refused_frame.is_some(), "original first frame retained diagnostically");
    assert!(
        observe(&streams, &request, true, || Ok(())).is_err(),
        "a rejected later frame must permanently veto cached first Refused"
    );
}

#[test]
fn old_resolver_purpose_cannot_use_workload_refusal_observations() {
    let NativeQueryRequest::Workload(query) = request() else { unreachable!() };
    let mut member = query.member;
    member.role = Role::ResolverQuery;
    member.delegations.cpu = None;
    member.delegations.gnu = GnuTransport::NumericPipe {
        read: Descriptor { source: 8, target: 3 },
        write: Descriptor { source: 9, target: 4 },
    };
    let request = NativeQueryRequest::Resolver(crate::resolver::SealedResolverQueryRequest {
        member,
        root: query.root,
        program_sha256: query.program_sha256,
    });
    request.validate_request().unwrap();
    let (streams, _peer, _stdout, _stderr) = streams();
    assert_eq!(
        observe(&streams, &request, true, || Ok(())).unwrap_err().kind(),
        io::ErrorKind::Unsupported
    );
}
