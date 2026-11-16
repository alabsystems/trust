// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual local transport controls only; no SDK/Root/member or native closure
//! is fabricated to exercise the data boundary.
use super::*;

fn limits() -> BrokerLimits {
    BrokerLimits {
        line_bytes: 1024,
        stream_bytes: 4096,
        timeout_ns: 1_000_000_000,
        capture_rusage: true,
    }
}
fn command() -> crate::CommandSpec {
    crate::CommandSpec {
        program: b"/compiler".to_vec(),
        arg0: None,
        args: vec![vec![0xff, 0x81]],
        cwd: b"/source".to_vec(),
        environment: vec![(b"LANG".to_vec(), b"C".to_vec())],
    }
}

#[test]
fn graph_finish_is_one_use_and_rejects_later_execute_or_publication() {
    // Actual socket/state controls only. No positive graph/native closure,
    // SDK, coordinator, local CPU owner or acknowledgement is fabricated.
    let (mut parent, endpoint) = CoordinatorBrokerServer::pair().unwrap();
    let mut peer = Channel::new(UnixStream::from(endpoint.original.try_clone().unwrap())).unwrap();
    let until = Instant::now() + Duration::from_secs(10);
    peer.send(
        &BrokerRequest::FinishGraph { sequence: 1 }.encode().unwrap(),
        until,
    )
    .unwrap();
    assert!(matches!(
        parent.receive(until).unwrap(),
        Some(BrokerRequest::FinishGraph { sequence: 1 })
    ));
    parent
        .refuse_graph("current producer is missing".into(), until)
        .unwrap();
    assert!(matches!(
        BrokerEvent::decode(&peer.receive(until).unwrap()).unwrap(),
        BrokerEvent::GraphFinished {
            sequence: 1,
            operation,
            failure: Some(_)
        } if operation==[0;16]
    ));
    assert!(parent.refuse_graph("duplicate".into(), until).is_err());

    let (mut parent, endpoint) = CoordinatorBrokerServer::pair().unwrap();
    let mut peer = Channel::new(UnixStream::from(endpoint.original.try_clone().unwrap())).unwrap();
    peer.send(
        &BrokerRequest::FinishGraph { sequence: 1 }.encode().unwrap(),
        until,
    )
    .unwrap();
    assert!(matches!(
        parent.receive(until).unwrap(),
        Some(BrokerRequest::FinishGraph { .. })
    ));
    peer.send(
        &BrokerRequest::encode_execute(2, &command(), limits()).unwrap(),
        until,
    )
    .unwrap();
    assert!(
        parent.receive(until).is_err(),
        "a final graph request cannot overlap a compiler request"
    );
    for publication in [false, true] {
        let (mut parent, endpoint) = CoordinatorBrokerServer::pair().unwrap();
        let mut peer =
            Channel::new(UnixStream::from(endpoint.original.try_clone().unwrap())).unwrap();
        peer.send(
            &BrokerRequest::FinishGraph { sequence: 1 }.encode().unwrap(),
            until,
        )
        .unwrap();
        assert!(matches!(
            parent.receive(until).unwrap(),
            Some(BrokerRequest::FinishGraph { .. })
        ));
        parent
            .refuse_graph("current graph refused".into(), until)
            .unwrap();
        let _negative_data = peer.receive(until).unwrap();
        let later = if publication {
            BrokerRequest::Publish {
                sequence: 2,
                selection: PublicationSelection {
                    unit_sha256: "a".repeat(64),
                    unit_id: "data".into(),
                    destinations: Vec::new(),
                },
            }
            .encode()
            .unwrap()
        } else {
            BrokerRequest::encode_execute(2, &command(), limits()).unwrap()
        };
        peer.send(&later, until).unwrap();
        assert!(
            parent.receive(until).is_err(),
            "no request may follow the final graph reply"
        );
    }
}

#[test]
fn native_parent_transport_preserves_os_bytes_and_refuses_a_second_active_request() {
    let (mut parent, endpoint) = CoordinatorBrokerServer::pair().unwrap();
    let mut peer = Channel::new(UnixStream::from(endpoint.original.try_clone().unwrap())).unwrap();
    let until = Instant::now() + Duration::from_secs(60);
    peer.send(
        &BrokerRequest::encode_execute(1, &command(), limits()).unwrap(),
        until,
    )
    .unwrap();
    let Some(BrokerRequest::Execute {
        sequence, command, ..
    }) = parent.receive(until).unwrap()
    else {
        panic!("actual queued request missing")
    };
    assert_eq!(sequence, 1);
    assert_eq!(command.args, [vec![0xff, 0x81]]);
    peer.send(
        &BrokerRequest::Cancel { sequence: 1 }.encode().unwrap(),
        until,
    )
    .unwrap();
    assert!(matches!(
        parent.receive(until).unwrap(),
        Some(BrokerRequest::Cancel { sequence: 1 })
    ));
    peer.send(
        &BrokerRequest::encode_execute(2, &command, limits()).unwrap(),
        until,
    )
    .unwrap();
    assert!(parent.receive(until).is_err());
    assert!(
        parent.receive(until).is_err(),
        "later data cannot clear a transport failure"
    );
}

#[test]
fn borrowed_command_preflight_refuses_nuls_and_aggregate_size_before_delivery() {
    for field in 0..3 {
        let mut command = command();
        match field {
            0 => command.program.push(0),
            1 => command.cwd.push(0),
            _ => command.arg0 = Some(vec![b'x', 0]),
        }
        assert!(BrokerRequest::encode_execute(1, &command, limits()).is_err());
    }
    let mut command = command();
    command.args = vec![vec![b'x'; crate::MAX_FIELD]; 17];
    assert!(BrokerRequest::encode_execute(1, &command, limits()).is_err());
}

#[test]
fn borrowed_output_transport_preserves_binary_chunks_and_failed_terminal_data() {
    let (mut parent, endpoint) = CoordinatorBrokerServer::pair().unwrap();
    let mut peer = Channel::new(UnixStream::from(endpoint.original.try_clone().unwrap())).unwrap();
    let until = Instant::now() + Duration::from_secs(10);
    let mut selected = limits();
    selected.stream_bytes = 256 * 1024;
    peer.send(
        &BrokerRequest::encode_execute(1, &command(), selected).unwrap(),
        until,
    )
    .unwrap();
    assert!(matches!(
        parent.receive(until).unwrap(),
        Some(BrokerRequest::Execute { .. })
    ));
    let stdout = (0..150_003).map(|n| (n % 256) as u8).collect::<Vec<_>>();
    let stderr = b"failed\0binary\xff-tail".to_vec();
    let expected_stdout = stdout.clone();
    let expected_stderr = stderr.clone();
    let writer = std::thread::spawn(move || {
        let header = BrokerCaptureData {
            started: false,
            status: None,
            accounting: crate::accounting::Observation::uncollected(),
            stdout: Vec::new(),
            stderr: Vec::new(),
            stdout_end: StreamEnd::ReadFailed,
            stderr_end: StreamEnd::Pending,
            truncated: false,
            failure: Some("untrusted transport fixture; no native completion".into()),
            elapsed_ns: 7,
        };
        // SAFETY: local wire DATA fixture only. No native child, original CPU,
        // source/SDK or successful execution owner is constructed or claimed.
        unsafe {
            parent
                .complete_with_output(&header, &stdout, &stderr, until)
                .unwrap();
        }
        parent
    });
    assert!(matches!(
        BrokerEvent::decode(&peer.receive(until).unwrap()).unwrap(),
        BrokerEvent::Started {
            sequence: 1,
            started: false
        }
    ));
    let mut observed = [Vec::new(), Vec::new()];
    loop {
        match BrokerEvent::decode(&peer.receive(until).unwrap()).unwrap() {
            BrokerEvent::Output {
                sequence,
                stderr,
                bytes,
            } => {
                assert_eq!(sequence, 1);
                observed[usize::from(stderr)].extend_from_slice(&bytes);
            }
            BrokerEvent::Completed {
                sequence,
                capture,
                stdout_len,
                stderr_len,
            } => {
                assert_eq!(sequence, 1);
                assert_eq!(
                    (stdout_len, stderr_len),
                    (expected_stdout.len() as u64, expected_stderr.len() as u64)
                );
                assert_eq!(capture.stdout_end, StreamEnd::ReadFailed);
                assert_eq!(capture.stderr_end, StreamEnd::Pending);
                assert!(capture.status.is_none() && capture.failure.is_some());
                assert!(capture.accounting.peak_rss_bytes.is_none());
                break;
            }
            _ => panic!("unexpected wire event"),
        }
    }
    assert_eq!(observed, [expected_stdout, expected_stderr]);
    let mut parent = writer.join().unwrap();
    peer.send(
        &BrokerRequest::encode_execute(2, &command(), selected).unwrap(),
        until,
    )
    .unwrap();
    assert!(matches!(
        parent.receive(until).unwrap(),
        Some(BrokerRequest::Execute { sequence: 2, .. })
    ));
}

#[test]
fn borrowed_output_header_cannot_silently_replace_another_stream_population() {
    let (mut parent, _endpoint) = CoordinatorBrokerServer::pair().unwrap();
    let header = BrokerCaptureData {
        started: false,
        status: None,
        accounting: crate::accounting::Observation::uncollected(),
        stdout: b"another population".to_vec(),
        stderr: Vec::new(),
        stdout_end: StreamEnd::Pending,
        stderr_end: StreamEnd::Pending,
        truncated: false,
        failure: Some("DATA fixture".into()),
        elapsed_ns: 0,
    };
    let until = Instant::now() + Duration::from_secs(1);
    // SAFETY: refusal-only DATA fixture; no execution or native owner exists.
    assert!(unsafe { parent.complete_with_output(&header, b"replacement", b"", until) }.is_err());
    assert!(
        parent.receive(until).is_err(),
        "the failed population cannot be retried"
    );
}
