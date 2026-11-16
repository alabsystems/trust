//! Real socket controls exercise the same production read/reducer functions.
//! Projected events are DATA, not actual Host/SDK/child retirement evidence.
use std::io::Write as _;
use std::net::Shutdown;
use std::os::unix::net::UnixStream;

use super::*;

#[test]
fn resident_observer_uses_actual_eof_then_ack_without_issuing_completion_authority() {
    use std::io::Read as _;
    let request = query::tests::request();
    let digest = Sha256::digest(request.binding_preimage().unwrap()).into();
    let bytes = wire(&frames(&request, digest));
    let (reader, mut writer) = UnixStream::pair().unwrap();
    let sender = std::thread::spawn(move || {
        writer.write_all(&bytes).unwrap();
        writer.shutdown(Shutdown::Write).unwrap();
        let mut received = Vec::new();
        writer.read_to_end(&mut received).unwrap();
        received
    });
    let data = observe_resident_query_channel(
        Channel::new(reader).unwrap(),
        &request,
        "host",
        "boot",
        Instant::now() + Duration::from_secs(1),
    )
    .unwrap();
    assert_eq!(sender.join().unwrap(), [0, 0, 0, 1, 1]);
    assert_eq!(data.stdout, [0, 255, 3]);
    assert!(
        matches!(
            data.completion.finished.status,
            crate::Status::Finished { outcome: crate::Outcome::Exit(7), .. }
        ),
        "transport observation does not claim successful native execution"
    );
}

#[test]
fn resident_observer_never_acknowledges_trailing_bytes() {
    use std::io::Read as _;
    let request = query::tests::request();
    let digest = Sha256::digest(request.binding_preimage().unwrap()).into();
    let mut bytes = wire(&frames(&request, digest));
    bytes.extend([0, 0, 0, 8, 1, 2]);
    let (reader, mut writer) = UnixStream::pair().unwrap();
    let sender = std::thread::spawn(move || {
        writer.write_all(&bytes).unwrap();
        writer.shutdown(Shutdown::Write).unwrap();
        let mut received = [0; 5];
        assert!(!matches!(writer.read(&mut received), Ok(5)));
    });
    assert!(
        observe_resident_query_channel(
            Channel::new(reader).unwrap(),
            &request,
            "host",
            "boot",
            Instant::now() + Duration::from_secs(1)
        )
        .is_err()
    );
    sender.join().unwrap();
}

#[test]
fn original_sdk_root_observation_matches_keeper_without_relabeling_program() {
    let mut request = query::tests::request();
    let mut sdk = crate::SdkCustody {
        execution: request.sdk_root.clone(),
        build: 1,
        lease_path: b"/sdk/lease".to_vec(),
        lease: crate::FileIdentity { device: 1, inode: 2 },
        inherited_fd: 5,
    };
    // These are Keeper field semantics, not an actual Host/SDK authority
    // fixture. Exercise the exact production preconnect equality check.
    request.validate().unwrap();
    validate_original_sdk(Some(&sdk), &request).unwrap();
    assert!(validate_original_sdk(None, &request).is_err());
    sdk.execution = b"/sdk/bin/targo".to_vec();
    assert!(validate_original_sdk(Some(&sdk), &request).is_err());
    sdk.execution = b"/foreign-sdk".to_vec();
    assert!(validate_original_sdk(Some(&sdk), &request).is_err());
    sdk.execution = request.sdk_root.clone();
    validate_original_sdk(Some(&sdk), &request).unwrap();
    request.program.path = b"/sdk/bin/targo".to_vec();
    assert!(request.validate().is_err(), "root equality never changes the selected tool profile");
}

fn frames(request: &query::Request, digest: [u8; 32]) -> Vec<Vec<u8>> {
    use crate::bootstrap_graph::query::tests::{prepared, started, terminal};
    let mut frames = [
        query::Event::Prepared(Box::new(prepared(request))),
        query::Event::Started(started()),
        query::Event::Output { stream: query::Stream::Stdout, offset: 0, bytes: vec![0, 255, 3] },
        query::Event::Output {
            stream: query::Stream::Stderr,
            offset: 0,
            bytes: b"actual failed prefix".to_vec(),
        },
        query::Event::Eof { stream: query::Stream::Stdout, bytes: 3 },
        query::Event::Eof { stream: query::Stream::Stderr, bytes: 20 },
    ]
    .iter()
    .map(|event| event.encode(request, digest).unwrap())
    .collect::<Vec<_>>();
    frames.push(terminal(request).encode(request, digest).unwrap());
    frames
}
fn wire(frames: &[Vec<u8>]) -> Vec<u8> {
    frames
        .iter()
        .flat_map(|frame| {
            (frame.len() as u32).to_be_bytes().into_iter().chain(frame.iter().copied())
        })
        .collect()
}
fn received(bytes: Vec<u8>, consume: impl FnOnce(&mut Channel, &mut Transcript, Instant)) {
    let (reader, mut writer) = UnixStream::pair().unwrap();
    let sender = std::thread::spawn(move || {
        writer.write_all(&bytes).unwrap();
        writer.shutdown(Shutdown::Write).unwrap();
    });
    let mut channel = Channel::new(reader).unwrap();
    let mut transcript = Transcript::new();
    let deadline = Instant::now() + Duration::from_secs(1);
    consume(&mut channel, &mut transcript, deadline);
    sender.join().unwrap();
}
#[test]
fn actual_framed_socket_preserves_binary_prefix_status_scope_and_complete_denominator() {
    let request = query::tests::request();
    let digest = [7; 32];
    let frames = frames(&request, digest);
    let bytes = wire(&frames);
    let original = bytes.clone();
    received(bytes, |channel, transcript, deadline| {
        let (completion, accounting) =
            receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                .unwrap();
        require_final_eof(channel, deadline, transcript).unwrap();
        assert!(channel.at_eof().unwrap());
        assert_eq!(transcript.stdout, [0, 255, 3]);
        assert_eq!(transcript.stderr, b"actual failed prefix");
        assert_eq!(transcript.raw, original);
        assert_eq!(transcript.bytes_seen, original.len() as u64);
        assert_eq!(transcript.frames_seen, 7);
        assert!(matches!(
            completion.finished.status,
            crate::Status::Finished { outcome: crate::Outcome::Exit(7), .. }
        ));
        assert_eq!(accounting.cpu_times, None);
        assert_eq!(accounting.peak_rss_bytes, None);
    });
}
#[test]
fn actual_eof_before_terminal_and_partial_frame_keep_received_prefix_without_completion() {
    let request = query::tests::request();
    let digest = [7; 32];
    let frames = frames(&request, digest);
    for partial in [false, true] {
        let mut bytes = wire(&frames[..4]);
        if partial {
            bytes.extend([0, 0, 0, 20, 1, 2, 3]);
        }
        let original = bytes.clone();
        received(bytes, |channel, transcript, deadline| {
            assert!(
                receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                    .is_err()
            );
            assert_eq!(transcript.stderr, b"actual failed prefix");
            assert_eq!(transcript.stdout, [0, 255, 3]);
            assert_eq!(transcript.raw, original);
            assert_eq!(transcript.bytes_seen, original.len() as u64);
            assert_eq!(transcript.frames_seen, 4);
            assert!(channel.poisoned());
            assert!(transcript.complete().is_err());
        });
    }
}
#[test]
fn actual_trailing_or_old_terminal_refuses_without_losing_original_raw_bytes() {
    let request = query::tests::request();
    let digest = [7; 32];
    let frames = frames(&request, digest);
    let mut trailing = wire(&frames);
    trailing.extend([0, 0, 0, 8, 1, 2]);
    let original = trailing.clone();
    received(trailing, |channel, transcript, deadline| {
        receive_operation(channel, &request, digest, "host", "boot", deadline, transcript).unwrap();
        assert!(require_final_eof(channel, deadline, transcript).is_err());
        assert_eq!(transcript.raw, original);
        assert_eq!(transcript.stderr, b"actual failed prefix");
        assert!(channel.poisoned());
    });
    let query::Terminal::Completed { completion, .. } = query::tests::terminal(&request) else {
        unreachable!()
    };
    let mut old = frames[..6].to_vec();
    old.push(completion.encode().unwrap());
    let old = wire(&old);
    received(old, |channel, transcript, deadline| {
        assert!(
            receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                .is_err()
        );
        assert_eq!(transcript.stderr, b"actual failed prefix");
        assert_eq!(transcript.frames_seen, 7);
    });
}
#[test]
fn actual_duplicate_start_bad_offset_foreign_host_or_early_terminal_never_completes() {
    let request = query::tests::request();
    let digest = [7; 32];
    let good = frames(&request, digest);
    let mut duplicate = good[..2].to_vec();
    duplicate.push(good[1].clone());
    let mut gap = good[..2].to_vec();
    gap.push(
        query::Event::Output { stream: query::Stream::Stdout, offset: 1, bytes: vec![1] }
            .encode(&request, digest)
            .unwrap(),
    );
    let early = vec![good[0].clone(), good[1].clone(), good[6].clone()];
    for frames in [duplicate, gap, early] {
        received(wire(&frames), |channel, transcript, deadline| {
            assert!(
                receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                    .is_err()
            );
            assert!(transcript.complete().is_err());
        });
    }
    received(wire(&good), |channel, transcript, deadline| {
        assert!(
            receive_operation(
                channel,
                &request,
                digest,
                "other-host",
                "boot",
                deadline,
                transcript
            )
            .is_err()
        );
        assert!(transcript.complete().is_err());
    });
}

#[test]
fn actual_policy_or_scope_drift_is_rejected_before_any_started_or_output_credit() {
    let request = query::tests::request();
    let digest = [7; 32];
    for original in [query::PREPARED_POLICY, query::PREPARED_SCOPE] {
        let mut frames = frames(&request, digest);
        let at = frames[0]
            .windows(original.len())
            .position(|bytes| bytes == original.as_bytes())
            .unwrap();
        frames[0][at..at + original.len()].fill(b'X');
        received(wire(&frames), |channel, transcript, deadline| {
            assert!(
                receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                    .is_err()
            );
            assert!(transcript.complete().is_err());
            assert_eq!(transcript.started, None);
            assert!(transcript.stdout.is_empty());
        });
    }
}

#[test]
fn actual_unknown_or_unwind_keeps_same_gate_closed_before_enrollment_connect() {
    use std::os::unix::fs::DirBuilderExt as _;
    use std::os::unix::net::UnixListener;
    let request = query::tests::request();
    let digest = [7; 32];
    let root = std::path::PathBuf::from("/tmp").join(format!(
        "bg-gate-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
    let path = root.join("s");
    let listener = UnixListener::bind(&path).unwrap();
    listener.set_nonblocking(true).unwrap();
    let mut gate = super::super::QueryState::new();
    gate.check(1).unwrap();
    gate.begin().unwrap();
    received(wire(&frames(&request, digest)[..4]), |channel, transcript, deadline| {
        assert!(
            receive_operation(channel, &request, digest, "host", "boot", deadline, transcript)
                .is_err()
        );
        assert_eq!(transcript.stderr, b"actual failed prefix");
    });
    assert!(gate.check(2).is_err());
    assert!(gate.enrollment_connect(|| UnixStream::connect(&path)).is_err());
    assert_eq!(listener.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    let mut unwound = super::super::QueryState::new();
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            unwound.begin().unwrap();
            panic!("actual coordinator unwind before query delivery");
        }))
        .is_err()
    );
    assert!(unwound.enrollment_connect(|| UnixStream::connect(&path)).is_err());
    assert_eq!(listener.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    drop(listener);
    std::fs::remove_file(path).unwrap();
    std::fs::remove_dir(root).unwrap();
}
#[test]
fn original_deadline_still_refuses_pending_native_control_after_all_bytes() {
    let request = query::tests::request();
    let digest = [7; 32];
    let bytes = wire(&frames(&request, digest));
    let (reader, mut writer) = UnixStream::pair().unwrap();
    let original = bytes.clone();
    let deadline = Instant::now() + Duration::from_secs(1);
    let (stop, stopped) = std::sync::mpsc::channel();
    let sender = std::thread::spawn(move || {
        writer.write_all(&bytes).unwrap();
        stopped.recv_timeout(Duration::from_secs(60)).unwrap();
        writer.shutdown(Shutdown::Write).unwrap();
    });
    let mut channel = Channel::new(reader).unwrap();
    let mut transcript = Transcript::new();
    receive_operation(&mut channel, &request, digest, "host", "boot", deadline, &mut transcript)
        .unwrap();
    assert_eq!(
        require_final_eof(&mut channel, deadline, &mut transcript).unwrap_err().kind(),
        io::ErrorKind::TimedOut
    );
    assert_eq!(transcript.raw, original);
    assert_eq!(transcript.stderr, b"actual failed prefix");
    stop.send(()).unwrap();
    sender.join().unwrap();
}
