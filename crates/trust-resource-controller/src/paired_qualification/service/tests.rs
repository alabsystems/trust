use super::*;
use crate::accounting::Observation;
use crate::{CompletionCause, Outcome};

fn binding() -> Binding {
    Binding { root_attempt: [1; 16], invocation_sha256: [2; 32] }
}
fn finished() -> Finished {
    Finished {
        binding: binding(),
        node: Node::Strict,
        result: Result::Captured {
            capture: Capture {
                started: true,
                outcome: Some(Outcome::Exit(7)),
                cause: Some(CompletionCause::Exited),
                runtime_ns: Some(0),
                retirement_confirmed: true,
                accounting: Some(Observation::uncollected()),
                member_attempt: Some([3; 16]),
                failure: None,
            },
            elapsed_ns: 0,
            input_failure: None,
        },
        lengths: [0, 17],
        ends: [StreamEnd::Eof, StreamEnd::Eof],
        truncated: [false; 2],
    }
}
#[test]
fn complete_required_node_population_preserves_separate_compile_and_verification_denominators() {
    for repetitions in [1, 3, 32] {
        let population = Node::population(repetitions).unwrap();
        assert_eq!(population.len(), 6 + 2 * repetitions as usize);
        assert_eq!(population.iter().filter(|node| node.is_compile()).count(), 2);
        assert_eq!(population.iter().filter(|node| node.is_verification()).count(), 2);
        assert_eq!(
            population.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),
            population.len()
        );
        for node in population {
            let registered = Registered { binding: binding(), node, original_compile_unit: None };
            let bytes = registered.encode(repetitions).unwrap();
            assert_eq!(Registered::decode(&bytes, &binding(), repetitions).unwrap(), registered);
            for cut in 0..bytes.len() {
                assert!(Registered::decode(&bytes[..cut], &binding(), repetitions).is_err());
            }
        }
    }
    for repetitions in [0, 33, u32::MAX] {
        assert!(Node::population(repetitions).is_err());
    }
    let invalid = Registered {
        binding: binding(),
        node: Node::Sample { target: 1, repetition: 1 },
        original_compile_unit: None,
    };
    assert!(invalid.encode(1).is_err());
    assert!(Registered { node: Node::Inventory { target: 2 }, ..invalid }.encode(32).is_err());
}
#[test]
fn known_failed_capture_preserves_optional_metrics_and_cannot_become_compile_eof_or_a_v1_frame() {
    let actual = finished();
    let bytes = actual.encode(1).unwrap();
    assert_eq!(Finished::decode(&bytes, &binding(), 1).unwrap(), actual);
    for cut in 0..bytes.len() {
        assert!(Finished::decode(&bytes[..cut], &binding(), 1).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(Finished::decode(&extra, &binding(), 1).is_err());
    let mut wrong = binding();
    wrong.invocation_sha256[0] ^= 1;
    assert!(Finished::decode(&bytes, &wrong, 1).is_err());
    assert!(Finished { node: Node::AyCompile, ..actual.clone() }.encode(1).is_err());
    assert!(Finished { ends: [StreamEnd::WriterClosed; 2], ..actual.clone() }.encode(1).is_err());
    if let Result::Captured { capture, .. } = &actual.result {
        assert_eq!(capture.outcome, Some(Outcome::Exit(7)));
        assert_eq!(capture.runtime_ns, Some(0));
        assert_eq!(capture.accounting.unwrap().cpu_times, None);
    } else {
        panic!("native outcome lost");
    }
    assert!(crate::workload::WorkloadInvocation::decode(&bytes).is_err());
    assert!(
        crate::workload::service::Chunk::decode(
            &bytes,
            &crate::workload::service::Binding {
                root_attempt: binding().root_attempt,
                invocation_sha256: binding().invocation_sha256
            }
        )
        .is_err()
    );
    let blocked = Finished {
        node: Node::Advisory,
        result: Result::Blocked { reason: "original compile was refused".into() },
        lengths: [0; 2],
        ends: [StreamEnd::Unobserved; 2],
        truncated: [false; 2],
        ..actual
    };
    assert_eq!(Finished::decode(&blocked.encode(1).unwrap(), &binding(), 1).unwrap(), blocked);
    assert!(Finished { lengths: [1, 0], ..blocked }.encode(1).is_err());
}
#[test]
fn continuation_requires_exact_complete_plan_node_and_outcome_binding() {
    let checkpoint = Checkpoint {
        binding: binding(),
        sequence: 70,
        node: Node::Sample { target: 1, repetition: 31 },
        outcome_sha256: [8; 32],
    };
    assert!(checkpoint.encode(31).is_err());
    let bytes = checkpoint.encode(32).unwrap();
    assert_eq!(Checkpoint::decode(&bytes, &binding(), 32).unwrap(), checkpoint);
    let ack = Control::Continue(checkpoint.clone());
    let encoded = ack.encode(32).unwrap();
    assert_eq!(Control::decode(&encoded, &binding(), 32).unwrap(), ack);
    assert!(crate::workload::Continuation::decode(&encoded).is_err());
    let mut wrong = binding();
    wrong.root_attempt[0] ^= 1;
    assert!(Control::decode(&encoded, &wrong, 32).is_err());
    let mut trailing = encoded;
    trailing.push(0);
    assert!(Control::decode(&trailing, &binding(), 32).is_err());
    let stop = Control::Stop(binding());
    assert_eq!(Control::decode(&stop.encode(1).unwrap(), &binding(), 1).unwrap(), stop);
    let final_frame = Final {
        binding: binding(),
        repetitions: 32,
        finished: 69,
        blocked: 1,
        inputs_unchanged: false,
        snapshot: [5; 16],
        members: 0,
    };
    assert_eq!(Final::decode(&final_frame.encode().unwrap(), &binding()).unwrap(), final_frame);
    assert!(Final { finished: 68, ..final_frame }.encode().is_err());
    assert!(Checkpoint { sequence: u64::MAX, ..checkpoint }.encode(32).is_err());
}
#[test]
fn stream_scopes_bounds_and_actual_compile_identity_are_not_interchangeable() {
    let chunk = Chunk {
        binding: binding(),
        node: Node::Strict,
        scope: OutputScope::NativeAction,
        stream: Stream::Stderr,
        offset: MAX_STREAM_BYTES - 1,
        bytes: vec![0xff],
    };
    assert_eq!(Chunk::decode(&chunk.encode(1).unwrap(), &binding(), 1).unwrap(), chunk);
    assert!(Chunk { offset: MAX_STREAM_BYTES, ..chunk.clone() }.encode(1).is_err());
    assert!(Chunk { bytes: vec![0; MAX_CHUNK_BYTES + 1], ..chunk.clone() }.encode(1).is_err());
    assert!(Chunk { node: Node::AyCompile, ..chunk.clone() }.encode(1).is_err());
    assert!(Chunk { scope: OutputScope::CompilerReport, ..chunk }.encode(1).is_err());
    let unit = CompileUnit {
        index: 7,
        unit_hash: "actual-unit-hash".into(),
        package: "ay-proof-common".into(),
        target: "ay_proof_common".into(),
        source: b"/ay/crates/ay-proof-common/src/lib.rs".to_vec(),
    };
    let registered =
        Registered { binding: binding(), node: Node::Advisory, original_compile_unit: Some(unit) };
    assert_eq!(
        Registered::decode(&registered.encode(1).unwrap(), &binding(), 1).unwrap(),
        registered
    );
    assert!(Registered { node: Node::ConsumerCompile, ..registered }.encode(1).is_err());
}

#[test]
fn distinct_ready_and_final_writer_closure_keep_actual_native_eof_separate() {
    let ready = Ready {
        binding: binding(),
        original_root: Identity { pid: 2, birth: 3, birth_kind: BirthKind::MacosWallMicroseconds },
        native_manifest: FileIdentity { device: 4, inode: 5 },
        reserved_domain: 28,
        dispatch_ceiling: 7,
        memory_bytes: 14 * 1024 * 1024 * 1024,
        repetitions: 32,
    };
    let bytes = ready.encode().unwrap();
    assert_eq!(Ready::decode(&bytes, binding().invocation_sha256).unwrap(), ready);
    assert!(crate::workload::service::Ready::decode(&bytes, binding().invocation_sha256).is_err());
    for cut in 0..bytes.len() {
        assert!(Ready::decode(&bytes[..cut], binding().invocation_sha256).is_err());
    }
    assert!(Ready { dispatch_ceiling: 8, ..ready }.encode().is_err());
    let end = DiagnosticEnd {
        binding: binding(),
        node: Node::AyCompile,
        scope: OutputScope::Diagnostics,
        stream: Stream::Stderr,
        length: 7,
        writer_closed: true,
        truncated: false,
    };
    assert_eq!(DiagnosticEnd::decode(&end.encode(1).unwrap(), &binding(), 1).unwrap(), end);
    assert!(Chunk::decode(&end.encode(1).unwrap(), &binding(), 1).is_err());
    assert!(DiagnosticEnd { scope: OutputScope::NativeAction, ..end.clone() }.encode(1).is_err());
    assert!(DiagnosticEnd { node: Node::Strict, ..end.clone() }.encode(1).is_err());
    assert!(DiagnosticEnd { length: MAX_STREAM_BYTES + 1, ..end }.encode(1).is_err());
}

#[test]
fn produced_observation_binds_both_original_targets_and_never_constructs_registration_rights() {
    let artifact = Artifact {
        binding: binding(),
        target: 0,
        executable: crate::MetadataFile {
            path: b"/output/debug/deps/a".to_vec(),
            sha256: [3; 32],
            bytes: 7,
            device: 8,
            inode: 9,
        },
    };
    let frame = artifact.encode(b"/output").unwrap();
    assert_eq!(Artifact::decode(&frame, &binding(), b"/output").unwrap(), artifact);
    assert!(Registered::decode(&frame, &binding(), 1).is_err());
    assert!(Artifact::decode(&frame, &binding(), b"/other-output").is_err());
    assert!(Artifact { target: 2, ..artifact.clone() }.encode(b"/output").is_err());
    let mut changed = artifact;
    changed.executable.path = b"/output/../foreign".to_vec();
    assert!(changed.encode(b"/output").is_err());
    assert!(crate::workload::host::produced::Registration::decode(&frame).is_err());
}
