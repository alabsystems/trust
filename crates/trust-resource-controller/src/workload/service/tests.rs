use checkpoint::{Action, Artifact, Body, Capture, Checkpoint};

use super::*;
use crate::accounting::{CpuTimes, Observation};
use crate::workload::InputFile;
use crate::workload::host::census;
use crate::{Call, Request, Status};

fn binding() -> Binding {
    Binding { root_attempt: [1; 16], invocation_sha256: [2; 32] }
}
fn invocation() -> WorkloadInvocation {
    let input = |name: &str| InputFile { path: name.as_bytes().to_vec(), sha256: [3; 32] };
    WorkloadInvocation {
        invocation: [4; 16],
        observed_host_store: None,
        root: b"/sdk".to_vec(),
        program: input("/sdk/bin/targo"),
        compiler: input("/sdk/bin/trustc"),
        cwd: b"/source".to_vec(),
        cargo_home: b"/cargo".to_vec(),
        output_root: b"/output".to_vec(),
        refutation_step: input("/source/step"),
        refutation_loop: input("/source/loop"),
        trust_spec_source: input("/source/spec"),
        repetitions: 32,
        timeout_ns: 1,
    }
}
fn file(target: u32) -> Artifact {
    Artifact {
        target,
        executable: MetadataFile {
            path: format!("/output/test{target}").into_bytes(),
            sha256: [4; 32],
            bytes: 99,
            device: 1,
            inode: u64::from(target) + 5,
        },
    }
}
fn capture_fixture() -> Capture {
    Capture {
        started: true,
        outcome: Some(crate::Outcome::Exit(0)),
        cause: Some(crate::CompletionCause::Exited),
        runtime_ns: Some(1),
        retirement_confirmed: true,
        accounting: Some(Observation::uncollected()),
        member_attempt: Some([5; 16]),
        failure: None,
    }
}

#[test]
fn postcompiler_root_diagnostics_never_decode_as_native_action_bytes_or_completion() {
    let value = finish::Diagnostic {
        binding: binding(),
        stream: Stream::Stderr,
        offset: 7,
        bytes: b"root diagnostic\0\xff".to_vec(),
    };
    let bytes = value.encode().unwrap();
    assert_eq!(finish::Diagnostic::decode(&bytes, &binding()).unwrap(), value);
    assert!(Chunk::decode(&bytes, &binding()).is_err());
    assert!(finish::Graph::decode(&bytes, &binding()).is_err());
    assert!(finish::decode_page(&bytes, &binding()).is_err());
    assert!(Request::decode(&bytes).is_err());
    let mut changed = value;
    changed.offset = MAX_STREAM_BYTES;
    assert!(changed.encode().is_err());
}

#[test]
fn service_ready_observes_original_widths_but_cannot_enter_any_member_dispatch() {
    let ready = Ready {
        binding: binding(),
        original_root: Identity { pid: 42, birth: 7, birth_kind: BirthKind::MacosWallMicroseconds },
        native_manifest: FileIdentity { device: 1, inode: 2 },
        reserved_domain: 28,
        dispatch_ceiling: 7,
        memory_bytes: 16 * 1024 * 1024 * 1024,
    };
    let bytes = ready.encode().unwrap();
    assert_eq!(Ready::decode(&bytes, [2; 32]).unwrap(), ready);
    assert!(Ready::decode(&bytes, [9; 32]).is_err());
    assert!(Call::decode(&bytes).is_err());
    assert!(Request::decode(&bytes).is_err());
    for cut in 0..bytes.len() {
        assert!(Ready::decode(&bytes[..cut], [2; 32]).is_err());
    }
    let mut changed = ready.clone();
    changed.dispatch_ceiling = 29;
    assert!(changed.encode().is_err());
    changed.dispatch_ceiling = 8;
    assert!(changed.encode().is_err());
    changed.dispatch_ceiling = 0;
    assert!(changed.encode().is_err());

    let initial = InitialReady {
        funded: Ready { reserved_domain: 1, dispatch_ceiling: 1, ..ready },
        original_ceiling: 28,
        maximum_dispatch: 7,
    };
    let bytes = initial.encode().unwrap();
    assert_eq!(InitialReady::decode(&bytes, [2; 32]).unwrap(), initial);
    assert!(Ready::decode(&bytes, [2; 32]).is_err());
    assert!(InitialReady::decode(&bytes, [9; 32]).is_err());
    for cut in 0..bytes.len() {
        assert!(InitialReady::decode(&bytes[..cut], [2; 32]).is_err());
    }
    let mut changed = initial.clone();
    changed.funded.reserved_domain = 28;
    assert!(changed.encode().is_err(), "maximum cannot masquerade as funded custody");
    changed = initial;
    changed.maximum_dispatch = 29;
    assert!(changed.encode().is_err());
}

#[test]
fn chunks_keep_exact_binary_prefixes_and_permanent_replay_gap_or_scope_failure() {
    let chunk = Chunk {
        binding: binding(),
        checkpoint: 2,
        stream: Stream::Stdout,
        offset: 0,
        bytes: b"raw\0binary\xff".to_vec(),
    };
    let encoded = chunk.encode().unwrap();
    assert_eq!(Chunk::decode(&encoded, &binding()).unwrap(), chunk);
    let mut receiver = Output::new(binding(), 2).unwrap();
    receiver.append(chunk.clone()).unwrap();
    assert!(receiver.append(chunk.clone()).is_err());
    let mut next = chunk.clone();
    next.offset = chunk.bytes.len() as u64;
    assert!(receiver.append(next).is_err());
    let (stdout, stderr, end, failed) = receiver.parts();
    assert_eq!(stdout, chunk.bytes);
    assert!(stderr.is_empty() && end.is_none() && failed);
    let mut receiver = Output::new(binding(), 2).unwrap();
    receiver.append(chunk.clone()).unwrap();
    let end = OutputEnd {
        binding: binding(),
        checkpoint: 2,
        scope: OutputScope::NativeAction,
        lengths: [chunk.bytes.len() as u64, 0],
        closed: [false, true],
        truncated: [false, false],
    };
    assert_eq!(OutputEnd::decode(&end.encode().unwrap(), &binding()).unwrap(), end);
    receiver.close(end).unwrap();
    assert!(!receiver.parts().2.unwrap().closed[0]);
    assert!(receiver.append(chunk).is_err());
    let mut wrong = OutputEnd {
        binding: binding(),
        checkpoint: 1,
        scope: OutputScope::NativeAction,
        lengths: [0, 0],
        closed: [true, true],
        truncated: [false, false],
    };
    assert!(wrong.encode().is_err());
    wrong.scope = OutputScope::CompilerGraph;
    assert!(wrong.encode().is_ok());
}

#[test]
fn compiled_checkpoint_requires_both_actual_artifacts_and_complete_original_population() {
    let invocation = invocation();
    let mut checkpoint = Checkpoint {
        binding: binding(),
        sequence: 1,
        body: Body::Compiled {
            succeeded: true,
            workers_retired: true,
            output_complete: true,
            jobs: 7,
            artifacts: vec![file(0), file(1)],
            failure: None,
        },
    };
    let encoded = checkpoint.encode(&invocation).unwrap();
    assert_eq!(Checkpoint::decode(&encoded, &binding(), &invocation).unwrap(), checkpoint);
    for cut in 0..encoded.len() {
        assert!(Checkpoint::decode(&encoded[..cut], &binding(), &invocation).is_err());
    }
    let Body::Compiled { artifacts, .. } = &mut checkpoint.body else { unreachable!() };
    artifacts[1] = file(0);
    assert!(checkpoint.encode(&invocation).is_err());
    let Body::Compiled { artifacts, .. } = &mut checkpoint.body else { unreachable!() };
    artifacts.pop();
    assert!(checkpoint.encode(&invocation).is_err());
    let Body::Compiled { artifacts, .. } = &mut checkpoint.body else { unreachable!() };
    *artifacts = vec![file(0), file(1)];
    artifacts[1].executable.path = b"/foreign/test1".to_vec();
    assert!(checkpoint.encode(&invocation).is_err());
}

#[test]
fn sample_checkpoint_retains_optional_measurements_and_exact_67_action_plan() {
    let invocation = invocation();
    let mut checkpoint = Checkpoint {
        binding: binding(),
        sequence: 67,
        body: Body::Harness {
            target: 1,
            action: Action::Sample { repetition: 32 },
            capture: capture_fixture(),
        },
    };
    let bytes = checkpoint.encode(&invocation).unwrap();
    assert_eq!(Checkpoint::decode(&bytes, &binding(), &invocation).unwrap(), checkpoint);
    let Body::Harness { capture, .. } = &mut checkpoint.body else { unreachable!() };
    capture.accounting.as_mut().unwrap().cpu_times = Some(CpuTimes { user_ns: 0, system_ns: 0 });
    capture.accounting.as_mut().unwrap().peak_rss_bytes = Some(0);
    let measured = checkpoint.encode(&invocation).unwrap();
    assert_ne!(bytes, measured);
    assert_eq!(Checkpoint::decode(&measured, &binding(), &invocation).unwrap(), checkpoint);
    let Body::Harness { capture, .. } = &mut checkpoint.body else { unreachable!() };
    capture.cause = Some(crate::CompletionCause::HostFault);
    let fault = checkpoint.encode(&invocation).unwrap();
    assert_ne!(measured, fault);
    assert_eq!(Checkpoint::decode(&fault, &binding(), &invocation).unwrap(), checkpoint);
    checkpoint.sequence = 66;
    assert!(checkpoint.encode(&invocation).is_err());
    checkpoint.sequence = 2;
    checkpoint.body =
        Body::Harness { target: 0, action: Action::Inventory, capture: capture_fixture() };
    assert!(checkpoint.encode(&invocation).is_ok());
    checkpoint.sequence = 3;
    assert!(checkpoint.encode(&invocation).is_err());
}

fn page(offset: u32, kinds: &[census::SourceKind]) -> census::Page {
    census::Page {
        request: census::Request {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            snapshot: [8; 16],
            offset,
        },
        total: 6,
        entries: kinds
            .iter()
            .enumerate()
            .map(|(index, kind)| census::Entry {
                member_attempt: [(index + offset as usize + 10) as u8; 16],
                kind: *kind,
                identity: None,
                started: None,
                terminal: Status::Unknown {
                    reason: "actual uncertain entry retained".into(),
                    started: None,
                },
                accounting: Observation::uncollected(),
                retired: false,
                drained: false,
            })
            .collect(),
    }
}
#[test]
fn final_graph_requires_contiguous_all_role_census_and_never_drops_unknown_metrics() {
    let kinds = [
        census::SourceKind::Compiler,
        census::SourceKind::Linker,
        census::SourceKind::Query,
        census::SourceKind::BuildScript,
        census::SourceKind::Inventory,
        census::SourceKind::Sample,
    ];
    let first = page(0, &kinds[..2]);
    let last = page(2, &kinds[2..]);
    let frame = finish::encode_page(&first).unwrap();
    assert_eq!(finish::decode_page(&frame, &binding()).unwrap(), first);
    let graph =
        finish::Graph { binding: binding(), succeeded: false, snapshot: [8; 16], members: 6 };
    assert_eq!(finish::Graph::decode(&graph.encode().unwrap(), &binding()).unwrap(), graph);
    let mut received = finish::Census::new(binding());
    assert!(received.check_finished(&graph).is_err());
    received.append(first.clone()).unwrap();
    assert!(received.check_finished(&graph).is_err());
    received.append(last.clone()).unwrap();
    received.check_finished(&graph).unwrap();
    assert_eq!(received.entries().len(), 6);
    assert!(
        received
            .entries()
            .iter()
            .all(|entry| entry.accounting.cpu_times.is_none() && !entry.retired && !entry.drained)
    );
    let mut changed = graph.clone();
    changed.members = 5;
    assert!(received.check_finished(&changed).is_err());
    let mut received = finish::Census::new(binding());
    received.append(first.clone()).unwrap();
    assert!(received.append(first.clone()).is_err());
    assert!(received.append(last.clone()).is_err());
    let mut duplicate = last;
    duplicate.entries[0].member_attempt = first.entries[0].member_attempt;
    let mut received = finish::Census::new(binding());
    received.append(first).unwrap();
    assert!(received.append(duplicate).is_err());
}
