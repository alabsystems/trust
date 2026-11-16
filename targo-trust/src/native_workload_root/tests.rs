//! Native stream/file controls and explicitly non-authoritative service data
//! controls. None fabricates a managed SDK, resource owner or completed run.
use sha2::{Digest as _, Sha256};
use trust_resource_controller::{BirthKind, FileIdentity, Identity};

use super::*;

fn invocation_data() -> WorkloadInvocation {
    let file = |path: &str| InputFile { path: path.as_bytes().to_vec(), sha256: [2; 32] };
    WorkloadInvocation {
        invocation: [1; 16],
        observed_host_store: None,
        root: b"/sdk".to_vec(),
        program: file("/sdk/bin/targo"),
        compiler: file("/sdk/bin/trustc"),
        cwd: b"/source".to_vec(),
        cargo_home: b"/cache".to_vec(),
        output_root: b"/output".to_vec(),
        refutation_step: file("/source/step"),
        refutation_loop: file("/source/loop"),
        trust_spec_source: file("/source/spec"),
        repetitions: 1,
        timeout_ns: 1,
    }
}
fn ready(protocol: &mut protocol::Protocol) -> service::Binding {
    let binding = service::Binding {
        root_attempt: [3; 16],
        invocation_sha256: Sha256::digest(protocol.invocation.encode().unwrap()).into(),
    };
    let ready = service::Ready {
        binding: binding.clone(),
        original_root: Identity { pid: 42, birth: 7, birth_kind: BirthKind::MacosWallMicroseconds },
        native_manifest: FileIdentity { device: 1, inode: 2 },
        reserved_domain: 28,
        dispatch_ceiling: 7,
        memory_bytes: 14 * 1024 * 1024 * 1024,
    };
    assert!(matches!(
        protocol.frame(&ready.encode().unwrap()).unwrap(),
        Some(protocol::Event::Ready)
    ));
    binding
}
fn compiler_checkpoint(protocol: &mut protocol::Protocol, binding: &service::Binding) -> Vec<u8> {
    protocol
        .frame(
            &service::Chunk {
                binding: binding.clone(),
                checkpoint: 1,
                stream: service::Stream::Stderr,
                offset: 0,
                bytes: b"original\0diagnostic\xff".to_vec(),
            }
            .encode()
            .unwrap(),
        )
        .unwrap();
    protocol
        .frame(
            &service::OutputEnd {
                binding: binding.clone(),
                checkpoint: 1,
                scope: service::OutputScope::CompilerGraph,
                lengths: [0, 20],
                closed: [true, true],
                truncated: [false, false],
            }
            .encode()
            .unwrap(),
        )
        .unwrap();
    checkpoint::Checkpoint {
        binding: binding.clone(),
        sequence: 1,
        body: Body::Compiled {
            succeeded: false,
            workers_retired: true,
            output_complete: true,
            jobs: 7,
            artifacts: Vec::new(),
            failure: Some("actual compiler failure".into()),
        },
    }
    .encode(&protocol.invocation)
    .unwrap()
}
#[test]
fn checkpoint_retains_exact_bytes_and_continuation_requires_final_census_after_ack() {
    let mut protocol = protocol::Protocol::new(invocation_data()).unwrap();
    let binding = ready(&mut protocol);
    let checkpoint = compiler_checkpoint(&mut protocol, &binding);
    let Some(protocol::Event::Checkpoint(output)) = protocol.frame(&checkpoint).unwrap() else {
        panic!("missing checkpoint")
    };
    assert_eq!(output.stderr, b"original\0diagnostic\xff");
    let continuation = protocol.take_continuation().unwrap();
    assert_eq!(continuation.checkpoint_sha256, <[u8; 32]>::from(Sha256::digest(&checkpoint)));
    assert!(protocol.take_continuation().is_none(), "same continuation cannot be sent twice");
    let page = workload::host::census::Page {
        request: workload::host::census::Request {
            root_attempt: binding.root_attempt,
            invocation_sha256: binding.invocation_sha256,
            snapshot: [4; 16],
            offset: 0,
        },
        total: 0,
        entries: Vec::new(),
    };
    protocol.frame(&service::finish::encode_page(&page).unwrap()).unwrap();
    let graph = service::finish::Graph { binding, succeeded: false, snapshot: [4; 16], members: 0 };
    assert!(matches!(
        protocol.frame(&graph.encode().unwrap()).unwrap(),
        Some(protocol::Event::Graph)
    ));
    assert!(
        protocol.frame(&graph.encode().unwrap()).is_err(),
        "trailing replay permanently refuses"
    );
    assert!(protocol.failure.is_some());
}
#[test]
fn graph_before_checkpoint_continuation_and_partial_census_permanently_refuse() {
    let mut protocol = protocol::Protocol::new(invocation_data()).unwrap();
    let binding = ready(&mut protocol);
    let checkpoint = compiler_checkpoint(&mut protocol, &binding);
    protocol.frame(&checkpoint).unwrap();
    let graph = service::finish::Graph { binding, succeeded: false, snapshot: [4; 16], members: 0 };
    assert!(protocol.frame(&graph.encode().unwrap()).unwrap_err().0.contains("continuation"));
    protocol.take_continuation();
    assert!(
        protocol.frame(&graph.encode().unwrap()).is_err(),
        "later ACK cannot repair earlier malformed order"
    );
    let mut other = protocol::Protocol::new(invocation_data()).unwrap();
    let binding = ready(&mut other);
    let graph = service::finish::Graph { binding, succeeded: false, snapshot: [4; 16], members: 0 };
    assert!(
        other.frame(&graph.encode().unwrap()).is_err(),
        "even zero-member graph needs complete original page"
    );
}
#[test]
fn diagnostic_offsets_and_scopes_cannot_replace_native_output() {
    let mut protocol = protocol::Protocol::new(invocation_data()).unwrap();
    let binding = ready(&mut protocol);
    let early = service::finish::Diagnostic {
        binding: binding.clone(),
        stream: service::Stream::Stderr,
        offset: 0,
        bytes: b"early".to_vec(),
    };
    assert!(protocol.frame(&early.encode().unwrap()).is_err());
    let mut protocol = protocol::Protocol::new(invocation_data()).unwrap();
    let binding = ready(&mut protocol);
    let checkpoint = compiler_checkpoint(&mut protocol, &binding);
    protocol.frame(&checkpoint).unwrap();
    protocol.take_continuation();
    let diagnostic = service::finish::Diagnostic {
        binding,
        stream: service::Stream::Stderr,
        offset: 0,
        bytes: b"root-only".to_vec(),
    };
    assert!(protocol.frame(&diagnostic.encode().unwrap()).unwrap().is_none());
    assert_eq!(protocol.diagnostic_lengths(), [0, 9]);
    assert!(protocol.frame(&diagnostic.encode().unwrap()).is_err());
}
#[test]
fn raw_partial_invalid_frame_reaches_original_file_before_decode_failure() {
    let directory = tempfile::tempdir().unwrap();
    let (tx, _rx) = mpsc::sync_channel(2);
    let pump = io::Pump::new(
        directory.path(),
        tx,
        Instant::now() + Duration::from_secs(5),
        Arc::new(AtomicBool::new(false)),
    )
    .unwrap();
    let mut pump = pump.lock().unwrap();
    let bytes = [0, 0, 0, 0, 0xff, 0];
    assert!(pump.accept(0, &bytes).is_err());
    let result = pump.finish();
    assert_eq!(fs::read(directory.path().join("root.stdout.frames.bin")).unwrap(), bytes);
    assert_eq!(result["streams"][0]["bytes_written"], 6);
    assert_eq!(result["streams"][0]["complete_bytes"], false);
    assert!(result["failure"].is_string());
    // A different original reader may already have read bytes when the first
    // observer fails. Keep those exact bytes on disk before propagating error.
    assert!(pump.accept(1, b"other actual stream\0\xff").is_err());
    assert_eq!(
        fs::read(directory.path().join("root.stderr.bin")).unwrap(),
        b"other actual stream\0\xff"
    );
    let result = pump.finish();
    assert_eq!(result["streams"][1]["complete_bytes"], false);
}
#[test]
fn raw_split_binary_frames_and_physical_eof_are_independent_from_graph_completion() {
    let directory = tempfile::tempdir().unwrap();
    let (tx, rx) = mpsc::sync_channel(2);
    let pump = io::Pump::new(
        directory.path(),
        tx,
        Instant::now() + Duration::from_secs(5),
        Arc::new(AtomicBool::new(false)),
    )
    .unwrap();
    let mut pump = pump.lock().unwrap();
    for bytes in [&[0, 0][..], &[0, 3, 0, 0xff][..], &[7][..]] {
        pump.accept(0, bytes).unwrap();
    }
    let io::Input::Frame(frame) = rx.recv().unwrap() else { panic!("not a frame") };
    assert_eq!(frame, [0, 0xff, 7]);
    pump.accept(0, &[]).unwrap();
    assert!(matches!(rx.recv().unwrap(), io::Input::Eof));
    pump.accept(1, b"actual stderr\0").unwrap();
    pump.accept(1, &[]).unwrap();
    let result = pump.finish();
    assert_eq!(result["streams"][0]["complete_bytes"], true);
    assert_eq!(result["streams"][1]["complete_bytes"], true);
    assert_eq!(
        fs::read(directory.path().join("root.stdout.frames.bin")).unwrap(),
        [0, 0, 0, 3, 0, 0xff, 7]
    );
    assert!(pump.accept(0, b"after EOF").is_err());
}
#[test]
fn disconnected_consumer_and_partial_eof_keep_actual_original_prefix_without_completion() {
    for disconnect in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let (tx, rx) = mpsc::sync_channel(1);
        if disconnect {
            drop(rx);
        }
        let pump = io::Pump::new(
            directory.path(),
            tx,
            Instant::now() + Duration::from_secs(5),
            Arc::new(AtomicBool::new(false)),
        )
        .unwrap();
        let mut pump = pump.lock().unwrap();
        let bytes = if disconnect { vec![0, 0, 0, 1, 0x7f] } else { vec![0, 0, 0, 7, 0xff] };
        if disconnect {
            assert!(pump.accept(0, &bytes).is_err());
        } else {
            pump.accept(0, &bytes).unwrap();
            assert!(pump.accept(0, &[]).is_err());
        }
        let report = pump.finish();
        assert!(report["failure"].is_string());
        assert_eq!(fs::read(directory.path().join("root.stdout.frames.bin")).unwrap(), bytes);
    }
}
#[test]
fn explicit_private_store_never_opens_a_sdk_or_delivers_to_an_account_root() {
    let fake = |path: &str| pair::FileIdentity {
        path: path.into(),
        resolved_path: path.into(),
        sha256: "a".repeat(64),
        link_text: None,
    };
    let request = Request {
        side: Side::Control,
        sdk_root: "/does-not-exist/sdk".into(),
        program: fake("/does-not-exist/sdk/bin/targo"),
        compiler: fake("/does-not-exist/sdk/bin/trustc"),
        cwd: "/does-not-exist/source".into(),
        target_directory: "/does-not-exist/results/control-target".into(),
        cargo_home: "/does-not-exist/cache".into(),
        proof_fixtures: Default::default(),
        trust_spec_source: fake("/does-not-exist/spec"),
        repetitions: 3,
        timeout_ns: 1,
    };
    let mut producer = NativeWorkloadProducer::new(Some("/must-not-open-private-store".into()));
    let refusal = workloads::Producer::start(&mut producer, &request).err().unwrap();
    assert!(refusal.0.contains("account fallback is forbidden"));
    assert!(producer.output.is_none());
    assert!(producer.observation.is_some());
}

#[test]
fn native_artifact_publication_is_checked_before_independent_consumer_hashing() {
    use std::os::unix::fs::PermissionsExt as _;
    let temporary = tempfile::tempdir().unwrap();
    let root = temporary.path().canonicalize().unwrap();
    let path = root.join("actual-output");
    fs::write(&path, b"retained actual publication bytes").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    let meta = fs::metadata(&path).unwrap();
    let mut reported = trust_resource_controller::MetadataFile {
        path: path.as_os_str().as_encoded_bytes().to_vec(),
        sha256: Sha256::digest(fs::read(&path).unwrap()).into(),
        bytes: meta.len(),
        device: meta.dev(),
        inode: meta.ino(),
    };
    let identity = artifact_identity(&reported, &root).unwrap();
    assert_eq!(identity, pair::file_identity(&path).unwrap());
    reported.bytes += 1;
    assert!(artifact_identity(&reported, &root).is_err());
    reported.bytes -= 1;
    reported.inode += 1;
    assert!(artifact_identity(&reported, &root).is_err());
    reported.inode -= 1;
    let alias = root.join("legacy-hardlink");
    fs::hard_link(&path, &alias).unwrap();
    assert!(
        artifact_identity(&reported, &root).is_err(),
        "original nlink1 publication boundary remains strict"
    );
    fs::remove_file(&alias).unwrap();
    fs::remove_file(&path).unwrap();
    fs::write(&alias, b"same bytes are insufficient for the original publication").unwrap();
    std::os::unix::fs::symlink(&alias, &path).unwrap();
    assert!(artifact_identity(&reported, &root).is_err());
}
