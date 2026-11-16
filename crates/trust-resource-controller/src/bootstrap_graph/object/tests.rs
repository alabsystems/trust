//! DATA/codec controls only; no fixture constructs an SDK or execution owner.
use super::*;
use crate::CompletionCause;

pub(crate) fn request() -> Request {
    let query = super::super::query::tests::request();
    Request {
        key: query.key,
        gnu: query.gnu,
        sdk_root: query.sdk_root,
        driver: MetadataFile { path: b"/sdk/bin/tippy-driver".to_vec(), ..query.program.clone() },
        compiler: query.program,
        source_kind: SourceKind::NativeLeafV1,
        source_root: b"/source".to_vec(),
        source_directory: FileIdentity { device: 1, inode: 10 },
        source: MetadataFile {
            path: b"/source/src/bootstrap/native_object.rs".to_vec(),
            sha256: SOURCE_SHA256,
            bytes: SOURCE_BYTES.len() as u64,
            device: 1,
            inode: 11,
        },
        output_root: b"/output".to_vec(),
        output_directory: FileIdentity { device: 1, inode: 12 },
        output_lock: FileIdentity { device: 1, inode: 13 },
        destination: b"native_leaf.o".to_vec(),
        timeout_ns: MAX_COMPILE_NS,
    }
}
pub(crate) fn prepared(request: &Request) -> Prepared {
    let query = super::super::query::tests::request();
    let mut inventory = super::super::query::tests::prepared(&query);
    inventory.policy = PREPARED_POLICY.into();
    inventory.scope = PREPARED_SCOPE.into();
    inventory.executable = request.driver.clone();
    inventory.runtime.push(request.compiler.clone());
    let operation: String = request.key.operation.iter().map(|b| format!("{b:02x}")).collect();
    Prepared {
        inventory,
        staging: format!(".trust-object-{operation}-{}.o", "a".repeat(32)).into_bytes(),
    }
}
fn terminal(request: &Request, exit: i32) -> Terminal {
    Terminal::Completed {
        completion: Box::new(MetadataCompletion {
            finished: StatusFrame {
                root_attempt: request.key.graph.query.binding.root_attempt,
                member_attempt: request.key.operation,
                status: Status::Finished {
                    outcome: Outcome::Exit(exit),
                    cause: CompletionCause::Exited,
                    runtime_ns: 8,
                },
            },
            inputs_unchanged: Ok(()),
        }),
        observation: crate::accounting::Observation::uncollected(),
        artifact: if exit == 0 {
            Some(MetadataFile {
                path: request.output_path(),
                sha256: [9; 32],
                bytes: 544,
                device: 1,
                inode: 14,
            })
        } else {
            None
        },
    }
}
#[test]
fn exact_source_and_fixed_argv_have_no_arbitrary_rust_or_backend_channel() {
    assert_eq!(SOURCE_BYTES, include_bytes!("../../../../../src/bootstrap/native_object.rs"));
    assert_eq!(SOURCE_BYTES.len(), 435);
    let request = request();
    let staging = prepared(&request).staging;
    assert_eq!(
        request.arguments(&staging).unwrap(),
        vec![
            b"--cap-lints=allow".to_vec(),
            b"--crate-name".to_vec(),
            b"trust_bootstrap_native_object".to_vec(),
            b"--crate-type=rlib".to_vec(),
            b"--emit=obj".to_vec(),
            b"-o".to_vec(),
            join(&request.output_root, &staging),
            request.source.path.clone(),
        ]
    );
    for leaf in [b"../escape.o".as_slice(), b"sub/file.o", b".hidden.o", b"alias", b"x\0.o"] {
        let mut bad = request.clone();
        bad.destination = leaf.to_vec();
        assert!(bad.encode().is_err());
    }
    for staging in [b".trust-object-other.o".as_slice(), b"../x.o", b"out.o"] {
        assert!(request.arguments(staging).is_err());
    }
    let mut bad = request.clone();
    bad.source.sha256[0] ^= 1;
    assert!(bad.encode().is_err());
    let mut bad = request.clone();
    bad.source.path = b"/source/arbitrary.rs".to_vec();
    assert!(bad.encode().is_err());
    let mut bad = request.clone();
    bad.driver.path = b"/sdk/bin/trustc".to_vec();
    assert!(bad.encode().is_err());
}
#[test]
fn full_object_request_and_new_versions_refuse_old_query_and_incomplete_binding() {
    let request = request();
    let bytes = request.encode().unwrap();
    assert!(Request::decode(&bytes).unwrap() == request);
    assert!(super::super::query::Request::decode(&bytes).is_err());
    assert!(Request::decode(&super::super::query::tests::request().encode().unwrap()).is_err());
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Request::decode(&trailing).is_err());
    let mut changed = request.clone();
    changed.output_lock.inode += 1;
    assert_ne!(request.binding_preimage().unwrap(), changed.binding_preimage().unwrap());
    changed = request.clone();
    changed.key.sequence += 1;
    assert_ne!(request.binding_preimage().unwrap(), changed.binding_preimage().unwrap());
    changed = request.clone();
    changed.source_directory.inode += 1;
    assert_ne!(request.binding_preimage().unwrap(), changed.binding_preimage().unwrap());
    changed = request.clone();
    changed.timeout_ns = MAX_COMPILE_NS + 1;
    assert!(changed.encode().is_err());
}
#[test]
fn prepared_streams_bind_original_operation_image_policy_and_stage() {
    let request = request();
    let digest = [7; 32];
    for event in [
        Event::Prepared(Box::new(prepared(&request))),
        Event::Started(super::super::query::tests::started()),
        Event::Output { stream: Stream::Stderr, offset: 0, bytes: vec![0, 255] },
        Event::Eof { stream: Stream::Stdout, bytes: 0 },
    ] {
        let bytes = event.encode(&request, digest).unwrap();
        assert_eq!(Event::decode(&bytes, &request, digest).unwrap(), event);
        assert!(Event::decode(&bytes, &request, [8; 32]).is_err());
        for end in 0..bytes.len() {
            assert!(Event::decode(&bytes[..end], &request, digest).is_err());
        }
    }
    for field in 0..5 {
        let mut bad = prepared(&request);
        match field {
            0 => bad.inventory.policy = "old-profile".into(),
            1 => bad.inventory.scope = "foreign".into(),
            2 => bad.inventory.executable.inode += 1,
            3 => bad.inventory.runtime.clear(),
            _ => bad.staging = b"foreign.o".to_vec(),
        }
        assert!(Event::Prepared(Box::new(bad)).encode(&request, digest).is_err());
    }
    assert!(
        Event::Output { stream: Stream::Stdout, offset: MAX_OUTPUT, bytes: vec![1] }
            .encode(&request, digest)
            .is_err()
    );
}
#[test]
fn distinct_terminal_preserves_status_missing_metrics_and_exact_artifact_binding() {
    let request = request();
    let digest = [7; 32];
    for exit in [0, 7] {
        let value = terminal(&request, exit);
        let bytes = value.encode(&request, digest).unwrap();
        assert_eq!(Terminal::decode(&bytes, &request, digest).unwrap(), value);
        assert!(Terminal::decode(&bytes, &request, [8; 32]).is_err());
        let Terminal::Completed { completion, observation, artifact } = value else {
            unreachable!()
        };
        assert!(observation.cpu_times.is_none() && observation.peak_rss_bytes.is_none());
        assert_eq!(artifact.is_some(), exit == 0);
        assert!(Terminal::decode(&completion.encode().unwrap(), &request, digest).is_err());
    }
    let mut bad = terminal(&request, 0);
    if let Terminal::Completed { artifact: Some(file), .. } = &mut bad {
        file.path = b"/output/foreign.o".to_vec();
    }
    assert!(bad.encode(&request, digest).is_err());
    let mut bad = terminal(&request, 0);
    if let Terminal::Completed { artifact, .. } = &mut bad {
        *artifact = None;
    }
    assert!(bad.encode(&request, digest).is_err());
    let mut bad = terminal(&request, 7);
    if let Terminal::Completed { artifact, .. } = &mut bad {
        *artifact = Some(MetadataFile {
            path: request.output_path(),
            sha256: [1; 32],
            bytes: 544,
            device: 1,
            inode: 14,
        });
    }
    assert!(bad.encode(&request, digest).is_err());
}
