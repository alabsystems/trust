use super::*;
use crate::{CompletionCause, Outcome};

fn prepared() -> MetadataPrepared {
    MetadataPrepared {
        root_attempt: [1; 16],
        member_attempt: [3; 16],
        root: b"/sealed".to_vec(),
        policy: "native-metadata/macho-arm64-sysroot-rpath-v1".into(),
        scope:
            "held-load-command-input-observations/local-same-uid-no-name-writers/system-runtime-tcb"
                .into(),
        executable: MetadataFile {
            path: b"/sealed/bin/program".to_vec(),
            sha256: [4; 32],
            bytes: 20,
            device: 1,
            inode: 2,
        },
        runtime: vec![MetadataFile {
            path: b"/sealed/lib/runtime.dylib".to_vec(),
            sha256: [5; 32],
            bytes: 40,
            device: 1,
            inode: 3,
        }],
        loader_paths: vec![b"/sealed/lib".to_vec()],
        system_dependencies: vec!["/usr/lib/libSystem.B.dylib".into()],
        host: "host".into(),
        boot: "abcdef".into(),
    }
}
fn finished() -> StatusFrame {
    StatusFrame {
        root_attempt: [1; 16],
        member_attempt: [3; 16],
        status: Status::Finished {
            outcome: Outcome::Exit(7),
            cause: CompletionCause::Exited,
            runtime_ns: 8,
        },
    }
}

#[test]
fn prepared_inventory_binds_original_attempt_and_requested_image() {
    let value = prepared();
    let request = super::super::tests::request(&[b"-vV"]);
    value.validate_for(&request).unwrap();
    let bytes = value.encode().unwrap();
    assert_eq!(MetadataPrepared::decode(&bytes, [1; 16], [3; 16]).unwrap(), value);
    assert!(MetadataPrepared::decode(&bytes, [2; 16], [3; 16]).is_err());
    assert!(MetadataPrepared::decode(&bytes, [1; 16], [4; 16]).is_err());
    let mut foreign = request;
    foreign.program_sha256 = [9; 32];
    assert!(value.validate_for(&foreign).is_err());
    for end in 0..bytes.len() {
        assert!(MetadataPrepared::decode(&bytes[..end], [1; 16], [3; 16]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(MetadataPrepared::decode(&trailing, [1; 16], [3; 16]).is_err());
}

#[test]
fn prepared_inventory_refuses_duplicate_foreign_or_excessive_input_data() {
    for alteration in 0..11 {
        let mut changed = prepared();
        match alteration {
            0 => changed.runtime.push(changed.runtime[0].clone()),
            1 => changed.runtime[0].path = b"/foreign/runtime".to_vec(),
            2 => changed.runtime[0].path = b"/sealed-foreign/runtime".to_vec(),
            3 => changed.runtime[0].bytes = MAX_IMAGE_BYTES + 1,
            4 => changed.runtime[0].inode = 0,
            5 => changed.loader_paths.push(changed.loader_paths[0].clone()),
            6 => changed.system_dependencies.push(changed.system_dependencies[0].clone()),
            7 => changed.scope.push('\n'),
            8 => changed.runtime = vec![changed.runtime[0].clone(); MAX_IMAGES + 1],
            9 => changed.loader_paths[0] = b"/foreign".to_vec(),
            10 => changed.root_attempt = changed.member_attempt,
            _ => unreachable!(),
        }
        assert!(changed.encode().is_err(), "accepted altered inventory field {alteration}");
    }
}

#[test]
fn completion_preserves_actual_failure_and_requires_post_drain_input_result() {
    for integrity in [Ok(()), Err("original runtime changed after execution".into())] {
        let completion = MetadataCompletion { finished: finished(), inputs_unchanged: integrity };
        let bytes = completion.encode().unwrap();
        assert_eq!(MetadataCompletion::decode(&bytes, [1; 16], [3; 16]).unwrap(), completion);
        assert_eq!(
            MetadataEvent::decode(&bytes, [1; 16], [3; 16]).unwrap(),
            MetadataEvent::Completed(completion)
        );
        for end in 0..bytes.len() {
            assert!(MetadataCompletion::decode(&bytes[..end], [1; 16], [3; 16]).is_err());
        }
    }
    assert!(MetadataEvent::Status(finished()).encode().is_err());
    assert!(MetadataEvent::decode(&finished().encode().unwrap(), [1; 16], [3; 16]).is_err());
    let mut wrong = MetadataCompletion { finished: finished(), inputs_unchanged: Ok(()) };
    wrong.finished.status = Status::Attached;
    assert!(wrong.encode().is_err());
    wrong.finished = finished();
    wrong.inputs_unchanged = Err(String::new());
    assert!(wrong.encode().is_err());
}
