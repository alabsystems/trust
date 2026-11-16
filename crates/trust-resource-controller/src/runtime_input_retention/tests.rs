use super::*;
use crate::{BirthKind, Context, Cpu, Identity, JobBinding, Memory, Subject};

fn query() -> ContextQuery {
    ContextQuery {
        binding: JobBinding {
            session: "s-abcd".into(),
            root_attempt: [1; 16],
            capability: [2; 32],
        },
        call_attempt: [3; 16],
    }
}
fn input(kind: Kind, path: &[u8], target: &[u8], inode: u64) -> Input {
    Input {
        kind,
        logical_path: path.to_vec(),
        target: target.to_vec(),
        alias: None,
        backing: FileIdentity { device: 1, inode },
        size: (kind == Kind::RuntimeFile).then_some(0),
        sha256: (kind == Kind::RuntimeFile).then_some([0; 32]),
        executable: false,
    }
}
fn request() -> Request {
    Request {
        query: query(),
        transfer: [4; 16],
        inputs: vec![
            input(Kind::RuntimeRoot, b"", b"/runtime", 1),
            input(Kind::RuntimeFile, b"bin/trustc", b"/runtime/bin/trustc", 2),
            input(Kind::OutputRoot, b"", b"/output", 3),
            input(Kind::OutputLock, b"lock", b"/output/lock", 4),
        ],
    }
}
fn context() -> ContextReply {
    let root = Identity { pid: 42, birth: 77, birth_kind: BirthKind::MacosWallMicroseconds };
    ContextReply {
        call_attempt: query().call_attempt,
        context: Context {
            session: query().binding.session,
            root_attempt: query().binding.root_attempt,
            host: "host".into(),
            boot: "abc123".into(),
            original_root: root,
            subject: Subject::Root { identity: root },
            cpu: Cpu::RetainedFixed {
                units: 1,
                native_manifest: FileIdentity { device: 1, inode: 20 },
            },
            memory: Memory {
                bytes: 1,
                namespace: [5; 16],
                marker: "1-2-3".into(),
                epoch: [6; 16],
                guard: FileIdentity { device: 1, inode: 21 },
            },
            sdk: None,
        },
    }
}
#[test]
fn retention_codec_preserves_complete_alias_population_and_refuses_partial_or_ambiguous_data() {
    let mut value = request();
    value.inputs[1].alias = Some(b"../actual-trustc".to_vec());
    value.inputs.push(input(Kind::RuntimeDirectory, b"lib", b"/runtime/lib", 5));
    assert!(Request::decode(&value.encode().unwrap()).unwrap() == value);
    let bytes = value.encode().unwrap();
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(Request::decode(&trailing).is_err());
    for mutation in 0..8 {
        let mut invalid = value.clone();
        match mutation {
            0 => invalid.transfer = invalid.query.call_attempt,
            1 => invalid.inputs.push(invalid.inputs[1].clone()),
            2 => invalid.inputs[1].size = None,
            3 => invalid.inputs[1].sha256 = None,
            4 => invalid.inputs[1].target = b"/foreign/trustc".to_vec(),
            5 => invalid.inputs[1].logical_path = b"../bin/trustc".to_vec(),
            6 => invalid.inputs[2].size = Some(1),
            _ => {
                invalid.inputs.remove(3);
            }
        }
        assert!(invalid.encode().is_err(), "mutation {mutation}");
    }
    // Distinct explicit aliases may retain separate OFDs of the same inode.
    let mut alias = value.inputs[1].clone();
    alias.logical_path = b"bin/alias".to_vec();
    value.inputs.push(alias);
    assert!(value.encode().is_ok());
    let mut huge = request();
    for n in 0..MAX_INPUTS {
        huge.inputs.push(input(
            Kind::RuntimeFile,
            format!("lib/{n}").as_bytes(),
            format!("/runtime/lib/{n}").as_bytes(),
            n as u64 + 10,
        ));
    }
    assert!(huge.encode().is_err());
    let mut directory_is_not_image = request();
    directory_is_not_image.inputs[0].executable = true;
    assert!(directory_is_not_image.encode().is_err());
}
#[test]
fn retention_support_and_transfer_versions_bind_original_call_and_never_cross_decode() {
    let request = request();
    let support = SupportQuery { query: query() };
    assert!(SupportQuery::decode(&support.encode().unwrap()).unwrap() == support);
    assert!(SupportQuery::decode(&request.encode().unwrap()).is_err());
    assert!(Request::decode(&support.encode().unwrap()).is_err());
    let ready = SupportReply::Supported { context: Box::new(context()) };
    assert_eq!(SupportReply::decode(&ready.encode().unwrap(), &support).unwrap(), ready);
    let accepted = Reply::Accepted { key: request.key(), context: context() };
    assert_eq!(Reply::decode(&accepted.encode().unwrap(), &request).unwrap(), accepted);
    assert!(SupportReply::decode(&accepted.encode().unwrap(), &support).is_err());
    assert!(Reply::decode(&ready.encode().unwrap(), &request).is_err());
    let mut foreign = request.clone();
    foreign.transfer = [9; 16];
    assert!(Reply::decode(&accepted.encode().unwrap(), &foreign).is_err());
    let mut foreign = support.clone();
    foreign.query.call_attempt = [9; 16];
    assert!(SupportReply::decode(&ready.encode().unwrap(), &foreign).is_err());
    for frame in [
        Transfer::Chunk { key: request.key(), offset: 0, count: 128 },
        Transfer::End { key: request.key(), count: 171 },
    ] {
        let bytes = frame.encode().unwrap();
        assert_eq!(Transfer::decode(&bytes).unwrap(), frame);
        let mut trailing = bytes;
        trailing.push(0);
        assert!(Transfer::decode(&trailing).is_err());
    }
    assert!(Transfer::Chunk { key: request.key(), offset: 0, count: 129 }.encode().is_err());
}

#[cfg(all(feature = "channel", any(target_os = "macos", target_os = "linux")))]
mod native;
