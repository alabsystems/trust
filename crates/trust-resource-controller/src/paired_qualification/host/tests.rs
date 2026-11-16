use super::*;
use crate::{
    BirthKind, Context, Cpu, FileIdentity, Identity, JobBinding, Memory, SdkCustody, Subject,
};

fn request() -> ReadyRequest {
    ReadyRequest {
        query: ContextQuery {
            binding: JobBinding {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            call_attempt: [9; 16],
        },
        invocation: crate::paired_qualification::tests::invocation(),
    }
}
fn reply(request: &ReadyRequest) -> ReadyReply {
    let root = Identity { pid: 42, birth: 123, birth_kind: BirthKind::MacosWallMicroseconds };
    ReadyReply {
        context: ContextReply {
            call_attempt: request.query.call_attempt,
            context: Context {
                session: request.query.binding.session.clone(),
                root_attempt: request.query.binding.root_attempt,
                host: "host".into(),
                boot: "abcd".into(),
                original_root: root,
                subject: Subject::Root { identity: root },
                cpu: Cpu::CooperativeShared {
                    ceiling: 2,
                    native_manifest: FileIdentity { device: 1, inode: 10 },
                },
                memory: Memory {
                    bytes: 1 << 30,
                    namespace: [1; 16],
                    marker: "1-42-1".into(),
                    epoch: [2; 16],
                    guard: FileIdentity { device: 1, inode: 11 },
                },
                sdk: Some(SdkCustody {
                    execution: b"/sdk".to_vec(),
                    build: 1,
                    lease_path: b"/leases/1".to_vec(),
                    lease: FileIdentity { device: 1, inode: 12 },
                    inherited_fd: 5,
                }),
            },
        },
        invocation_sha256: [8; 32],
        primary: PrimaryCpu {
            inherited_fd: 6,
            slot: 0,
            backing: FileIdentity { device: 1, inode: 20 },
        },
        supplementary: vec![PrimaryCpu {
            inherited_fd: 7,
            slot: 1,
            backing: FileIdentity { device: 1, inode: 21 },
        }],
    }
}
#[test]
fn paired_ready_round_trip_preserves_complete60_and_distinct_v2() {
    let request = request();
    let frame = request.encode().unwrap();
    assert!(ReadyRequest::decode(&frame).unwrap() == request);
    let reply = reply(&request);
    let bytes = reply.encode().unwrap();
    assert!(ReadyReply::decode(&bytes, &request).unwrap() == reply);
    assert_eq!(reply.cpu_set().count(), 2);
    let old = crate::workload::host::ReadyRequest {
        query: request.query.clone(),
        invocation: request.invocation.consumer.clone(),
    };
    assert!(ReadyRequest::decode(&old.encode().unwrap()).is_err());
    assert!(crate::workload::host::ReadyRequest::decode(&frame).is_err());
    assert!(crate::workload::host::ReadyReply::decode(&bytes, &old).is_err());
    let old_reply = crate::workload::host::ReadyReply {
        context: reply.context.clone(),
        invocation_sha256: reply.invocation_sha256,
        primary: reply.primary.clone(),
        supplementary: reply.supplementary.clone(),
    };
    assert!(ReadyReply::decode(&old_reply.encode().unwrap(), &request).is_err());
}
#[test]
fn paired_ready_rejects_truncation_trailing_bytes_and_foreign_call() {
    let request = request();
    let frame = request.encode().unwrap();
    for length in 0..frame.len() {
        assert!(ReadyRequest::decode(&frame[..length]).is_err());
    }
    let mut extra = frame;
    extra.push(0);
    assert!(ReadyRequest::decode(&extra).is_err());
    let bytes = reply(&request).encode().unwrap();
    for length in 0..bytes.len() {
        assert!(ReadyReply::decode(&bytes[..length], &request).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(ReadyReply::decode(&extra, &request).is_err());
    let mut foreign = request.clone();
    foreign.query.call_attempt = [7; 16];
    assert!(ReadyReply::decode(&bytes, &foreign).is_err());
    foreign = request.clone();
    foreign.query.binding.root_attempt = [6; 16];
    assert!(ReadyReply::decode(&bytes, &foreign).is_err());
    foreign = request;
    foreign.query.binding.session = "s-ff".into();
    assert!(ReadyReply::decode(&bytes, &foreign).is_err());
}
#[test]
fn paired_ready_never_drops_ay_subject_or_reinterprets_resource_observations() {
    let request = request();
    let original = request.encode().unwrap();
    let mut changed = request.clone();
    changed.invocation.ay.source_commit[0] ^= 1;
    assert_ne!(changed.encode().unwrap(), original);
    changed = request.clone();
    changed.invocation.ay.crate_tree[0] ^= 1;
    assert_ne!(changed.encode().unwrap(), original);
    changed = request.clone();
    changed.invocation.ay.lockfile.sha256[0] ^= 1;
    assert_ne!(changed.encode().unwrap(), original);
    for mutation in 0..8 {
        let mut value = reply(&request);
        match mutation {
            0 => value.invocation_sha256 = [0; 32],
            1 => value.context.context.sdk = None,
            2 => {
                value.context.context.cpu = Cpu::RetainedFixed {
                    units: 2,
                    native_manifest: FileIdentity { device: 1, inode: 10 },
                }
            }
            3 => value.primary.inherited_fd = 5,
            4 => value.supplementary[0].inherited_fd = value.primary.inherited_fd,
            5 => value.supplementary[0].slot = value.primary.slot,
            6 => value.supplementary[0].backing = value.primary.backing,
            7 => value.supplementary[0].backing.inode = 0,
            _ => unreachable!(),
        }
        assert!(value.encode().is_err(), "mutation {mutation}");
    }
}
