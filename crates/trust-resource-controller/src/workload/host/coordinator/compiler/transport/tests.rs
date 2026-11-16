// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Framing DATA only; no native original/witness or resource is fabricated.
use super::*;
fn request() -> TransportRequest {
    TransportRequest {
        query: crate::ContextQuery {
            binding: crate::JobBinding {
                session: "s-ab12".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            call_attempt: [3; 16],
        },
        selected: CompilerSelection {
            root_attempt: [1; 16],
            member_attempt: [4; 16],
            coordinator_attempt: [5; 16],
            prepared_sha256: [6; 32],
        },
    }
}
#[test]
fn transport_request_is_complete_and_bound_to_one_original_preparation() {
    let request = request();
    let bytes = request.encode().unwrap();
    let actual = TransportRequest::decode(&bytes).unwrap();
    assert!(actual.query == request.query);
    assert_eq!(actual.selected, request.selected);
    let mut legacy = bytes.clone();
    legacy[16..24].copy_from_slice(&1u64.to_be_bytes());
    assert!(
        TransportRequest::decode(&legacy).is_err(),
        "five-original profile cannot admit complete control transfer"
    );
    for end in 0..bytes.len() {
        assert!(TransportRequest::decode(&bytes[..end]).is_err());
    }
    let mut extra = bytes;
    extra.push(0);
    assert!(TransportRequest::decode(&extra).is_err());
    let mut wrong = request.clone();
    wrong.selected.root_attempt = [7; 16];
    assert!(wrong.encode().is_err());
    wrong = request.clone();
    wrong.selected.member_attempt = wrong.selected.coordinator_attempt;
    assert!(wrong.encode().is_err());
    wrong = request;
    wrong.selected.prepared_sha256 = [0; 32];
    assert!(wrong.encode().is_err());
}

#[test]
fn transport_reply_never_discards_context_target_or_preparation_identity() {
    // Syntactic protocol DATA only. No native owner/SDK/endpoint is created.
    let request = request();
    let root = Identity {
        pid: 200,
        birth: 20,
        birth_kind: BirthKind::LinuxStartTicks,
    };
    let file = crate::FileIdentity {
        device: 1,
        inode: 2,
    };
    let mut reply = TransportReply {
        selected: request.selected.clone(),
        context: crate::ContextReply {
            call_attempt: request.query.call_attempt,
            context: crate::Context {
                session: request.query.binding.session.clone(),
                root_attempt: request.selected.root_attempt,
                host: "host".into(),
                boot: "ab12".into(),
                original_root: root,
                subject: crate::Subject::Root { identity: root },
                cpu: crate::Cpu::CooperativeShared {
                    ceiling: 2,
                    native_manifest: file,
                },
                memory: crate::Memory {
                    bytes: 1,
                    namespace: [7; 16],
                    marker: "1-2-3".into(),
                    epoch: [8; 16],
                    guard: file,
                },
                sdk: Some(crate::SdkCustody {
                    execution: b"/sdk".to_vec(),
                    build: 1,
                    lease_path: b"/lease".to_vec(),
                    lease: file,
                    inherited_fd: 5,
                }),
            },
        },
        target: Identity {
            pid: 201,
            birth: 21,
            birth_kind: root.birth_kind,
        },
        advertisement: b"opaque-native-observation".to_vec(),
        backings: [file; TRANSPORT_ORIGINALS],
    };
    let bytes = reply.encode().unwrap();
    let actual = TransportReply::decode(&bytes, &request).unwrap();
    assert_eq!(actual.context, reply.context);
    assert_eq!(actual.target, reply.target);
    assert_eq!(actual.advertisement, reply.advertisement);
    assert_eq!(actual.backings, reply.backings);
    let mut legacy = bytes.clone();
    legacy[16..24].copy_from_slice(&1u64.to_be_bytes());
    assert!(TransportReply::decode(&legacy, &request).is_err());
    for end in 0..bytes.len() {
        assert!(TransportReply::decode(&bytes[..end], &request).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(TransportReply::decode(&extra, &request).is_err());
    let mut stale = request.clone();
    stale.selected.prepared_sha256 = [9; 32];
    assert!(TransportReply::decode(&bytes, &stale).is_err());
    stale = request.clone();
    stale.query.call_attempt = [10; 16];
    assert!(TransportReply::decode(&bytes, &stale).is_err());
    reply.backings[0].inode = 0;
    assert!(reply.encode().is_err());
    reply.backings[0] = file;
    reply.target = root;
    assert!(reply.encode().is_err());
    reply.target.pid += 1;
    reply.context.context.sdk = None;
    assert!(reply.encode().is_err());
}
