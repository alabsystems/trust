//! Codec fixtures are DATA only, never actual Root/SDK/output/retirement owners.
use super::*;
use crate::{BirthKind, Context, Identity, JobBinding, Memory, SdkCustody};

fn fid(inode: u64) -> FileIdentity {
    FileIdentity { device: 0, inode }
}
pub(super) fn key() -> Key {
    Key {
        query: ContextQuery {
            binding: JobBinding {
                session: "s-abcd".into(),
                root_attempt: [1; 16],
                capability: [9; 32],
            },
            call_attempt: [2; 16],
        },
        graph: [3; 16],
    }
}
pub(super) fn enrollment() -> Enrollment {
    Enrollment {
        key: key(),
        source: b"/source".to_vec(),
        output: b"/source/build".to_vec(),
        gnu: GnuIdentity::NumericPipe { read: fid(10), write: fid(11) },
    }
}
pub(super) fn context() -> ContextReply {
    let identity = Identity { pid: 42, birth: 77, birth_kind: BirthKind::MacosWallMicroseconds };
    ContextReply {
        call_attempt: key().query.call_attempt,
        context: Context {
            session: key().query.binding.session,
            root_attempt: key().query.binding.root_attempt,
            host: "host".into(),
            boot: "a".into(),
            original_root: identity,
            subject: Subject::Root { identity },
            cpu: Cpu::RetainedFixed { units: 7, native_manifest: fid(1) },
            memory: Memory {
                bytes: 1024,
                namespace: [4; 16],
                marker: "1-2-3".into(),
                epoch: [5; 16],
                guard: fid(2),
            },
            sdk: Some(SdkCustody {
                execution: b"/sdk".to_vec(),
                build: 1,
                lease_path: b"/sdk/lease".to_vec(),
                lease: fid(3),
                inherited_fd: 5,
            }),
        },
    }
}
fn attachment() -> OutputAttachment {
    OutputAttachment { key: key(), root: fid(12), lock: fid(13) }
}

#[test]
fn support_and_enrollment_have_distinct_versions_and_purposes() {
    let query = SupportQuery { key: key() };
    let request = enrollment();
    assert!(SupportQuery::decode(&query.encode().unwrap()).unwrap() == query);
    assert!(Enrollment::decode(&request.encode().unwrap()).unwrap() == request);
    assert!(SupportQuery::decode(&request.encode().unwrap()).is_err());
    assert!(Enrollment::decode(&query.encode().unwrap()).is_err());
    assert_ne!(query.hello().unwrap(), request.hello().unwrap());
}

#[test]
fn graph_nonce_and_original_query_are_complete_binding_data() {
    for nonce in [[0; 16], [1; 16], [2; 16]] {
        let mut request = enrollment();
        request.key.graph = nonce;
        assert!(request.encode().is_err());
    }
    let reply = SupportReply::Supported {
        key: key(),
        remaining_root_ns: 1_000_000_000,
        context: Box::new(context()),
    }
    .encode()
    .unwrap();
    let mut query = SupportQuery { key: key() };
    query.key.query.binding.capability[0] ^= 1;
    assert!(SupportReply::decode(&reply, &query).is_err());
    query = SupportQuery { key: key() };
    query.key.graph[0] ^= 1;
    assert!(SupportReply::decode(&reply, &query).is_err());
}

#[test]
fn unequal_numeric_pipe_inodes_and_byte_paths_are_preserved() {
    let mut request = enrollment();
    request.source = b"/source-\xff".to_vec();
    let decoded = Enrollment::decode(&request.encode().unwrap()).unwrap();
    assert!(decoded == request);
    assert!(matches!(decoded.gnu, GnuIdentity::NumericPipe { read, write } if read != write));
}

#[test]
fn paths_and_transport_kinds_are_closed_before_delivery() {
    for path in [b"relative".as_slice(), b"/", b"/a/../b", b"/a//b", b"/a\0b"] {
        let mut request = enrollment();
        request.source = path.to_vec();
        assert!(request.encode().is_err());
        request = enrollment();
        request.gnu = GnuIdentity::NamedFifo { path: path.to_vec(), backing: fid(1) };
        assert!(request.encode().is_err());
    }
    let mut request = enrollment();
    request.output = request.source.clone();
    assert!(request.encode().is_err());
    request = enrollment();
    request.gnu = GnuIdentity::NumericPipe { read: fid(0), write: fid(1) };
    assert!(request.encode().is_err());
}

#[test]
fn successful_context_requires_original_fixed_root_and_sdk_observations() {
    let request = SupportQuery { key: key() };
    let mut observations = Vec::new();
    let mut absent = context();
    absent.context.sdk = None;
    observations.push(absent);
    let mut cooperative = context();
    cooperative.context.cpu = Cpu::CooperativeShared { ceiling: 7, native_manifest: fid(1) };
    observations.push(cooperative);
    let mut member = context();
    member.context.subject = Subject::RegisteredMember {
        identity: Identity { pid: 43, birth: 78, birth_kind: BirthKind::MacosWallMicroseconds },
        attempt: [8; 16],
    };
    observations.push(member);
    let mut wrong_call = context();
    wrong_call.call_attempt[0] ^= 1;
    observations.push(wrong_call);
    for observed in observations {
        assert!(
            SupportReply::Supported {
                key: request.key.clone(),
                remaining_root_ns: 1_000_000_000,
                context: Box::new(observed)
            }
            .encode()
            .is_err()
        );
    }
}

#[test]
fn support_requires_an_observed_finite_nonexpired_root_budget() {
    let reply =
        SupportReply::Supported { key: key(), remaining_root_ns: 0, context: Box::new(context()) };
    assert!(reply.encode().is_err());
    let query = SupportQuery { key: key() };
    let reply = SupportReply::Supported {
        key: key(),
        remaining_root_ns: 123,
        context: Box::new(context()),
    };
    assert!(SupportReply::decode(&reply.encode().unwrap(), &query).unwrap() == reply);
}

#[test]
fn enrollment_reply_binds_complete_request_digest_and_context() {
    let request = enrollment();
    let digest = [6; 32]; // Opaque equality fixture, not a computed authentication claim.
    for reply in [
        EnrollmentReply::Prepared { key: key(), enrollment_sha256: digest, context: context() },
        EnrollmentReply::Enrolled { key: key(), enrollment_sha256: digest, context: context() },
    ] {
        let bytes = reply.encode().unwrap();
        assert!(EnrollmentReply::decode(&bytes, &request, digest).unwrap() == reply);
        assert!(EnrollmentReply::decode(&bytes, &request, [7; 32]).is_err());
        assert!(SupportReply::decode(&bytes, &SupportQuery { key: key() }).is_err());
    }
    let before = request.binding_preimage().unwrap();
    let mut changed = request.clone();
    changed.output.extend(b"-other");
    assert_ne!(before, changed.binding_preimage().unwrap());
    changed = request;
    changed.gnu = GnuIdentity::NamedFifo { path: b"/gnu".to_vec(), backing: fid(10) };
    assert_ne!(before, changed.binding_preimage().unwrap());
}

#[test]
fn output_attachment_and_reply_bind_original_root_and_lock_separately() {
    let request = attachment();
    assert!(OutputAttachment::decode(&request.encode().unwrap()).unwrap() == request);
    let digest = [6; 32];
    for reply in [
        OutputReply::Prepared { key: key(), attachment_sha256: digest, context: context() },
        OutputReply::Attached { key: key(), attachment_sha256: digest, context: context() },
    ] {
        let bytes = reply.encode().unwrap();
        assert!(OutputReply::decode(&bytes, &request, digest).unwrap() == reply);
        assert!(OutputReply::decode(&bytes, &request, [7; 32]).is_err());
        assert!(EnrollmentReply::decode(&bytes, &enrollment(), digest).is_err());
    }
    let original = request.binding_preimage().unwrap();
    let mut changed = request.clone();
    std::mem::swap(&mut changed.root, &mut changed.lock);
    assert_ne!(original, changed.binding_preimage().unwrap());
    assert_ne!(original, enrollment().binding_preimage().unwrap());
}

#[test]
fn every_frame_rejects_missing_bytes_trailing_bytes_and_legacy_context() {
    let query = SupportQuery { key: key() };
    let request = enrollment();
    let output = attachment();
    type Rejection = Box<dyn Fn(&[u8]) -> bool>;
    let checks: Vec<(Vec<u8>, Rejection)> = vec![
        (query.encode().unwrap(), Box::new(|b| SupportQuery::decode(b).is_err())),
        (request.encode().unwrap(), Box::new(|b| Enrollment::decode(b).is_err())),
        (output.encode().unwrap(), Box::new(|b| OutputAttachment::decode(b).is_err())),
    ];
    for (bytes, rejected) in checks {
        for end in 0..bytes.len() {
            assert!(rejected(&bytes[..end]), "accepted truncated frame at {end}");
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(rejected(&extra));
        assert!(rejected(&context().encode().unwrap()));
    }
}

#[test]
fn refusals_remain_bound_and_never_create_a_success_observation() {
    let query = SupportQuery { key: key() };
    let refused = SupportReply::Refused { key: key(), reason: "old backend".into() };
    assert!(SupportReply::decode(&refused.encode().unwrap(), &query).unwrap() == refused);
    for reason in ["", "bad\0reason"] {
        assert!(SupportReply::Refused { key: key(), reason: reason.into() }.encode().is_err());
    }
    let bytes =
        EnrollmentReply::Refused { key: key(), reason: "not eligible".into() }.encode().unwrap();
    assert!(matches!(
        EnrollmentReply::decode(&bytes, &enrollment(), [6; 32]).unwrap(),
        EnrollmentReply::Refused { .. }
    ));
}
