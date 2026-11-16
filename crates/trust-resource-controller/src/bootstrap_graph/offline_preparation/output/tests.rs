// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Packet DATA only. These tests create no native output, lock or SDK owner.
use super::*;

fn request() -> PreparationOutputAttachment {
    PreparationOutputAttachment {
        key: super::super::tests::request().key,
        root: FileIdentity {
            device: 3,
            inode: 4,
        },
        lock: FileIdentity {
            device: 3,
            inode: 5,
        },
    }
}

#[test]
fn early_output_frames_are_distinct_and_bind_full_original_operation_and_digest() {
    let request = request();
    let bytes = request.encode().unwrap();
    assert!(PreparationOutputAttachment::decode(&bytes).unwrap() == request);
    assert!(crate::bootstrap_graph::OutputAttachment::decode(&bytes).is_err());
    let old = request.physical_binding().encode().unwrap();
    assert!(PreparationOutputAttachment::decode(&old).is_err());
    let digest = [0x31; 32];
    for reply in [
        PreparationOutputReply::Prepared {
            request: request.clone(),
            attachment_sha256: digest,
            remaining_input_ns: MAX_BUDGET_NS,
            context: crate::bootstrap_graph::tests::context(),
        },
        PreparationOutputReply::Custodied {
            request: request.clone(),
            attachment_sha256: digest,
            remaining_input_ns: 1,
            context: crate::bootstrap_graph::tests::context(),
        },
    ] {
        let encoded = reply.encode().unwrap();
        assert!(PreparationOutputReply::decode(&encoded, &request, digest).unwrap() == reply);
        assert!(PreparationOutputReply::decode(&encoded, &request, [0x32; 32]).is_err());
        let mut other = request.clone();
        other.key.operation = [0x72; 16];
        assert!(PreparationOutputReply::decode(&encoded, &other, digest).is_err());
        for cut in 0..encoded.len() {
            assert!(PreparationOutputReply::decode(&encoded[..cut], &request, digest).is_err());
        }
        let mut trailing = encoded;
        trailing.push(0);
        assert!(PreparationOutputReply::decode(&trailing, &request, digest).is_err());
    }
    for cut in 0..bytes.len() {
        assert!(PreparationOutputAttachment::decode(&bytes[..cut]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(PreparationOutputAttachment::decode(&trailing).is_err());
}

#[test]
fn early_output_rejects_aliases_foreign_sequence_and_extended_remaining_budget() {
    let original = request();
    let mut changed = original.clone();
    changed.lock = changed.root;
    assert!(changed.encode().is_err());
    changed = original.clone();
    changed.key.sequence = 2;
    assert!(changed.encode().is_err());
    for remaining_input_ns in [0, MAX_BUDGET_NS + 1] {
        let reply = PreparationOutputReply::Custodied {
            request: original.clone(),
            attachment_sha256: [0x31; 32],
            remaining_input_ns,
            context: crate::bootstrap_graph::tests::context(),
        };
        assert!(reply.encode().is_err());
    }
}
