use super::*;

fn request() -> SourceAttachment {
    SourceAttachment {
        key: super::super::tests::key(),
        source_directory: FileIdentity { device: 1, inode: 10 },
        holder_directory: FileIdentity { device: 1, inode: 11 },
        holder_name: HOLDER_NAME.to_vec(),
        original_record: SourceRecord {
            identity: FileIdentity { device: 1, inode: 12 },
            bytes: 100,
            sha256: [4; 32],
        },
        withheld_record: SourceRecord {
            identity: FileIdentity { device: 1, inode: 13 },
            bytes: 200,
            sha256: [5; 32],
        },
    }
}
#[test]
fn source_frames_bind_original_key_records_and_context_without_record_text() {
    let value = request();
    let bytes = value.encode().unwrap();
    assert!(SourceAttachment::decode(&bytes).unwrap() == value);
    for end in 0..bytes.len() {
        assert!(SourceAttachment::decode(&bytes[..end]).is_err());
    }
    let digest = [6; 32];
    for reply in [
        SourceReply::Prepared {
            key: value.key.clone(),
            attachment_sha256: digest,
            context: super::super::tests::context(),
        },
        SourceReply::Attached {
            key: value.key.clone(),
            attachment_sha256: digest,
            context: super::super::tests::context(),
        },
        SourceReply::Refused { key: value.key.clone(), reason: "original unavailable".into() },
    ] {
        let encoded = reply.encode().unwrap();
        assert!(SourceReply::decode(&encoded, &value, digest).unwrap() == reply);
        let mut foreign = value.clone();
        foreign.key.graph[0] ^= 1;
        assert!(SourceReply::decode(&encoded, &foreign, digest).is_err());
    }
    let reply = SourceReply::Attached {
        key: value.key.clone(),
        attachment_sha256: digest,
        context: super::super::tests::context(),
    }
    .encode()
    .unwrap();
    assert!(SourceReply::decode(&reply, &value, [7; 32]).is_err());
    assert!(super::super::OutputAttachment::decode(&bytes).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(SourceAttachment::decode(&trailing).is_err());
}
#[test]
fn arbitrary_locator_alias_and_unbounded_records_refuse() {
    let value = request();
    for bytes in [0, RECORD_LIMIT + 1, u64::MAX] {
        let mut changed = value.clone();
        changed.original_record.bytes = bytes;
        assert!(changed.encode().is_err());
    }
    let mut changed = value.clone();
    changed.holder_name = b"../.trust-build-lock".to_vec();
    assert!(changed.encode().is_err());
    changed = value.clone();
    changed.original_record.identity = changed.withheld_record.identity;
    assert!(changed.encode().is_err());
    assert!(SourceAttachment::decode(&vec![0; ATTACHMENT_LIMIT + 1]).is_err());
    changed = value.clone();
    changed.withheld_record.sha256[0] ^= 1;
    assert_ne!(value.binding_preimage().unwrap(), changed.binding_preimage().unwrap());
}
