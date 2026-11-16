//! Codec observations only; these fixtures create no original input owners.
use super::*;

fn request() -> ConfigurationAttachment {
    ConfigurationAttachment {
        key: crate::bootstrap_graph::tests::key(),
        sequence: 1,
        relative: b"config/bootstrap.toml".to_vec(),
        file: FileIdentity { device: 1, inode: 8 },
        bytes: 16,
        sha256: [9; 32],
        modified: Timestamp { seconds: -1, nanoseconds: 2 },
        changed: Timestamp { seconds: 3, nanoseconds: 4 },
        input_remaining_ns: 60_000_000_000,
    }
}

#[test]
fn complete_configuration_binding_is_distinct_and_rejects_partial_or_trailing_frames() {
    let value = request();
    let frame = value.encode().unwrap();
    assert!(ConfigurationAttachment::decode(&frame).unwrap() == value);
    for end in 0..frame.len() {
        assert!(ConfigurationAttachment::decode(&frame[..end]).is_err());
    }
    let mut extra = frame.clone();
    extra.push(0);
    assert!(ConfigurationAttachment::decode(&extra).is_err());
    assert!(crate::bootstrap_graph::SourceAttachment::decode(&frame).is_err());
    let mut other = value.clone();
    other.sha256[0] ^= 1;
    assert_ne!(value.binding_preimage().unwrap(), other.binding_preimage().unwrap());
    other = value.clone();
    other.key.graph[0] ^= 1;
    assert_ne!(value.binding_preimage().unwrap(), other.binding_preimage().unwrap());
    other = value.clone();
    other.input_remaining_ns -= 1;
    assert_ne!(value.binding_preimage().unwrap(), other.binding_preimage().unwrap());
    other = value.clone();
    other.sequence += 1;
    assert_ne!(value.binding_preimage().unwrap(), other.binding_preimage().unwrap());
}

#[test]
fn acknowledgement_binds_the_complete_configuration_and_original_context() {
    let value = request();
    let digest = [17; 32];
    for reply in [
        ConfigurationReply::Prepared {
            key: value.key.clone(),
            attachment_sha256: digest,
            remaining_input_ns: 1_000_000_000,
            context: crate::bootstrap_graph::tests::context(),
        },
        ConfigurationReply::Attached {
            key: value.key.clone(),
            attachment_sha256: digest,
            remaining_input_ns: 1_000_000_000,
            context: crate::bootstrap_graph::tests::context(),
        },
        ConfigurationReply::Refused {
            key: value.key.clone(),
            reason: "original input unavailable".into(),
        },
    ] {
        let frame = reply.encode().unwrap();
        assert!(ConfigurationReply::decode(&frame, &value, digest).unwrap() == reply);
        let mut foreign = value.clone();
        foreign.key.graph[0] ^= 1;
        assert!(ConfigurationReply::decode(&frame, &foreign, digest).is_err());
    }
    let frame = ConfigurationReply::Attached {
        key: value.key.clone(),
        attachment_sha256: digest,
        remaining_input_ns: 1_000_000_000,
        context: crate::bootstrap_graph::tests::context(),
    }
    .encode()
    .unwrap();
    assert!(ConfigurationReply::decode(&frame, &value, [18; 32]).is_err());
}

#[test]
fn selectors_are_bounded_normal_relative_components() {
    assert!(relative(b"bootstrap.toml"));
    assert!(relative(b"config/space and ' quotes.toml"));
    assert!(relative(&[0xff]));
    for path in [b"".as_slice(), b"/a", b"a/", b"a//b", b"./a", b"a/../b", b"a\0b"] {
        assert!(!relative(path));
    }
    assert!(!relative(&vec![b'a'; MAX_COMPONENT_BYTES + 1]));
    assert!(!relative("a/".repeat(MAX_COMPONENTS).as_bytes()));
    assert!(relative(format!("{}a", "a/".repeat(MAX_COMPONENTS - 1)).as_bytes()));
    let mut value = request();
    value.bytes = MAX_BYTES + 1;
    assert!(value.encode().is_err());
    value = request();
    value.file.inode = 0;
    assert!(value.encode().is_err());
    for input_remaining_ns in [0, MAX_INPUT_NS + 1, u64::MAX] {
        value = request();
        value.input_remaining_ns = input_remaining_ns;
        assert!(value.encode().is_err());
    }
    for sequence in [0, MAX_FILES as u64 + 1, u64::MAX] {
        value = request();
        value.sequence = sequence;
        assert!(value.encode().is_err());
    }
}

#[test]
fn aggregate_reservations_are_ordered_bounded_and_never_refunded_by_a_refusal() {
    let mut budget = ConfigurationBudget::default();
    let mut first = request();
    first.bytes = MAX_BYTES - 10;
    budget.reserve(&first).unwrap();
    assert_eq!(budget.remaining_bytes(), 10);
    let mut second = request();
    second.sequence = 2;
    second.bytes = 11;
    assert!(budget.reserve(&second).is_err());
    assert_eq!(budget.remaining_bytes(), 10);
    assert_eq!(budget.remaining_files(), MAX_FILES - 1);
    assert!(budget.reserve(&first).is_err());
    second.bytes = 10;
    budget.reserve(&second).unwrap();
    assert_eq!(budget.remaining_bytes(), 0);
    second.sequence = 3;
    second.bytes = 0;
    assert!(budget.reserve(&second).is_err());
    assert_eq!(budget.remaining_files(), MAX_FILES - 2);
}

#[test]
fn bounded_count_remains_independent_of_empty_file_sizes() {
    let mut budget = ConfigurationBudget::default();
    let mut value = request();
    value.bytes = 0;
    for sequence in 1..=MAX_FILES as u64 {
        value.sequence = sequence;
        budget.reserve(&value).unwrap();
    }
    assert_eq!(budget.remaining_files(), 0);
    assert_eq!(budget.remaining_bytes(), MAX_BYTES);
    assert!(budget.reserve(&value).is_err());
}
