//! DATA-only codec controls; none creates a native owner or availability claim.
use super::*;

pub(crate) fn request() -> Request {
    let query = super::super::query::tests::request();
    Request {
        key: query.key,
        gnu: query.gnu,
        control_sdk_root: b"/control-sdk".to_vec(),
        source_root: b"/source".to_vec(),
        source_directory: FileIdentity { device: 1, inode: 10 },
        output_root: b"/output".to_vec(),
        output_directory: FileIdentity { device: 1, inode: 11 },
        output_lock: FileIdentity { device: 1, inode: 12 },
        configured_targo: b"/private-seed/bin/cargo".to_vec(),
        configured_compiler: b"/private-seed/bin/rustc".to_vec(),
        cargo_home: b"/physical/cargo-home".to_vec(),
        environment: vec![
            (b"CARGO_HOME".to_vec(), b"/physical/cargo-home".to_vec()),
            (b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec()),
            (b"TARGO_BUILD_WARNINGS".to_vec(), vec![]),
            (b"CALLER_OS_BYTES".to_vec(), vec![255, 254]),
        ],
        budget_ns: MAX_BUDGET_NS,
    }
}
fn envelope() -> Envelope {
    let mut manifests = vec![
        b"Cargo.toml".to_vec(),
        b"library/Cargo.toml".to_vec(),
        b"src/bootstrap/Cargo.toml".to_vec(),
    ];
    // Projection DATA only, not a mirrored list of real source recipes.
    manifests.extend((0..51).map(|index| format!("tools/t{index:03}/Cargo.toml").into_bytes()));
    manifests.sort();
    Envelope {
        manifests,
        input_paths: vec![
            b"/source/.cargo/config.toml".to_vec(),
            b"/source/Cargo.lock".to_vec(),
            b"/source/Cargo.toml".to_vec(),
        ],
    }
}

#[test]
fn whole_request_preserves_private_seed_control_sdk_spelling_and_complete_policy() {
    let request = request();
    let bytes = request.encode().unwrap();
    let decoded = Request::decode(&bytes).unwrap();
    assert!(decoded == request);
    assert_eq!(decoded.configured_targo, b"/private-seed/bin/cargo");
    assert_eq!(decoded.configured_compiler, b"/private-seed/bin/rustc");
    assert_eq!(decoded.control_sdk_root, b"/control-sdk");
    assert_eq!(decoded.cargo_home, b"/physical/cargo-home");
    assert!(decoded.environment.contains(&(b"TARGO_BUILD_WARNINGS".to_vec(), vec![])));
    assert!(!decoded.environment.iter().any(|(name, _)| name == b"CARGO_BUILD_WARNINGS"));
    assert!(decoded.hello().unwrap().windows(PURPOSE.len()).any(|part| part == PURPOSE.as_bytes()));
    let mut absent_instead_of_empty = request.clone();
    absent_instead_of_empty.environment.retain(|(name, _)| name != b"TARGO_BUILD_WARNINGS");
    assert_ne!(
        request.binding_preimage().unwrap(),
        absent_instead_of_empty.binding_preimage().unwrap()
    );
    assert!(super::super::query::Request::decode(&bytes).is_err());
    assert!(super::super::object::Request::decode(&bytes).is_err());
    assert!(Request::decode(&super::super::query::tests::request().encode().unwrap()).is_err());
}

#[test]
fn offline_profile_refuses_policy_aliases_duplicate_environment_and_invalid_originals() {
    let original = request();
    for bad in [vec![], b"false".to_vec(), b"1".to_vec()] {
        let mut request = original.clone();
        request.environment[1].1 = bad;
        assert!(request.encode().is_err());
    }
    let mut request = original.clone();
    request.environment.remove(1);
    assert!(request.encode().is_err());
    let mut request = original.clone();
    request.environment.push(request.environment[0].clone());
    assert!(request.encode().is_err());
    for name in [b"BAD=NAME".as_slice(), b"BAD\0NAME", b""] {
        let mut request = original.clone();
        request.environment.push((name.to_vec(), vec![]));
        assert!(request.encode().is_err());
    }
    for budget in [0, MAX_BUDGET_NS + 1, u64::MAX] {
        let mut request = original.clone();
        request.budget_ns = budget;
        assert!(request.encode().is_err());
    }
    for path in [b"relative".as_slice(), b"/source/../other", b"/source//other", b"/source\0"] {
        let mut request = original.clone();
        request.configured_targo = path.to_vec();
        assert!(request.encode().is_err());
    }
    let mut request = original.clone();
    request.output_directory = request.source_directory;
    assert!(request.encode().is_err());
    let mut request = original;
    request.source_directory.inode = 0;
    assert!(request.encode().is_err());
}

#[test]
fn every_envelope_row_generates_only_the_canonical_locked_offline_fetch() {
    let request = request();
    let envelope = envelope();
    assert_eq!(envelope.manifests.len(), 54);
    let bytes = envelope.encode(&request, [3; 32]).unwrap();
    assert!(Envelope::decode(&bytes, &request, [3; 32]).unwrap() == envelope);
    for (index, manifest) in envelope.manifests.iter().enumerate() {
        assert_eq!(
            envelope.fetch_arguments(&request, index).unwrap(),
            vec![
                b"fetch".to_vec(),
                b"--locked".to_vec(),
                b"--offline".to_vec(),
                b"--manifest-path".to_vec(),
                joined(&request.source_root, manifest),
            ]
        );
    }
    assert!(envelope.fetch_arguments(&request, 54).is_err());
    assert!(Envelope::decode(&bytes, &request, [4; 32]).is_err());
    let mut foreign = request.clone();
    foreign.key.sequence += 1;
    assert!(Envelope::decode(&bytes, &foreign, [3; 32]).is_err());
    for end in 0..bytes.len() {
        assert!(Envelope::decode(&bytes[..end], &request, [3; 32]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Envelope::decode(&trailing, &request, [3; 32]).is_err());
}

#[test]
fn envelope_syntax_never_accepts_escaped_duplicate_or_missing_base_roots() {
    let original = envelope();
    for path in [
        b"../Cargo.toml".as_slice(),
        b"/Cargo.toml",
        b"other.rs",
        b"x//Cargo.toml",
        b"x/./Cargo.toml",
    ] {
        let mut envelope = original.clone();
        envelope.manifests[3] = path.to_vec();
        envelope.manifests.sort();
        assert!(envelope.validate().is_err());
    }
    let mut envelope = original.clone();
    envelope.manifests[3] = envelope.manifests[2].clone();
    assert!(envelope.validate().is_err());
    let mut envelope = original.clone();
    envelope.manifests.remove(0);
    assert!(envelope.validate().is_err());
    let mut envelope = original;
    envelope.input_paths[0] = b"relative".to_vec();
    assert!(envelope.validate().is_err());
}

#[test]
fn request_frames_are_bounded_complete_and_version_separated() {
    let bytes = request().encode().unwrap();
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(Request::decode(&trailing).is_err());
    let mut version = bytes;
    // Header's eight-byte magic and eight-byte kind precede the version.
    version[23] = 2;
    assert!(Request::decode(&version).is_err());
}
