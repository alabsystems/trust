//! SDK root observations are DATA. These cases neither construct a Keeper nor
//! qualify an actual Host query, admitted operation or completed runtime.
use std::path::Path;

use super::*;

#[test]
fn actual_original_source_offer_builds_the_production_frame_and_transfers_same_descriptions() {
    use std::os::unix::net::UnixStream;

    use build_helper::trust_repo_lock::management::{
        Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
    };
    use trust_resource_controller::Channel;
    use trust_resource_controller::bootstrap_graph::transport;

    let directory = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(directory.path()).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual source producer and wire control".into(),
            contract: "original close-only source; no Host or release grant".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let deadline = Instant::now() + Duration::from_secs(60);
    let scope =
        ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), deadline).unwrap();
    let source = scope.original_source(&root).unwrap();
    let offer = source.close_only_offer().unwrap();
    let key = diagnostic_request().key.graph;
    let (request, received) = offer
        .with_descriptions(|fds, data| {
            let request = source_request(&key, data);
            transport::check_source(&request, &fds, deadline)?;
            assert_eq!(request.source_directory, fd_identity(source.directory()?)?);
            let bytes = request.encode()?;
            assert!(SourceAttachment::decode(&bytes)? == request);
            let (left, right) = UnixStream::pair()?;
            let (mut sender, mut receiver) = (Channel::new(left)?, Channel::new(right)?);
            transport::send_source(&mut sender, &request, &fds, deadline, || {
                offer.check_current()
            })?;
            let received = transport::receive_source(&mut receiver, &request, deadline, || {
                offer.check_current()
            })?;
            Ok((request, received))
        })
        .unwrap();
    transport::check_source(&request, &received.each_ref().map(AsFd::as_fd), deadline).unwrap();
    drop(scope);
    assert!(offer.check_current().is_err(), "source owner loss must be permanent");
    // Received descriptions remain real read-only observations after owner
    // loss; they cannot mint the actual original producer or Manager authority.
    transport::check_source(&request, &received.each_ref().map(AsFd::as_fd), deadline).unwrap();
}

#[test]
fn sdk_execution_root_selects_only_its_exact_original_tool_paths() {
    let root = b"/original/sdk";
    let (observed, tool) = sdk_program(root, Path::new("/original/sdk/bin/trustc")).unwrap();
    assert_eq!(observed, Path::new("/original/sdk"));
    assert_eq!(tool, query::Tool::Compiler);
    let (_, tool) = sdk_program(root, Path::new("/original/sdk/bin/targo")).unwrap();
    assert_eq!(tool, query::Tool::Targo);
    for invalid in ["/original/bin/trustc", "/original/sdk/trustc", "/foreign/sdk/bin/targo"] {
        assert!(sdk_program(root, Path::new(invalid)).is_err());
    }
    assert!(sdk_program(b"/original/sdk/bin/targo", Path::new("/original/sdk/bin/targo")).is_err());
    assert!(sdk_program(b"relative-sdk", Path::new("relative-sdk/bin/trustc")).is_err());
}

fn diagnostic_request() -> query::Request {
    query::Request {
        key: query::OperationKey {
            graph: Key {
                query: trust_resource_controller::ContextQuery {
                    binding: trust_resource_controller::JobBinding {
                        session: "s-abcd".into(),
                        root_attempt: [1; 16],
                        capability: [9; 32],
                    },
                    call_attempt: [2; 16],
                },
                graph: [3; 16],
            },
            sequence: 1,
            operation: [4; 16],
        },
        gnu: GnuIdentity::NamedFifo {
            path: b"/not-opened/credits".to_vec(),
            backing: FileIdentity { device: 1, inode: 2 },
        },
        tool: query::Tool::Compiler,
        sdk_root: b"/sdk".to_vec(),
        program: MetadataFile {
            path: b"/sdk/bin/trustc".to_vec(),
            sha256: [5; 32],
            bytes: 7,
            device: 1,
            inode: 9,
        },
        cwd: b"/source".to_vec(),
        arguments: vec![b"--version".to_vec()],
        environment: vec![
            (b"LANG".to_vec(), b"C".to_vec()),
            (b"LC_ALL".to_vec(), b"C".to_vec()),
            (b"CARGO".to_vec(), b"/sdk/bin/targo".to_vec()),
            (b"RUSTC".to_vec(), b"/sdk/bin/trustc".to_vec()),
            (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
            (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
        ],
        timeout_ns: query::MAX_QUERY_NS,
    }
}

#[test]
fn query_request_diagnostics_preserve_strict_refusals_without_values_or_private_keys() {
    let request = diagnostic_request();
    validate_request(&request).unwrap();
    let mut extra = request.clone();
    extra.environment.push((b"PRIVATE_POLICY".to_vec(), b"must-not-be-printed".to_vec()));
    let mut late = request.clone();
    late.timeout_ns += 1;
    let mut foreign = request.clone();
    foreign.program.path = b"/foreign/secret-path".to_vec();
    let mut key = request.clone();
    key.key.sequence = 0;
    for (rejected, field) in [
        (extra, "PRIVATE_POLICY"),
        (late, "timeout_ns=60000000001"),
        (foreign, "program_binding_matches=false"),
        (key, "key_binding_valid=false"),
    ] {
        let original = rejected.validate().unwrap_err();
        let diagnostic = validate_request(&rejected).unwrap_err();
        assert_eq!(diagnostic.kind(), original.kind());
        let text = diagnostic.to_string();
        assert!(text.contains("native SDK query request validation"));
        assert!(text.contains(field), "{text}");
        for private in ["must-not-be-printed", "/foreign/secret-path", "/not-opened/credits"] {
            assert!(!text.contains(private), "{text}");
        }
    }
}

#[test]
fn query_preparation_diagnostics_retain_original_os_error_and_bound_key_names() {
    let original = io::Error::from_raw_os_error(libc::ENOTCONN);
    let kind = original.kind();
    let error = preparation_error("original GNU witnesses", None, original);
    assert_eq!(error.kind(), kind);
    assert!(error.to_string().contains("original GNU witnesses"));
    let cause = error.get_ref().unwrap().source().unwrap();
    assert_eq!(cause.downcast_ref::<io::Error>().unwrap().raw_os_error(), Some(libc::ENOTCONN));

    let mut request = diagnostic_request();
    for _ in 0..128 {
        request.environment.push((vec![b'\n'; 4096], b"secret-value".to_vec()));
    }
    let text = validate_request(&request).unwrap_err().to_string();
    assert!(text.contains("environment_count=134"));
    assert!(text.contains("\\n"));
    assert!(!text.contains('\n'));
    assert!(!text.contains("secret-value"));
    assert!(text.len() < 8192);
}
