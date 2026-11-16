//! Projection fixtures exercise only DATA syntax/binding, never actual native
//! Host, SDK, GNU ownership, successful child execution or retirement authority.
use super::*;
use crate::{BirthKind, CompletionCause, FileIdentity, Identity, Outcome};

pub(crate) fn request() -> Request {
    Request {
        key: OperationKey {
            graph: crate::bootstrap_graph::tests::key(),
            sequence: 1,
            operation: [4; 16],
        },
        gnu: GnuIdentity::NamedFifo {
            path: b"/original/credits".to_vec(),
            backing: FileIdentity { device: 1, inode: 2 },
        },
        tool: Tool::Compiler,
        sdk_root: b"/sdk".to_vec(),
        program: MetadataFile {
            path: b"/sdk/bin/trustc".to_vec(),
            sha256: [1; 32],
            bytes: 7,
            device: 1,
            inode: 9,
        },
        cwd: b"/source".to_vec(),
        arguments: vec![
            b"--print".to_vec(),
            b"sysroot".to_vec(),
            b"--print".to_vec(),
            b"target-libdir".to_vec(),
        ],
        environment: vec![
            (b"LANG".to_vec(), b"C".to_vec()),
            (b"LC_ALL".to_vec(), b"C".to_vec()),
            (b"CARGO".to_vec(), b"/sdk/bin/targo".to_vec()),
            (b"RUSTC".to_vec(), b"/sdk/bin/trustc".to_vec()),
            (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
            (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
        ],
        timeout_ns: MAX_QUERY_NS,
    }
}
pub(crate) fn prepared(request: &Request) -> MetadataPrepared {
    MetadataPrepared {
        root_attempt: request.key.graph.query.binding.root_attempt,
        member_attempt: request.key.operation,
        root: request.sdk_root.clone(),
        policy: PREPARED_POLICY.into(),
        scope: PREPARED_SCOPE.into(),
        executable: request.program.clone(),
        runtime: vec![],
        loader_paths: vec![],
        system_dependencies: vec![],
        host: "host".into(),
        boot: "boot".into(),
    }
}
pub(crate) fn started() -> Started {
    Started {
        identity: Identity { pid: 42, birth: 7, birth_kind: BirthKind::MacosWallMicroseconds },
        monotonic_ns: 8,
        unix_ns: 9,
    }
}
pub(crate) fn terminal(request: &Request) -> Terminal {
    Terminal::Completed {
        completion: MetadataCompletion {
            finished: StatusFrame {
                root_attempt: request.key.graph.query.binding.root_attempt,
                member_attempt: request.key.operation,
                status: Status::Finished {
                    outcome: Outcome::Exit(7),
                    cause: CompletionCause::Exited,
                    runtime_ns: 8,
                },
            },
            inputs_unchanged: Ok(()),
        },
        observation: crate::accounting::Observation::uncollected(),
    }
}
#[test]
fn exact_bootstrap_forms_do_not_widen_resolver_or_admit_producing_inputs() {
    assert!(classify(Tool::Formatter, &[b"--version".to_vec()]).is_ok());
    for arguments in [
        vec![b"--check".to_vec()],
        vec![b"--version".to_vec(), b"input.rs".to_vec()],
        vec![b"--config-path".to_vec(), b"/source".to_vec()],
    ] {
        assert!(classify(Tool::Formatter, &arguments).is_err());
    }
    for arguments in [vec![b"--version".to_vec(), b"--verbose".to_vec()], request().arguments] {
        classify(Tool::Compiler, &arguments).unwrap();
        assert!(crate::resolver::classify_resolver_query(&arguments).is_err());
        for extra in [
            b"input.rs".as_slice(),
            b"--emit=link",
            b"@args",
            b"--target=custom.json",
            b"-Zcodegen-backend=/foreign",
            b"--out-dir=/outside",
        ] {
            let mut arguments = arguments.clone();
            arguments.push(extra.to_vec());
            assert!(classify(Tool::Compiler, &arguments).is_err());
        }
    }
    assert!(classify(Tool::Targo, &[b"build".to_vec()]).is_err());
    assert!(classify(Tool::Targo, &[b"--unverified".to_vec(), b"--version".to_vec()]).is_ok());
}
#[test]
fn complete_query_binding_rejects_foreign_nonce_sequence_gnu_image_environment_and_budget() {
    let request = request();
    let bytes = request.encode().unwrap();
    assert!(Request::decode(&bytes).unwrap() == request);
    assert!(request.hello().unwrap().windows(PURPOSE.len()).any(|s| s == PURPOSE.as_bytes()));
    let mut cases = Vec::new();
    let mut bad = request.clone();
    bad.key.sequence = 0;
    cases.push(bad);
    let mut bad = request.clone();
    bad.key.operation = bad.key.graph.graph;
    cases.push(bad);
    let mut bad = request.clone();
    bad.program.path = b"/configured/stage0/bin/trustc".to_vec();
    cases.push(bad);
    let mut bad = request.clone();
    bad.environment[0] = bad.environment[1].clone();
    cases.push(bad);
    let mut bad = request.clone();
    bad.environment.push((b"DYLD_LIBRARY_PATH".to_vec(), b"/foreign".to_vec()));
    cases.push(bad);
    let mut bad = request.clone();
    bad.timeout_ns = MAX_QUERY_NS + 1;
    cases.push(bad);
    for bad in cases {
        assert!(bad.encode().is_err());
    }
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Request::decode(&trailing).is_err());
    let mut different = request.clone();
    different.key.sequence += 1;
    assert_ne!(request.binding_preimage().unwrap(), different.binding_preimage().unwrap());
    different = request.clone();
    different.gnu = GnuIdentity::NumericPipe {
        read: FileIdentity { device: 0, inode: 3 },
        write: FileIdentity { device: 0, inode: 4 },
    };
    assert_ne!(request.binding_preimage().unwrap(), different.binding_preimage().unwrap());
}

#[test]
fn runtime_text_encoding_and_unknown_policy_keys_never_become_query_environment() {
    for key in [b"__CF_USER_TEXT_ENCODING".as_slice(), b"RUSTC_BOOTSTRAP", b"PRIVATE_POLICY"] {
        for value in [b"".as_slice(), b"0x1F5:0:0", b"1"] {
            for replacing in [false, true] {
                let mut request = request();
                let extra = (key.to_vec(), value.to_vec());
                if replacing {
                    request.environment[0] = extra;
                } else {
                    request.environment.push(extra);
                }
                assert!(request.validate().is_err());
                assert!(request.encode().is_err());
            }
        }
    }
}
#[test]
fn prepared_and_raw_stream_events_bind_actual_selected_image_and_full_operation() {
    let request = request();
    let digest = [7; 32];
    for event in [
        Event::Prepared(Box::new(prepared(&request))),
        Event::Started(started()),
        Event::Output { stream: Stream::Stderr, offset: 2, bytes: vec![0, 255, 1] },
        Event::Eof { stream: Stream::Stdout, bytes: 7 },
    ] {
        let bytes = event.encode(&request, digest).unwrap();
        assert_eq!(Event::decode(&bytes, &request, digest).unwrap(), event);
        assert!(Event::decode(&bytes, &request, [8; 32]).is_err());
        let mut different = request.clone();
        different.key.operation = [5; 16];
        assert!(Event::decode(&bytes, &different, digest).is_err());
        for end in 0..bytes.len() {
            assert!(Event::decode(&bytes[..end], &request, digest).is_err());
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(Event::decode(&extra, &request, digest).is_err());
    }
    let mut image = prepared(&request);
    image.executable.inode += 1;
    assert!(Event::Prepared(Box::new(image)).encode(&request, digest).is_err());
    for event in [
        Event::Output { stream: Stream::Stdout, offset: 0, bytes: vec![] },
        Event::Output { stream: Stream::Stdout, offset: 0, bytes: vec![0; MAX_CHUNK + 1] },
        Event::Output { stream: Stream::Stdout, offset: u64::MAX, bytes: vec![1] },
        Event::Eof { stream: Stream::Stdout, bytes: MAX_OUTPUT + 1 },
    ] {
        assert!(event.encode(&request, digest).is_err());
    }
}
#[test]
fn terminal_preserves_failed_status_unknown_metrics_and_refuses_old_or_misbound_results() {
    let request = request();
    let digest = [7; 32];
    let terminal = terminal(&request);
    let bytes = terminal.encode(&request, digest).unwrap();
    assert_eq!(Terminal::decode(&bytes, &request, digest).unwrap(), terminal);
    let Terminal::Completed { completion, observation } = &terminal else { unreachable!() };
    assert!(matches!(
        completion.finished.status,
        Status::Finished { outcome: Outcome::Exit(7), .. }
    ));
    assert_eq!(observation.cpu_times, None);
    assert_eq!(observation.peak_rss_bytes, None);
    assert!(Terminal::decode(&completion.encode().unwrap(), &request, digest).is_err());
    let mut different = request.clone();
    different.key.sequence += 1;
    assert!(Terminal::decode(&bytes, &different, digest).is_err());
    different = request.clone();
    if let GnuIdentity::NamedFifo { backing, .. } = &mut different.gnu {
        backing.inode += 1;
    }
    assert!(Terminal::decode(&bytes, &different, digest).is_err());
    for end in 0..bytes.len() {
        assert!(Terminal::decode(&bytes[..end], &request, digest).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Terminal::decode(&trailing, &request, digest).is_err());
    for terminal in [
        Terminal::Refused { reason: "unsupported original image".into() },
        Terminal::Unknown { reason: "native retirement unavailable".into() },
    ] {
        let bytes = terminal.encode(&request, digest).unwrap();
        assert_eq!(Terminal::decode(&bytes, &request, digest).unwrap(), terminal);
    }
}

#[test]
fn dependency_planner_is_closed_pure_source_form_with_distinct_actual_program_role() {
    let mut value = request();
    value.tool = Tool::DependencyPlanner;
    value.sdk_root = b"/python".to_vec();
    value.program.path = b"/python/bin/python3.14".to_vec();
    value.arguments = vec![
        b"-I".to_vec(),
        b"-S".to_vec(),
        b"-B".to_vec(),
        b"/source/scripts/bootstrap_dependency_closure.py".to_vec(),
        b"plan".to_vec(),
        b"--repo-root".to_vec(),
        b"/source".to_vec(),
    ];
    value
        .environment
        .retain(|(key, _)| matches!(key.as_slice(), b"LANG" | b"LC_ALL" | b"CARGO_HOME"));
    assert!(Request::decode(&value.encode().unwrap()).unwrap() == value);
    for index in 0..value.arguments.len() {
        let mut changed = value.clone();
        changed.arguments[index] = b"replacement".to_vec();
        assert!(changed.encode().is_err());
    }
    let mut changed = value.clone();
    changed.environment.push((b"PYTHONPATH".to_vec(), b"/other".to_vec()));
    assert!(changed.encode().is_err());
    let mut changed = value;
    changed.tool = Tool::Compiler;
    assert!(changed.encode().is_err());
}
