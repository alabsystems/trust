use super::*;
use crate::{CommandSpec, Delegations, Descriptor, JobBinding};

fn invocation() -> ResolverInvocation {
    ResolverInvocation {
        host_store: None,
        root: b"/sealed".to_vec(),
        program: b"/sealed/bin/targo".to_vec(),
        program_sha256: [1; 32],
        compiler: b"/sealed/bin/trustc".to_vec(),
        compiler_sha256: [2; 32],
        cwd: b"/frozen/source".to_vec(),
        cargo_home: b"/owned/cargo".to_vec(),
    }
}

fn query() -> SealedResolverQueryRequest {
    SealedResolverQueryRequest {
        member: Request {
            binding: JobBinding {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            member_attempt: [3; 16],
            role: Role::ResolverQuery,
            command: CommandSpec {
                program: b"/sealed/bin/trustc".to_vec(),
                arg0: None,
                args: vec![b"-vV".to_vec()],
                cwd: b"/frozen/source".to_vec(),
                environment: vec![
                    (b"LANG".to_vec(), b"C".to_vec()),
                    (b"LC_ALL".to_vec(), b"C".to_vec()),
                    (b"CARGO".to_vec(), b"/sealed/bin/targo".to_vec()),
                    (b"RUSTC".to_vec(), b"/sealed/bin/trustc".to_vec()),
                    (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
                    (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
                ],
            },
            delegations: Delegations {
                cpu: None,
                fences: vec![],
                gnu: GnuTransport::NumericPipe {
                    read: Descriptor { source: 5, target: 3 },
                    write: Descriptor { source: 6, target: 4 },
                },
            },
            timeout_ns: Some(RESOLVER_MAX_QUERY_NS),
        },
        root: b"/sealed".to_vec(),
        program_sha256: [4; 32],
    }
}

#[test]
fn invocation_is_exact_sealed_sdk_and_semantic_metadata_without_free_form_flags() {
    let value = invocation();
    let bytes = value.encode().unwrap();
    assert_eq!(ResolverInvocation::decode(&bytes).unwrap(), value);
    assert_eq!(
        RESOLVER_SEMANTIC_ARGUMENTS,
        &[b"metadata".as_slice(), b"--locked", b"--offline", b"--format-version", b"1"]
    );
    for end in 0..bytes.len() {
        assert!(ResolverInvocation::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(ResolverInvocation::decode(&trailing).is_err());
    for change in 0..5 {
        let mut invalid = value.clone();
        match change {
            0 => invalid.program = b"/other/bin/targo".to_vec(),
            1 => invalid.compiler = b"/sealed/bin/wrapper".to_vec(),
            2 => invalid.root = b"/sealed/../other".to_vec(),
            3 => invalid.cwd = b"relative".to_vec(),
            _ => invalid.cargo_home = b"/owned//cargo".to_vec(),
        }
        assert!(invalid.encode().is_err());
    }
}

#[test]
fn resolver_query_is_new_role5_without_linker4_or_metadata3_reinterpretation() {
    let value = query();
    let bytes = value.encode().unwrap();
    assert!(SealedResolverQueryRequest::decode(&bytes).unwrap() == value);
    assert_eq!(RESOLVER_REQUEST_ROLE, 5);
    assert_eq!(crate::METADATA_REQUEST_ROLE, 3);
    assert_eq!(crate::MACHO_LINKER_REQUEST_ROLE, 4);
    assert!(crate::Call::decode(&value.member.encode().unwrap()).is_err());
    assert!(crate::SealedMetadataRequest::decode(&bytes).is_err());
    assert!(Request::decode(&bytes).is_err());
    for end in 0..bytes.len() {
        assert!(SealedResolverQueryRequest::decode(&bytes[..end]).is_err());
    }
    assert_eq!(&RESOLVER_PROTOCOL_MARKER[..16], b"TRUSTRESOLVER001");
    assert_eq!(u64::from_be_bytes(RESOLVER_PROTOCOL_MARKER[24..32].try_into().unwrap()), 5);
}

#[test]
fn resolver_query_requires_actual_closed_command_environment_and_fixed_borrow_descriptions() {
    for change in 0..10 {
        let mut invalid = query();
        match change {
            0 => invalid.member.role = Role::SealedMetadata,
            1 => invalid.member.role = Role::MetadataProbe,
            2 => invalid.member.command.program = b"/sealed/bin/wrapper".to_vec(),
            3 => invalid.member.command.args.push(b"--emit=link".to_vec()),
            4 => invalid
                .member
                .command
                .environment
                .push((b"DYLD_INSERT_LIBRARIES".to_vec(), b"/foreign".to_vec())),
            5 => invalid
                .member
                .command
                .environment
                .push((b"CARGO".to_vec(), b"/other/bin/targo".to_vec())),
            6 => invalid.member.delegations.cpu = Some(Descriptor { source: 7, target: 5 }),
            7 => invalid.member.timeout_ns = None,
            8 => invalid.member.delegations.gnu = GnuTransport::None,
            _ => invalid.member.command.arg0 = Some(b"other".to_vec()),
        }
        assert!(invalid.encode().is_err(), "mutation{change}");
    }
    let hello = query().hello().unwrap();
    assert!(std::str::from_utf8(&hello).unwrap().contains("sealed-resolver-query-v1"));
    assert!(!std::str::from_utf8(&hello).unwrap().contains(&"02".repeat(32)));
}
