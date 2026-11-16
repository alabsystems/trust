use super::*;
use crate::{CommandSpec, Delegations, Descriptor, JobBinding};

pub(crate) fn query() -> CompilerQuery {
    CompilerQuery {
        member: Request {
            binding: JobBinding {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            member_attempt: [3; 16],
            role: Role::WorkloadQuery,
            command: CommandSpec {
                program: b"/sdk/bin/trustc".to_vec(),
                arg0: None,
                args: vec![b"-vV".to_vec()],
                cwd: b"/source".to_vec(),
                environment: vec![
                    (b"LANG".to_vec(), b"C".to_vec()),
                    (b"LC_ALL".to_vec(), b"C".to_vec()),
                    (b"CARGO".to_vec(), b"/sdk/bin/targo".to_vec()),
                    (b"RUSTC".to_vec(), b"/sdk/bin/trustc".to_vec()),
                    (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
                    (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
                ],
            },
            delegations: Delegations {
                cpu: Some(Descriptor { source: 7, target: 6 }),
                gnu: GnuTransport::None,
                fences: vec![],
            },
            timeout_ns: Some(MAX_QUERY_NS),
        },
        root: b"/sdk".to_vec(),
        program_sha256: [4; 32],
    }
}

#[test]
fn registered_original_bootstrap_is_distinct_and_cannot_claim_root_or_reuse_query_frame() {
    let query = query();
    let request = MemberOriginalRequest {
        query: crate::ContextQuery { binding: query.member.binding.clone(), call_attempt: [9; 16] },
        member_attempt: query.member.member_attempt,
    };
    let bytes = request.encode().unwrap();
    assert!(MemberOriginalRequest::decode(&bytes).unwrap() == request);
    assert!(CompilerQuery::decode(&bytes).is_err());
    assert!(MemberOriginalRequest::decode(&query.encode().unwrap()).is_err());
    let mut root = request.clone();
    root.member_attempt = request.query.binding.root_attempt;
    assert!(root.encode().is_err());
    for count in 0..bytes.len() {
        assert!(MemberOriginalRequest::decode(&bytes[..count]).is_err());
    }
}

#[test]
fn workload_queries_cannot_enter_legacy_proxy_or_resolver_dispatch() {
    let request = query();
    let bytes = request.encode().unwrap();
    assert!(CompilerQuery::decode(&bytes).unwrap() == request);
    assert!(crate::resolver::SealedResolverQueryRequest::decode(&bytes).is_err());
    assert!(crate::Call::decode(&request.member.encode().unwrap()).is_err());
    assert!(crate::Call::Member(Box::new(request.member.clone())).encode().is_err());
    assert!(
        crate::accounting::AccountedRequest {
            request: request.member.clone(),
            scope: crate::accounting::Scope::ChildAndWaitedDescendantsV1
        }
        .encode()
        .is_err()
    );
    assert!(!request.member.role.is_proxy_member());
    for count in 0..bytes.len() {
        assert!(CompilerQuery::decode(&bytes[..count]).is_err());
    }
    let mut extra = bytes;
    extra.push(0);
    assert!(CompilerQuery::decode(&extra).is_err());
    let mut old_role = request;
    old_role.member.role = Role::ResolverQuery;
    old_role.member.delegations.cpu = None;
    old_role.member.delegations.gnu = GnuTransport::NumericPipe {
        read: Descriptor { source: 7, target: 3 },
        write: Descriptor { source: 8, target: 4 },
    };
    assert!(old_role.encode().is_err());
}

#[test]
fn workload_query_has_no_producing_flags_extra_environment_or_numeric_credit() {
    for changed in 0..9 {
        let mut request = query();
        match changed {
            0 => request.member.command.args.push(b"--emit=link".to_vec()),
            1 => request.member.command.args = vec![b"@opaque".to_vec()],
            2 => request.member.command.args.extend([b"--target".to_vec(), b"foreign".to_vec()]),
            3 => request
                .member
                .command
                .environment
                .push((b"DYLD_INSERT_LIBRARIES".to_vec(), b"/foreign".to_vec())),
            4 => request.member.command.environment[4].1 = b"relative".to_vec(),
            5 => request.member.command.environment[5].1 = b"1".to_vec(),
            6 => request.member.delegations.cpu = None,
            7 => {
                request.member.delegations.gnu = GnuTransport::NumericPipe {
                    read: Descriptor { source: 8, target: 3 },
                    write: Descriptor { source: 9, target: 4 },
                }
            }
            8 => request.member.timeout_ns = Some(MAX_QUERY_NS + 1),
            _ => unreachable!(),
        }
        assert!(request.encode().is_err(), "changed {changed}");
    }
}

#[test]
fn workload_terminal_preserves_actual_cancel_signal_and_optional_observed_zero() {
    let completed = crate::MetadataCompletion {
        finished: crate::StatusFrame {
            root_attempt: [1; 16],
            member_attempt: [3; 16],
            status: crate::Status::Finished {
                outcome: crate::Outcome::Signal(9),
                cause: crate::CompletionCause::Cancelled,
                runtime_ns: 1,
            },
        },
        inputs_unchanged: Err("original input changed after actual retirement".into()),
    };
    for measured in [false, true] {
        let observation = crate::accounting::Observation {
            cpu_times: measured.then_some(crate::accounting::CpuTimes { user_ns: 0, system_ns: 0 }),
            peak_rss_bytes: measured.then_some(0),
            ..crate::accounting::Observation::uncollected()
        };
        let value = Completion {
            phase: 0,
            kind: MemberKind::CompilerQuery,
            completed: completed.clone(),
            observation,
        };
        let bytes = value.encode().unwrap();
        assert_eq!(Completion::decode(&bytes, [1; 16], [3; 16]).unwrap(), value);
        assert!(Completion::decode(&bytes, [1; 16], [4; 16]).is_err());
        assert!(Completion::decode(&completed.encode().unwrap(), [1; 16], [3; 16]).is_err());
        assert!(crate::MetadataCompletion::decode(&bytes, [1; 16], [3; 16]).is_err());
        let mut mismatched = value;
        mismatched.phase = 1;
        assert!(mismatched.encode().is_err());
    }
}
