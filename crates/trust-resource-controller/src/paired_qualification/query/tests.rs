use super::*;
use crate::{CommandSpec, Delegations, Descriptor, JobBinding, Role};

pub(crate) fn query() -> CompilerQuery {
    let invocation = crate::paired_qualification::tests::invocation();
    let consumer = &invocation.consumer;
    let mut environment = vec![
        (b"LANG".to_vec(), b"C".to_vec()),
        (b"LC_ALL".to_vec(), b"C".to_vec()),
        (b"CARGO".to_vec(), consumer.program.path.clone()),
        (b"RUSTC".to_vec(), consumer.compiler.path.clone()),
        (b"CARGO_HOME".to_vec(), consumer.cargo_home.clone()),
        (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
        (b"SCCACHE_CACHE_SIZE".to_vec(), b"50G".to_vec()),
    ];
    for key in [
        b"CC_x86_64_unknown_linux_musl".as_slice(),
        b"CXX_x86_64_unknown_linux_musl",
        b"AR_x86_64_unknown_linux_musl",
        b"RANLIB_x86_64_unknown_linux_musl",
    ] {
        let mut value = invocation.ay.root.clone();
        value.extend_from_slice(tool_suffix(key).unwrap());
        environment.push((key.to_vec(), value));
    }
    let member = Request {
        binding: JobBinding { session: "s-ab".into(), root_attempt: [1; 16], capability: [2; 32] },
        member_attempt: [3; 16],
        role: Role::WorkloadQuery,
        command: CommandSpec {
            program: consumer.compiler.path.clone(),
            arg0: None,
            args: vec![b"-vV".to_vec()],
            cwd: invocation.ay.root.clone(),
            environment,
        },
        delegations: Delegations {
            cpu: Some(Descriptor { source: 7, target: 6 }),
            gnu: GnuTransport::None,
            fences: vec![],
        },
        timeout_ns: Some(MAX_QUERY_NS),
    };
    CompilerQuery { member, invocation }
}

#[test]
fn actual_config_environment_survives_paired_codec_without_old_profile_widening() {
    let base = query();
    let bytes = base.encode().unwrap();
    assert!(CompilerQuery::decode(&bytes).unwrap() == base);
    assert!(base.member.validate().is_err());
    assert!(base.member.encode().is_err());
    assert!(crate::workload::host::CompilerQuery::decode(&bytes).is_err());
    assert!(crate::Request::decode(&bytes).is_err());
    let mut old = crate::workload::host::CompilerQuery {
        member: base.member.clone(),
        root: base.invocation.consumer.root.clone(),
        program_sha256: base.invocation.consumer.compiler.sha256,
    };
    assert!(old.encode().is_err());
    old.member.command.environment.truncate(6);
    old.encode().unwrap();
    assert!(CompilerQuery::decode(&old.encode().unwrap()).is_err());
    for cwd in [&base.invocation.consumer.cwd, &base.invocation.ay.root] {
        let mut value = base.clone();
        value.member.command.cwd = cwd.clone();
        assert!(CompilerQuery::decode(&value.encode().unwrap()).unwrap() == value);
    }
}

#[test]
fn paired_query_refuses_unknown_or_changed_environment_and_owner_inputs() {
    for mutation in 0..24 {
        let mut q = query();
        match mutation {
            0 => q.member.command.cwd = b"/source/foreign".to_vec(),
            1 => q.member.command.cwd.extend_from_slice(b"/.."),
            2 => q.member.command.program = b"/foreign/bin/trustc".to_vec(),
            3 => q.member.command.environment[0].1 = b"en_US".to_vec(),
            4 => q.member.command.environment[2].1 = b"/foreign/bin/targo".to_vec(),
            5 => q.member.command.environment[3].1 = b"/foreign/bin/trustc".to_vec(),
            6 => q.member.command.environment[4].1 = b"/foreign/home".to_vec(),
            7 => q.member.command.environment[5].1 = b"1".to_vec(),
            8 => q.member.command.environment[6].1 = vec![b'x'; 65],
            9 => q.member.command.environment[7].1 = b"/foreign/zig.sh".to_vec(),
            10 => q.member.command.environment[8].1.extend_from_slice(b"/../zig.sh"),
            11 => q.member.command.environment[9].0 = b"DYLD_INSERT_LIBRARIES".to_vec(),
            12 => q.member.command.environment[10].0 = b"CARGO_MAKEFLAGS".to_vec(),
            13 => q.member.command.environment.push(q.member.command.environment[0].clone()),
            14 => {
                q.member.command.environment.remove(0);
            }
            15 => q.member.command.environment[6].0 = b"RUSTFLAGS".to_vec(),
            16 => q.member.role = Role::Compile,
            17 => q.member.delegations.cpu = None,
            18 => {
                q.member.delegations.gnu = GnuTransport::NumericPipe {
                    read: Descriptor { source: 8, target: 3 },
                    write: Descriptor { source: 9, target: 4 },
                }
            }
            19 => q.member.delegations.fences.push(Descriptor { source: 8, target: 9 }),
            20 => q.member.timeout_ns = Some(MAX_QUERY_NS + 1),
            21 => q.member.command.args.push(b"--emit=link".to_vec()),
            22 => q.member.command.args = vec![b"@opaque".to_vec()],
            23 => q.invocation.ay.cargo_config.sha256 = [0; 32],
            _ => unreachable!(),
        }
        assert!(q.encode().is_err(), "mutation {mutation}");
    }
}

#[test]
fn paired_query_rejects_truncated_extra_unknown_and_cross_version_frames() {
    let bytes = query().encode().unwrap();
    for n in 0..bytes.len() {
        assert!(CompilerQuery::decode(&bytes[..n]).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(CompilerQuery::decode(&extra).is_err());
    for version in [0u64, 1, 3, u64::MAX] {
        let mut other = bytes.clone();
        other[16..24].copy_from_slice(&version.to_be_bytes());
        assert!(CompilerQuery::decode(&other).is_err());
    }
}

pub(crate) fn completion() -> Completion {
    Completion {
        invocation_sha256: [4; 32],
        completed: crate::MetadataCompletion {
            finished: crate::StatusFrame {
                root_attempt: [1; 16],
                member_attempt: [3; 16],
                status: crate::Status::Finished {
                    outcome: crate::Outcome::Signal(9),
                    cause: crate::CompletionCause::Cancelled,
                    runtime_ns: 1,
                },
            },
            inputs_unchanged: Err("actual changed input".into()),
        },
        observation: crate::accounting::Observation::uncollected(),
    }
}
#[test]
fn paired_retirement_requires_exact_full_binding_attempts_and_distinct_version() {
    let query = query();
    let completion = completion();
    let bytes = completion.encode().unwrap();
    assert_eq!(Completion::decode(&bytes, &query, [4; 32]).unwrap(), completion);
    assert!(Completion::decode(&bytes, &query, [5; 32]).is_err());
    let mut changed = query.clone();
    changed.member.member_attempt[0] ^= 1;
    assert!(Completion::decode(&bytes, &changed, [4; 32]).is_err());
    let mut changed = query.clone();
    changed.member.binding.root_attempt[0] ^= 1;
    assert!(Completion::decode(&bytes, &changed, [4; 32]).is_err());
    assert!(crate::workload::host::Completion::decode(&bytes, [1; 16], [3; 16]).is_err());
    assert!(crate::MetadataCompletion::decode(&bytes, [1; 16], [3; 16]).is_err());
    for n in 0..bytes.len() {
        assert!(Completion::decode(&bytes[..n], &query, [4; 32]).is_err());
    }
    let mut extra = bytes;
    extra.push(0);
    assert!(Completion::decode(&extra, &query, [4; 32]).is_err());
}

#[test]
fn process_builder_environment_policy_needs_no_synthetic_request_or_fd() {
    let query = query();
    validate_environment(&query.invocation, &query.member.command.environment).unwrap();
    let mut base = query.member.command.environment[..6].to_vec();
    validate_environment(&query.invocation, &base).unwrap();
    for mutation in 0..7 {
        let mut env = base.clone();
        match mutation {
            0 => {
                env.pop();
            }
            1 => env.push(env[0].clone()),
            2 => env.push((b"SCCACHE_CACHE_SIZE".to_vec(), b"50G\0".to_vec())),
            3 => env.push((b"DYLD_LIBRARY_PATH".to_vec(), b"/foreign".to_vec())),
            4 => env[3].1 = b"/foreign/bin/trustc".to_vec(),
            5 => env[4].1 = b"relative".to_vec(),
            6 => env.push((b"CC_x86_64_unknown_linux_musl".to_vec(), b"/foreign/zig.sh".to_vec())),
            _ => unreachable!(),
        }
        assert!(validate_environment(&query.invocation, &env).is_err(), "mutation {mutation}");
    }
    base.push((b"SCCACHE_CACHE_SIZE".to_vec(), b"50G".to_vec()));
    let mut wrong_plan = query.invocation;
    wrong_plan.ay.cargo_config.sha256 = [0; 32];
    assert!(validate_environment(&wrong_plan, &base).is_err());
}
