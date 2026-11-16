use super::*;
use crate::bootstrap_graph::{SourceRecord, source};
use crate::{CompletionCause, FileIdentity, Outcome};

pub(crate) fn advanced() -> Advanced {
    let input = preparation::work::tests::inputs();
    let mut targo = input.compiler.clone();
    targo.path = [input.seed_root.as_slice(), b"/bin/targo"].concat();
    let mut formatter = input.compiler.clone();
    formatter.path = [input.seed_root.as_slice(), b"/bin/trustfmt"].concat();
    let graph = input.attempt.key.graph.clone();
    let record = |inode, hash| SourceRecord {
        identity: FileIdentity { device: 1, inode },
        bytes: 100,
        sha256: [hash; 32],
    };
    Advanced {
        key: Key { attempt: input.attempt, compilation: [21; 16] },
        source: SourceAttachment {
            key: graph.clone(),
            source_directory: FileIdentity { device: 1, inode: 31 },
            holder_directory: FileIdentity { device: 1, inode: 32 },
            holder_name: source::HOLDER_NAME.to_vec(),
            original_record: record(33, 1),
            withheld_record: record(34, 2),
        },
        output: OutputAttachment {
            key: graph,
            root: FileIdentity { device: 1, inode: 35 },
            lock: FileIdentity { device: 1, inode: 36 },
        },
        gnu: input.compiler_queries[0].request.gnu.clone(),
        seed: SeedInputs {
            root: input.seed_root,
            compiler: input.compiler,
            targo,
            formatter,
            compiler_queries: input.compiler_queries,
        },
    }
}
pub(crate) fn member() -> MemberRequest {
    let advanced = advanced();
    MemberRequest {
        command: CommandSpec {
            program: advanced.seed.compiler.path,
            arg0: Some(b"selected compiler".to_vec()),
            args: vec![b"--crate-name".to_vec(), b"actual_input".to_vec(), vec![0xfe]],
            cwd: b"/source".to_vec(),
            environment: vec![(b"LANG".to_vec(), b"C".to_vec())],
        },
        key: advanced.key,
        sequence: 1,
        member: [22; 16],
        program: ProgramRole::SeedCompiler,
        gnu: advanced.gnu,
        fixed_units: 1,
        timeout_ns: 1_000_000_000,
    }
}
#[test]
fn complete_original_arguments_roundtrip_without_normalizing_forwarded_or_non_utf8_words() {
    let request = AdvanceRequest {
        attempt: advanced().key.attempt,
        original_arguments: vec![b"build".to_vec(), b"--".to_vec(), vec![0xfe], vec![]],
    };
    let bytes = request.encode().unwrap();
    assert!(AdvanceRequest::decode(&bytes).unwrap() == request);
    for end in 0..bytes.len() {
        assert!(AdvanceRequest::decode(&bytes[..end]).is_err());
    }
    let mut changed = request.clone();
    changed.original_arguments[2].push(0);
    assert!(changed.encode().is_err());
    let mut changed = request.clone();
    changed.original_arguments.clear();
    assert!(changed.encode().is_err());
    let mut trailing = bytes;
    trailing.push(0);
    assert!(AdvanceRequest::decode(&trailing).is_err());
}
#[test]
fn advanced_seed_and_original_source_output_bindings_roundtrip_as_data_only() {
    let value = advanced();
    let bytes = value.encode().unwrap();
    assert!(Advanced::decode(&bytes).unwrap() == value);
    for end in 0..bytes.len() {
        assert!(Advanced::decode(&bytes[..end]).is_err());
    }
    assert!(AdvanceRequest::decode(&bytes).is_err());
    for alias in [
        [0; 16],
        value.key.attempt.key.operation,
        value.key.attempt.key.graph.query.binding.root_attempt,
    ] {
        let mut changed = value.clone();
        changed.key.compilation = alias;
        assert!(changed.encode().is_err());
    }
    let mut changed = value.clone();
    changed.source.key.graph[0] ^= 1;
    assert!(changed.encode().is_err());
    let mut changed = value.clone();
    changed.output.key.graph[0] ^= 1;
    assert!(changed.encode().is_err());
}
#[test]
fn native_seed_role_and_query_projection_mismatches_refuse() {
    let value = advanced();
    for index in 0..9 {
        let mut changed = value.clone();
        match index {
            0 => changed.seed.targo.path = b"/foreign/targo".to_vec(),
            1 => changed.seed.formatter.sha256 = [0; 32],
            2 => changed.seed.compiler_queries.swap(0, 1),
            3 => changed.seed.compiler_queries[0].request.key.graph.graph[0] ^= 1,
            4 => changed.seed.compiler_queries[0].stdout.clear(),
            5 => changed.seed.compiler_queries[0].command.cwd.push(b'x'),
            6 => {
                changed.seed.compiler_queries[0].request.key.sequence =
                    changed.key.attempt.key.sequence
            }
            7 => {
                changed.seed.compiler_queries[1].request.key.operation =
                    changed.seed.compiler_queries[0].request.key.operation
            }
            _ => {
                changed.gnu = GnuIdentity::NumericPipe {
                    read: FileIdentity { device: 7, inode: 8 },
                    write: FileIdentity { device: 7, inode: 9 },
                }
            }
        }
        assert!(changed.encode().is_err(), "mutation {index}");
    }
}
#[test]
fn member_preserves_complete_command_and_issued_role_is_only_a_bound_reference() {
    let value = member();
    let bytes = value.encode().unwrap();
    assert!(MemberRequest::decode(&bytes).unwrap() == value);
    for end in 0..bytes.len() {
        assert!(MemberRequest::decode(&bytes[..end]).is_err());
    }
    let mut issued = value.clone();
    issued.program = ProgramRole::IssuedProgram { producer: [23; 16], artifact: 0 };
    assert!(MemberRequest::decode(&issued.encode().unwrap()).unwrap() == issued);
    // The codec exposes only a producer reference. Native execution MUST
    // refuse it without its actual successful producer/held runtime owner.
    issued.program = ProgramRole::IssuedProgram { producer: issued.member, artifact: 0 };
    assert!(issued.encode().is_err());
    assert_ne!(
        value.hello().unwrap(),
        RetireRequest { key: value.key.clone(), sequence: value.sequence, member: value.member }
            .hello()
            .unwrap()
    );
}
#[test]
fn member_rejects_ambiguous_environment_invalid_credit_bounds_and_foreign_lifetime_ids() {
    let value = member();
    for index in 0..9 {
        let mut changed = value.clone();
        match index {
            0 => changed.sequence = 0,
            1 => changed.sequence = MAX_MEMBERS + 1,
            2 => changed.fixed_units = 0,
            3 => changed.timeout_ns = 0,
            4 => changed.timeout_ns = MAX_MEMBER_NS + 1,
            5 => changed.member = changed.key.compilation,
            6 => changed.command.environment.push(changed.command.environment[0].clone()),
            7 => changed.command.args.push(vec![0]),
            _ => changed.command.cwd = b"relative".to_vec(),
        }
        assert!(changed.encode().is_err(), "mutation {index}");
    }
}
#[test]
fn only_terminal_native_retirement_observations_can_encode_and_they_do_not_construct_owners() {
    let member = member();
    let request =
        RetireRequest { key: member.key, sequence: member.sequence, member: member.member };
    let value = Retired {
        request: request.clone(),
        status: Status::Finished {
            outcome: Outcome::Exit(0),
            cause: CompletionCause::Exited,
            runtime_ns: 1,
        },
    };
    let bytes = value.encode().unwrap();
    assert!(Retired::decode(&bytes).unwrap() == value);
    assert!(RetireRequest::decode(&request.encode().unwrap()).unwrap() == request);
    for status in [Status::Attached, Status::Unknown { reason: "unresolved".into(), started: None }]
    {
        assert!(Retired { request: request.clone(), status }.encode().is_err());
    }
    for end in 0..bytes.len() {
        assert!(Retired::decode(&bytes[..end]).is_err());
    }
    assert!(MemberRequest::decode(&bytes).is_err());
}
