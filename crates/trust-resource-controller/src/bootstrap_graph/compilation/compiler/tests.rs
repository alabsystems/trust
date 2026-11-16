//! DATA controls only: no constructed compiler/native Root/retirement owner.
use super::*;

#[test]
fn paired_linker_declaration_is_distinct_from_compiler_and_public_profiles() {
    let declaration = BOOTSTRAP_FIXED_LINKER_PROTOCOL_MARKER;
    assert_eq!(&declaration[..16], b"TRUSTBTFIXLLD001");
    let (words, tail) = declaration[16..].as_chunks::<8>();
    assert!(tail.is_empty());
    let fields: Vec<u64> = words.iter().copied().map(u64::from_be_bytes).collect();
    assert_eq!(fields, [1, 1, 1, 1, 1, 0]);
    assert_ne!(declaration, BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER);
    assert_ne!(declaration, crate::workload::WORKLOAD_MEMBER_PROTOCOL_MARKER);
}

use crate::{BirthKind, CompletionCause, Outcome};

pub(crate) fn adopted() -> Adopted {
    let member = super::super::tests::member();
    let seed = super::super::tests::advanced().seed;
    let mut paired = seed.compiler.clone();
    paired.path = [seed.root.as_slice(), b"/bin/rust-lld"].concat();
    paired.inode += 1;
    let mut query = member.key.attempt.key.graph.query.clone();
    query.call_attempt = [51; 16];
    Adopted {
        request: AdoptRequest {
            query,
            gnu: member.gnu,
            compiler: Identity {
                pid: 101,
                birth: 202,
                birth_kind: BirthKind::MacosWallMicroseconds,
            },
        },
        member: RetireRequest { key: member.key, sequence: member.sequence, member: member.member },
        adoption: [52; 16],
        inputs: CompilerInputs { root: seed.root, compiler: seed.compiler, paired_linker: paired },
        remaining_ns: 60_000_000_000,
    }
}
pub(crate) fn linker() -> PairedLinkerRequest {
    PairedLinkerRequest {
        adopted: adopted(),
        generation: 1,
        member: [53; 16],
        command: CommandSpec {
            program: b"/held-seed/lib/rustlib/aarch64-apple-darwin/bin/gcc-ld/ld64.lld".to_vec(),
            arg0: None,
            args: vec![b"-o".to_vec(), b"/owned/output".to_vec(), vec![0xfe]],
            environment: vec![(b"LANG".to_vec(), b"C".to_vec())],
            cwd: b"/source".to_vec(),
        },
        timeout_ns: 60_000_000_000,
    }
}
#[test]
fn compiler_adoption_preserves_actual_request_identity_and_rejects_foreign_full_binding() {
    let adopted = adopted();
    let bytes = adopted.encode().unwrap();
    assert!(Adopted::decode(&bytes).unwrap() == adopted);
    let bytes = adopted.request.encode().unwrap();
    assert!(AdoptRequest::decode(&bytes).unwrap() == adopted.request);
    for end in 0..bytes.len() {
        assert!(AdoptRequest::decode(&bytes[..end]).is_err());
    }
    let mut changed = adopted.clone();
    changed.request.compiler.birth += 1;
    assert!(!adopted.same_owner(&changed));
    let mut changed = adopted.clone();
    changed.request.query.binding.root_attempt = [99; 16];
    assert!(changed.validate().is_err());
    let mut changed = adopted.clone();
    changed.remaining_ns -= 1;
    assert!(adopted.same_owner(&changed), "remaining time is restriction data, not a new adoption");
    for remaining_ns in [0, MAX_MEMBER_NS + 1] {
        changed.remaining_ns = remaining_ns;
        assert!(changed.encode().is_err());
    }
    for identity in [
        Identity { pid: 1, ..adopted.request.compiler },
        Identity { birth: 0, ..adopted.request.compiler },
    ] {
        let mut changed = adopted.request.clone();
        changed.compiler = identity;
        assert!(changed.encode().is_err());
    }
}
#[test]
fn adoption_and_paired_linker_reject_all_aliased_parent_identities() {
    let value = adopted();
    let graph = &value.member.key.attempt.key.graph;
    let aliases = [
        [0; 16],
        value.member.member,
        value.member.key.compilation,
        value.member.key.attempt.key.operation,
        graph.graph,
        graph.query.call_attempt,
        graph.query.binding.root_attempt,
        value.request.query.call_attempt,
    ];
    for alias in aliases {
        let mut changed = value.clone();
        changed.adoption = alias;
        assert!(changed.encode().is_err());
    }
    for alias in aliases.into_iter().chain([value.adoption]) {
        let mut changed = linker();
        changed.member = alias;
        assert!(changed.encode().is_err());
    }
    for generation in [0, MAX_MEMBERS + 1] {
        let mut changed = linker();
        changed.generation = generation;
        assert!(changed.encode().is_err());
    }
}
#[test]
fn paired_linker_complete_command_roundtrips_and_retirement_cannot_retarget_its_loan() {
    let request = linker();
    let bytes = request.encode().unwrap();
    assert!(PairedLinkerRequest::decode(&bytes).unwrap() == request);
    for end in 0..bytes.len() {
        assert!(PairedLinkerRequest::decode(&bytes[..end]).is_err());
    }
    let retired = request.retirement();
    let bytes = retired.encode().unwrap();
    assert!(LinkerRetire::decode(&bytes).unwrap() == retired);
    let mut changed = retired.clone();
    changed.adopted.remaining_ns -= 1;
    assert!(retired.same_loan(&changed));
    for index in 0..4 {
        let mut changed = retired.clone();
        match index {
            0 => changed.adopted.adoption = [99; 16],
            1 => changed.generation += 1,
            2 => changed.member = [99; 16],
            _ => changed.adopted.request.compiler.birth += 1,
        }
        assert!(!retired.same_loan(&changed));
    }
    let mut changed = request.clone();
    changed.command.environment.push((b"LANG".to_vec(), b"unissued duplicate".to_vec()));
    assert!(changed.encode().is_err());
    let mut changed = request;
    changed.command.cwd.push(0);
    assert!(changed.encode().is_err());
}
#[test]
fn private_paired_linker_refuses_unheld_runtime_inputs_before_submission() {
    for controls in [
        vec![b"--load-pass-plugin".to_vec(), b"/foreign/pass.dylib".to_vec()],
        vec![b"--load-pass-plugin=/foreign/pass.dylib".to_vec()],
        vec![b"-mllvm".to_vec(), b"-load=/foreign/pass.dylib".to_vec()],
        vec![b"-mllvm=-load=/foreign/pass.dylib".to_vec()],
    ] {
        let mut wrong = linker();
        wrong.command.args.extend(controls);
        assert!(wrong.validate().is_err());
        assert!(wrong.hello().is_err());
        assert!(wrong.encode().is_err());
    }
    let ordinary = linker();
    crate::linker::validate_arguments(&ordinary.command.args).unwrap();
    ordinary.validate().unwrap();
}

#[test]
fn real_closure_data_preserves_failed_target_or_postcheck_instead_of_success_alias() {
    let request = linker().retirement();
    for status in [
        Status::Finished {
            outcome: Outcome::Exit(0),
            cause: CompletionCause::HostFault,
            runtime_ns: 1,
        },
        Status::Finished {
            outcome: Outcome::Exit(7),
            cause: CompletionCause::Exited,
            runtime_ns: 2,
        },
        Status::Refused { reason: "held paired LLD refused".into() },
    ] {
        let value = LinkerRetired { request: request.clone(), status };
        let bytes = value.encode().unwrap();
        assert!(LinkerRetired::decode(&bytes).unwrap() == value);
        for end in 0..bytes.len() {
            assert!(LinkerRetired::decode(&bytes[..end]).is_err());
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert!(LinkerRetired::decode(&trailing).is_err());
    }
    for status in
        [Status::Attached, Status::Unknown { reason: "closure missing".into(), started: None }]
    {
        assert!(LinkerRetired { request: request.clone(), status }.encode().is_err());
    }
}

#[test]
fn compiler_inputs_keep_private_runtime_and_paired_file_binding_without_control_sdk_alias() {
    let original = adopted();
    for mutation in 0..5 {
        let mut value = original.clone();
        match mutation {
            0 => value.inputs.root = b"/control-sdk".to_vec(),
            1 => value.inputs.paired_linker.path = b"/control-sdk/bin/rust-lld".to_vec(),
            2 => value.inputs.paired_linker.sha256 = [0; 32],
            3 => value.inputs.paired_linker = value.inputs.compiler.clone(),
            _ => value.inputs.compiler.path = b"/foreign/compiler".to_vec(),
        }
        assert!(value.encode().is_err());
    }
    let mut changed = original.clone();
    changed.inputs.paired_linker.inode += 1;
    assert!(!original.same_owner(&changed));
}

#[test]
fn private_compiler_declaration_is_distinct_from_public_worker_and_standalone_profile() {
    let declaration = BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER;
    assert_eq!(&declaration[..16], b"TRUSTBTFIXCOMP01");
    let (fields, remainder) = declaration[16..].as_chunks::<8>();
    assert!(remainder.is_empty());
    let fields: Vec<u64> = fields.iter().map(|value| u64::from_be_bytes(*value)).collect();
    assert_eq!(fields, [1, 1, 0x76, 2, 1, 0]);
    assert_ne!(declaration, crate::workload::WORKLOAD_MEMBER_PROTOCOL_MARKER);
    assert_ne!(&declaration[..16], b"TRUSTBTFIX000001");
}
