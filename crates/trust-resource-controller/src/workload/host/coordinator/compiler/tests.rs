// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Codec/equality controls only, never a native prepared child or grant.
use super::*;
use crate::{Delegations, GnuTransport, JobBinding};

fn request() -> MemberRequest {
    MemberRequest {
        binding: JobBinding {
            session: "s-ab12".into(),
            root_attempt: [1; 16],
            capability: [9; 32],
        },
        member_attempt: [2; 16],
        role: Role::CoordinatorCompiler([3; 16]),
        command: CommandSpec {
            program: b"/sdk/bin/trustc".to_vec(),
            arg0: None,
            args: vec![b"-vV".to_vec()],
            environment: vec![(b"SEMANTIC".to_vec(), b"selected".to_vec())],
            cwd: b"/work".to_vec(),
        },
        delegations: Delegations {
            cpu: Some(Descriptor {
                source: 6,
                target: 6,
            }),
            gnu: GnuTransport::None,
            fences: Vec::new(),
        },
        timeout_ns: Some(1_000_000),
    }
}
fn prepared(request: &MemberRequest) -> CompilerPrepared {
    CompilerPrepared {
        root_attempt: request.binding.root_attempt,
        member_attempt: request.member_attempt,
        coordinator_attempt: [3; 16],
        identity: Identity {
            pid: 42,
            birth: 43,
            birth_kind: BirthKind::MacosWallMicroseconds,
        },
        command: request.command.clone(),
    }
}
#[test]
fn full_final_command_roundtrips_and_cannot_cross_attempt_image_or_command() {
    let original = request();
    original.validate().unwrap();
    let mut aliases_sdk = original.clone();
    aliases_sdk.delegations.cpu.as_mut().unwrap().target = 5;
    assert!(
        aliases_sdk.validate().is_err(),
        "compiler CPU cannot alias actual SDK5/linker5"
    );
    let mut observation = prepared(&original);
    observation
        .command
        .environment
        .push((b"ATERM_WORKLOAD_HOST_STORE_FD_V1".to_vec(), b"7".to_vec()));
    let bytes = observation.encode().unwrap();
    let decoded = CompilerPrepared::decode(&bytes, &original).unwrap();
    assert!(decoded == observation);
    for end in 0..bytes.len() {
        assert!(CompilerPrepared::decode(&bytes[..end], &original).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(CompilerPrepared::decode(&trailing, &original).is_err());
    for mutation in 0..5 {
        let mut other = original.clone();
        match mutation {
            0 => other.member_attempt = [4; 16],
            1 => other.role = Role::CoordinatorCompiler([4; 16]),
            2 => other.command.program = b"/other/compiler".to_vec(),
            3 => other.command.args.push(b"--emit=link".to_vec()),
            4 => other.command.cwd = b"/other/work".to_vec(),
            _ => unreachable!(),
        }
        assert!(CompilerPrepared::decode(&bytes, &other).is_err());
    }
    assert!(
        Plan::decode(&bytes).is_err(),
        "command DATA cannot decode as coordinator startup"
    );
    observation.command.args[0].push(0);
    assert!(observation.encode().is_err());
}
#[test]
fn compiler_selection_is_bounded_distinct_and_requires_nonzero_binding() {
    let selection = CompilerSelection {
        root_attempt: [1; 16],
        member_attempt: [2; 16],
        coordinator_attempt: [3; 16],
        prepared_sha256: [4; 32],
    };
    let bytes = selection.encode().unwrap();
    assert_eq!(CompilerSelection::decode(&bytes).unwrap(), selection);
    for end in 0..bytes.len() {
        assert!(CompilerSelection::decode(&bytes[..end]).is_err());
    }
    let mut bad = selection;
    bad.coordinator_attempt = bad.member_attempt;
    assert!(bad.encode().is_err());
    bad.coordinator_attempt = [3; 16];
    bad.prepared_sha256 = [0; 32];
    assert!(bad.encode().is_err());
}
#[cfg(feature = "client")]
#[test]
fn every_final_environment_byte_and_native_identity_changes_selection() {
    let request = request();
    let original = prepared(&request);
    let digest = original.digest().unwrap();
    let mut changed = original.clone();
    changed.command.environment[0].1.push(b'!');
    assert_ne!(changed.digest().unwrap(), digest);
    changed = original.clone();
    changed
        .command
        .environment
        .push((b"TRUST_CPU_IMPLICIT_FD".to_vec(), b"6".to_vec()));
    assert_ne!(changed.digest().unwrap(), digest);
    changed = original;
    changed.identity.birth += 1;
    assert_ne!(changed.digest().unwrap(), digest);
}
