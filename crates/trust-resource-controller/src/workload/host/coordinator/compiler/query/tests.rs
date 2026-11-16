// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Pure command-construction controls; these create no admitted native owner.
use super::*;

fn binding() -> JobBinding {
    JobBinding {
        session: "s-ab12".into(),
        root_attempt: [1; 16],
        capability: [2; 32],
    }
}
fn command() -> CommandSpec {
    CommandSpec {
        program: b"/sdk/bin/trustc".to_vec(),
        arg0: None,
        args: vec![
            b"-".to_vec(),
            b"--crate-name".to_vec(),
            b"___".to_vec(),
            b"--print=cfg".to_vec(),
        ],
        cwd: b"/original/package".to_vec(),
        environment: vec![
            (b"CARGO".to_vec(), b"/outputs/changed-targo".to_vec()),
            (b"RUSTC".to_vec(), b"/sdk/bin/trustc".to_vec()),
            (b"ENV_USED_BY_RUST".to_vec(), vec![0xff, b'=', b'!']),
        ],
    }
}
fn value<'a>(command: &'a CommandSpec, name: &[u8]) -> Option<&'a [u8]> {
    command
        .environment
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.as_slice())
}
#[test]
fn closed_query_preserves_semantics_and_installs_only_its_original_transport() {
    let original = command();
    let mut proposed = original.clone();
    proposed.environment.extend([
        (
            b"ATERM_RESOURCE_JOB_V3".to_vec(),
            b"caller locator is DATA".to_vec(),
        ),
        (b"TRUST_CPU_IMPLICIT_FD".to_vec(), b"99".to_vec()),
        (b"TRUST_CPU_HANDOFF".to_vec(), b"foreign original".to_vec()),
        (
            b"CARGO_MAKEFLAGS".to_vec(),
            b"--jobserver-auth=98,99".to_vec(),
        ),
    ]);
    let projected = compiler_query_command(&binding(), &proposed, b"/held/aterm", &[]).unwrap();
    let unpolluted = compiler_query_command(&binding(), &original, b"/held/aterm", &[]).unwrap();
    assert!(
        projected == unpolluted,
        "caller transport cannot be forwarded as an original"
    );
    assert_eq!(projected.program, original.program);
    assert_eq!(projected.args, original.args);
    assert_eq!(projected.arg0, None);
    assert_eq!(projected.cwd, original.cwd);
    for (name, bytes) in &original.environment {
        assert_eq!(value(&projected, name), Some(bytes.as_slice()));
    }
    assert_eq!(
        value(&projected, b"ATERM_RESOURCE_INSPECTOR"),
        Some(b"/held/aterm".as_slice())
    );
    assert_eq!(
        value(&projected, b"ATERM_SDK_LEASE_V3"),
        Some(b"5".as_slice())
    );
    assert_eq!(
        value(&projected, b"ATERM_WORKLOAD_CPU_FDS_V1"),
        Some(b"6".as_slice())
    );
    assert_eq!(
        value(&projected, b"ATERM_WORKLOAD_HOST_STORE_FD_V1"),
        Some(b"7".as_slice())
    );
    assert_eq!(
        value(&projected, b"TRUST_CPU_IMPLICIT_FD"),
        None,
        "the workload adopter owns this original, not implicit adoption"
    );
    assert_eq!(value(&projected, b"TRUST_CPU_HANDOFF"), None);
    assert_eq!(value(&projected, b"CARGO_MAKEFLAGS"), None);
    let mut changed = original;
    changed.environment[2].1.push(b'?');
    assert!(
        compiler_query_command(&binding(), &changed, b"/held/aterm", &[]).unwrap() != projected,
        "ordinary inherited bytes remain full semantic input"
    );
}

#[test]
fn held_native_constructor_inputs_change_the_complete_query_command() {
    let original = command();
    let projected = compiler_query_command(&binding(), &original, b"/held/aterm", &[]).unwrap();
    for variant in 0..3 {
        let mut root = binding();
        match variant {
            0 => root.session = "s-ab13".into(),
            1 => root.root_attempt[0] += 1,
            2 => root.capability[0] += 1,
            _ => unreachable!(),
        }
        assert!(
            compiler_query_command(&root, &original, b"/held/aterm", &[]).unwrap() != projected
        );
    }
    assert!(
        compiler_query_command(&binding(), &original, b"/other/held-aterm", &[]).unwrap()
            != projected
    );
    let runtime = vec![(b"DYLD_LIBRARY_PATH".to_vec(), b"/held/sdk/lib".to_vec())];
    let with_runtime =
        compiler_query_command(&binding(), &original, b"/held/aterm", &runtime).unwrap();
    assert!(with_runtime != projected);
    assert_eq!(
        value(&with_runtime, b"DYLD_LIBRARY_PATH"),
        Some(b"/held/sdk/lib".as_slice())
    );
    assert_eq!(value(&projected, b"DYLD_LIBRARY_PATH"), None);
}

#[test]
fn query_projection_refuses_producing_private_loader_and_ambiguous_commands() {
    for name in [
        b"ATERM_UNRECOGNIZED".as_slice(),
        b"aterm_resource_job_v3",
        b"TRUST_CPU_OTHER",
        b"DYLD_LIBRARY_PATH",
        b"LD_PRELOAD",
    ] {
        let mut proposed = command();
        proposed
            .environment
            .push((name.to_vec(), b"caller supplied".to_vec()));
        assert!(compiler_query_command(&binding(), &proposed, b"/held/aterm", &[]).is_err());
    }
    for variant in 0..7 {
        let mut proposed = command();
        match variant {
            0 => proposed.args.push(b"--emit=metadata".to_vec()),
            1 => proposed.args.push(b"@arguments".to_vec()),
            2 => proposed.arg0 = Some(proposed.program.clone()),
            3 => proposed.environment.push(proposed.environment[0].clone()),
            4 => proposed.cwd.push(0),
            5 => proposed.program = vec![b'/'; crate::MAX_FIELD + 1],
            6 => proposed.environment[0].1.push(0),
            _ => unreachable!(),
        }
        assert!(compiler_query_command(&binding(), &proposed, b"/held/aterm", &[]).is_err());
    }
    assert!(compiler_query_command(&binding(), &command(), b"relative-aterm", &[]).is_err());
    for runtime in [
        vec![(b"LD_PRELOAD".to_vec(), b"/foreign/library".to_vec())],
        vec![(b"DYLD_LIBRARY_PATH".to_vec(), Vec::new())],
        vec![(b"DYLD_LIBRARY_PATH".to_vec(), b"/held\0/other".to_vec())],
    ] {
        assert!(compiler_query_command(&binding(), &command(), b"/held/aterm", &runtime).is_err());
    }
}
#[test]
fn actual_gnu_advertisement_changes_full_producing_command_without_losing_semantics() {
    let mut original = command();
    original.args = vec![
        b"--resource-worker-v3".to_vec(),
        b"--resource-subgroups-v3".to_vec(),
        b"input.rs".to_vec(),
        b"--emit=metadata".to_vec(),
    ];
    let one = compiler_producing_command(
        &binding(),
        &original,
        b"/held/aterm",
        &[],
        b"live original endpoint one",
    )
    .unwrap();
    let two = compiler_producing_command(
        &binding(),
        &original,
        b"/held/aterm",
        &[],
        b"different live original endpoint",
    )
    .unwrap();
    assert!(one != two);
    assert_eq!(one.args, original.args);
    assert_eq!(one.cwd, original.cwd);
    for (key, bytes) in &original.environment {
        assert_eq!(value(&one, key), Some(bytes.as_slice()));
    }
    assert!(compiler_query_command(&binding(), &original, b"/held/aterm", &[]).is_err());
    assert!(
        compiler_producing_command(&binding(), &command(), b"/held/aterm", &[], b"endpoint")
            .is_err()
    );
    original.environment.push((
        b"TRUST_JOBSERVER_UNKNOWN".to_vec(),
        b"not an original".to_vec(),
    ));
    assert!(
        compiler_producing_command(&binding(), &original, b"/held/aterm", &[], b"endpoint")
            .is_err()
    );
}
