use super::*;

#[test]
fn workload_support_marker_declares_only_its_distinct_closed_protocol() {
    assert_eq!(&WORKLOAD_PROTOCOL_MARKER[..16], b"TRUSTWORKLOAD001");
    let fields = WORKLOAD_PROTOCOL_MARKER[16..]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|value| u64::from_be_bytes(*value))
        .collect::<Vec<_>>();
    assert_eq!(fields, [3, 6, 7, 40, 48, 1]);
    assert_ne!(WORKLOAD_PROTOCOL_MARKER, crate::resolver::RESOLVER_PROTOCOL_MARKER);
}
fn invocation() -> WorkloadInvocation {
    let file = |path: &[u8]| InputFile { path: path.into(), sha256: [7; 32] };
    WorkloadInvocation {
        invocation: [8; 16],
        observed_host_store: None,
        root: b"/sdk".into(),
        program: file(b"/sdk/bin/targo"),
        compiler: file(b"/sdk/bin/trustc"),
        cwd: b"/sources/vc".into(),
        cargo_home: b"/cache/cargo".into(),
        output_root: b"/outputs/run".into(),
        refutation_step: file(b"/sources/ay/proofs/step.rs"),
        refutation_loop: file(b"/sources/ay/proofs/loop.rs"),
        trust_spec_source: file(b"/sources/spec.rs"),
        repetitions: 3,
        timeout_ns: 3_600_000_000_000,
    }
}

#[test]
fn initial_pair_data_is_distinct_from_full_startup_and_binds_one_root_phase() {
    use host::initial;

    use crate::{
        Context, ContextQuery, ContextReply, Cpu, FileIdentity, Identity, JobBinding, Memory,
        SdkCustody, Subject,
    };
    let query = ContextQuery {
        binding: JobBinding { session: "s-ab".into(), root_attempt: [1; 16], capability: [2; 32] },
        call_attempt: [9; 16],
    };
    let request =
        initial::ReadyRequest { query: query.clone(), invocation: invocation(), phase: [10; 16] };
    let bytes = request.encode().unwrap();
    assert!(initial::ReadyRequest::decode(&bytes).unwrap() == request);
    assert!(host::ReadyRequest::decode(&bytes).is_err());
    assert!(crate::paired_qualification::host::ReadyRequest::decode(&bytes).is_err());
    let full = host::ReadyRequest { query: query.clone(), invocation: invocation() };
    assert!(initial::ReadyRequest::decode(&full.encode().unwrap()).is_err());
    for length in 0..bytes.len() {
        assert!(initial::ReadyRequest::decode(&bytes[..length]).is_err());
    }
    let mut changed = request.clone();
    changed.query.call_attempt = [11; 16];
    assert!(changed.encode().unwrap() != bytes, "whole-request binding retains the original query");
    changed.phase = [0; 16];
    assert!(changed.encode().is_err());
    let identity =
        Identity { pid: 42, birth: 7, birth_kind: crate::BirthKind::MacosWallMicroseconds };
    // Synthetic codec DATA only: no SDK, Claim or FD custody is constructed.
    let context = ContextReply {
        call_attempt: query.call_attempt,
        context: Context {
            session: query.binding.session.clone(),
            root_attempt: query.binding.root_attempt,
            host: "apple:host".into(),
            boot: "abcd".into(),
            original_root: identity,
            subject: Subject::Root { identity },
            cpu: Cpu::CooperativeShared {
                ceiling: 4,
                native_manifest: FileIdentity { device: 1, inode: 10 },
            },
            memory: Memory {
                bytes: 1 << 30,
                namespace: [1; 16],
                marker: "1-42-1".into(),
                epoch: [2; 16],
                guard: FileIdentity { device: 1, inode: 11 },
            },
            sdk: Some(SdkCustody {
                execution: b"/sdk".to_vec(),
                build: 42,
                lease_path: b"/leases/42".to_vec(),
                lease: FileIdentity { device: 1, inode: 90 },
                inherited_fd: 19,
            }),
        },
    };
    let mut reply = initial::ReadyReply {
        context,
        invocation_sha256: [12; 32],
        phase: request.phase,
        primary: host::PrimaryCpu {
            inherited_fd: 6,
            slot: 0,
            backing: FileIdentity { device: 1, inode: 13 },
        },
        keeper: host::keeper::Request {
            root_attempt: query.binding.root_attempt,
            invocation_sha256: [12; 32],
            phase: request.phase,
            nonce: [14; 16],
            native_slot: 0,
            native: FileIdentity { device: 1, inode: 13 },
            shadow: FileIdentity { device: 1, inode: 14 },
            memory_guard: FileIdentity { device: 1, inode: 11 },
            memory_epoch: [2; 16],
            memory_scope_sha256: [15; 32],
        },
    };
    let encoded = reply.encode().unwrap();
    assert!(initial::ReadyReply::decode(&encoded, &request).unwrap() == reply);
    assert!(host::ReadyReply::decode(&encoded, &full).is_err());
    let mut extra = encoded.clone();
    extra.extend_from_slice(&[0; 8]);
    assert!(initial::ReadyReply::decode(&extra, &request).is_err());
    changed.phase = [13; 16];
    assert!(initial::ReadyReply::decode(&encoded, &changed).is_err());
    reply.primary.slot = 4;
    assert!(reply.encode().is_err());
    reply.primary.slot = 0;
    reply.context.context.cpu =
        Cpu::RetainedFixed { units: 4, native_manifest: FileIdentity { device: 1, inode: 10 } };
    assert!(reply.encode().is_err(), "fixed V1 is not converted by the new codec");
}
#[test]
fn exact_invocation_roundtrip_is_data_and_old_roles_remain_closed() {
    let value = invocation();
    let frame = value.encode().unwrap();
    assert_eq!(WorkloadInvocation::decode(&frame).unwrap(), value);
    assert!(crate::Request::decode(&frame).is_err());
    assert!(crate::resolver::ResolverInvocation::decode(&frame).is_err());
    for length in 0..frame.len() {
        assert!(WorkloadInvocation::decode(&frame[..length]).is_err());
    }
    let mut extra = frame;
    extra.push(0);
    assert!(WorkloadInvocation::decode(&extra).is_err());
}
#[test]
fn normalized_bound_paths_and_exact_sdk_siblings_are_required() {
    for mode in 0..9 {
        let mut value = invocation();
        match mode {
            0 => value.root = b"/sdk/../other".into(),
            1 => value.cwd = b"relative".into(),
            2 => value.cargo_home = b"/cache//cargo".into(),
            3 => value.output_root = b"/sdk/target".into(),
            4 => value.output_root = b"/sources/vc/target".into(),
            5 => value.output_root = b"/cache/cargo/target".into(),
            6 => value.program.path = b"/different/bin/targo".into(),
            7 => value.compiler.path = b"/different/bin/trustc".into(),
            8 => value.refutation_loop.path = value.refutation_step.path.clone(),
            _ => unreachable!(),
        }
        assert!(value.encode().is_err(), "mode {mode}");
    }
}
#[test]
fn finite_population_and_invocation_identity_are_mandatory() {
    for mode in 0..4 {
        let mut value = invocation();
        match mode {
            0 => value.invocation = [0; 16],
            1 => value.repetitions = 0,
            2 => value.repetitions = WORKLOAD_MAX_REPETITIONS + 1,
            3 => value.timeout_ns = 0,
            _ => unreachable!(),
        }
        assert!(value.encode().is_err(), "mode {mode}");
    }
}
#[test]
fn continuation_cannot_cross_original_root_checkpoint_or_invocation() {
    let value = Continuation {
        invocation_sha256: [1; 32],
        root_attempt: [2; 16],
        checkpoint: 1,
        checkpoint_sha256: [3; 32],
        decision: Decision::Continue,
    };
    assert_eq!(Continuation::decode(&value.encode().unwrap()).unwrap(), value);
    value.check_binding([1; 32], [2; 16], 1, [3; 32]).unwrap();
    for mode in 0..4 {
        let mut altered = value.clone();
        match mode {
            0 => altered.invocation_sha256[0] ^= 1,
            1 => altered.root_attempt[0] ^= 1,
            2 => altered.checkpoint += 1,
            3 => altered.checkpoint_sha256[0] ^= 1,
            _ => unreachable!(),
        }
        assert!(altered.check_binding([1; 32], [2; 16], 1, [3; 32]).is_err());
    }
    let mut invalid = value.clone();
    invalid.checkpoint = 0;
    assert!(invalid.encode().is_err());
    invalid.checkpoint = WORKLOAD_MAX_CHECKPOINTS + 1;
    assert!(invalid.encode().is_err());
    invalid.checkpoint = 1;
    invalid.root_attempt = [0; 16];
    assert!(invalid.encode().is_err());
    let mut stop = value;
    stop.decision = Decision::Stop;
    assert_eq!(Continuation::decode(&stop.encode().unwrap()).unwrap(), stop);
}
